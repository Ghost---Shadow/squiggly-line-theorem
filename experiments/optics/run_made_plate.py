"""
Round 3: two runs (predictions R1 and R2 in docs/networks/polarizer-classifier.md). Writes results/made_plate.json and
results/made_<name>_seed<k>.npy (the trained parameters, shape (plates, 96, 96), radians).
Same recipe (results/recipe.json), 4 epochs, seeds 0, 1, 2, full test set.

R1  linear3 with the angles rounded to 45 and 135 degrees: the light is computed from the ROUNDED angle and the slope is taken at
    the UNROUNDED angle (optics.Device.slope_at_unrounded). Evaluated with the rounded angles in the plain forward pass.
    Described, not judged: the share of the angles under the digit within 10 degrees of a rounding boundary (0 or 90 degrees).
R2  pol_stack3 trained with the standard four-level rounding of round 2 and a fresh random shift of every plate in [-2, 2] pixels
    (rows and columns) at every step. Evaluated four ways: (a) four levels; (b) plus plates 2 and 3 moved 2 px (+x);
    (c) plus 5 degrees of Gaussian angle error (mean of 5 draws); (d) (b) and (c) together (mean of 5 draws).
Run: /c/ProgramData/miniconda3/python.exe experiments/optics/run_made_plate.py
"""
import json
import sys
import time
from pathlib import Path

import numpy as np
import torch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import optics

DEVICE = "cuda" if torch.cuda.is_available() else "cpu"
RESULTS = Path(__file__).resolve().parent / "results"
SEEDS = (0, 1, 2)
EPOCHS = 4
TWO_LEVELS = optics.get_levels(degrees=[45.0, 135.0])
FOUR_LEVELS = optics.get_levels(degrees=[0.0, 45.0, 90.0, 135.0])
NOISE_DEGREES, NOISE_DRAWS, SHIFT = 5, 5, 2


def main():
    started = time.time()
    recipe = json.loads((RESULTS / "recipe.json").read_text())["chosen"]
    design_gap = json.loads((RESULTS / "sweep.json").read_text())["settings"]["geometry"]["design_gap"]
    data = optics.load_mnist(device=DEVICE)
    fit_x, fit_y, _, _ = optics.split_validation(*data["train"])
    test_x, test_y = data["test"]
    out = dict(settings=dict(epochs=EPOCHS, recipe=recipe, seeds=list(SEEDS), noise_degrees=NOISE_DEGREES, noise_draws=NOISE_DRAWS,
                             shift=SHIFT, shift_train_range=2, design_gap=design_gap),
               torch_version=torch.__version__, device=str(DEVICE), runs={})

    def save():
        out["wall_seconds"] = time.time() - started
        (RESULTS / "made_plate.json").write_text(json.dumps(out, indent=2))

    def log(message):
        print(message, flush=True)

    def accuracy(model):
        return optics.evaluate(model, test_x, test_y)["accuracy"]

    def train(name, kind, seed, **extra):
        model, history = optics.train_device(kind, seed, fit_x, fit_y, EPOCHS, learning_rate=recipe["learning_rate"],
                                             temperature=recipe["temperature"], light_weight=recipe["light_weight"],
                                             device=DEVICE, design_gap=design_gap, log=log, **extra)
        np.save(RESULTS / f"made_{name}_seed{seed}.npy", np.stack([optics.get_angle_map(model, i) for i in range(len(model.plates))]))
        return model, history

    def noisy_accuracy(model, seed):
        draws = []
        for draw in range(NOISE_DRAWS):
            generator = torch.Generator().manual_seed(4000 + 100 * seed + 10 * draw + NOISE_DEGREES)
            model.set_noise(NOISE_DEGREES, generator)
            draws.append(accuracy(model))
        model.set_noise(None)
        return dict(draws=draws, mean=float(np.mean(draws)))

    for seed in SEEDS:
        run = out["runs"][str(seed)] = {}
        # R1
        model, history = train("slope_ste2_linear3", "linear3", seed, levels=TWO_LEVELS, slope_at_unrounded=True)
        angles = np.degrees(model.plates[0].detach().cpu().numpy()) % 180.0
        under_digit = angles[20:76, 20:76]
        to_boundary = np.minimum.reduce([np.abs(under_digit - 0.0), np.abs(under_digit - 90.0), np.abs(under_digit - 180.0)])
        run["r1_linear3_slope_at_unrounded"] = dict(
            accuracy=accuracy(model), share_within_10_deg_of_boundary=float((to_boundary < 10.0).mean()),
            share_within_10_deg_of_boundary_whole_plate=float((np.minimum.reduce([np.abs(angles), np.abs(angles - 90.0), np.abs(angles - 180.0)]) < 10.0).mean()),
            share_at_45_or_135_under_digit=float((np.minimum(np.abs(under_digit - 45.0), np.abs(under_digit - 135.0)) < 1e-3).mean()),
            history=history)
        log(f"R1 seed {seed}: {run['r1_linear3_slope_at_unrounded']['accuracy']:.4f}, within 10 deg of a boundary "
            f"{run['r1_linear3_slope_at_unrounded']['share_within_10_deg_of_boundary']:.3f}")
        save()
        del model
        # R2
        model, history = train("shift_ste4_pol_stack3", "pol_stack3", seed, levels=FOUR_LEVELS, shift_range=2)
        model.set_levels(FOUR_LEVELS)
        entry = dict(history=history)
        entry["a_four_levels"] = accuracy(model)
        model.shifts = [(0, 0), (0, SHIFT), (0, SHIFT)]
        entry["b_shifted_2px"] = accuracy(model)
        entry["d_shifted_and_error"] = noisy_accuracy(model, seed)
        model.shifts = None
        entry["c_error"] = noisy_accuracy(model, seed)
        run["r2_shift_ste4_pol_stack3"] = entry
        log(f"R2 seed {seed}: a {entry['a_four_levels']:.4f} b {entry['b_shifted_2px']:.4f} c {entry['c_error']['mean']:.4f} d {entry['d_shifted_and_error']['mean']:.4f}")
        save()
        del model
    log(f"wall time {out['wall_seconds']:.0f} s")


if __name__ == "__main__":
    main()
