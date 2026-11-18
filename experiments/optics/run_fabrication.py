"""
Round 2: plates that can be made. Writes experiments/optics/results/fabrication.json, every trained plate as
results/fab_<name>_seed<k>.npy (shape (plates, 96, 96), radians, the trained parameters before any rounding), and the
8-bit PNG export of the 4-level plates of seed 0.

Same recipe (results/recipe.json), 4 epochs, seeds 0, 1, 2, full test set, as in round 1 (run_sweep.py).
Run: /c/ProgramData/miniconda3/python.exe experiments/optics/run_fabrication.py

Fixed before the run
  * Determinism check: the retrained free linear3 and pol_stack3 are compared with the round-1 accuracy in sweep.json.
    A difference above DETERMINISM_LIMIT = 0.005 in test accuracy is called a problem.
  * Shifts are along +x (columns): plates 2 and 3 of the stack, or the one plate of linear3, move by s pixels, zero-filled
    (the plate and its aperture move; nothing wraps). Plate 1 of the stack stays in the plane of the digit.
  * Levels: {45, 135} degrees and {0, 45, 90, 135} for linear3; 4, 8, 16 evenly spaced levels from 0 over 180 degrees for the
    stack. Angles are taken mod 180 degrees, and the nearest level is nearest round the half-turn.
  * Angle error is Gaussian, added to every angle (after rounding, for the rounded plates), 5 draws per setting.
"""
import json
import math
import sys
import time
from pathlib import Path

import numpy as np
import torch
from PIL import Image

sys.path.insert(0, str(Path(__file__).resolve().parent))
import optics

DEVICE = "cuda" if torch.cuda.is_available() else "cpu"
RESULTS = Path(__file__).resolve().parent / "results"
SEEDS = (0, 1, 2)
EPOCHS = 4
DETERMINISM_LIMIT = 0.005
NOISE_DEGREES = (2, 5, 10)
NOISE_DRAWS = 5
SHIFTS = (1, 2, 4)
SHIFT_TRAIN_RANGE = 2
LEVELS_LINEAR_ROUND = {"2level_45_135": [45.0, 135.0], "4level": [0.0, 45.0, 90.0, 135.0]}
LEVELS_STACK_ROUND = {"4level": 4, "8level": 8, "16level": 16}
FOUR_LEVELS = optics.get_levels(degrees=[0.0, 45.0, 90.0, 135.0])
TWO_LEVELS = optics.get_levels(degrees=[45.0, 135.0])


def main():
    started = time.time()
    recipe = json.loads((RESULTS / "recipe.json").read_text())["chosen"]
    sweep = json.loads((RESULTS / "sweep.json").read_text())
    design_gap = sweep["settings"]["geometry"]["design_gap"]
    data = optics.load_mnist(device=DEVICE)
    fit_x, fit_y, _, _ = optics.split_validation(*data["train"])
    test_x, test_y = data["test"]
    out = dict(settings=dict(epochs=EPOCHS, recipe=recipe, seeds=list(SEEDS), determinism_limit=DETERMINISM_LIMIT,
                             noise_degrees=list(NOISE_DEGREES), noise_draws=NOISE_DRAWS, shifts=list(SHIFTS),
                             shift_train_range=SHIFT_TRAIN_RANGE, shift_direction="+x (columns); plates 2 and 3 of the stack, the one plate of linear3",
                             levels_linear_round={k: v for k, v in LEVELS_LINEAR_ROUND.items()},
                             levels_stack_round=LEVELS_STACK_ROUND, design_gap=design_gap),
               torch_version=torch.__version__, device=str(DEVICE), runs={})
    if DEVICE == "cuda":
        out["gpu"] = torch.cuda.get_device_name(0)

    def save():
        out["wall_seconds"] = time.time() - started
        (RESULTS / "fabrication.json").write_text(json.dumps(out, indent=2))

    def log(message):
        print(message, flush=True)

    def accuracy(model, images=test_x, labels=test_y):
        return optics.evaluate(model, images, labels)["accuracy"]

    def train(name, kind, seed, **extra):
        model, history = optics.train_device(kind, seed, fit_x, fit_y, EPOCHS, learning_rate=recipe["learning_rate"],
                                             temperature=recipe["temperature"], light_weight=recipe["light_weight"],
                                             device=DEVICE, design_gap=design_gap, log=log, **extra)
        np.save(RESULTS / f"fab_{name}_seed{seed}.npy",
                np.stack([optics.get_angle_map(model, index) for index in range(len(model.plates))]))
        return model, history

    def with_shifts(model, kind, shift):
        model.shifts = [(0, 0), (0, shift), (0, shift)] if kind == "pol_stack3" else [(0, shift)]
        result = accuracy(model)
        model.shifts = None
        return result

    def with_noise(model, std, seed, kind):
        draws = []
        for draw in range(NOISE_DRAWS):
            generator = torch.Generator().manual_seed(3000 + 100 * seed + 10 * draw + int(std))
            model.set_noise(std, generator)
            draws.append(accuracy(model))
        model.set_noise(None)
        return dict(draws=draws, mean=float(np.mean(draws)))

    # theta -> theta + 180 degrees leaves the output unchanged (a plate axis and its opposite are the same plate)
    probe = optics.Device("pol_stack3", 0, design_gap=design_gap, device=DEVICE)
    with torch.no_grad():
        before, _ = probe.get_screen(test_x[:20])
        for table in probe.plates:
            table.add_(math.pi)
        after, _ = probe.get_screen(test_x[:20])
    out["half_turn_check"] = dict(max_difference=float((before - after).abs().max()), max_brightness=float(before.max()))
    log(f"theta + 180 degrees: {out['half_turn_check']}")

    for seed in SEEDS:
        run = {}
        out["runs"][str(seed)] = run
        for kind in ("linear3", "pol_stack3"):
            # 1. free plates, retrained exactly as in round 1
            free, history = train(f"free_{kind}", kind, seed)
            free_accuracy = accuracy(free)
            stored = sweep["runs"][f"{kind}/{seed}"]["accuracy"]
            run[f"free_{kind}"] = dict(accuracy=free_accuracy, round1_accuracy=stored, difference=free_accuracy - stored, history=history)
            log(f"free {kind} seed {seed}: {free_accuracy:.4f} (round 1: {stored:.4f})")
            # 2. rounding after training, no retraining
            rounded = {}
            options = ({k: optics.get_levels(degrees=v) for k, v in LEVELS_LINEAR_ROUND.items()} if kind == "linear3"
                       else {k: optics.get_levels(count=v) for k, v in LEVELS_STACK_ROUND.items()})
            for label, levels in options.items():
                free.set_levels(levels)
                rounded[label] = accuracy(free)
            free.set_levels(None)
            run[f"free_{kind}"]["rounded_after_training"] = rounded
            # 4. angle error on the free plate
            run[f"free_{kind}"]["angle_error"] = {str(std): with_noise(free, std, seed, kind) for std in NOISE_DEGREES}
            # 5. shifts on the free plate
            run[f"free_{kind}"]["shift"] = {str(shift): with_shifts(free, kind, shift) for shift in SHIFTS}
            log(f"  rounded {rounded}; noise {({k: v['mean'] for k, v in run[f'free_{kind}']['angle_error'].items()})}; "
                f"shift {run[f'free_{kind}']['shift']}")
            save()
            del free

        # 3. rounding in the training
        for name, kind, levels in (("ste2_linear3", "linear3", TWO_LEVELS), ("ste4_linear3", "linear3", FOUR_LEVELS),
                                   ("ste4_pol_stack3", "pol_stack3", FOUR_LEVELS)):
            model, history = train(name, kind, seed, levels=levels)
            entry = dict(accuracy=accuracy(model), history=history)
            log(f"{name} seed {seed}: {entry['accuracy']:.4f}")
            if name == "ste4_pol_stack3":
                entry["angle_error"] = {str(std): with_noise(model, std, seed, kind) for std in NOISE_DEGREES}
            if seed == 0 and name.startswith("ste4"):
                entry["accuracy_first2000"] = accuracy(model, test_x[:2000], test_y[:2000])
                export_plates(model, kind)
            run[name] = entry
            save()
            del model

        # 6. trained with a random shift of every plate at every step
        model, history = train("shift_pol_stack3", "pol_stack3", seed, shift_range=SHIFT_TRAIN_RANGE)
        run["shift_pol_stack3"] = dict(history=history, shift={str(shift): with_shifts(model, "pol_stack3", shift) for shift in (0,) + SHIFTS})
        log(f"shift-trained stack seed {seed}: {run['shift_pol_stack3']['shift']}")
        save()
        del model
    log(f"wall time {out['wall_seconds']:.0f} s")


def export_plates(model, kind):
    """The 4-level plates of seed 0 as 8-bit PNG: pixel value = level index x 60 (0, 60, 120, 180)."""
    for index, table in enumerate(model.plates):
        level_index = optics.get_level_index(table.detach().cpu(), FOUR_LEVELS).numpy().astype(np.uint8)
        Image.fromarray(level_index * 60, mode="L").save(RESULTS / f"plate_{kind}_4level_{index}.png")


if __name__ == "__main__":
    main()
