"""
Round 4: an ordinary lamp (predictions S1 to S3 in docs/networks/polarizer-classifier.md). Writes results/lamp.json and
results/lamp_<device>_seed<k>.npy (trained parameters, (plates, 96, 96), radians).

Lamp light: every pixel under the digit glows on its own (horizontally polarized), brightness adds on the screen.
  * Training: optics random_phase option (an independent random phase at every input pixel, fresh for every digit at every step).
  * Evaluation: the exact table W[j, x] (optics.Device.get_lamp_table), score_j = sum_x W[j, x] strength(x)^2.
Trained: pol_stack3 and linear3, seeds 0, 1, 2, same recipe, 4 epochs. Also evaluated under the lamp: the round-2 free plates
(fab_free_pol_stack3_seed<k>.npy, fab_free_linear3_seed<k>.npy), which were trained for laser light.

Checks stated before the run
  * Monte Carlo (can fail): for the lamp-trained stack of seed 0 and the first 200 test digits, the window sums of the exact table
    must agree with the mean over 256 random-phase draws to within 5 standard errors (the standard error of the mean from the 256
    draws), for every one of the 200 x 10 entries (plus 1e-9 for entries with no spread).
  * Every entry of W is >= 0 (by construction, cannot fail).
Run: /c/ProgramData/miniconda3/python.exe experiments/optics/run_lamp.py
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
MC_DIGITS, MC_DRAWS, MC_TOLERANCE = 200, 256, 5.0


def main():
    started = time.time()
    recipe = json.loads((RESULTS / "recipe.json").read_text())["chosen"]
    design_gap = json.loads((RESULTS / "sweep.json").read_text())["settings"]["geometry"]["design_gap"]
    data = optics.load_mnist(device=DEVICE)
    fit_x, fit_y, _, _ = optics.split_validation(*data["train"])
    test_x, test_y = data["test"]
    out = dict(settings=dict(epochs=EPOCHS, recipe=recipe, seeds=list(SEEDS), design_gap=design_gap, monte_carlo=dict(
        digits=MC_DIGITS, draws=MC_DRAWS, tolerance_standard_errors=MC_TOLERANCE)),
        torch_version=torch.__version__, device=str(DEVICE), runs={})

    def save():
        out["wall_seconds"] = time.time() - started
        (RESULTS / "lamp.json").write_text(json.dumps(out, indent=2))

    def log(message):
        print(message, flush=True)

    for seed in SEEDS:
        run = out["runs"][str(seed)] = {}
        # laser-trained plates under the lamp
        for kind in ("pol_stack3", "linear3"):
            model = optics.Device(kind, seed, design_gap=design_gap, device=DEVICE)
            saved = np.load(RESULTS / f"fab_free_{kind}_seed{seed}.npy")
            with torch.no_grad():
                for index, table in enumerate(model.plates):
                    table.copy_(torch.tensor(saved[index], dtype=torch.float32))
            run[f"laser_trained_{kind}_under_lamp"] = optics.evaluate_lamp(model, test_x, test_y)
            log(f"laser-trained {kind} seed {seed} under the lamp: {run[f'laser_trained_{kind}_under_lamp']}")
        save()
        # lamp-trained
        for kind in ("pol_stack3", "linear3"):
            torch.manual_seed(5000 + seed)
            model, history = optics.train_device(kind, seed, fit_x, fit_y, EPOCHS, learning_rate=recipe["learning_rate"],
                                                 temperature=recipe["temperature"], light_weight=recipe["light_weight"],
                                                 device=DEVICE, design_gap=design_gap, log=log, random_phase=True)
            np.save(RESULTS / f"lamp_{kind}_seed{seed}.npy", np.stack([optics.get_angle_map(model, i) for i in range(len(model.plates))]))
            table = model.get_lamp_table()
            entry = optics.evaluate_lamp(model, test_x, test_y, table)
            entry["history"] = history
            entry["min_W"] = float(table[0].min())
            run[f"lamp_trained_{kind}"] = entry
            log(f"lamp-trained {kind} seed {seed}: {({k: v for k, v in entry.items() if k != 'history'})}")
            if kind == "pol_stack3" and seed == 0:
                out["monte_carlo_check"] = monte_carlo_check(model, table, test_x[:MC_DIGITS])
                log(f"Monte Carlo check: {out['monte_carlo_check']}")
            save()
            del model
    log(f"wall time {out['wall_seconds']:.0f} s")


@torch.no_grad()
def monte_carlo_check(model, table, digits):
    """Exact window sums sum_x W[j, x] a(x)^2 against the mean over random-phase draws of the screen windows."""
    window_table, _ = table
    strength = digits.repeat_interleave(2, dim=1).repeat_interleave(2, dim=2).reshape(digits.shape[0], -1)
    exact = ((strength ** 2).double() @ window_table.double().T)
    model.random_phase = True
    model.train()
    draws = []
    for _ in range(MC_DRAWS):
        window_sums, _, _ = model(digits)
        draws.append(window_sums.double())
    model.random_phase = False
    model.eval()
    draws = torch.stack(draws)
    mean = draws.mean(dim=0)
    standard_error = draws.std(dim=0, unbiased=True) / MC_DRAWS ** 0.5
    deviation = (mean - exact).abs()
    within = deviation <= MC_TOLERANCE * standard_error + 1e-9
    return dict(entries=int(within.numel()), entries_outside=int((~within).sum()),
                largest_deviation_in_standard_errors=float((deviation / standard_error.clamp_min(1e-30)).max()),
                mean_deviation_in_standard_errors=float((deviation / standard_error.clamp_min(1e-30)).mean()),
                relative_difference_of_total=float((mean.sum() - exact.sum()).abs() / exact.sum()),
                passed=bool(within.all()))


if __name__ == "__main__":
    main()
