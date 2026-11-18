"""
Train every device for seeds 0, 1, 2 on the fit set (the 60000 training digits minus the 5000 validation digits used by
tune_recipe.py), evaluate on the 10000 test digits, and write experiments/optics/results/sweep.json and one trained
angle map per device kind, plate_<device>.npy (seed 0; shape (plates, 96, 96), radians).

The recipe (learning rate, temperature, light weight) is read from results/recipe.json, chosen once on validation data.
Every device uses the same recipe and the same number of epochs. pixels_linear uses Adam at the fixed learning rate 1e-3
(a reference; it was not tuned).

Run: /c/ProgramData/miniconda3/python.exe experiments/optics/run_sweep.py [epochs]
"""
import json, sys, time
from pathlib import Path
import numpy as np
import torch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import optics

DEVICE = "cuda" if torch.cuda.is_available() else "cpu"
RESULTS = Path(__file__).resolve().parent / "results"
SEEDS = (0, 1, 2)
TRAINED = ["linear3", "circular1", "pol_stack3", "pol_stack3_short_gap", "phase1", "phase3", "pixels_linear"]
PIXELS_LINEAR_LR = 1e-3


def get_all_plates(model):
    """All plates of a device, shape (plates, 96, 96), radians."""
    return np.stack([optics.get_angle_map(model, index) for index in range(len(model.plates))])


def main():
    epochs = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    recipe = json.loads((RESULTS / "recipe.json").read_text())["chosen"]
    started = time.time()
    data = optics.load_mnist(device=DEVICE)
    fit_x, fit_y, val_x, val_y = optics.split_validation(*data["train"])
    test_x, test_y = data["test"]
    design_gap, sideways = optics.get_design_gap()
    out = dict(
        settings=dict(epochs=epochs, batch_size=100, optimizer="Adam, cosine decay of the learning rate to zero",
                      recipe=recipe, pixels_linear_learning_rate=PIXELS_LINEAR_LR, fit_digits=int(fit_x.shape[0]),
                      test_digits=int(test_x.shape[0]), seeds=list(SEEDS),
                      geometry=dict(pixel=optics.PIXEL, digit_pixels=optics.DIGIT_PIXELS,
                                    aperture_pixels=optics.APERTURE_PIXELS, grid_pixels=optics.GRID_PIXELS,
                                    window_pixels=optics.WINDOW_PIXELS, window_centres=optics.WINDOW_CENTRES,
                                    design_gap=design_gap, largest_sideways_move=sideways)),
        torch_version=torch.__version__, device=str(DEVICE), runs={})
    if DEVICE == "cuda":
        out["gpu"] = torch.cuda.get_device_name(0)

    def save():
        out["wall_seconds"] = time.time() - started
        (RESULTS / "sweep.json").write_text(json.dumps(out, indent=2))

    def log(message):
        print(message, flush=True)

    for seed in SEEDS:
        for kind in TRAINED:
            lr = PIXELS_LINEAR_LR if kind == "pixels_linear" else recipe["learning_rate"]
            model, history = optics.train_device(
                kind, seed, fit_x, fit_y, epochs, learning_rate=lr, temperature=recipe["temperature"],
                light_weight=recipe["light_weight"], device=DEVICE, design_gap=design_gap, log=log)
            res = optics.evaluate(model, test_x, test_y)
            res["history"] = history
            out["runs"][f"{kind}/{seed}"] = res
            log(f"{kind} seed {seed}: {({k: v for k, v in res.items() if k != 'history'})}")
            if seed == 0 and kind != "pixels_linear":
                np.save(RESULTS / f"plate_{kind}.npy", get_all_plates(model))
            save()
        model = optics.Device("pol_stack3_untrained", seed, design_gap=design_gap, device=DEVICE)
        res = optics.evaluate(model, test_x, test_y)
        out["runs"][f"pol_stack3_untrained/{seed}"] = res
        log(f"pol_stack3_untrained seed {seed}: {res}")
        if seed == 0:
            np.save(RESULTS / "plate_pol_stack3_untrained.npy", get_all_plates(model))
        save()
    log(f"wall time {out['wall_seconds']:.0f} s")


if __name__ == "__main__":
    main()
