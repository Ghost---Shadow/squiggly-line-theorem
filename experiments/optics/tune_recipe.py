"""
Choose the training recipe ONCE, on a validation split of 5000 training digits, with the three-plate polarizer stack
(kind pol_stack3, seed 0). Each candidate is trained for TUNE_EPOCHS epochs on the first TUNE_DIGITS digits of the fit set
(a shortened run, to keep the search cheap) and scored by accuracy on the 5000 validation digits. The best one is written to
experiments/optics/results/recipe.json and is used for every device in run_sweep.py.
Run: /c/ProgramData/miniconda3/python.exe experiments/optics/tune_recipe.py
"""
import itertools, json, sys, time
from pathlib import Path
import torch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import optics

DEVICE = "cuda" if torch.cuda.is_available() else "cpu"
TUNE_DIGITS, TUNE_EPOCHS = 25000, 1
GRID = dict(learning_rate=[0.02, 0.05, 0.1], temperature=[10.0, 30.0, 100.0], light_weight=[1.0, 5.0])
RESULTS = Path(__file__).resolve().parent / "results"


def main():
    RESULTS.mkdir(exist_ok=True)
    data = optics.load_mnist(device=DEVICE)
    fit_x, fit_y, val_x, val_y = optics.split_validation(*data["train"])
    fit_x, fit_y = fit_x[:TUNE_DIGITS], fit_y[:TUNE_DIGITS]
    rows = []
    for lr, temp, lw in itertools.product(*GRID.values()):
        started = time.time()
        model, _ = optics.train_device("pol_stack3", 0, fit_x, fit_y, TUNE_EPOCHS, learning_rate=lr,
                                       temperature=temp, light_weight=lw, device=DEVICE)
        res = optics.evaluate(model, val_x, val_y)
        row = dict(learning_rate=lr, temperature=temp, light_weight=lw, validation_accuracy=res["accuracy"],
                   delivered=res["delivered"], seconds=time.time() - started)
        rows.append(row)
        print(row, flush=True)
    best = max(rows, key=lambda row: row["validation_accuracy"])
    out = dict(chosen={k: best[k] for k in GRID}, candidates=rows, tune_digits=TUNE_DIGITS, tune_epochs=TUNE_EPOCHS,
               validation_digits=int(val_x.shape[0]), kind="pol_stack3", seed=0)
    (RESULTS / "recipe.json").write_text(json.dumps(out, indent=2))
    print("chosen", out["chosen"])


if __name__ == "__main__":
    main()
