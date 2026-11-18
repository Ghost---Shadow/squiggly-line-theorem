"""
Make the picture of what the trained three-plate polarizer stack does to the digits 0 to 9.

Run from the repository root (CPU only, deterministic):

    /c/ProgramData/miniconda3/python.exe experiments/optics/make_digit_animation.py

Writes
    book/figures/12-optical-digits.gif   ten frames, digits 0..9 in order, looping, 1.2 s a frame
    book/figures/12-optical-digits.png   all ten digits at once (two rows of five input/screen pairs)

Which images: for each digit d the FIRST image labelled d in the MNIST test set. The rule is fixed
here and is not changed by how an image looks, and a wrongly read one stays in.

Device: kind "pol_stack3", seed 0, the saved plates results/plate_pol_stack3.npy, design gap read
from results/sweep.json (the same rebuild as in polarizer_classifier.ipynb).

Left panel: the strength of the light (|E|, as the digit sends it) over the 96 x 96 plate aperture.
Right panel: the brightness |E_x|^2 + |E_y|^2 on the screen over the same 96 x 96 region. Every
screen panel is scaled to ITS OWN brightest point (so the colours of two panels cannot be compared
with each other; the printed shares can). Window j is the answer for the digit j.
The "share" printed is the light in the brightest window divided by the light in all ten windows.
"""
import json
import sys
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import torch
from matplotlib.patches import Rectangle
from PIL import Image

REPO = Path.cwd()
OPTICS_DIR = REPO / "experiments" / "optics"
RESULTS = OPTICS_DIR / "results"
FIGURES = REPO / "book" / "figures"
sys.path.insert(0, str(OPTICS_DIR))
sys.path.insert(0, str(REPO / "experiments" / "part1"))
import optics
from common import use_style

torch.set_default_dtype(torch.float32)      # common.py sets float64; every tensor here says its dtype anyway
use_style()
GIF_PATH = FIGURES / "12-optical-digits.gif"
PNG_PATH = FIGURES / "12-optical-digits.png"
FRAME_MILLISECONDS = 1200
HALF = optics.WINDOW_PIXELS // 2
LIGHT_MAP = "mako"          # single hue, dark to light, for the light in
SCREEN_MAP = "rocket"       # dark to light, for the screen
GREEN = "#55a868"


def load_plates():
    design_gap = json.loads((RESULTS / "sweep.json").read_text())["settings"]["geometry"]["design_gap"]
    model = optics.Device("pol_stack3", seed=0, design_gap=design_gap, device="cpu")
    saved = np.load(RESULTS / "plate_pol_stack3.npy")
    with torch.no_grad():
        for index, table in enumerate(model.plates):
            table.copy_(torch.tensor(saved[index], dtype=torch.float32))
    return model


def first_of_each_digit():
    images, labels = optics.load_mnist(root=str(OPTICS_DIR / "data"), device="cpu")["test"]
    indices = [int((labels == digit).nonzero()[0, 0]) for digit in range(10)]
    return indices, images[indices], labels[indices]


def run_all():
    model = load_plates()
    indices, images, labels = first_of_each_digit()
    results = []
    with torch.no_grad():
        for position in range(10):
            digit_image = images[position:position + 1]
            field = model.make_input(digit_image)
            low, size = model.start, model.aperture_pixels
            light_in = field.abs().pow(2).sum(dim=1)[0, low:low + size, low:low + size].sqrt().numpy()
            screen, _ = model.get_screen(digit_image)
            crop = screen[0, low:low + size, low:low + size]
            window_light = (crop.reshape(1, -1) @ model.window_masks)[0].numpy()
            results.append(dict(digit=int(labels[position]), index=indices[position], light_in=light_in,
                                screen=crop.numpy(), windows=window_light, brightest=int(window_light.argmax()),
                                share=float(window_light.max() / window_light.sum())))
    return results


def draw_windows(axis, brightest, label_size, thin=0.8, thick=2.6):
    for index, (row, column) in enumerate(optics.WINDOW_CENTRES):
        top_left = (column - HALF - 0.5, row - HALF - 0.5)
        axis.add_patch(Rectangle(top_left, 2 * HALF, 2 * HALF, fill=False, edgecolor="white", linewidth=thin))
        axis.text(column - 0.5, row - HALF - 1.5, str(index), color="white", fontsize=label_size,
                  ha="center", va="bottom", fontweight="bold")
    row, column = optics.WINDOW_CENTRES[brightest]
    axis.add_patch(Rectangle((column - HALF - 0.5, row - HALF - 0.5), 2 * HALF, 2 * HALF, fill=False,
                             edgecolor=GREEN, linewidth=thick))


def plain(axis):
    axis.grid(False)
    axis.set_xticks([])
    axis.set_yticks([])


def make_frame(result):
    figure, (left, right) = plt.subplots(1, 2, figsize=(9.0, 4.5), dpi=100)
    left.imshow(result["light_in"], cmap=LIGHT_MAP, vmin=0, vmax=1)
    right.imshow(result["screen"], cmap=SCREEN_MAP, vmin=0, vmax=result["screen"].max())
    draw_windows(right, result["brightest"], label_size=10)
    for axis in (left, right):
        plain(axis)
    left.set_title("Light in", fontsize=13)
    right.set_title("Light on the screen", fontsize=13)
    left.set_xlabel(f"the digit shown: {result['digit']}", fontsize=13)
    right.set_xlabel(f"brightest window: {result['brightest']}", fontsize=13)
    figure.text(0.5, 0.012, "each screen is scaled to its own brightest point; plates: 3 polarizer plates, trained",
                ha="center", va="bottom", fontsize=8, color="0.35")
    figure.subplots_adjust(left=0.03, right=0.97, top=0.9, bottom=0.14, wspace=0.08)
    figure.canvas.draw()
    pixels = np.asarray(figure.canvas.buffer_rgba())[:, :, :3].copy()
    plt.close(figure)
    return Image.fromarray(pixels)


def make_still(results):
    figure = plt.figure(figsize=(18.0, 5.6), dpi=100)
    grid = figure.add_gridspec(2, 10, left=0.005, right=0.995, top=0.93, bottom=0.08, wspace=0.06, hspace=0.35)
    for position, result in enumerate(results):
        row, pair = divmod(position, 5)
        left = figure.add_subplot(grid[row, 2 * pair])
        right = figure.add_subplot(grid[row, 2 * pair + 1])
        left.imshow(result["light_in"], cmap=LIGHT_MAP, vmin=0, vmax=1)
        right.imshow(result["screen"], cmap=SCREEN_MAP, vmin=0, vmax=result["screen"].max())
        draw_windows(right, result["brightest"], label_size=7, thin=0.6, thick=2.0)
        plain(left)
        plain(right)
        left.set_title("Light in", fontsize=10)
        right.set_title("Light on the screen", fontsize=10)
        left.set_xlabel(f"the digit shown: {result['digit']}", fontsize=10)
        right.set_xlabel(f"brightest window: {result['brightest']}", fontsize=10)
    figure.text(0.5, 0.012, "Each screen is scaled to its own brightest point. Green outline: the window with the most light.",
                ha="center", va="bottom", fontsize=10, color="0.35")
    figure.savefig(PNG_PATH, dpi=100)
    plt.close(figure)


def main():
    FIGURES.mkdir(parents=True, exist_ok=True)
    results = run_all()
    print("digit  test_index  brightest_window  share_of_window_light  correct")
    for result in results:
        print(f"{result['digit']:5d}  {result['index']:10d}  {result['brightest']:16d}  {result['share']:21.4f}  "
              f"{'yes' if result['brightest'] == result['digit'] else 'NO (read wrongly)'}")
    print(f"correct: {sum(r['brightest'] == r['digit'] for r in results)} of 10")
    frames = [make_frame(result) for result in results]
    quantised = [frame.quantize(colors=128, method=Image.Quantize.MEDIANCUT, dither=Image.Dither.NONE) for frame in frames]
    quantised[0].save(GIF_PATH, save_all=True, append_images=quantised[1:], duration=FRAME_MILLISECONDS, loop=0, optimize=True)
    make_still(results)
    print(f"wrote {GIF_PATH} ({GIF_PATH.stat().st_size / 1e6:.2f} MB) and {PNG_PATH}")


if __name__ == "__main__":
    main()
