"""
optics.py

A small simulation of a diffractive classifier made of polarizer plates.
The model is the one in docs/networks/polarizer-classifier.md.

Lengths are in wavelengths (wavelength = 1). The light is a vector field of shape
(batch, 2, H, W), complex64: channel 0 is the horizontal vibration, channel 1 the vertical one.
The lossless phase plates use scalar light, shape (batch, 1, H, W).

Every tensor here has an explicit dtype. (experiments/part1/common.py sets torch's default dtype to
float64 when imported; nothing in this file depends on the default.)
"""

import math
import time

import numpy as np
import torch
import torch.nn.functional as functional

COMPLEX = torch.complex64
REAL = torch.float32

# ----------------------------------------------------------------------------------------------
# Geometry (all lengths in wavelengths)
# ----------------------------------------------------------------------------------------------
PIXEL = 2.0                 # one pixel of the grid, of the plates and of the digit
DIGIT_PIXELS = 56           # a 28 x 28 digit, each pixel repeated 2 x 2
APERTURE_PIXELS = 96        # side of the square plate aperture; light outside it is blocked
GRID_PIXELS = 256           # side of the simulation grid (aperture plus padding)
WINDOW_PIXELS = 12          # side of a screen window
CLASS_COUNT = 10

# Ten windows in a 3-4-3 layout, as (row centre, column centre) in pixels inside the 96 x 96
# aperture. Window j is the answer for the digit j, in reading order.
WINDOW_CENTRES = (
    [(16, 48 + shift) for shift in (-28, 0, 28)]
    + [(48, 48 + shift) for shift in (-36, -12, 12, 36)]
    + [(80, 48 + shift) for shift in (-28, 0, 28)]
)


def get_design_gap(pixel=PIXEL, digit_pixels=DIGIT_PIXELS, aperture_pixels=APERTURE_PIXELS):
    """
    The gap the plate geometry asks for, and the sideways move it is built from.

    s is the largest distance, in wavelengths, from the centre of any digit pixel to the centre of
    any window. The steepest bend a plate of pixel `pixel` can make has sin(phi) = 1 / (2 pixel)
    (the angle may change by at most a quarter turn per pixel). The gap that lets that bend cover
    the distance s is d = s / tan(phi), about 2 pixel s for small bends.
    """
    half_digit = (digit_pixels - 1) / 2
    corner_offsets = np.array([[-half_digit, -half_digit], [-half_digit, half_digit],
                               [half_digit, -half_digit], [half_digit, half_digit]])
    centre = (aperture_pixels - 1) / 2
    longest_pixels = 0.0
    for row, column in WINDOW_CENTRES:
        window = np.array([row - centre, column - centre])
        for corner in corner_offsets:
            longest_pixels = max(longest_pixels, float(np.linalg.norm(window - corner)))
    sideways = longest_pixels * pixel
    sine_bend = 1.0 / (2.0 * pixel)
    tangent_bend = sine_bend / math.sqrt(1.0 - sine_bend ** 2)
    return sideways / tangent_bend, sideways


# ----------------------------------------------------------------------------------------------
# The building blocks
# ----------------------------------------------------------------------------------------------
def apply_polarizer_plate(field, theta):
    """E <- u (u . E) with u = (cos theta, sin theta) at every pixel. `theta` broadcasts over (batch, H, W)."""
    axis_x = torch.cos(theta).to(REAL)
    axis_y = torch.sin(theta).to(REAL)
    shadow = axis_x * field[:, 0] + axis_y * field[:, 1]
    return torch.stack([axis_x * shadow, axis_y * shadow], dim=1)


def apply_phase_plate(field, phase):
    """A lossless plate: multiply the light by exp(i phase) at every pixel."""
    return field * torch.polar(torch.ones_like(phase, dtype=REAL), phase.to(REAL))


def apply_aperture(field, mask):
    """Light outside the plate aperture is blocked."""
    return field * mask


def get_transfer_function(grid_pixels, gap, pixel=PIXEL, device=None):
    """
    exp(2 pi i gap sqrt(1 - fx^2 - fy^2)) for fx^2 + fy^2 <= 1 and 0 otherwise (evanescent parts dropped).
    `grid_pixels` is the side of a square grid, or a (rows, columns) pair.
    Built in float64 so that the large phase 2 pi gap is exact before it is rounded to complex64.
    """
    rows, columns = (grid_pixels, grid_pixels) if isinstance(grid_pixels, int) else grid_pixels
    freq_y, freq_x = torch.meshgrid(torch.fft.fftfreq(rows, d=pixel, dtype=torch.float64),
                                    torch.fft.fftfreq(columns, d=pixel, dtype=torch.float64), indexing="ij")
    radius_squared = freq_x ** 2 + freq_y ** 2
    travelling = radius_squared <= 1.0
    phase = 2.0 * math.pi * gap * torch.sqrt((1.0 - radius_squared).clamp_min(0.0))
    kernel = torch.where(travelling, torch.polar(torch.ones_like(phase), phase),
                         torch.zeros((), dtype=torch.complex128))
    return kernel.to(COMPLEX).to(device)


def propagate(field, gap, pixel=PIXEL, transfer=None):
    """
    Angular-spectrum rule, each component separately. With gap == 0 the field is returned untouched
    (no FFT, so there is no round-off). A precomputed `transfer` may be passed for speed.
    """
    if gap == 0:
        return field
    if transfer is None:
        transfer = get_transfer_function(tuple(field.shape[-2:]), gap, pixel, field.device)
    return torch.fft.ifft2(torch.fft.fft2(field) * transfer)


def apply_linear_analyzer(field, direction):
    """Keep only the horizontal ("h") or only the vertical ("v") vibration."""
    keep = {"h": 0, "v": 1}[direction]
    mask = torch.zeros(1, 2, 1, 1, dtype=REAL, device=field.device)
    mask[:, keep] = 1.0
    return field * mask


def get_circular_vector(handedness):
    """(1, i)/sqrt 2 for "same" (the handedness of the input light) and (1, -i)/sqrt 2 for "opposite"."""
    sign = {"same": 1.0, "opposite": -1.0}[handedness]
    return torch.tensor([1.0, sign * 1j], dtype=COMPLEX) / math.sqrt(2.0)


def apply_circular_analyzer(field, handedness):
    """Keep the part of the light along e (the circular vector): E <- e (conj(e) . E)."""
    vector = get_circular_vector(handedness).to(field.device).view(1, 2, 1, 1)
    coefficient = (vector.conj() * field).sum(dim=1, keepdim=True)
    return coefficient * vector


def get_window_masks(aperture_pixels=APERTURE_PIXELS, window_pixels=WINDOW_PIXELS):
    """(aperture_pixels**2, 10) of 0/1: which aperture pixel belongs to which window."""
    masks = torch.zeros(CLASS_COUNT, aperture_pixels, aperture_pixels, dtype=REAL)
    half = window_pixels // 2
    for index, (row, column) in enumerate(WINDOW_CENTRES):
        masks[index, row - half:row + half, column - half:column + half] = 1.0
    return masks.reshape(CLASS_COUNT, -1).T.contiguous()


# ----------------------------------------------------------------------------------------------
# Data
# ----------------------------------------------------------------------------------------------
def load_mnist(root="experiments/optics/data", device="cpu"):
    """Digits as float32 in 0..1 (the size of the light), shape (n, 28, 28), and int64 labels."""
    from torchvision import datasets
    out = {}
    for name, train in (("train", True), ("test", False)):
        data = datasets.MNIST(root=root, train=train, download=False)
        out[name] = (data.data.to(REAL).div(255.0).to(device), data.targets.to(torch.int64).to(device))
    return out


def split_validation(train_images, train_labels, validation_count=5000, split_seed=12345):
    """A fixed split of the training set: (fit images, fit labels, validation images, validation labels)."""
    generator = torch.Generator().manual_seed(split_seed)
    order = torch.randperm(train_images.shape[0], generator=generator).to(train_images.device)
    validation, fit = order[:validation_count], order[validation_count:]
    return train_images[fit], train_labels[fit], train_images[validation], train_labels[validation]


# ----------------------------------------------------------------------------------------------
# The device
# ----------------------------------------------------------------------------------------------
# kind -> (light, number of plates, analyzer, gap multiplier, plate type, trained)
KINDS = {
    "linear3": dict(light="linear", plates=1, analyzer="vertical", gap_scale=1.0, plate="polarizer", trained=True),
    "circular1": dict(light="circular", plates=1, analyzer="opposite", gap_scale=1.0, plate="polarizer", trained=True),
    "pol_stack3": dict(light="linear", plates=3, analyzer=None, gap_scale=1.0, plate="polarizer", trained=True),
    "pol_stack3_short_gap": dict(light="linear", plates=3, analyzer=None, gap_scale=1 / 20, plate="polarizer", trained=True),
    "phase1": dict(light="scalar", plates=1, analyzer=None, gap_scale=1.0, plate="phase", trained=True),
    "phase3": dict(light="scalar", plates=3, analyzer=None, gap_scale=1.0, plate="phase", trained=True),
    "pol_stack3_untrained": dict(light="linear", plates=3, analyzer=None, gap_scale=1.0, plate="polarizer", trained=False),
}


class Device(torch.nn.Module):
    """
    digit (as the size of the light) -> [input polarizer] -> plate, gap, plate, gap, ... -> [analyzer] -> screen.

    The first plate sits in the plane of the digit. Each plate is a table of APERTURE_PIXELS^2 angles
    (or phases); light outside the aperture is blocked. The screen reads brightness
    |E_x|^2 + |E_y|^2 and sums it inside ten windows.

    For one plate the order is plate, analyzer, gap, screen. For three plates it is
    plate, gap, plate, gap, plate, gap, screen.
    """

    def __init__(self, kind, seed=0, grid_pixels=GRID_PIXELS, design_gap=None, pixel=PIXEL,
                 aperture_pixels=APERTURE_PIXELS, device="cpu"):
        super().__init__()
        self.kind = kind
        self.config = KINDS[kind]
        self.grid_pixels = grid_pixels
        self.pixel = pixel
        self.aperture_pixels = aperture_pixels
        if design_gap is None:
            design_gap = get_design_gap(pixel)[0]
        self.gap = design_gap * self.config["gap_scale"]
        generator = torch.Generator().manual_seed(seed)
        scale = math.pi if self.config["plate"] == "polarizer" else 2.0 * math.pi
        self.plates = torch.nn.ParameterList([
            torch.nn.Parameter(torch.rand(aperture_pixels, aperture_pixels, generator=generator, dtype=REAL) * scale)
            for _ in range(self.config["plates"])])
        # buffers that depend on the grid (not saved, so that a trained device can be moved to a bigger grid)
        mask = torch.zeros(grid_pixels, grid_pixels, dtype=REAL)
        start = (grid_pixels - aperture_pixels) // 2
        mask[start:start + aperture_pixels, start:start + aperture_pixels] = 1.0
        self.register_buffer("aperture_mask", mask, persistent=False)
        self.register_buffer("window_masks", get_window_masks(aperture_pixels), persistent=False)
        self.register_buffer("transfer", get_transfer_function(grid_pixels, self.gap, pixel), persistent=False)
        self.start = start
        self.to(device)

    # -- light in -------------------------------------------------------------------------------
    def make_input(self, digits):
        """(batch, 28, 28) sizes in 0..1 -> the field in the digit plane, (batch, 1 or 2, G, G) complex64."""
        big = digits.repeat_interleave(2, dim=1).repeat_interleave(2, dim=2)
        low = (self.grid_pixels - DIGIT_PIXELS) // 2
        size = torch.zeros(digits.shape[0], self.grid_pixels, self.grid_pixels, dtype=REAL, device=digits.device)
        size[:, low:low + DIGIT_PIXELS, low:low + DIGIT_PIXELS] = big
        size = size.to(COMPLEX)
        light = self.config["light"]
        if light == "scalar":
            return size.unsqueeze(1)
        if light == "linear":                           # horizontal light
            return torch.stack([size, torch.zeros_like(size)], dim=1)
        vector = get_circular_vector("same").to(digits.device)   # circular light (1, i)/sqrt 2
        return torch.stack([size * vector[0], size * vector[1]], dim=1)

    def embed(self, table):
        """An aperture-sized table of angles -> the grid (zero outside; the aperture mask blocks that region)."""
        pad = self.start
        return functional.pad(table, (pad, self.grid_pixels - self.aperture_pixels - pad,
                                      pad, self.grid_pixels - self.aperture_pixels - pad))

    # -- the screen -----------------------------------------------------------------------------
    def get_screen(self, digits):
        """Brightness on the screen plane, (batch, G, G), and the light that left the digit, (batch,)."""
        field = self.make_input(digits)
        light_in = (field.abs() ** 2).sum(dim=(1, 2, 3))
        plate_count = len(self.plates)
        for index, table in enumerate(self.plates):
            angles = self.embed(table)
            if self.config["plate"] == "polarizer":
                field = apply_polarizer_plate(field, angles)
            else:
                field = apply_phase_plate(field, angles)
            field = apply_aperture(field, self.aperture_mask)
            if index == plate_count - 1 and self.config["analyzer"] is not None:
                analyzer = self.config["analyzer"]
                if analyzer == "vertical":
                    field = apply_linear_analyzer(field, "v")
                else:
                    field = apply_circular_analyzer(field, analyzer)
            field = propagate(field, self.gap, self.pixel, self.transfer)
        return (field.abs() ** 2).sum(dim=1), light_in

    def forward(self, digits):
        """(window sums (batch, 10), light into the screen plane (batch,), light that left the digit (batch,))"""
        screen, light_in = self.get_screen(digits)
        low, size = self.start, self.aperture_pixels
        crop = screen[:, low:low + size, low:low + size].reshape(screen.shape[0], -1)
        return crop @ self.window_masks, screen.sum(dim=(1, 2)), light_in


class PixelsLinear(torch.nn.Module):
    """The reference: a plain linear classifier on the 784 pixels."""

    def __init__(self, seed=0, device="cpu"):
        super().__init__()
        torch.manual_seed(seed)
        self.layer = torch.nn.Linear(784, CLASS_COUNT, dtype=REAL)
        self.to(device)

    def forward(self, digits):
        return self.layer(digits.reshape(digits.shape[0], -1))


# ----------------------------------------------------------------------------------------------
# Training and evaluation
# ----------------------------------------------------------------------------------------------
def get_loss(window_sums, light_in, labels, temperature, light_weight):
    """
    Cross-entropy of temperature * (window sums / their total), minus a small reward for the share of the
    light that left the digit and landed in a window. The division by the total makes the first term blind
    to the brightness of the lamp.
    """
    total = window_sums.sum(dim=1, keepdim=True)
    shares = window_sums / (total + 1e-12)
    cross_entropy = functional.cross_entropy(temperature * shares, labels)
    delivered = (total.squeeze(1) / (light_in + 1e-12)).mean()
    return cross_entropy - light_weight * delivered, cross_entropy.detach(), delivered.detach()


def train_device(kind, seed, train_images, train_labels, epochs, batch_size=100, learning_rate=0.05,
                 temperature=30.0, light_weight=1.0, device="cpu", design_gap=None, log=None):
    """
    Train one device with Adam and a cosine decay of the learning rate to zero.
    `kind` is a key of KINDS, or "pixels_linear". Returns the model and a list of per-epoch dicts.
    """
    if kind == "pixels_linear":
        model = PixelsLinear(seed, device)
    else:
        model = Device(kind, seed, design_gap=design_gap, device=device)
    parameters = [p for p in model.parameters() if p.requires_grad]
    optimizer = torch.optim.Adam(parameters, lr=learning_rate)
    steps_per_epoch = train_images.shape[0] // batch_size
    total_steps = epochs * steps_per_epoch
    scheduler = torch.optim.lr_scheduler.LambdaLR(
        optimizer, lambda step: 0.5 * (1.0 + math.cos(math.pi * step / total_steps)))
    generator = torch.Generator(device="cpu").manual_seed(1000 + seed)
    history = []
    for epoch in range(epochs):
        order = torch.randperm(train_images.shape[0], generator=generator).to(train_images.device)
        loss_sum = delivered_sum = 0.0
        started = time.time()
        for step in range(steps_per_epoch):
            chosen = order[step * batch_size:(step + 1) * batch_size]
            images, labels = train_images[chosen], train_labels[chosen]
            if kind == "pixels_linear":
                loss = functional.cross_entropy(model(images), labels)
                delivered = torch.zeros(())
            else:
                window_sums, _, light_in = model(images)
                loss, _, delivered = get_loss(window_sums, light_in, labels, temperature, light_weight)
            optimizer.zero_grad(set_to_none=True)
            loss.backward()
            optimizer.step()
            scheduler.step()
            loss_sum += float(loss.detach())
            delivered_sum += float(delivered)
        record = dict(epoch=epoch, loss=loss_sum / steps_per_epoch, delivered=delivered_sum / steps_per_epoch,
                      seconds=time.time() - started)
        history.append(record)
        if log is not None:
            log(f"  {kind} seed {seed} epoch {epoch}: loss {record['loss']:.4f} "
                f"delivered(train) {record['delivered']:.4f} {record['seconds']:.1f}s")
    return model, history


@torch.no_grad()
def evaluate(model, images, labels, batch_size=250, scale=1.0, return_predictions=False):
    """
    Test accuracy; `delivered` = light in the ten windows / light that left the digit; `correct_share` = light in
    the correct window / all light on the screen plane. Both are averaged over the digits.
    `scale` multiplies the digits (the brightness of the lamp).
    """
    model.eval()
    correct = 0
    delivered_sum = share_sum = 0.0
    predictions = []
    for start in range(0, images.shape[0], batch_size):
        digits = images[start:start + batch_size] * scale
        target = labels[start:start + batch_size]
        if isinstance(model, PixelsLinear):
            scores = model(digits)
            predictions.append(scores.argmax(dim=1))
            correct += int((predictions[-1] == target).sum())
            continue
        window_sums, screen_light, light_in = model(digits)
        predictions.append(window_sums.argmax(dim=1))
        correct += int((predictions[-1] == target).sum())
        delivered_sum += float((window_sums.sum(dim=1) / light_in).sum())
        share_sum += float((window_sums.gather(1, target.unsqueeze(1)).squeeze(1) / screen_light).sum())
    count = images.shape[0]
    result = dict(accuracy=correct / count)
    if not isinstance(model, PixelsLinear):
        result.update(delivered=delivered_sum / count, correct_share=share_sum / count)
    if return_predictions:
        result["predictions"] = torch.cat(predictions).cpu()
    return result


def get_angle_map(model, plate_index=0):
    """The trained table of one plate as a numpy array (radians)."""
    return model.plates[plate_index].detach().cpu().numpy().copy()
