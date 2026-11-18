# What is in `results/`

Angles are in radians in every `.npy` file, one table of 96 x 96 numbers per plate, shape `(plates, 96, 96)`. A plate
axis at `t` and at `t + 180 degrees` is the same plate, so only `t` modulo 180 degrees matters.

Round 1 (`run_sweep.py`, `tune_recipe.py`)
- `recipe.json`: the 18 candidates of the recipe search and the chosen learning rate, temperature and light weight.
- `sweep.json`: every device, seeds 0, 1, 2: test accuracy, `delivered`, `correct_share`, settings, wall time.
- `plate_<device>.npy`: the trained plates of seed 0 for each device kind (free angles). `plate_pol_stack3_untrained.npy`
  is the random start, never trained.

Round 2 (`run_fabrication.py`)
- `fabrication.json`: every number of round 2: determinism check, rounding after training, rounding in the training,
  angle error, shifts, the shift-trained stack, per seed.
- `fab_<name>_seed<k>.npy`: the trained parameters (before any rounding) of every trained plate. Names: `free_linear3`,
  `free_pol_stack3` (round-1 recipe again), `ste2_linear3` (rounded to 45 and 135 degrees in the forward pass),
  `ste4_linear3` and `ste4_pol_stack3` (rounded to 0, 45, 90, 135 degrees), `shift_pol_stack3` (trained with a random shift of
  each plate at every step). For the `ste` plates the made plate is the rounded table, not the stored one: round each angle
  modulo 180 degrees to the nearest level.
- `plate_<device>_4level_<plate>.png`: the 4-level plates of seed 0 (`linear3`: plate 0; `pol_stack3`: plates 0, 1, 2 in the
  order the light meets them), 8-bit grey, 96 x 96 pixels. **Pixel value = level index x 60**: 0, 60, 120, 180 mean the
  axis angle 0, 45, 90, 135 degrees, so `angle in degrees = pixel value / 60 x 45`. Row 0 is the top row of the plate as
  the light meets it; column 0 is the left.
