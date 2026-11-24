# 35. The landscape: connected fits and collapsed classes

**In the repository:**
[`ModeConnectivity.lean`](../lean/SquigglyLine/Supporting/NetworkShape/ModeConnectivity.lean),
[`NeuralCollapse.lean`](../lean/SquigglyLine/Supporting/NetworkShape/NeuralCollapse.lean),
notes [`mode-connectivity.md`](../docs/supporting/network-shape/mode-connectivity.md) and
[`neural-collapse.md`](../docs/supporting/network-shape/neural-collapse.md).
**You need:** chapters 9, 10 and 14.

## The idea

Train the same network twice from different starts. You get two sets of
weights that both fit. Walk in a straight line from one to the other. Often
the loss rises on the way: there is a hill between them. People have
reported that the two fits can still be joined by a curved path with no
hill (**recalled**: Garipov et al. 2018; Draxler et al. 2018), and that
after relabelling the neurons, even the straight line has no hill
(**recalled**: Entezari et al. 2022; Ainsworth et al. 2023). The last claim
is a conjecture.

Keep training a classifier long after it gets every training label right,
and its last layer is reported to settle into a tidy shape: one point for
each class, the points as far apart as they can be (**recalled**: Papyan,
Han and Donoho 2020). This is **neural collapse**.

The repository does not prove either report. It proves the small exact
statements that sit under them.

> A model linear in its weights has no hill between two fits. With two
> weights multiplied, the hill is exactly the product of how far the fits
> differ in each. And for any number of classes, arrows of length one
> cannot all overlap by less than minus one over the number of other
> classes.

## An example you can do by hand

**The hill.** The model is one weight times another, `first × second`. Both
`(2, 3)` and `(3, 2)` give 6, so both fit the target 6. Halfway along the
line the weights are `(2.5, 2.5)`, and the output is `6.25`. It is off by
`0.25`. The formula below gives the hill as
`0.25 × (2 − 3) × (3 − 2) = −0.25`, and `6 − (−0.25) = 6.25`.

The worst case is a fit and its mirror. `(2, 3)` and `(−2, −3)` both give 6.
Halfway, the weights are `(0, 0)` and the output is 0, whatever the target.

**The arrows.** Three arrows of length one, at 120 degrees to each other in
a plane, overlap by `−0.5` each. They add up to zero. You cannot do better:
the limit for three classes is `−1 / 2`.

## The statement

Here is the hill for two weights multiplied.

```lean
theorem two_layer_hill_exactly
    {first_a first_b second_a second_b target : ℝ}
    (first_fits : first_a * first_b = target)
    (second_fits : second_a * second_b = target)
    (fraction : ℝ) :
    let blended_a      := (1 - fraction) * first_a + fraction * second_a
    let blended_b      := (1 - fraction) * first_b + fraction * second_b
    let output         := blended_a * blended_b
    let hill           :=
      fraction * (1 - fraction)
        * ((first_a - second_a) * (first_b - second_b))  -- largest halfway along, zero at both fits
    let expected_output := target - hill
    output = expected_output := by
```

*Read aloud:* a fraction of the way between two fits of the same target,
the output is the target minus `fraction × (1 − fraction)` times the
difference in the first weight times the difference in the second.

The names `first_a` and `first_b` are the two weights of the first fit, and
`second_a` and `second_b` those of the second. For a model that is linear
in its weights there is no such term. The theorem `no_barrier` says the
error anywhere on the line is no larger than at the worse end, and
`line_between_two_fits_is_all_fits` says the line between two fits is all fits.

Here is the limit on how far apart the classes can be.

```lean
theorem simplex_is_as_far_apart_as_arrows_get
    [Nonempty Classes]
    {arrows : ClassArrows Classes Space}
    (arrows_have_length_one : ∀ this_class, ‖arrows this_class‖ = 1)
    {overlap_limit : ℝ}
    (overlaps_at_most_limit :
      ∀ this_class other_class, this_class ≠ other_class →
        inner ℝ (arrows this_class) (arrows other_class) ≤ overlap_limit) :
    let class_count : ℝ   := Fintype.card Classes
    let other_class_count := class_count - 1
    let lowest_possible : ℝ := -1                                  -- the simplex: every overlap is `-1 / other_class_count`
    lowest_possible ≤ other_class_count * overlap_limit := by      -- a squared length is never negative
```

*Read aloud:* if every pair of class arrows overlaps by at most
`overlap_limit`, then the number of other classes times `overlap_limit` is
at least minus one.

`inner ℝ` is the overlap of two arrows: 1 if they point the same way, 0 at
a right angle, minus 1 if opposite. `ClassArrows` is one arrow for each
class. The arrangement that reaches the limit is the **simplex**, and
`farthest_apart_arrangement_is_the_centred_one` says that evenly spread arrows reach the
limit exactly when they add up to zero.

## Why it is true

**No hill.** The model is linear, so its outputs blend like the weights do.
Midway along the line the error is the same blend of the two errors
(`residual_on_the_line_between_two_settings`). A blend of two zero errors is zero, and a
blend is never larger than the larger of the two.

**The hill.** Write the output at the blended weights and multiply it out.
Both fits give the target, so the terms with the target collect together,
and what is left is `fraction × (1 − fraction)` times the product of the
differences. The Lean proof is one `linear_combination` of the two
statements that the fits fit.

**The mirror.** If `(a, b)` fits, so does `(−a, −b)`, because the two signs
cancel (`mirror_image_is_the_same_function`). Halfway between them both weights are zero
(`halfway_to_the_mirror_image_everything_is_lost`). But the mirror is the same function. The hill
comes from writing one function in two ways.

**The arrows.** Add up all the arrows. The squared length of the sum is the
number of arrows, one from each arrow's own length, plus the overlaps of
every pair (`squared_length_of_a_sum_is_the_sum_of_overlaps`). A squared length is never
negative. So if every overlap is at most `overlap_limit`, the sum is at most
`class_count × (1 + other_class_count × overlap_limit)`, and that cannot be
below zero.

## What it explains

**Why straight lines can be bad.** In a real network, relabelling the
neurons plays the part of the sign flip. Two networks may compute nearly
the same function with their neurons in another order. The straight line
between them mixes unlike neurons, and the loss rises. Line the neurons up
first and the hill may go. The two-weight model shows this exactly for the
sign flip. That it always happens for wide networks is the conjecture, and
it stays **open**.

**Why the class points sum to zero.** Part of the shape in neural collapse
is plain geometry. The farthest-apart arrangement is the centred one. And
the counting result of chapter 34, `full_compression_merges_exactly_equal_labels`, gives the first
part in counting form: a layer squeezed to as many places as labels has one
place for each class.

## How this meets the squiggly line

The hill is a product of two differences, and a product only appears when
weights multiply. So it is depth, the thing that made the model squiggly,
that made the hill. A model linear in its weights is the lift of chapter
11 with the features held fixed, and chapter 10 showed its fits form one
flat sheet. How far a point must be pushed to change its label depends on
how far apart the class points are, which is the nearness of chapter 4. The
simplex makes that distance as large as it can be for every pair at once.

## Run it yourself

[`ch35_the_landscape.ipynb`](../experiments/part5/ch35_the_landscape.ipynb) uses a linear model in its weights (fixed
sine and cosine features, 12 coefficients, 5 data points), the two-weight model, and unit arrows. It is evidence, not
proof. It has 9 checks that could fail, all passing, and 6 lines that are not counted (a mirror identity, a
control built as a counterexample, a curved path that fits by construction, two repeats of earlier checks, and one
reported number). **Measured** on the linear model: two exact fits 8.42 apart have a largest error on the line between them of
`6.3e-15`, and for 200 random pairs that do not fit, no point on the line is above the worse end (largest excess
`0.0`). **Measured** on two weights multiplied: for 300 random pairs of fits, the multiplied output agrees with the
formula `target - hill` to `3.6e-15`. Dropping the hill term (the linear-model answer) misses by up to 15.80, which
is only the largest hill among the random draws: a report, not a test. Halfway
between `(2, 3)` and `(3, 2)` the model output is 6.25; the hill `-0.25` is **from the formula**. For 200 random targets
the mirror fits, and the multiplied output at the midpoint is exactly 0 and its squared error is the target squared;
this follows from the form of the model (a product of two zeros), is printed as by construction and is not counted.

The squared error of the product model along the straight line peaks at 0.0625 halfway between `(2, 3)` and `(3, 2)`
and at 36.00 halfway to the mirror `(-2, -3)`; both agree with the hill squared (**from the formula**) to rounding
error; that repeats the check of the two-weight model and is not counted twice. The linear model's line has squared error at most `4.1e-29`, which repeats the check of the linear model. The curved path `(a, 6 / a)` is drawn for contrast:
it fits by construction, its loss `7.9e-31` is not evidence, and the chapter does not prove it.

![Squared error of the output along the straight line between two fits: the product model's straight line rises to 0.0625 for the swap and 36.00 for the mirror, with dots from the hill formula on it; the linear model's line is at zero; the curved path is drawn at zero because it fits by construction](figures/35-hill-along-the-line.png)

For the arrows, a gradient search for unit arrows with the lowest largest overlap, for 2 to 10 classes, never went below
`-1 / (classes - 1)` (smallest margin `-2.2e-16`, rounding) and came within `6.5e-04` of it (the tolerance was `1e-3`;
the notebook does not record whether the steps, the learning rate and the tolerance were fixed before the first run); the best arrangements add up
to a vector of length at most `1.3e-03`, the simplex. Random unit arrangements (2000 per class count) stayed above the limit, with a smallest gap of 0.000, 0.032, 0.268,
0.319, 0.344, 0.416, 0.427, 0.480 and 0.480 for 2 to 10 classes: for 4 or more classes random draws are nowhere near the
limit, so they do not test it; only the search does. For arrows of length 1.5 the notebook builds the explicit simplex
vectors, so that every overlap is `-2.25 / (classes - 1)`: for four classes the largest overlap is `-0.750`, below the
unit limit `-0.333`, by 0.417. That is an explicit counterexample, by construction, not a measurement and not counted.
This checks the geometry only; no network was trained to collapse.

![Lowest largest overlap between two arrows against the number of classes: the search for unit arrows lies on the limit, the best random arrangements lie above it (for 4 or more classes by a wide margin, so they do not test the limit there), and explicit simplex arrows of length 1.5, built so that every overlap is below the limit, lie below it](figures/35-class-overlap-limit.png)

Run it:

```bash
jupyter nbconvert --to notebook --execute --inplace experiments/part5/ch35_the_landscape.ipynb
```

## What is not shown

- **Real networks.** The no-hill result is for models linear in their
  weights. The hill is shown for two weights multiplied. **open**
- **That shuffling neurons removes the hill.** It is shown here only for
  the sign flip of the two-weight model. **open**
- **Curved paths.** That fits of a deep network can be joined by a curved
  path with no hill is not addressed. **open**
- **That training goes to the simplex.** The geometry is proved. That the
  last layer of a trained network lands there is reported for simplified
  models where the last-layer features are free to move (**recalled**, not
  checked here). For real networks it is an observation. **open**

## Check yourself

1. Two fits of the target 6 are `(1, 6)` and `(3, 2)` for the model
   `first × second`. What is the output halfway along the line between
   them?
2. For five classes, what is the lowest overlap that every pair of arrows
   of length one can reach at once?
3. A model is linear in its weights, and two settings of the weights both
   fit the data exactly. What is the error at a point a third of the way
   between them?

**Answers.** (1) The halfway weights are `(2, 4)`, so the output is 8. By
`two_layer_hill_exactly` it is `6 − 0.25 × (1 − 3) × (6 − 2)`, which is
`6 + 2 = 8`. (2) By `simplex_is_as_far_apart_as_arrows_get`, four times the limit is at
least `−1`, so it is `−1 / 4`. (3) Zero, by `line_between_two_fits_is_all_fits`: the line between
two fits is all fits.

Previous: [34. Capacity and compression](34-capacity-and-compression.md) · Next: [36. Attention](36-attention.md)
