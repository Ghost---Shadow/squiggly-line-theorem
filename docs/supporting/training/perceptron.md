# The perceptron, XOR and no free lunch: nearness to a boundary

**Proofs:** [`Depth.lean`](../../../lean/SquigglyLine/Networks/Depth.lean), [`NetworkSlope.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean), [`CrossEntropy.lean`](../../../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean), [`Perceptron.lean`](../../../lean/SquigglyLine/Supporting/Training/Perceptron.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/Training/Perceptron.lean`](../../../lean/SquigglyLine/Supporting/Training/Perceptron.lean) unless another file is named),
**argued**, **recalled**, or **open**.

## The idea

The theorem is about the distance from the data to a line. A classifier has
a line too: its boundary, where the score is zero. The distance from the data
to the boundary is called the **margin**. Three old results are statements
about that distance.

## The margin is a nearest-point distance

Take a flat boundary through the origin, at right angles to a direction `u`
of length one. A point whose score against `u` is `s` lies at least `|s|`
from the boundary (**proved**: `margin_is_a_distance_to_the_boundary`).

So "every example scores at least `γ` on its correct side" means "no example
is nearer than `γ` to the boundary". The margin is the nearest-point distance
of the theorem, measured to a boundary.

## The perceptron: nearness sets the number of steps

The perceptron is the oldest learning rule (**recalled**: Rosenblatt 1958).
Whenever it gets an example wrong, it adds that example to its weights, with
the sign of its label.

Suppose the examples lie within `R` of the origin, and some flat boundary
keeps every one of them at least `γ` away on its correct side. Then

- each mistake moves the weights at least `γ` along the true direction
  (**proved**: `each_mistake_moves_weights_along_the_true_direction`), and
- each mistake adds at most `R²` to the squared size of the weights
  (**proved**: `each_mistake_adds_at_most_radius_squared`).

The first grows like the number of mistakes and the second like its square
root. They cannot both go on, so the perceptron makes at most

```
(R / γ)²  mistakes
```

(**proved**: `perceptron_mistake_bound`; the result is Novikoff's, 1962,
**recalled**.)

This is the rule of the whole repository in its first form. The work of
training is set by a distance. Data that sits near the boundary is slow to
learn, and data that sits far from it is fast. The number of parameters does
not appear.

## XOR: when no flat boundary is near enough

Four points: `(0,0)` and `(1,1)` are "no", `(0,1)` and `(1,0)` are "yes". No
flat boundary splits them (**proved**: `no_flat_boundary_splits_xor`; **recalled**:
Minsky and Papert 1969). The margin is not small here. It does not exist.

There are two repairs, and they are the two ways this repository makes a
squiggly line.

- **A lift.** Add the product `x·y` as a third feature. Upstairs the boundary
  is flat (**proved**: `one_lifted_feature_splits_xor`). This is
  `docs/networks/kernel-trick.md`.
- **A fold.** Fold the plane along the line `x = y`, which is what `|x − y|`
  does. After the fold a flat boundary works (**proved**:
  `one_fold_splits_xor`). This is one ReLU layer, as in [`Depth.lean`](../../../lean/SquigglyLine/Networks/Depth.lean).

## Can XOR be done with no hidden layer by changing the encoding?

Two ways to do it are sometimes offered. Each one is true as far as it goes,
and each one hides a lift.

- **One input per corner.** Replace the two inputs by four, one for each of
  the four corners: the input for the present corner is one and the rest are
  zero. Then a flat layer fits XOR. It fits anything: with one feature per
  input, any labels at all are a flat function, and the weights are the
  labels (**proved**: `table_lookup_fits_anything`). This is a table lookup. The four new
  inputs are not flat functions of the old two. Making them is the lift, and
  it is the work a hidden layer would have done.
- **One class per corner.** Keep the two inputs and ask for four outputs, one
  for each corner. A flat layer with a softmax does this too. A flat layer
  with one score per class names the nearest of its anchor points
  (**proved**: `flat_layer_names_the_nearest_anchor`), so it can tell any distinct points
  apart (**proved**: `anchor_scores_highest_at_itself`). But this names the corner. It
  does not compute XOR of it. Reading "corner 1 or corner 2" off the four
  outputs is a second step, and that step is the hidden layer.

A softmax on its own changes nothing. With the two original inputs and two
classes, the answer changes where two flat scores are equal, which is again a
flat boundary, and no flat boundary splits XOR (**proved**:
`two_flat_scores_do_not_split_xor`).

So the old statement stands: with the two inputs as given and one yes-or-no
output, no network without a hidden layer computes XOR. What the two
encodings show is the point of `docs/networks/kernel-trick.md`: any problem
is flat in some lift, and choosing the lift is where the work is.

One more thing seen in such experiments: the training loss ends small and not
zero. That is not rounding error. Against a sure label, no finite scores
bring cross-entropy to zero (**proved**: `cross_entropy_of_a_sure_label_is_greater_than_zero` in
[`CrossEntropy.lean`](../../../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean)). The loss only stops falling when training stops.

## No free lunch: squiggle helps only if labels vary gently

Fix an input the model has not seen, and any guess at its label. Among all
the possible ways to label the inputs, exactly half agree with the guess
there (**proved**: `no_free_lunch`; **recalled**: Wolpert
1996). So with no assumption about the labels, no learner beats a coin on
unseen inputs.

In the terms of the line: if an unseen label is `+1` or `−1` with equal
chance, a prediction `h` costs `h² + 1` on average (**proved**:
`flat_is_best_on_an_unseen_label`). The best line is flat at zero, and every bend away
from it only adds.

So nothing here can say that a squigglier line is better in general. A line
through the training points helps on new points only when nearby inputs have
nearby labels, that is, when the truth itself has a bounded slope. That
assumption is where every result about new inputs in this repository gets its
content (`docs/supporting/new-inputs/`).

## What is not shown

- **A perceptron with a moving lift.** The bound is for fixed features.
- **Margins for boundaries that are not flat.** For a score of slope `K` the
  matching statement is `flipping_a_classifier_needs_a_move_of_score_over_slope` in [`NetworkSlope.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean).
- **How large the margin of real data is** after a network's lift. **open**
- **A bound on test error from the margin.** Known (**recalled**: Vapnik),
  not formalised.
