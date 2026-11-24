# How steep a network can be, and what that slope costs

**Proofs:** [`HardChoices.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/HardChoices.lean), [`NetworkSlope.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean), [`SignedDistance.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/SignedDistance.lean), [`Temperature.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Temperature.lean), [`VanishingGradients.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/VanishingGradients.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean) unless another file is
named), **argued**, **recalled**, or **open**.

## The idea

The theorem says a line is near the data only by being steep:
`vertical / √(1 + K²) ≤ nearest ≤ vertical`, where `K` is the slope. So the
slope of a network is the price of its nearness. This note collects the
places where that slope shows up under other names.

## The slope of a network is a product

A network is a stack of layers. If layer `i` stretches distances by at most
`Kᵢ`, the whole stack stretches them by at most the product of the `Kᵢ`
(**proved**: `network_slope_is_at_most_product_of_layer_slopes`).

A ReLU has slope at most one (**proved**: `relu_slope_is_at_most_one`). So a layer
"weights, then ReLU" is no steeper than the size of its weights (**proved**:
`layer_slope_is_at_most_weight_size`), and

```
slope of the network  ≤  product of the sizes of the weight layers
```

The sandwich then reads in that product: a network can be nearer to a data
point than its vertical error only by the factor `√(1 + product²)`
(**proved**: `vertical_error_of_network_is_at_most_stretch_times_nearest_distance`).

Two habits act on this product directly. Weight decay shrinks every factor.
Spectral normalisation holds every factor at one (**recalled**: Miyato et al.
2018). Both are limits on how squiggly the network may get. The product is
also what the best-known bounds on test error for deep networks are written
in (**recalled**: Bartlett, Foster and Telgarsky 2017).

## The gradient comes back through the same product

Backpropagation sends the error back through the layers in reverse, each
layer applying its transpose (**proved**: `backpropagation_runs_the_layers_in_reverse`). The size
of what comes back is bounded by the same product as the signal going forward
(**proved**: `gradient_coming_back_is_at_most_the_same_product`).

So slope and gradient share one fate. A product well below one is a flat
network and a vanishing gradient. A product well above one is a squiggly
network and an exploding gradient ([`VanishingGradients.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/VanishingGradients.lean)).

## Adversarial examples

The boundary of a classifier is where its score is zero. How far is an input
from the boundary?

If the score has slope at most `K`, flipping the sign of a score `s` takes a
move of at least `s / K` (**proved**: `flipping_a_classifier_needs_a_move_of_score_over_slope`). This is the
slope sandwich again, for a boundary in place of a line: a steep classifier
is one whose boundary passes near its data.

For a linear model the worst case is exact. Nudge every input by `ε`, each in
the direction of the sign of its weight. The score moves by `ε` times the sum
of the sizes of the weights, and no nudge of that size moves it more
(**proved**: `worst_small_nudge_moves_the_score_by_size_times_summed_weights`, `no_nudge_moves_the_score_by_more`). With a thousand
inputs the sum is large even when each weight is small. That is the usual
account of why images can be changed invisibly (**recalled**: Goodfellow,
Shlens and Szegedy 2015).

## Temperature

Dividing the scores by a temperature `T` divides their slope by `T`. It never
changes their order, so it never changes which answer is ranked first
(**proved**: `larger_score_has_larger_share`, `temperature_never_changes_the_ranking`).

So temperature is a way to change the slope of a classifier after training
without touching what it gets right. That is why it is used to repair
overconfidence (**recalled**: Guo et al. 2017). The overconfidence came from
cross-entropy asking for more slope without end
(`docs/supporting/training/cross-entropy.md`).

## A critic of slope one

One kind of generative model trains a critic to tell real samples from made
ones, and holds the critic to slope one (**recalled**: Arjovsky, Chintala and
Bottou 2017). Pair each real sample with a made one. The total gap such a
critic can report is at most the total distance between the pairs
(**proved**: `critic_of_slope_one_reports_at_most_the_distance`).

So a slope-one critic measures how far the made samples are from the real
ones. It cannot say "infinitely wrong" about a sample that is nearly right.
The distance field of the real data is such a critic
(`distance_field_slope_is_at_most_one` in [`SignedDistance.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/SignedDistance.lean)).

## Temperature trades quality for diversity

Notes from 14 Nov 2026. Proofs in
[`lean/SquigglyLine/Supporting/NetworkShape/Temperature.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Temperature.lean).

Sampling at a temperature means taking the softmax of the scores divided by
the temperature. Write `β` for one over the temperature, so a cold sampler
has a large `β`.

- **Quality.** The average score of a sample never falls as `β` rises
  (**proved**: `colder_sampler_picks_better_on_average`). The proof pairs every two
  answers: the better of the two gains more share from a larger `β`
  (**proved**: `average_score_rises_as_temperature_falls_cross_multiplied`).
- **Diversity.** A cold softmax puts nearly all its share on the top score
  (**proved**: `cold_softmax_picks_the_top_score` in [`HardChoices.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/HardChoices.lean)), so its
  samples are nearly all the same.

So one dial moves both, in opposite directions. The dial is the slope of the
scores: dividing by the temperature multiplies their slope by `β`. A steep
sampler is sharp and repeats itself; a gentle one is varied and worse on
average.

Not shown: a measure of diversity that falls at every step as `β` rises,
such as the entropy. Only the two ends are proved.

## A codebook snaps to the nearest code

Proofs in the same file.

A codebook autoencoder (VQ-VAE) replaces the encoder's output by the nearest
entry of a learned codebook. The decoder's output moves by at most its slope
times the distance to the entry (**proved**: `snapping_moves_output_at_most_slope_times_distance`), and the
nearest entry is the one that keeps that bound smallest (**proved**:
`nearest_entry_is_the_gentlest_snap`). So what the snap costs is nearness times slope,
the product this project is about.

The other two parts are proved elsewhere. Moving a code to the mean of the
points snapped to it is the second half of a k-means step
(`docs/supporting/new-inputs/neighbours.md`). The snap has slope zero, and
the gradient is passed across it by the straight-through trick
(`attention.md`).

## What is not shown

- **That networks reach the bound.** The product of layer sizes is an upper
  limit. A trained network is usually far less steep than it
  (**recalled**). How steep a random network is remains the main open
  problem.
- **Tightness of the adversarial bound** for networks that are not linear.
- **That the best slope-one critic gives a distance between distributions.**
  Only the easy direction is proved.
- **Test-error bounds.** Recalled, not proved.
