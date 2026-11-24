# Spectral bias: strong directions first

**Proofs:** [`DoubleDescent.lean`](../../../lean/SquigglyLine/Networks/DoubleDescent.lean), [`Optimisers.lean`](../../../lean/SquigglyLine/Supporting/Training/Optimisers.lean), [`SpectralBias.lean`](../../../lean/SquigglyLine/Supporting/Training/SpectralBias.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/Training/SpectralBias.lean`](../../../lean/SquigglyLine/Supporting/Training/SpectralBias.lean)), **recalled**, **argued**, or **open**.

## The idea

A network does not learn everything at the same speed. It is reported to learn
the smooth, slow-changing part of a function first and the fine wiggles later
(**recalled**: Rahaman et al. 2019, "On the Spectral Bias of Neural Networks").
This is called spectral bias.

For a model that is linear in its weights the whole thing is one line of
algebra, and it comes straight out of the kernel.

## One direction at a time

Recall the kernel `K`. One step of gradient descent sends the error `r` to
`r − ηKr`, where `η` is the step size.

Pick a direction `u` of the labels that the kernel only stretches: `K u = λ u`.
Call `λ` the strength of that direction. Then each step multiplies the part of
the error along `u` by the same number:

```
error along u after one step  =  (1 − ηλ) × error along u before
```

(**proved**: `one_step_shrinks_one_direction`.) So after `t` steps

```
error along u after t steps  =  (1 − ηλ)^t × error along u at the start
```

(**proved**: `each_direction_runs_on_its_own_clock`.) The directions do not talk
to each other. Each one shrinks on its own clock.

## What follows

**Strong directions are learned first.** If one direction is stronger than
another, a smaller share of its error is left at every step
(**proved**: `strong_directions_first`).

**The clock of a direction is `1 / (ηλ)` steps.** The share of the error left
after `t` steps is caught between two simple numbers:

```
1 − t·ηλ   ≤   share left   ≤   e^(−t·ηλ)
```

(**proved**: `spectral_bias`.) The right side says every direction with some
strength is learned in the end. The left side says it cannot be hurried: until
`t` is near `1 / (ηλ)`, almost all of the error is still there.

**A direction of strength zero is never learned.** Its error stays exactly
where it started, for ever (**proved**: `direction_of_zero_strength_is_never_learned`).
This is the training-time side of `no_fit_along_a_direction_of_zero_strength`.

## Three things this explains

**Early stopping.** Suppose the true pattern lies in strong directions and the
noise in the labels is spread over weak ones. Stop after `t` steps, with `t`
well below `1 / (ηλ)` for the weak directions. The left bound says the noise
has hardly been fitted. The right bound says the pattern has. **argued** from
the two bounds; that real data splits this way is **open**.

**Grokking.** Sometimes a network fits its training data early and only much
later starts to do well on new data. If the part that generalises lies in a
weak direction, its clock `1 / (ηλ)` is long. The left bound says nothing
visible happens to it for about that long, and the right bound says it then
does get learned. **argued**; whether this is what happens in a real grokking
run is **open**.

**Double descent over training time.** Test error sometimes goes down, up and
down again as training runs. With clocks of different lengths, the pattern is
learned on the fast clocks, the noise on the middle ones, and the last of the
pattern on the slow ones. **argued**, not proved.

## How this meets the squiggly line

Which directions are strong depends on the model. In the Fourier model the
strength of a frequency is the square of the size its coefficient is allowed.
If high frequencies are given small sizes, the smooth part is learned first and
the squiggles last. So the order in which squiggles appear during training is
set by the same sizes that set how squiggly the model is at the start.

## The same factor, under four changes to the step

Notes from 14 Nov 2026. Proofs in
[`lean/SquigglyLine/Supporting/Training/Optimisers.lean`](../../../lean/SquigglyLine/Supporting/Training/Optimisers.lean).

Everything above comes from one number: a step of size `η` multiplies the
error in a direction of strength `λ` by `1 - η λ`. Four common changes to
the step can be read off the same number.

**A schedule.** If the step size changes from step to step, what is left of
the error is the product of the factors `1 - η_t λ` (**proved**:
`schedule_multiplies_its_factors`). While every `η_t λ` is between zero and two the error
never grows (**proved**: `schedule_never_grows_the_error_below_the_edge`). A step that is too large for
a direction makes its error grow (**proved**: `step_too_large_grows_the_error`). Warmup
starts with small steps so that the sharpest directions are not hit with a
factor above one before they have settled (**argued**).

**The condition number.** Say the strengths lie between `m` and `M`. The
step `2 / (m + M)` shrinks every direction by at least `(M - m) / (M + m)` a
step (**proved**: `condition_number_sets_the_speed`), and the weakest direction by
exactly that (**proved**: `weakest_direction_shrinks_by_exactly_that_factor`). With `κ = M / m`
the factor is `(κ - 1) / (κ + 1)`. So the more uneven the strengths, the
slower the best plain step is.

**Momentum.** With momentum `β` a step also adds `β` times the last move.
At `η λ = 2 (1 + β)` an error that flips sign every step is carried forward
at full size, for ever (**proved**: `momentum_moves_the_edge_of_stability`,
`flipping_error_at_the_momentum_edge_keeps_its_size`). With `β = 0` this is the edge
`η λ = 2` of `edge-of-stability.md`. So momentum moves the edge of
stability from `2 / η` to `2 (1 + β) / η`.

**Steps on part of the data.** Let each of several clients take one step
from the same weights, each on its own gradient. The average of where they
land, weighted by their shares of the data, is one step on the gradient of
all the data (**proved**: `average_of_steps_is_a_step_on_the_average`). With one example per
client and equal shares this says a step on a random example is the full
step on average (**proved**: `step_on_a_random_example_is_the_full_step_on_average`). It is stochastic gradient
descent in the mean, and federated averaging after one local step.

Not shown: that directions below momentum's edge are stable, the noise of a
random example around its mean, and federated averaging after more than one
local step, where the average is no longer a single step.

## All the directions at once, and the Fourier case

[`KernelSpectrum.lean`](../../../lean/SquigglyLine/Supporting/Training/KernelSpectrum.lean)
adds two things. Given an orthonormal basis of directions that the kernel only
stretches, the squared loss after `t` steps is the sum over the basis of
`(1 − ηλ_i)^(2t)` times the squared start part
(`loss_after_many_steps_is_a_sum_over_directions`). And for `N` inputs evenly spaced over one
period, with a kernel that is a sum of `a_k² cos(k × gap)` over frequencies
below `N / 2`, the sampled wave of frequency `m` is such a direction, with
strength `N / 2 × a_m²` (`fourier_direction_is_stretched`,
`fourier_spectral_bias`). The book's chapter 18 has the plain-English proof.

## What is not shown

- **Deep networks.** The kernel of a deep network changes while it trains. The
  statement here is for a fixed kernel. **open**
- **That smooth means strong.** For the Fourier model on evenly spaced inputs
  the strengths follow from the sizes of the coefficients
  (`fourier_direction_is_stretched` in
  [`KernelSpectrum.lean`](../../../lean/SquigglyLine/Supporting/Training/KernelSpectrum.lean):
  the sampled wave of frequency `m` has strength `N / 2 × a_m²`). That the
  sizes fall with frequency is a choice of model. For common networks the
  strong directions are reported to be the smooth ones; that is not derived
  here. **open**
- **Step size.** The bounds need `ηλ ≤ 1` for the direction in question.
