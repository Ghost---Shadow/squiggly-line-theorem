# Mixing: graph networks, diffusion schedules, augmentation, guidance

**Proofs:** [`Averaging.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean), [`Mixing.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Mixing.lean), [`OnAverage.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/OnAverage.lean).

Notes from 14 Nov 2026. Each statement is marked **proved**, **argued**,
**recalled** or **open**.

## The idea

`averaging.md` shows that an average is never squigglier than what it
averages. Many parts of modern models are averages under another name.
This note lists five, one thing that looks like an average and is not, and
two facts about averages themselves.

## More averages, and one thing that is not

Proofs in
[`lean/SquigglyLine/Supporting/NewInputs/Mixing.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Mixing.lean).

- **Graph networks.** A message-passing layer replaces each node by a
  weighted sum of the nodes. If each node's weights add to one and every
  weight is at least `m`, two nodes end no further apart than `1 - n m`
  times the range of the values, for `n` nodes (**proved**:
  `message_passing_layer_shrinks_the_spread`). After `L` layers the factor is
  `(1 - n m)^L` (**proved**: `depth_blurs_the_nodes`). This is
  the blurring of deep graph networks, and it is the same statement as the
  merging of tokens under attention. On a real graph a node gives weight
  only to its neighbours, so the floor holds only after enough layers for
  every node to reach every other; that step is not shown.
- **The diffusion noising schedule.** Follow the share of the variance that
  is signal and the share that is noise. A step keeps `1 - β` of each and
  adds `β` of fresh noise. The two shares still add to one (**proved**:
  `noising_step_keeps_total_variance_at_one`), and after `n` steps the signal's share is
  `(1 - β)^n` of what it was (**proved**: `signal_share_after_many_noising_steps`).
  The forward process is an average of the data with noise, with the
  weight on the data shrinking geometrically.
- **Data augmentation.** Average a model over a group of moves of the
  input, such as shifts or flips. The averaged model gives the same answer
  before and after any of the moves (**proved**: `averaged_model_ignores_the_moves`).
  If the moves keep distances it is no steeper than the model it was made
  from (**proved**: `averaged_model_is_no_steeper`). Training on
  augmented data pushes toward this average (**argued**).
- **The baseline.** In policy gradient the push on the score of an action
  is "action taken minus prediction", times the reward. Averaged over the
  action taken, "action taken minus prediction" is zero (**proved**:
  `baseline_pushes_nothing_on_average`). So subtracting the same baseline from every
  reward leaves the average push as it was (**proved**:
  `subtracting_a_baseline_keeps_the_average_push`). That it lowers the noise is not shown.
- **Classifier-free guidance.** The guided prediction is `1 + w` of the
  prediction with the prompt minus `w` of the prediction without. It moves
  from the plain prediction toward the prompt, `1 + w` times as far as the
  prompt alone does (**proved**: `guidance_moves_along_the_prompt_direction`, `guided_step_is_longer_by_one_plus_strength`). For
  `w > 0` it is not on the stretch between the two predictions
  (**proved**: `guidance_is_not_an_average`). One weight is negative, so this
  is not an average. It is the one step of a diffusion sampler that can
  leave the region the examples span.

## The median, and random directions

Proofs in
[`lean/SquigglyLine/Supporting/NewInputs/OnAverage.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/OnAverage.lean).

- **The loss chooses the average.** Squared error is least at the mean
  (`weighted_mean_is_the_best_single_guess`). Absolute error is least at a median: a value
  with at most half the points below it and at most half above
  (**proved**: `absolute_error_is_least_at_a_median`). So a line trained on squared error
  goes through the mean of the labels at each input, and one trained on
  absolute error through their median, which a few wild labels do not move.
- **Random directions are nearly at right angles, on average.** Take a
  random vector whose coordinates are uncorrelated, each with mean square
  `s`. Its overlap with a fixed vector has mean square `s` times that
  vector's squared length (**proved**: `random_directions_are_nearly_at_right_angles`). For vectors
  of length one in `d` dimensions, `s = 1 / d` and the mean squared overlap
  is `1 / d`. This is the on-average form of the fact behind section 5 of
  the README: random features in many dimensions hardly overlap, which is
  why travel falls as the model grows. That the overlap is small with high
  chance, and not just on average, is not shown.

## How this meets the squiggly line

Through **averages**. A layer that averages cannot add squiggle and pulls
its inputs together: that is the blurring of graph networks, the fading of
the signal in the noising schedule, and the gentleness of a model averaged
over moves. Guidance is the exception that shows the rule: with one weight
negative it can leave the region an average must stay in.

## What is not shown

- **Graph networks on a sparse graph.** The rate needs every weight to have
  a floor, which holds only after enough layers for every node to reach
  every other.
- **That a baseline lowers the noise** of the policy gradient.
- **The reverse process of diffusion**, and what guidance does over a whole
  sampling run.
- **That random directions hardly overlap with high chance**, and not just
  on average.
