# 48. The waves of the primes

**In the repository:**
[`PrimeWaves.lean`](../lean/SquigglyLine/Connections/PrimeWaves.lean),
note [`riemann-hypothesis.md`](../docs/connections/riemann-hypothesis.md),
notebook [`prime_clocks.ipynb`](../experiments/connections/prime_clocks.ipynb).
**You need:** chapters 3, 4 and 6.

This chapter looks for a connection between the squiggly line and the
Riemann zeta function, a famous function from number theory. Nothing in it
is a step towards the Riemann hypothesis, the famous open question about
where that function is zero. The author's brief was: "I am not saying both
are equivalent. I just want some connection, both have squiggly lines."
That is all the chapter offers, and the last sections say exactly where it
stops.

One more thing to say before the start. The author of the note read a
survey and Wikipedia about the two theorems cited below. The original
papers were not read. Every cited statement is marked **cited**, and every
statement from memory is marked **recalled**, which means not checked
against a source.

## The idea

You have met sums of waves. Chapter 6 proved the squiggly line theorem for
one wave: the squigglier the wave, the closer it passes to the data, and
the steeper it must be. This chapter has a sum of two waves, and the
frequencies are not chosen at random or learned. They come from prime
numbers.

First the zeta function, in two sentences. It is the sum
`1/1^s + 1/2^s + 1/3^s + ...`, and it takes a complex number `s` as input.
A complex number has a real part and a height, and you can write
`s = real_part + i × height`, where `i` is the number whose square is
minus one. This is the only place complex numbers appear in the chapter.

Now walk up a vertical line: keep the real part fixed and let the height
grow. One term of the sum, `1/n^s`, then turns out to be a wave in the
height. Its amplitude is `n^(-real_part)` and its frequency is `log n`
(**recalled**: this is the definition written out). So on a vertical line
the zeta function is a sum of waves, one squiggly line for its real part
and one for its imaginary part.

A whole number is a product of primes in exactly one way. So `log n` is a
sum of logarithms of primes, and every frequency in the sum is built from
the frequencies `log 2`, `log 3`, `log 5` and so on. Think of each prime as
a **clock hand** that turns at the speed `log prime`. The whole sum is
driven by the prime clocks (**recalled**).

Four words, used from here on:

- A **label** is a value on the vertical axis: a height that a curve may
  or may not pass through.
- The **band** of a wave is the range of labels between its lowest and
  its highest possible value.
- A curve **covers** a band **within a reach** if, near every input and
  for every label of the band, there is an input at most the reach away
  where the curve has exactly that label. This is `COVERS_WITHIN` from
  chapter 4.
- A **warp** moves each input to another input. Nothing else is asked of
  it: it need not be smooth or even continuous. Chapter 4 has the warp
  theorem.

The result of the chapter, in one sentence for two different primes:

> The waves of two different primes have no common period. So their two
> clocks reach every pair of positions, so the sum of the two waves covers
> a band within a reach, and so the warp theorem and both bounds of the
> squiggly line theorem apply to it. For two frequencies with a common
> period this fails.

## An example you can do by hand

Start with the control, the case where it fails. Take two waves with
frequencies 1 and 2, both with amplitude 1:

```
cos t + cos 2t
```

Each cosine can be as low as -1, so the band of the sum goes from -2 to 2.
Does the sum reach -2? School algebra says no. Use `cos 2t = 2 (cos t)^2 - 1`:

```
cos t + cos 2t  =  cos t + 2 (cos t)^2 - 1
                =  2 (cos t + 1/4)^2 - 9/8
```

To check the second line, expand `2 (cos t + 1/4)^2`. It is
`2 (cos t)^2 + cos t + 1/8`, and `1/8 - 9/8 = -1`. A square is never
negative, so the sum is never below `-9/8`. That is -1.125. The labels
from -2 up to -9/8 are never reached, however far you walk up the line.
The two hands cannot both be at the bottom together: they turn in step.

(**Checked**, by evaluating on a fine grid: the smallest value of
`cos t + cos 2t` is -1.125.)

Now two primes, 2 and 3. The wave is `cos(t log 2) + cos(t log 3)`. The two
hands can be brought to the same position again only if some whole number
of turns of one equals a whole number of turns of the other, that is, if
`2^a = 3^b` for whole numbers `a` and `b` above zero. That is impossible:
the left side is even and the right side is odd. So the two hands never
fall into step. Over a long walk they come as near as you like to every
combination of positions, and sooner or later both are near the bottom
together.

(**Checked**, by the same kind of one-off evaluation: the smallest value of
`cos(t log 2) + cos(t log 3)` for heights up to 20,000 is -1.999998, at a
height near 16,457.)

## The statement

The first statement: two different primes. First in plain English. Pick
any position for each of the two clock hands, and any tolerance above
zero. Then there is a height at which the first hand is exactly at its
position and the second is within the tolerance of its position. Positions
are angles in radians. Adding whole turns, `turns × (2 × PI)`, changes
nothing.

```lean
theorem two_prime_clocks_reach_every_pair_of_phases
    {first_prime second_prime : ℕ}
    (first_is_prime : first_prime.Prime)
    (second_is_prime : second_prime.Prime)
    (primes_differ : first_prime ≠ second_prime)
    (first_target_phase : ℝ)
    (second_target_phase : ℝ)
    {tolerance : ℝ}
    (tolerance_pos : 0 < tolerance) :
    let first_frequency  := Real.log first_prime
    let second_frequency := Real.log second_prime
    ∃ (height : ℝ) (first_turns : ℤ) (second_turns : ℤ),
      let first_phase     := height * first_frequency
      let second_phase    := height * second_frequency
      let first_is_exact  :=
        first_phase = first_target_phase + first_turns * (2 * PI)
      let second_is_close :=
        |second_phase - (second_target_phase + second_turns * (2 * PI))|
          < tolerance
      first_is_exact ∧ second_is_close := by
```

*Read aloud:* for two different primes, any two target positions and any
tolerance above zero, some height puts the first hand exactly on its
target, up to whole turns, and the second within the tolerance of its
target, up to whole turns.

The notation: `ℕ` is the whole numbers, `ℝ` the real numbers and `ℤ` the
whole numbers with negatives allowed. `first_prime.Prime` says that the
number is prime. `Real.log` is the natural logarithm, here the frequency
of the clock. `∃` means "there is". `|x|` is the size of `x` without its
sign. `PI` is π. The lines starting `let` give names to pieces, as in the
earlier chapters. This is Kronecker's theorem of 1884 for two frequencies,
in the form that says such a height exists. It does not say how often such
heights occur, and it does not say how high the first one is.

Second, the band. Take the sum of the two waves with amplitudes
`first_amplitude` and `second_amplitude`, neither negative. Its band is
from minus the sum of the two amplitudes up to their sum. Take a narrower
band strictly inside: from `-inner_edge` to `inner_edge`, where
`inner_edge` is at least 0 and below the sum of the amplitudes. The
statement says that there is a reach such that within the reach of every
height, the wave takes every label of the narrower band.

```lean
theorem two_prime_wave_covers_a_narrower_band
    {first_prime second_prime : ℕ}
    (first_is_prime : first_prime.Prime)
    (second_is_prime : second_prime.Prime)
    (primes_differ : first_prime ≠ second_prime)
    {first_amplitude : ℝ}
    {second_amplitude : ℝ}
    (second_amplitude_nonneg : 0 ≤ second_amplitude)
    {inner_edge : ℝ}
    (inner_edge_inside : inner_edge < first_amplitude + second_amplitude) :
    let wave :=
      MAKE_TWO_PRIME_WAVE first_prime second_prime
        first_amplitude second_amplitude
    let narrower_band := Set.Icc (-inner_edge) inner_edge
    ∃ reach : ℝ, COVERS_WITHIN wave reach narrower_band := by
```

*Read aloud:* the sum of the waves of two different primes covers every
narrower band within some reach.

`MAKE_TWO_PRIME_WAVE` is the sum `first_amplitude × cos(height × log
first_prime) + second_amplitude × cos(height × log second_prime)`. With
amplitudes `first_prime^(-real_part)` and `second_prime^(-real_part)` it
is the real part of the two terms of the zeta sum that belong to the two
primes. `Set.Icc (-inner_edge) inner_edge` is
the set of labels from `-inner_edge` to `inner_edge`, both ends included.
The Lean statement also allows a negative `inner_edge`. The narrower band
is then empty and the statement says nothing. The proof gets the reach
from compactness, so it gives **no number** for it.

Third, the control, which is the example by hand above.

```lean
theorem commensurate_wave_misses_part_of_its_band
    (height : ℝ) :
    let slow_wave := cos height
    let fast_wave := cos (2 * height)   -- twice the frequency: a common period of `2 * PI`
    let lowest_value : ℝ := -9 / 8
    lowest_value ≤ slow_wave + fast_wave := by
```

*Read aloud:* at every height, `cos height + cos (2 × height)` is at least
`-9/8`.

So the statement that the sum takes every label of its band is false for
the frequencies 1 and 2. What the proofs for the primes use is only that
the ratio of the two frequencies is not a fraction. That is
`ratio_of_prime_logs_is_irrational`: it holds for two different primes,
and `Irrational` in Lean means "not a fraction of whole numbers". The
control is one inequality about one pair of frequencies. It is not a
theorem about every pair with a common period.

Other results of the file are named without quoting:
`two_prime_wave_stays_inside_its_band` (the wave never leaves its band),
`two_prime_wave_takes_every_label_inside_its_band` (every label strictly
inside the full band is reached somewhere),
`two_prime_wave_fits_any_target_after_a_bounded_warp` (the warp theorem
for the sum), `two_prime_wave_slope_is_at_most_amplitudes_times_frequencies`
and `two_prime_wave_is_near_the_data_and_pays_the_slope_tax`, which the
section on the squiggly line returns to.

## Why it is true

**The clocks never line up.** If the ratio of the two frequencies were a
fraction, then some power of the one prime would equal some power of the
other, as `2^a = 3^b` in the example. One number would be a product of
primes in two ways. Unique factorisation forbids it. That is
`ratio_of_prime_logs_is_irrational`.

**Steps of an irrational size reach everywhere.** Let the first hand make
one full turn. The second hand moves by `2 × PI` times the ratio of the
frequencies. Because the ratio is not a fraction, these steps round the
circle never come back to where they started, and they come near every
point of the circle. This is a theorem already in Mathlib, the Lean
library of mathematics. So bring the first hand exactly to its position
(that fixes the height up to whole turns). Then choose how many whole
turns of the first hand to add, so that the second hand lands within the
tolerance. That is the first statement above.

**Finitely many steps are enough.** The circle is compact: whenever
infinitely many open balls cover it, finitely many of them already do.
Put a small ball round the position that each step reaches. These balls
cover the circle, so finitely many of them do, and the largest step count
among those finitely many is a limit. This is
`irrational_steps_come_near_every_point_in_bounded_time`, and it gives the
fixed distance from any starting height, in
`two_prime_clocks_reach_every_pair_of_phases_within_a_fixed_distance`.
Compactness proves that a limit exists and does not compute it. That is why
the reach has no number.

**Passing through every label.** Start from any height. Within the reach
there is a height where the first wave is at its bottom and the second is
almost at its bottom, so the sum is at or below any label of the narrower
band. Within the reach there is another height where both are at or near
the top, so the sum is at or above the label.
A continuous curve takes every value between two of its values, so
between those two heights it passes through the label exactly. Both
heights are within the reach of the start, so the height where the label
is hit is too.

## What it explains

Two cited theorems are where the prime clocks are used. Neither is proved
in this repository.

**Voronin's universality theorem** (**cited**: Voronin 1975, as stated in
Theorem 1 of Matsumoto's survey, arXiv 1407.4216, and on Wikipedia, "Zeta
function universality"). Take a compact set with connected complement
inside the strip where the real part is between 1/2 and 1. Take any
function that is continuous on the set, analytic inside it, and has no
zero on it. Then for every tolerance, the heights at which the zeta
function, shifted up by that height, stays within the tolerance of the
function on the whole set make up a positive share of all heights.

In plain words: slide a window up the strip. What the zeta function does
inside the window comes as near as you like to any target function without
zeros, and it does so again and again. One squiggly curve passes close to
every such target.

The proof moves the prime clocks. The tool it needs is stronger than the
first statement in two ways. It is for all the primes at once, in place of
two. And it says that the good heights are a positive share of all
heights, where the first statement says only that one exists. So the Lean
file holds **a small special case of one tool that the proof uses**. The
proof needs much more: the stronger form of that tool, a step that
replaces the zeta function by a finite product over primes, and a step
about rearranging series in a space of functions. None of that is here.

How the two theorems sit side by side:

| | The squiggly line theorem | Voronin's theorem |
|---|---|---|
| The curve | a wave of frequency `frequency` | the zeta function on a window of the strip |
| What it gets near | every label in its band | every analytic target with no zero |
| How | move the input by at most `π / frequency` | shift the height |
| Exact or near | exact (`sineWave_exists_warp`) | within a tolerance |
| The move | a different small move for each input | one shift for the whole window |
| How far | at most `π / frequency`, shorter for a squigglier wave | no small bound is known |

Both say that nearness is used by moving the input, not the output. For a
single wave in this repository the move is small and is different for each
input. For the sum of two prime waves the move is bounded, with no number
for the bound. In Voronin's theorem the move is one shift for the whole
window, and it is not small. One effective result (**cited**, from the
same Wikipedia page, credited there to Garunkštis) bounds the first good
height for a tiny disc by `exp(exp(10 / tolerance^13))`.

**Bagchi's theorem** (**cited**: B. Bagchi, thesis, Indian Statistical
Institute, 1981, and a paper of 1987 in Acta Mathematica Hungarica. The
statement was read in Matsumoto's survey as summarised and in two arXiv
papers, not in Bagchi's papers). The Riemann hypothesis is true if and
only if the zeta function comes close to **itself** in the way Voronin's
theorem describes: for every such set and every tolerance, the heights at
which the shifted zeta function stays within the tolerance of the
unshifted one on the whole set make up a positive share of all heights.

One direction is short (**recalled** reasoning). If the hypothesis is true,
the zeta function has no zero in the strip, so it is itself an allowed
target in Voronin's theorem. The other direction uses known bounds on how
many zeros can lie to the right of 1/2.

So here is the connection in one sentence. By Bagchi's theorem, the Riemann
hypothesis can be restated as a statement about nearness for one squiggly
curve: the curve of the zeta function passes close to itself again and
again. The restatement is as hard as the hypothesis. What this repository
shares with it is the kind of statement (a squiggly curve, a target,
nearness reached by moving the input) and one elementary tool, the prime
clocks of the first statement. It shares no route to a proof.

## How this meets the squiggly line

It uses nearness and slope, from chapters 3 and 4, and the squiggly line
theorem for one wave, from chapter 6.

**The slope limit.** `two_prime_wave_slope_is_at_most_amplitudes_times_frequencies`
says that the sum of the two waves has slope at most
`|first_amplitude| × log first_prime + |second_amplitude| × log
second_prime`. A larger prime has a larger frequency, so its wave may be
steeper.

**The sandwich.** `two_prime_wave_is_near_the_data_and_pays_the_slope_tax`
says: for data whose labels lie in the narrower band, the sum passes within
the reach of every data point, and the vertical error is at most
`√(1 + slope_limit²)` times the nearest distance, with the slope limit
above. These are the two bounds of the squiggly line theorem, with the
primes put in.

**What is not proved there.** The reach here is one fixed number with no
formula. The theorem for a single wave says more: its reach is
`π / frequency`, so it shrinks as the wave gets squigglier. That part is
not proved for the prime wave. In particular, nothing here proves that a
larger prime brings the wave closer to data.

## Run it yourself

The Lean statement says that a good height exists. It does not say how
high. The notebook
[`prime_clocks.ipynb`](../experiments/connections/prime_clocks.ipynb)
measures that. The predictions and the stop rule were written and pushed on
24 November 2026 **before** the notebook was run. The verdicts were added
afterwards and the predictions were not edited.

The clock of a prime is at the angle `height × log prime`, taken round the
circle. For the first several primes the clocks together are a point on a
**torus**: the set of positions of several clock hands at once. With two
hands it is a square whose opposite edges are joined. The height draws a
line on the torus. The distance from the line to a target is the
straight-line distance between the angles, each difference taken the short
way round.

The three predictions:

- **M1, two clocks, the rate.** Draw the line for the primes 2 and 3 up to
  some top height, and take the largest distance from any point of the
  torus to the line. It falls like one over the top height: the fitted
  slope of its logarithm against the logarithm of the top height, for top
  heights from 30 to 30,000, is between -1.3 and -0.7.
- **M2, the control.** For frequencies 1 and 2 the nearest the line comes
  to the target `(π, π)` is `π × √0.2` = 1.405 (from the formula). It
  stays at or above 1.40 for every top height up to 30,000, while for the
  primes 2 and 3 it is below 0.01 by a top height of 30,000.
- **M3, more primes cost more.** For the first 2, 3, 4 and 5 primes, take
  40 random targets and for each the first height at which all the clocks
  together are within distance 0.3 of the target. The median first height
  grows by a factor of at least 3 with each added prime, and each median is
  within a factor of 3 of a volume estimate (torus volume over the
  cross-section of the ball times the speed, times `ln 2`).

The stop rule: no height above 5,000,000 is searched, and a target not
reached by then is reported as not reached. No setting is tuned after
seeing a result.

The three panels of the figure show the line of the two clocks and the
closed line of the control, the fall of the largest distance, and the wait
against the number of primes.

![Three panels. Left: the line of the clocks of 2 and 3 on the torus up to height 40, and the closed line for frequencies 1 and 2, with the target marked. Middle: the largest distance from the line falls as the height grows, slope -0.92 on log axes. Right: the first height within 0.3 of a target against the number of primes, 2 to 5, on a log axis, with the volume estimate beside it.](../graphs/prime_clocks.png)

What was measured:

- **M1 held.** The fitted slope is -0.92 (measured), inside the predicted
  range. The largest distance falls from 0.70 at a top height of 30 to
  0.0022 at 30,000. The fall is not even: the last three points, from
  8,544 to 30,000, fall only from 0.0026 to 0.0022. With the last
  point left out the slope is -0.96, and with the last three left out it
  is also -0.96. The predicted range was wide, and the area argument that
  gave it almost forces a slope near -1, so **this prediction was not a
  hard test**.
- **M2 held.** For frequencies 1 and 2 the nearest distance to `(π, π)` is
  1.40496 (found by a search along the line) at every top height from 30
  to 30,000, and 1.40496 from the formula. These are the same quantity found
  in two ways, not an experiment against a theory. For the primes 2 and 3
  it is 0.41, 0.028, 0.0026 and 0.0015 (found by search) at top heights
  of 30, 300, 3,000 and 30,000. The predicted bound was 0.01.
- **M3 held.** Every target was reached. The largest first height was
  215,994, far below the stop at 5,000,000.

| Primes | Median first height (measured) | Volume estimate (from the formula) | Ratio | Factor from the row above |
|---|---|---|---|---|
| 2 | 16.8 | 35.1 | 0.48 | |
| 3 | 213.4 | 294.0 | 0.73 | 12.7 |
| 4 | 7,036.9 | 3,363.6 | 2.09 | 33.0 |
| 5 | 69,774.6 | 45,688.6 | 1.53 | 9.9 |

Each factor is above the predicted 3, and each ratio is between 1/3 and 3.
The factors are uneven (12.7, 33.0, 9.9): with 40 targets the median is
rough. Each added prime made the wait about ten to thirty times longer, at
a tolerance of 0.3. That is all that was measured: five primes and one
tolerance. It says nothing about the zeta function itself, and it cannot
be compared with the bound cited above, which is about a small tolerance
for a fixed window, not about the number of primes. That many primes and a
small tolerance would need far greater heights is a guess from these
numbers, not a measurement.

**What the checks are worth.** Some printed checks cannot fail. The first
height is found by a closed formula on each step, so halving the sampling
step cannot change it, and the notebook says so. The check that can fail
is an independent coarse search. It was run on all 40 targets for 2 and 3
primes and on the 5 earliest targets for 4 and 5 primes, and it never found
an earlier hit. For 5 primes the step was not halved at all, for cost. A
second reader went through the notebook, and the first writer fixed what
was found. No printed number of M1, M2 or M3 changed. Three settings were
fixed before the run and are not in the predictions: the seed for the
random targets, the 12 heights used for M1, and the least-squares fit.

To run it (about a minute and a half):

```
python -m jupyter nbconvert --to notebook --execute --inplace experiments/connections/prime_clocks.ipynb
```

## What is not shown

- **It is not progress on the Riemann hypothesis.** What is proved here is
  Kronecker's theorem for two frequencies, which is from 1884, in the form
  that says a good height exists, and consequences of it for a sum of two
  waves. Voronin's and Bagchi's theorems are cited, not proved here.
  Bagchi's theorem restates the hypothesis. It has not led to a proof.
- **The squiggly line theorem is about something else.** It compares a
  smooth curve with a squiggly one against data, with the amplitude held
  fixed: the squigglier curve is closer and steeper, and the loss does not
  change. The Riemann hypothesis is about where one function is zero. No
  statement of this repository about nearness, slope or loss implies
  anything about those zeros.
- **The sum of waves is only literal to the right of 1.** The sum
  `1/1^s + 1/2^s + ...` converges only when the real part is above 1.
  Voronin's theorem and the hypothesis are about the strip between 1/2 and
  1, where the zeta function is defined in another way. There the picture
  of prime clocks is a guide to the proof, not a formula.
- **The Lean statement is weaker than the pictures.** It is for two
  primes. It proves that a reach exists and gives no number for it. The
  warp it gives is a different move for each input, where Voronin's
  theorem has one shift for a whole window, and the warp may be any
  function. It says nothing about the zeta function itself.
- **The words are the same and the objects differ.** "Covers", "near" and
  "move the input" mean points of a graph in this repository and functions
  on a window in Voronin's theorem.

Still open: the same for any finite number of primes (Mathlib has no
Kronecker theorem in several dimensions), a number for the reach, how the
height needed grows as the tolerance shrinks, a harder prediction for M1,
and more than 40 targets for M3.

## Check yourself

1. Can the wave `cos t + cos 2t` ever be as low as -2? What is the lowest
   value it reaches?
2. Why can the two clocks of the primes 2 and 3 never fall into step?
3. The sum of two prime waves covers a narrower band within a reach. How
   large is the reach?
4. Someone says: "the squiggly line theorem plus this chapter brings us
   closer to proving the Riemann hypothesis". Is that right?
5. In the measurement, how much longer did the wait for a target at
   tolerance 0.3 become with each added prime?

**Answers.** (1) No. It is `2 (cos t + 1/4)^2 - 9/8`, never below `-9/8`,
which is -1.125. That is `commensurate_wave_misses_part_of_its_band`. The
band reaches down to -2, so part of the band is missed. (2) Falling into
step would need `2^a = 3^b` for whole numbers `a` and `b` above zero, and
one side is even and the other odd. In general it is
`ratio_of_prime_logs_is_irrational`. (3) The statement
`two_prime_wave_covers_a_narrower_band` says that a reach exists. The proof
uses compactness, so it gives no number for the reach. (4) No. What is
proved is Kronecker's theorem for two frequencies, from 1884, and
consequences for a sum of two waves. Voronin's and Bagchi's theorems are
only cited. Bagchi's theorem restates the hypothesis and has not led to a
proof. No statement here about nearness, slope or loss says anything about
the zeros of the zeta function. (5) Between 9.9 and 33.0 times longer,
about ten to thirty times, measured for 2 to 5 primes and one tolerance.
It says nothing about the zeta function itself.

Previous: [47. What is not here](47-what-is-not-here.md) · Next: [49. Parity is a zigzag](49-parity-is-a-zigzag.md)
