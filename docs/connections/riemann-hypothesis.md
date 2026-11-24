# The squiggly line and the Riemann zeta function

**Proofs:** [`PrimeWaves.lean`](../../lean/SquigglyLine/Connections/PrimeWaves.lean).

Written 24 Nov 2026. This note looks for a connection between the squiggly
line theorem and the Riemann hypothesis. It does not say the two are
equivalent, and nothing here is a step towards the hypothesis. The section
"What the connection does not say" is part of the result.

Each statement is marked:

- **proved**: checked by Lean in the file above;
- **cited**: a published theorem. I read it in a survey or on Wikipedia, not
  in the original paper. The source I read is named;
- **checked**: a number computed for this note;
- **recalled**: from memory, not checked against a source.

## The picture: the zeta function is a sum of waves

The Riemann zeta function is the sum

    zeta(s) = 1/1^s + 1/2^s + 1/3^s + ...

for a complex number `s` whose real part is above 1. Walk up a vertical
line: fix the real part `σ` and let the height `t` grow, `s = σ + i t`. One
term of the sum is then

    1/n^s = n^(-σ) * (cos(t log n) - i sin(t log n)).

So as a function of the height, each term is a wave. Its amplitude is
`n^(-σ)` and its frequency is `log n`. The zeta function on a vertical line
is a sum of waves: one squiggly line for its real part and one for its
imaginary part. (**recalled**; this is the definition written out.)

This repository already studies sums of waves. Chapter 11 of the book takes
frequencies at random, and
[`SineCloser.lean`](../../lean/SquigglyLine/Theorem/SineCloser.lean) proves
the squiggly line theorem for one wave. What is different here is where the
frequencies come from. They are not random and not learned. They are the
logarithms of the whole numbers.

A whole number is a product of primes in exactly one way, so `log n` is a
sum of logarithms of primes. Every frequency in the sum is built from the
frequencies `log 2, log 3, log 5, ...` of the primes. Think of each prime as
a clock hand that turns at the speed `log p`. Then the whole sum is driven
by the prime clocks. Euler's product formula says the same thing: the zeta
function is a product of one factor for each prime, and the factor of `p`
depends on the height only through the hand of the clock of `p`.
(**recalled**)

## What is proved here

All four statements are in
[`PrimeWaves.lean`](../../lean/SquigglyLine/Connections/PrimeWaves.lean).
They are about the waves of two different primes `p` and `q`.

1. **The two clocks never line up again**
   (`ratio_of_prime_logs_is_irrational`, **proved**). The ratio
   `log q / log p` is not a fraction. If it were `a / b`, then
   `q^b = p^a`, and one number would be a product of primes in two ways.

2. **The two clocks reach every pair of positions**
   (`two_prime_clocks_reach_every_pair_of_phases`, **proved**). Choose any
   position for each hand and any tolerance. At some height the first hand
   is exactly at its position and the second is within the tolerance of its
   position. This is Kronecker's theorem of 1884 for two frequencies. The
   proof uses a theorem already in Mathlib: steps of an irrational size
   round a circle come near every point.

3. **The sum of the two waves takes every label inside its band**
   (`two_prime_wave_takes_every_label_inside_its_band`, **proved**). Take

       wave(t) = A cos(t log p) + B cos(t log q).

   It always stays between `-(A + B)` and `A + B`
   (`two_prime_wave_stays_inside_its_band`, **proved**). And for every label
   strictly between those two numbers there is a height where the wave has
   exactly that label. In the words of
   [`Oscillation.lean`](../../lean/SquigglyLine/Theorem/Oscillation.lean),
   the wave covers its band. With `A = p^(-σ)` and `B = q^(-σ)` the wave is
   the real part of the two terms `1/p^s + 1/q^s` of the sum over primes.

4. **The control: clocks that do line up miss part of their band**
   (`commensurate_wave_misses_part_of_its_band`, **proved**). With
   frequencies 1 and 2 the sum `cos t + cos 2t` never goes below `-9/8`,
   though its band goes down to `-2`. So statement 3 needs the frequencies
   to be those of different primes. It fails for frequencies with a common
   period.

Two numbers to go with this (**checked**, by evaluating the waves on a fine
grid): the smallest value of `cos t + cos 2t` is `-1.125`. The smallest value
of `cos(t log 2) + cos(t log 3)` for heights up to 20,000 is `-1.999998`, at
a height near 16,457.

## What this is the first step of: Voronin's theorem

**Voronin's universality theorem** (**cited**; Voronin 1975, as stated in
Theorem 1 of Matsumoto's survey, arXiv 1407.4216, and on Wikipedia, "Zeta
function universality"). Take a compact set `K` with connected complement
inside the strip where the real part of `s` is between 1/2 and 1. Take any
function `f` that is continuous on `K`, analytic inside it, and has no zero
on `K`. Then for every tolerance `ε`, the heights `τ` at which

    |zeta(s + iτ) - f(s)| < ε   for every s in K

make up a positive share of all heights. Voronin's first version was for a
disc of radius below 1/4 with its centre at 3/4.

In plain words: slide a window up the strip. What the zeta function does
inside the window comes as near as you like to any target function without
zeros, and it does so again and again. One squiggly curve passes close to
every such target.

The proof moves the prime clocks. The survey's words: "since {log p} is
linearly independent over Q, we can apply the Kronecker-Weyl approximation
theorem." That is statement 2 above for all the primes at once, in place of
two. So the Lean file holds the two-prime case of the first step of the
proof. It holds nothing of the other steps.

### How this sits beside the squiggly line theorem

| | The squiggly line theorem | Voronin's theorem |
|---|---|---|
| The curve | a wave of frequency `w` | the zeta function on a window of the strip |
| What it gets near | every label in its band | every analytic target with no zero |
| How | move the input by at most `π / w` | shift the height by `τ` |
| Exact or near | exact (`sineWave_exists_warp`) | within `ε` |
| The move | a different small move for each input | one shift for the whole window |
| How far | at most `π / w`, shorter for a squigglier wave | no small bound is known |

Both say that nearness is used by moving the input, not the output. In this
repository the move is small and is different for each input. In Voronin's
theorem the move is one shift for the whole window, and it is not small. One
effective result (**cited**, from the same Wikipedia page, credited there to
Garunkštis) bounds the first good height for a tiny disc by
`exp(exp(10 / ε^13))`.

## Where the Riemann hypothesis comes in

The Riemann hypothesis says that the zeta function has no zero whose real
part is above 1/2. (The zeros of interest lie in the strip between 0 and 1,
and the hypothesis puts them all on the line 1/2.)

**The target must have no zeros, and that is the hypothesis showing
through.** A function that is close enough to a function with a zero has a
zero too. So if the zeta function came close, at a positive share of
heights, to a target with a zero in the strip, it would have many zeros to
the right of 1/2. Wikipedia puts it this way: under the Riemann hypothesis
the zeta function has no zeros in the strip, so it could not approximate
such a function. (**cited** for the conclusion; the step from "close" to
"has a zero" is Rouché's theorem, **recalled**.)

**Bagchi's theorem** (**cited**; B. Bagchi, thesis, Indian Statistical
Institute, 1981, and "Recurrence in topological dynamics and the Riemann
hypothesis", Acta Math. Hungar. 50 (1987), 227 to 240. I read the statement
in Theorem 20 of Matsumoto's survey as summarised, and in arXiv 1812.11729
and 1405.1553; I did not read Bagchi's papers.) The Riemann hypothesis is
true if and only if the zeta function comes close to **itself** in this
way: for every such set `K` and every `ε`, the heights `τ` at which

    |zeta(s + iτ) - zeta(s)| < ε   for every s in K

make up a positive share of all heights.

One direction is short. If the hypothesis is true, the zeta function has no
zero in the strip, so it is itself an allowed target in Voronin's theorem.
(**recalled** reasoning; the other direction uses known bounds on how many
zeros can lie to the right of 1/2.)

So here is the connection in one sentence. **The Riemann hypothesis is
equivalent to a statement about nearness for one squiggly curve: the curve
of the zeta function passes close to itself again and again.** And the first
step in proving that this curve passes close to anything at all is the
statement proved here for two primes.

## What the connection does not say

- **It is not progress on the Riemann hypothesis.** What is proved here is
  Kronecker's theorem for two frequencies, which is from 1884, and a
  consequence of it for a sum of two waves. Voronin's and Bagchi's theorems
  are cited, not proved here. Bagchi's theorem restates the hypothesis. It
  has not led to a proof.
- **The squiggly line theorem is about something else.** It compares a
  smooth curve with a squiggly one against data, with the amplitude held
  fixed: the squigglier curve is closer and steeper, and the loss does not
  change. The Riemann hypothesis is about where one function is zero. No
  statement of this repository about nearness, slope or loss implies
  anything about those zeros.
- **The sum of waves is only literal to the right of 1.** The sum
  `1/1^s + 1/2^s + ...` converges only when the real part of `s` is above 1.
  Voronin's theorem and the hypothesis are about the strip between 1/2 and
  1, where the zeta function is defined in another way. There the picture
  of prime clocks is a guide to the proof, not a formula.
- **The Lean statement is weaker than the pictures.** It is for two primes.
  It gives no bound on the height (no reach), so it is not yet the
  `COVERS_WITHIN` of this repository. It says nothing about the zeta
  function itself.
- **The words are the same and the objects differ.** "Covers", "near" and
  "move the input" mean points of a graph in this repository and functions
  on a window in Voronin's theorem.

## The measurement: how far must the clocks run?

The Lean statement says a good height exists. It does not say how high. The
notebook `experiments/connections/prime_clocks.ipynb` measures that. This
section was written and pushed on 24 Nov 2026 **before** the notebook was
run. The verdicts are added below it afterwards and the predictions are not
edited.

**What is measured.** The clock of the prime `p` is at the angle `t log p`,
taken round the circle. For the first `N` primes the clocks together are a
point on a torus with `N` angles, and the height `t` draws a line on it. The
distance from that point to a target is the usual straight-line distance
between the `N` angles, each difference taken the short way round.

**What I had already seen when writing this:** the two numbers in "What is
proved here" (the smallest values of the two sums of waves up to height
20,000), and nothing else.

- **M1, two clocks, the rate.** Let `gap(T)` be the largest distance from
  any point of the torus to the line drawn up to height `T`, for the primes
  2 and 3. A line of length `T` on a torus of fixed area leaves strips of
  width about `area / length`, so I predict `gap(T)` falls like `1 / T`:
  the fitted slope of `log gap` against `log T`, for `T` from 30 to 30,000,
  is between -1.3 and -0.7. The prediction fails if the slope is outside
  that range.
- **M2, the control.** For frequencies 1 and 2 the line closes after one
  turn, and the nearest it comes to the target `(π, π)` is
  `π * sqrt(0.2) = 1.405` (from the formula: minimise
  `(t - π)^2 + (2t - π)^2`). I predict the measured nearest distance stays
  at or above 1.40 for every `T` up to 30,000, while for the primes 2 and 3
  it is below 0.01 by `T` = 30,000. The prediction fails if either number is
  on the wrong side.
- **M3, more primes cost more.** For the first `N` primes, `N` from 2 to 5,
  take 40 random targets and for each the first height at which all `N`
  clocks are within distance 0.3 of the target. A ball of radius 0.3 is a
  smaller share of the torus for each added prime, so I predict the median
  first height grows by a factor of at least 3 with each added prime. I also
  predict each median is within a factor of 3 of the volume estimate
  `torus volume / (cross-section of the ball * speed) * ln 2`, where the
  speed is `sqrt(sum of (log p)^2)` and the cross-section is the volume of a
  ball of radius 0.3 in `N - 1` dimensions. The prediction fails if any
  factor between neighbours is below 3, or any median is off the estimate by
  more than a factor of 3.

**Stop rule.** No height above 5,000,000 is searched. A target not reached
by then is reported as not reached, and a median that would need such a
target is reported as not measured, not as a number. The sampling step in
height is chosen so that the answer does not change by more than 2% when the
step is halved; the notebook prints that check. The same rule is used for
every `N` and every pair of frequencies. No setting is tuned after seeing a
result.

**Why this matters for the connection.** If M3 holds, the height needed
grows fast with the number of primes. That is the measured side of the
statement that Voronin's theorem gives no useful bound on the height.

## Open

- The same for any finite number of primes. Mathlib has no Kronecker
  theorem in several dimensions.
- A reach for statement 3: every label of a narrower band is taken within a
  fixed distance of every height.
- A measurement of how the height needed grows as the tolerance shrinks and
  as primes are added.
- The other two candidates in
  [the proposal](../../book/proposals/proposal-20261124.md) (the waves under
  the count of primes, and the zeros as crossings of a real curve) are not
  checked and not started.
