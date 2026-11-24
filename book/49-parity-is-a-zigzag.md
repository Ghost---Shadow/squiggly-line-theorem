# 49. Parity is a zigzag

**In the repository:**
[`ParityZigzag.lean`](../lean/SquigglyLine/Connections/ParityZigzag.lean),
note [`p-versus-np.md`](../docs/connections/p-versus-np.md),
notebook [`parity_zigzag.ipynb`](../experiments/connections/parity_zigzag.ipynb).
**You need:** chapters 3, 8 and 32.

This chapter looks for a connection between the squiggly line and P versus NP, a
famous open question about computers. Nothing in it is progress on that question.
The one connection it finds is a known reason, resting on an unproved assumption,
why a method like this repository's is **not expected** to settle it. The section
"What is not shown" is part of the result.

Each statement is marked. **Proved**: checked by Lean in the files named above.
**Cited**: a published theorem; the author read summaries of the sources, not the
papers, for every cited item below. **Recalled**: from memory, not checked. **The
author's reading**: not a theorem. **Found by search**: the notebook's search only.

## The idea

A problem is in **P** if a computer can solve it in a number of steps that grows
like a fixed power of the size of the input. It is in **NP** if a proposed answer
can be checked that fast. Whether every problem that is quick to check is also
quick to solve is the open question "P versus NP" (**recalled**).

One way to attack it is through **circuits**: networks of AND, OR and NOT gates,
each taking one or two bits and giving one. The **size** of a circuit is its
number of gates. Everything in P can be computed by circuits that are not too
large, so to show that P is not NP it would be enough to show that some problem in
NP needs very large circuits: a **lower bound** (**recalled**).

Several known lower bounds, for weak kinds of circuit, have one shape: find
something a small circuit of that kind cannot do much of, and a function that does
a lot of it (**the author's reading**; other known lower bounds, such as those for
circuits without NOT gates, use different ideas, and the author does not claim
they fit). The standard hard function is **parity**: 0 if an even number of the
input bits are on, 1 if odd. Turn the bits on one at a time and it goes 0, 1, 0, 1.
It is the squiggliest function of bits, and depth makes that squiggle cheap.

## An example you can do by hand

Take four bits. The number of bits on is the **count**:

```
count    0  1  2  3  4
parity   0  1  0  1  0
```

Use the tent layer of chapter 8, `2 × relu(input) − 4 × relu(input − 1/2)`, which
has two neurons. It sends `input` to `2 × input` up to one half and to
`2 − 2 × input` after. Four bits is `2^2`, so use two layers and feed in the share
of bits that are on: 0, 1/4, 1/2, 3/4, 1.

- After the first layer: 0, 1/2, 1, 1/2, 0.
- After the second layer: 0, 1, 0, 1, 0. That is the parity, from four neurons.

Why can one straight piece not do this? The output must be below one half at count
0, above at count 1 and below at count 2, and no straight piece is higher in the
middle than at both ends. So the network must turn between count 0 and count 2,
and a ReLU unit gives one turn, at its kink.

## The statement

Flip any one bit of any string of bits and the parity changes from 0 to 1 or from
1 to 0. This is the first statement.

```lean
theorem flipping_any_bit_flips_parity
    {bit_count : ℕ}
    (bits : BitString bit_count)
    (position : Fin bit_count) :
    let flipped_bits := Function.update bits position (!bits position)
    GET_PARITY flipped_bits = 1 - GET_PARITY bits := by
```

`BitString bit_count` is a string of bits, one for each position, each a `Bool`
(`true` or `false`). `Fin bit_count` is the type of the positions
`0, 1, ..., bit_count − 1`. `Function.update bits position new_bit` is `bits` with
the bit at `position` replaced by `new_bit`. `!bit` is the other bit. `GET_PARITY`
is 0 if the number of bits on is even and 1 if it is odd.

For `2^L` bits, where `L` is the number of layers, put the share of bits that are
on through `L` tent layers and the output is the parity. This is the second
statement.

```lean
theorem deep_narrow_network_computes_parity
    (layer_count : ℕ)
    (bits : BitString (2 ^ layer_count)) :
    let share_of_ones : ℝ := (COUNT_ONES bits : ℝ) / 2 ^ layer_count
    let network_output := APPLY_TENT^[layer_count] share_of_ones
    network_output = GET_PARITY bits := by
```

`COUNT_ONES bits` is how many bits are on. `APPLY_TENT^[layer_count]` is the tent
layer applied `layer_count` times in a row. The network reads the count divided by
`2^L`, not the bits. It has `2 L` neurons for `2^L` bits.

A network with one hidden layer cannot do this cheaply. This is the third
statement.

```lean
theorem shallow_network_needs_one_unit_per_two_bits
    {Index : Type*}
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    (bit_count : ℕ)
    (computes_parity : ∀ bits : BitString bit_count,
      |EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          (COUNT_ONES bits : ℝ)
        - GET_PARITY bits| < 1 / 2) :
    let units_needed := bit_count / 2   -- whole-number division: one unit per two bits
    let unit_count   := units.card
    units_needed ≤ unit_count := by
```

*Read aloud:* a network with one hidden layer of ReLU units that reads the count of
bits that are on, and whose output is closer than one half to the parity for every
string of bits, has at least `n / 2` units, where `n` is the number of bits and the
division rounds down.

`EVALUATE_SHALLOW_NETWORK` is the Python `sum(gain[j] × max(slope[j] × input +
bias[j], 0) for j in units)`, with no constant added at the output. `Finset Index`
is a finite set of unit names, `units.card` is how many there are, and `|...|` is
the absolute value. `bit_count / 2` is whole-number division: 9 bits give 4. For
`2^L` bits the bound is `2^L / 2`: for 1,024 bits, 512 units against 20 neurons.

The bound can be about doubled, and then it cannot be improved.
`shallow_network_needs_one_unit_per_bit_less_one` (**proved**, after the
measurement below) says that the same network has at least `n − 1` units. It asks
less of the network: only that the output is below one half at every even count
and above one half at every odd count. A zigzag with a kink at each count from 1
to `n − 1` computes the parity, so `n − 1` units are also enough. For 1,024 bits
that is 1,023 units against 20 neurons.

## Why it is true

**Flipping a bit.** Split the count into the bit at `position` and all the others.
The flip changes the one bit and leaves the others alone, so the count moves by
exactly one, which swaps even and odd.

**The deep network.** This is `Depth.lean`, which chapter 8 met. Each tent layer
doubles the number of turns, and on the grid of shares `0, 1/2^L, ..., 1` the stack
alternates between 0 and 1. The count over `2^L` is a grid point (`tent_layers_zigzag_on_the_grid`).

**The shallow network.** This is chapter 32 read for parity. "Closer than one half
to the parity" means below one half at an even count and above one half at an odd
count (every count is the count of some string, `some_bit_string_has_each_count`).
A ReLU unit is flat on one side of its kink and straight on the other, so on a
stretch with no kink the whole sum is a straight line, and a straight line cannot
be lower at both ends than in the middle (`not_zigzag`). The stretch from count
`2 × turn` to count `2 × turn + 2` is low, high, low, so it holds the kink of some
unit (`every_up_and_down_holds_a_kink`). These stretches do not overlap and a unit has one
kink, so each needs a different unit (`one_unit_per_turn`): one for every two bits.

**The sharper bound.** Count crossings, not tops. From each count to the next the
network goes from one side of one half to the other, so it crosses one half
somewhere in between: `n` crossings. Between two crossings next to each other
there is a count, where the network is off one half. A straight line that is at
one half at two places is at one half everywhere between them, so the network
bends between the two crossings. These stretches do not overlap: `n − 1` kinks
(`one_unit_per_crossing_less_one`).

**Half of all functions.** The fourth statement, named and not quoted:
`half_of_all_functions_change_at_any_flip` says that, among all functions of bits,
exactly half change at any given flip. Pair each function with the one that has the
opposite value at the string and the same value elsewhere. A function that changed
at the flip is paired with one that did not, and back, so the groups are equal.

## What it explains

| | In this repository | In the theory of circuits |
|---|---|---|
| The squiggly function | a zigzag with `2^L` teeth | parity of `n` bits |
| The weak model | one hidden layer | AND, OR, NOT gates in a fixed number of layers |
| The lower bound | one unit per turn (`one_unit_per_turn`) | a size exponential in a root of the number of bits (Håstad 1986, **cited**) |
| The strong model | `L` tent layers | circuits with more layers |

Håstad's proof is not a count of turns. It uses a tool called the switching lemma:
fix most of the input bits at random, and a small circuit with few layers becomes a
very simple function, while parity stays parity on the bits left. The author puts
the two side by side because they have the same shape, not because they are the
same proof (**the author's reading**).

Linial, Mansour and Nisan (1993, **cited**) built on Håstad's tool and showed that
a function computed by a small circuit with few layers is close to a polynomial of
low degree. A function of bits is a sum of simple waves, one for each set of bits,
with the size of the set as its frequency. Such a circuit is made almost entirely
of low frequencies, and parity of all the bits is the single wave of the highest.

For networks the matching result is Telgarsky's (2016, **cited**): a few layers
make many oscillations, units added at a fixed depth make few.
`DepthSeparation.lean` proves the case of one hidden layer; his theorem, for any
fixed depth, is not proved here.

**The barrier.** The natural proofs barrier (Razborov and Rudich 1997, **cited**)
says why a count of this kind is not expected to settle P versus NP. A property of
functions is **natural** if it can be decided quickly from the table of all the
values of the function and a large enough share of all functions have it. It is
**useful** if no function with small circuits has it. A lower bound of the shape
above needs a useful property. The theorem is conditional: **if** pseudorandom
functions of sufficient strength exist (functions with small circuits that no fast
test can tell from random ones, as cryptography assumes), then no natural property
is useful against circuits of polynomial size. The "if" matters. It is believed and
not proved.

Take "is squiggly" in the plainest sense: changes at many flips of one bit. It can
be read off the table quickly, by counting the flips that change the value, and by
the fourth statement a random function changes at half of all flips on average. So
it is natural. That is the author's reading: the barrier is stated for exact
definitions of "quickly" and "large enough", and the author has not checked them.

For this plain sense no barrier is needed. Parity is as squiggly as a function can
be and has small circuits, so "is squiggly" is not useful against circuits of
polynomial size, with no assumption at all. The second statement is that fact for
networks: a shallow model pays one unit per turn, a deep model does not, so a count
of turns cannot bound it. What the barrier adds is that a cleverer count will not
help either, as long as it stays natural. **So, if pseudorandom functions exist, a
method like this repository's, which measures how squiggly a function is in a way
that is quick to check and common among all functions, cannot separate P from
NP.** That is the connection. It is negative and conditional, and the step from
"this repository's method" to "a natural property" is the author's reading, not a
theorem.

**A second, weaker link.** Blum and Rivest (1988 and 1992, **cited**) showed that
for a network of three threshold units, deciding whether any setting of the
weights fits a given set of examples is NP-complete. This is a link in subject
only: it is about the worst case, and says nothing about the large networks that
gradient descent trains every day.

## How this meets the squiggly line

Through **folds** (chapter 8) and **depth against width** (chapter 32): `L` tent
layers give `2^L` turns from `2 L` neurons, while a wide and shallow network pays
one unit per turn. "Squiggly" has two senses here. For a curve it means slope and
reach (chapters 3 and 4). For a function of bits it means sensitivity or high
frequency. Parity read through the count of bits is a zigzag in the first sense
too, and that is the only place where a proof joins the two. Elsewhere only the
word joins them, and the author's reading of the barrier.

## Run it yourself

[`parity_zigzag.ipynb`](../experiments/connections/parity_zigzag.ipynb) tests four
predictions, Z1 to Z4, which the author wrote and pushed in the note **before** the
notebook was run, with the stop rule: for each number of units from 1 to 8, 200
random starts, 3,000 steps of gradient descent on a loss that is zero when every
count is on the right side of one half by 0.05, one seed, nothing changed after a
result is seen. The network is the Lean one, for 8 bits. Its **margin** is the
smallest over the nine counts of how far the output is on the right side of one
half; it computes parity exactly when the margin is above 0. The helper who wrote
the notebook set other choices before the run, not in the pushed note, and tried
no alternatives: Adam with step size 0.01, starting slopes of plus or minus 1,
starting kinks uniform from −1 to 9, starting gains normal with standard deviation
1, the margin taken at the last step.

The predictions: Z1 (a Lean theorem), no start gets a margin above 0 for 1, 2 or
3 units. Z2, none does for 4, 5 or 6 units. This rested on the author's argument
that the true number is `n − 1`, which had **not been checked by Lean** when the
prediction was written: the network is a curve of straight pieces, at most one
more than it has units, and it must turn between every two neighbouring counts
from 1 to `n − 1`. This one could fail. Z3, the search
finds a margin above 0 for 7 and for 8 units. A 7-unit network that computes
parity was built, but that is **by construction, cannot fail** and is not
evidence; if Z3 fails, Z2 is weak evidence. Z4 (a Lean theorem, in floating
point), `L` tent layers on `count / 2^L` give the parity, `L` from 1 to 10. The
verdicts as printed (`k` is the number of units; counts are **found by search**):

```
[PASS] Z1: successful starts for k = 1, 2, 3: k = 1: 0, k = 2: 0, k = 3: 0; best margins -0.0101, -0.0264, -0.0128; predicted none
[PASS] Z2: starts with a margin above 0 for k = 4, 5, 6, found by search: k = 4: 0, k = 5: 0, k = 6: 0; predicted none (weak: Z3 failed, so the search could not have found a network even if one existed)
[FAIL] Z3: search finds a margin above 0 for k = 7 (0 starts) and for k = 8 (0 starts); predicted at least one each
[PASS] Z4: largest absolute difference over L = 1 to 10 and every count: 0.0e+00; predicted at most 1e-12
```

Best margin over 200 starts (no start had a margin above 0):

| Units | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| Best margin | −0.010121 | −0.026449 | −0.012795 | −0.019669 | −0.004136 | −0.018790 | −0.004136 | −0.009655 |

Z1 and Z4 passed, as they must, since they are proved in Lean. Z3 **failed**: the
search could not find a network that is known to exist, with 7 or 8 units. The notebook printed that the
search is weak and Z2 is weak evidence. Z2 passed in that no start succeeded at 4,
5 or 6 units, but the same search also failed at 7 and 8, where a network exists.
The summary counts it as passed but not evidence (3 of 4 passed, 2 as evidence).
So the measurement neither broke nor supported the claim of `n − 1`. The claim
was proved in Lean afterwards (the sharper bound above), so it does not rest on
this search.

**Diagnostic, added after the run and after a second reader's review; not one of the
predictions, and it changes no verdict.** It is there to tell a weak search from a
bug. Averaged over the 200 starts, dead units (ReLU zero at all nine counts) rose
from 0.12 at the start for 1 unit to 0.71 for 8, and at the end were 0.23 for 1
unit, 1.26 for 7 and 1.16 for 8. With the best margin recorded at **any** step, no
start was above 0 at any step either (best margins from −0.000025 to −0.000290
over the eight values of `k`). Started once from the known 7-unit network, with
gains rescaled to margin 0.05 and noise of 0.01 on every weight, the same training
had margin −0.027735 at the start, 0.072912 at best and 0.051090 at the last step,
above 0: the training code can hold a parity network, but the 200 random starts do
not reach one. The best margins for 5 and 7 units, −0.0041364590 and −0.0041357322,
agree to six digits only; they come from different starts (138 and 123), with 4 and
6 live units and outputs that differ by 0.200, so they are different networks. A search that
finds nothing does not prove that nothing exists, and nothing was tuned to rescue
it. From the formula, for 1,024 bits: 20 neurons for the deep network, 512 for the
first Lean bound, 1,023 for the sharper one (the figure calls it the unproved claim,
which it was when the notebook ran). An experiment is evidence, not a proof. To run it:
`python -m jupyter nbconvert --to notebook --execute --inplace experiments/connections/parity_zigzag.ipynb`

![Three panels. Left: parity of the count for 8 bits as dots at 0 and 1, with the output of three tent layers drawn through them as a zigzag. Middle: the best margin found by search against the number of units from 1 to 8, all below the line at 0, with markers at 4 and 7. Right: neurons against the number of bits on log axes, where the deep network grows slowly and the Lean bound and the unproved claim grow in proportion to the bits](../graphs/parity_zigzag.png)

## What is not shown

- **It is not progress on P versus NP.** The main connection is a barrier. If its
  assumption holds, arguments of this repository's kind will not settle the
  question.
- **Parity is easy.** It is in P: a program computes it in one pass over the bits.
  The Lean statements compare two kinds of small network on an easy function and
  say nothing about a hard problem.
- **The Lean networks see only the count.** Both read how many bits are on, not
  which. A shallow network on the bits themselves is not covered.
- **Cited, not proved here.** Håstad's theorem, the theorem of Linial, Mansour and
  Nisan, Telgarsky's theorem beyond one hidden layer, and the barrier. Mathlib has
  no switching lemma and no pseudorandom functions.
- **"Squiggly" is used in more than one sense.** For a curve it means slope and
  reach. For a function of bits it means sensitivity or high frequency. Parity
  read through the count of bits is a zigzag in the first sense too, and that is
  the only place where the two senses are joined by a proof.
- **The barrier has an assumption.** It needs pseudorandom functions to exist.
  That is believed and not proved. Proving it would itself show that P is not NP
  (**recalled**).
- **The search settled nothing.** The bound of `n − 1` units is proved in Lean.
  The search, 200 starts for each number of units for 8 bits, could not find
  even the network that exists, so it is evidence for nothing.

## Check yourself

1. For 1,024 bits, how many neurons does the deep network have, and what is the
   Lean lower bound for one hidden layer?
2. Does this chapter show that P differs from NP, or bring that closer?
3. When is the natural proofs barrier a theorem, and when is it not?
4. The search found no parity network with 4, 5 or 6 units. Why is that weak
   evidence for `n − 1`?

**Answers.** (1) 10 layers, so 20 neurons; the first bound is `1,024 / 2 = 512`
units (`shallow_network_needs_one_unit_per_two_bits`) and the sharper one is 1,023
(`shallow_network_needs_one_unit_per_bit_less_one`). (2) No. Parity is in P, the
connection is a barrier, and the Lean networks see only the count. (3) Only if
pseudorandom functions of sufficient strength exist, which is believed and not
proved; and that the repository's method is "natural" is the author's reading.
(4) With 7 and 8 units, where a network exists, the same search found none (Z3),
and a search that finds nothing does not prove that nothing exists. The bound
itself is proved in Lean and does not need the search.

Previous: [48. The waves of the primes](48-the-waves-of-the-primes.md) · Next: [Glossary](glossary.md)
