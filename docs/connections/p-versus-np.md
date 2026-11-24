# The squiggly line and P versus NP

**Proofs:** [`ParityZigzag.lean`](../../lean/SquigglyLine/Connections/ParityZigzag.lean), with [`DepthSeparation.lean`](../../lean/SquigglyLine/Supporting/NetworkShape/DepthSeparation.lean) and [`Depth.lean`](../../lean/SquigglyLine/Networks/Depth.lean).

Written 24 Nov 2026. This note looks for a connection between the squiggly
line theorem and the question whether P equals NP. It does not say the two
are equivalent, and nothing here is a step towards the question. The
strongest connection found is a known reason, resting on an unproved
assumption, why a method like this repository's is **not expected** to
settle it. The section "What the connection does not
say" is part of the result.

Each statement is marked:

- **proved**: checked by Lean in the files above;
- **cited**: a published theorem. I read summaries of the sources named
  (encyclopedia pages, lecture notes, abstracts), not the papers themselves;
- **recalled**: from memory, not checked against a source;
- **my reading**: an interpretation of mine, not a theorem.

## Words used

- A **bit** is a 0 or a 1. A **function of bits** takes a string of bits and
  gives one bit.
- To **flip** a bit is to change it from 0 to 1 or from 1 to 0.
- A **circuit** is a network of gates. Each gate takes one or two bits and
  gives one: AND, OR or NOT. Its **size** is its number of gates.
- A **unit** is one neuron of a network. A **tent layer** is the two-neuron
  layer of `Depth.lean`, whose graph is a tent.

## The question

A problem is in **P** if a computer can solve it in a number of steps that
grows like a fixed power of the size of the input. It is in **NP** if a
proposed answer can be checked that fast. Whether every problem that is
quick to check is also quick to solve is the open question "P versus NP".
(**recalled**)

One way to attack it is through circuits: networks of AND, OR and NOT gates.
Everything in P can be computed by circuits that are not too large. So to
show that P is not NP it would be enough to show that some problem in NP
needs very large circuits. Results of that kind are called lower bounds.
(**recalled**)

## One way lower bounds are proved: by something like counting squiggles

Several of the lower bounds that are known, for weak kinds of circuit, have
this shape. Find something that a small circuit of that kind cannot do much
of, and a function that does a lot of it. (**my reading** of the results
cited below. Other known lower bounds, such as those for circuits without
NOT gates, use different ideas, and I do not claim they fit.) The standard
hard function is **parity**: 0 if an even number of the input bits are on, 1
if an odd number are.

Parity is the squiggliest function of bits. Turn the bits on one at a time
and it goes 0, 1, 0, 1, ...

What is proved here, in
[`ParityZigzag.lean`](../../lean/SquigglyLine/Connections/ParityZigzag.lean):

1. **Flipping any one bit flips the parity**
   (`flipping_any_bit_flips_parity`, **proved**). No function of bits
   changes more often.
2. **A deep narrow network computes parity**
   (`deep_narrow_network_computes_parity`, **proved**). For `2^L` bits, feed
   the share of bits that are on into `L` tent layers of two neurons each.
   The output is the parity. This is
   [`Depth.lean`](../../lean/SquigglyLine/Networks/Depth.lean): each layer
   doubles the number of turns.
3. **A shallow network needs one unit for every two bits**
   (`shallow_network_needs_one_unit_per_two_bits`, **proved**). Take a
   network with one hidden layer of ReLU units that reads the same count. If
   its output is closer than one half to the parity for every input, it has
   at least `n / 2` units for `n` bits. The parity goes up and down `n / 2`
   times, and each up-and-down needs a unit.
4. **Being squiggly is common**
   (`half_of_all_functions_change_at_any_flip`, **proved**). Fix an input
   and one of its bits. Among all functions of bits, exactly half change
   their value when that bit is flipped.

So for `2^L` bits the deep network has `2 L` neurons and the shallow one
needs `2^L / 2`. For 1,024 bits that is 20 neurons against 512.

A similar count, in the theory of circuits:

| | In this repository | In the theory of circuits |
|---|---|---|
| The squiggly function | a zigzag with `2^L` teeth | parity of `n` bits |
| The weak model | one hidden layer | AND, OR, NOT gates in a fixed number of layers `d` |
| The lower bound | one unit per turn (`card_ge_of_zigzag`) | size `2^(c n^(1/(d-1)))` (Håstad 1986, **cited**) |
| The strong model | `L` tent layers | circuits with more layers |

Håstad's proof is not a count of turns. It uses a tool called the switching
lemma: fix most of the input bits at random, and a small circuit with few
layers becomes a very simple function, while parity stays parity on the bits
that are left. I put it beside the count of turns because the two have the
same shape, not because they are the same proof. (**my reading**)

Linial, Mansour and Nisan (1993, **cited**) built on Håstad's tool and
showed that a function computed by a small circuit with few layers is close
to a polynomial of low degree. A function of bits can be written as a sum of
simple waves, one for each set of bits; the wave of a set is the parity of
those bits, and the size of the set plays the part of a frequency. Their
theorem says that such a circuit is made almost entirely of low
frequencies. Parity of all the bits is the single wave of the highest
frequency. Chapter 18 of the book has a statement of the same flavour for
training: strong, low-frequency directions are learned first.

For networks the matching result is Telgarsky's (2016, **cited**): a few
layers make a function with many oscillations, and adding units at a fixed
depth makes few. `DepthSeparation.lean` proves the case of one hidden layer.
Telgarsky's theorem is for any fixed depth, and that is not proved here.

## The barrier: why this kind of counting is not expected to settle P versus NP

**The natural proofs barrier** (Razborov and Rudich 1997, **cited**). Call a
property of functions *natural* if

- it can be decided quickly from the table of all the values of the
  function, and
- a large enough share of all functions have it.

Call it *useful* if no function with small circuits has it. A lower bound of
the shape above needs a property that is useful. The theorem: **if**
pseudorandom functions of sufficient strength exist (functions with small
circuits that no fast test can tell from random ones, as cryptography
assumes), then no natural property is useful against circuits of polynomial
size. The "if" matters. It is believed and not proved.

Now look at "is squiggly" in the plainest sense: changes at many flips of
one bit.

- It can be read off the table of values quickly: go through the table and
  count the flips that change the value. (**my reading**)
- A large share of functions have it. By statement 4, a function drawn at
  random changes at half of all flips on average.

So "is squiggly" in this sense is natural (**my reading**; the barrier is
stated for exact definitions of "quickly" and "large enough" that I have not
checked this against).

For this plain sense no barrier is needed. Parity is as squiggly as a
function can be (statement 1), and it has small circuits. So "is squiggly" is
simply not useful against circuits of polynomial size. Statement 2 is that
fact for networks: depth makes squiggles cheap, `L` layers give `2^L` turns.
A count of turns beats a shallow model because a shallow model pays one unit
per turn. A deep model does not pay that price, so a count of turns cannot
bound it.

What the barrier adds is that a cleverer count will not help either, as
long as it stays natural. **So, if pseudorandom functions exist, a method
like this repository's, which measures how squiggly a function is in a way
that is quick to check and common among all functions, cannot separate P
from NP.** That is the connection. It is a negative one, it is conditional,
and the step from "this repository's method" to "a natural property" is my
reading, not a theorem.

## A second, weaker link: finding the weights

Blum and Rivest (1988 and 1992, **cited**) showed that for a network of
three threshold units, deciding whether any setting of the weights fits a
given set of examples is NP-complete.

The squiggly line theorem says that a squigglier curve passes closer to the
data and that the loss at the start cannot see this. A fit that exists still
has to be found. Blum and Rivest say that in the worst case, finding it is
as hard as any problem in NP. This is a link in subject only. It is about
the worst case, and it says nothing about the large networks that gradient
descent trains every day.

## What the connection does not say

- **It is not progress on P versus NP.** The main connection is a barrier.
  If its assumption holds, arguments of this repository's kind will not
  settle the question.
- **Parity is easy.** It is in P. A program computes it in one pass over the
  bits. The Lean statements compare two kinds of small network on an easy
  function. They say nothing about a hard problem.
- **The Lean networks see only the count.** Both read how many bits are on,
  not which. A shallow network that reads the bits themselves is not covered.
- **Håstad's theorem, the theorem of Linial, Mansour and Nisan,
  Telgarsky's theorem beyond one hidden layer, and the barrier are cited,
  not proved here.** Mathlib has no switching lemma and
  no pseudorandom functions.
- **"Squiggly" is used in more than one sense.** For a curve it means slope
  and reach. For a function of bits it means sensitivity or high frequency.
  Parity read through the count of bits is a zigzag in the first sense too,
  and that is the only place where the two senses are joined by a proof.
- **The barrier has an assumption.** It needs pseudorandom functions to
  exist. That is believed and not proved. Proving it would itself show that
  P is not NP. (**recalled**)

## The measurement: how many units does a shallow network really need?

This section was written and pushed on 24 Nov 2026 **before** the notebook
`experiments/connections/parity_zigzag.ipynb` was run. The verdicts are
added below it afterwards and the predictions are not edited.

**A claim that is not in Lean.** Statement 3 says a shallow network needs at
least `n / 2` units for `n` bits. I think the true number is `n - 1`. The
reason: the network is a curve made of straight pieces, and it has at most
one more piece than it has units. To be below one half at every even count
and above one half at every odd count, the curve must turn between every two
neighbouring counts from 1 to `n - 1`, and a straight piece cannot turn. So
it needs at least `n` pieces and so at least `n - 1` units. The Lean proof
counts only the turns at the tops, which is why it gets half of this. This
argument is mine, is not checked by Lean, and could be wrong. The
measurement is there to try to break it.

**What is measured.** For `n` = 8 bits the network reads the count of bits
that are on, a whole number from 0 to 8, and has `k` ReLU units in one
hidden layer, with no extra constant added at the output (the same network
as in the Lean statement). It "computes parity" if its output is below one
half at every even count and above one half at every odd count. For each
`k` from 1 to 8 the notebook searches for such a network: 200 random
starting points, each trained by gradient descent on a loss that is zero
exactly when every count is on the right side of one half by a margin of
0.05. It records, for each `k`, the best margin found.

- **Z1, the theorem.** For `k` = 1, 2, 3 (fewer than `n / 2` = 4 units) no
  start finds a network that computes parity. This is statement 3, proved in
  Lean, so a failure here would mean a mistake in the notebook, not in the
  theorem.
- **Z2, the claim above.** For `k` = 4, 5, 6 (at least `n / 2` and fewer than
  `n - 1` = 7 units) no start finds a network that computes parity either.
  The prediction fails if any single start, for any of these `k`, does. A
  failure would refute the argument above.
- **Z3, enough units.** For `k` = 7 a network that computes parity exists: a
  zigzag with a kink at each count from 1 to 7. The notebook builds it and
  checks it (this check holds by construction and is not evidence). I
  predict that the search also finds one for `k` = 7 and for `k` = 8, from at
  least one of the 200 starts. This prediction is about the search, not
  about the mathematics: if it fails, the search is too weak, and then Z2 is
  not good evidence either. The verdict on Z2 will say so.
- **Z4, deep against shallow.** `L` tent layers applied to the share of bits
  that are on give exactly the parity for every count from 0 to `2^L`, for
  `L` from 1 to 10. This is statement 2, proved in Lean; the notebook checks
  it in floating point. A failure would mean a mistake in the notebook.

**Stop rule.** 200 starts for each `k`, 3,000 steps of gradient descent for
each start, one fixed seed, no more. No setting is changed after a result is
seen. If Z3 fails, nothing is tuned to rescue it: the result is reported as
"the search could not find the network that is known to exist".

**What a search can and cannot show.** A search that finds nothing does not
prove that nothing exists. Z2 can refute the claim above. It cannot prove
it.

**What I had already seen when writing this.** One calculation, done to check
that Z3 does not rest on a false statement: with kinks fixed at the counts 1
to 7, a linear programme finds output weights for 7 units that compute
parity. With kinks fixed at 1.5, 2.5, ..., 6.5 it finds none for 6 units.
That second result is for one placement of the kinks and is not the search
of Z2.

### What was measured (24 Nov 2026)

The notebook is
[`experiments/connections/parity_zigzag.ipynb`](../../experiments/connections/parity_zigzag.ipynb).
A Sonnet helper wrote and ran it once from the predictions above and changed
nothing afterwards. I read its report and the chapter it wrote from its
stored output. No second reader has checked this notebook. Settings the
helper fixed before the run, which are not in the predictions above: the
Adam optimiser with step size 0.01, starting slopes of plus or minus 1,
starting kinks uniform from -1 to 9, starting gains normal with standard
deviation 1, and the seed `default_rng(0)`.

![Three panels. Left: parity of the count for 8 bits, with the output of three tent layers drawn through it as a zigzag. Middle: the best margin found by the search against the number of units from 1 to 8, all below zero. Right: neurons against the number of bits on log axes for the deep network, the Lean bound and the unproved claim.](../../graphs/parity_zigzag.png)

Best margin over 200 starts (found by search). A network computes parity
exactly when its margin is above 0. No start reached that for any number of
units.

| Units | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| Best margin | -0.010 | -0.026 | -0.013 | -0.020 | -0.004 | -0.019 | -0.004 | -0.010 |

- **Z1 held**, as it must: no start succeeded with 1, 2 or 3 units.
- **Z3 failed.** The search found no network with 7 units or with 8, though
  one with 7 exists (the notebook builds it by a linear programme; its margin
  is 1.0, by construction). So the search is too weak to find a network even
  where one is known to exist.
- **Z2 held in the letter and shows nothing.** No start succeeded with 4, 5
  or 6 units. But the same search failed where success was possible, so its
  finding nothing here is not evidence for the claim of `n - 1` units. The
  claim was neither broken nor supported.
- **Z4 held**, as it must: the largest difference between the tent layers
  and the parity, over 1 to 10 layers and every count, was 0.

Nothing was tuned after the result, as the stop rule says. The claim that a
shallow network needs `n - 1` units stays what it was: my argument, not
checked by Lean and not tested by this run.

## Open

- A shallow network on the bits themselves.
- The claim of `n - 1` units: a proof in Lean, or a search strong enough to
  find the 7-unit network, which this one was not.
- How the share of flips that change a function is spread round one half,
  for a function drawn at random. The Lean statement gives the average.
- Whether any of this belongs in the book is the author's decision.
