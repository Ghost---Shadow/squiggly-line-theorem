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

## Open

- A shallow network on the bits themselves.
- How the share of flips that change a function is spread round one half,
  for a function drawn at random. The Lean statement gives the average.
- Whether any of this belongs in the book is the author's decision.
