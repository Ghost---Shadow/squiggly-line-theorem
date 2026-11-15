# Disclaimer: what Lean does and does not tell you

**Short version.** The proofs in this repository are checked by Lean, a proof assistant.
A green build means one thing: *each theorem follows from its stated hypotheses and
definitions.* It does not mean that the statements say what the plain words around them
say, that the definitions are the right ones, or that the hypotheses describe real neural
networks. The statements, the definitions and the prose were written by a human and an LLM
working together, and either can be wrong. Lean catches mistakes in a proof. It does not
catch a mistake in what is being proved.

This page says what you can rely on, what you cannot, and how to check for yourself.

## What a green build means

When the Lean project builds with no `sorry`:

- every proof step is accepted by Lean's small trusted checker (the kernel);
- every theorem follows from the hypotheses written in its statement, using Lean's logic and
  Mathlib's library of already-checked mathematics;
- no step is skipped, assumed silently or left as "obvious".

That is a strong guarantee about the *derivation*. It is a guarantee about nothing else.

## Where Lean is strong

- **No gaps in the derivation.** A paper proof can skip a step or lean on a condition it
  never states. Lean cannot be talked past a step. `rate_le_one` and
  `direction_is_stretched` appear in the statement of `spectral_bias` because the proof
  needs them.
- **The stated hypotheses are on the page.** Anything written as a hypothesis of a theorem,
  such as `rate_le_one`, is visible in its statement, so that part of the audit is a short
  list. This is not all the assumptions: see weakness 3c, which is the larger part.
- **Arithmetic and algebra mistakes are caught.** A wrong sign, a missed case, an
  inequality that goes the wrong way: these do not build.
- **It is reproducible.** Anyone can rebuild from scratch and get the same answer. CI does
  this on every push.
- **It rests on shared work.** The proofs lean on Mathlib, which many people use and review,
  not on code written for this project alone.

## Where Lean is weak: what it cannot check

### 1. That the statement says what the prose says

Lean checks the theorem you wrote, not the theorem you meant. If the statement is weaker,
different or subtly off compared with the sentence in the book, Lean is silent. The plain
words next to a theorem (the "read aloud" lines, the chapter text, the README) are not
checked by anything.

### 2. That a definition is the right one

A definition such as `GET_RESIDUAL`, `GET_TRAVEL` or `MOVE_ALONG` is whatever its body says.
If the body does not match its name, every theorem that uses it is still true, and may be
about something other than you think. Readable names make a statement easy to follow and
can also make a wrong definition look right.

### 3. That the hypotheses describe the real world

This is the largest gap. Chapter 18 shows it plainly. The proved decay along a direction is
`(1 - rate) ^ step_count`, which is exponential. In Lean that is derived, not assumed. But it
is derived *from a model*: linear in the weights, a fixed kernel, full-batch gradient descent
on squared loss. Real training has minibatch noise, a kernel that moves, other optimisers.
So "training decays exponentially" is an assumption of the model, and the theorem tells
you nothing about real networks to the extent that the model does not fit.

Many results here are exact only for models linear in their weights. The chapters mark
deep networks, noise and other settings as **open**.

### 3a. That the hypotheses can hold at all

A theorem whose hypotheses contradict each other is provable and says nothing. Lean will
accept it. Unless a concrete example is built where all the hypotheses hold, a result may be
empty.

### 3b. That the hypotheses are not doing the work

If a hypothesis is nearly the conclusion restated, the theorem is easy and says little. Lean
cannot judge that. Only reading the statement can.

### 3c. Assumptions that are not written as hypotheses

A theorem's hypothesis list is not the whole list of what it assumes. Assumptions can sit in
places Lean does not flag, and you have to read for them:

- **In definitions.** `TAKE_GRADIENT_STEP` is plain gradient descent on squared loss. That is
  a choice of optimiser and loss, built into a definition, and every theorem about
  "training" inherits it without a hypothesis saying so. `LinearPredictor` builds in
  linearity the same way.
- **In types.** Working over the real numbers, in a finite-dimensional inner product space,
  with a fixed data set, is an assumption about the setting that no statement lists.
- **In the form of the conclusion.** Stating a bound with `Real.exp (-(step_count * rate))`
  frames the result as exponential decay. The bound is proved, not assumed, so it is not a
  logical hypothesis. But the choice to present it that way carries a modelling picture the
  reader may take for a finding about networks. The same goes for choosing to measure error
  along an eigenvector, or to compare two directions.
- **In what was chosen to be proved.** A theorem about the sine case says nothing about other
  cases, and the title of a chapter can suggest more than the statement covers.

So auditing the listed hypotheses is necessary and not enough. You also have to read the
definitions the statement uses, the setting it lives in, and the way the conclusion is put.

### 4. Lean's own conventions, which differ from ordinary mathematics

Lean totalises some operations, and a statement can be technically true for a strange reason:

- division by zero is zero (`x / 0 = 0`);
- the square root of a negative real is zero;
- the logarithm of zero is zero;
- subtraction on natural numbers stops at zero (`3 - 5 = 0`).

A theorem that quietly depends on one of these may not mean what it appears to. A careful
statement guards against this with explicit hypotheses; Lean does not warn you.

### 5. The trusted base

A green build trusts, at minimum: Lean's kernel, Mathlib, the compiler and the machine it
ran on. These are widely used and very reliable. They are not infinitely so, and a bug in
any of them could in principle accept a false proof. This is rare, but it is not zero.

### 6. Things a build does not forbid by itself

- `sorry` (a proof left unfinished) is caught here by a CI text search. It is not enforced by
  the build itself, and a text search is a blunt tool.
- A new `axiom`, `native_decide` (which trusts the compiler), `unsafe` code or similar
  declarations can make a build pass without a real proof. The README states that each
  theorem depends only on Lean's three standard axioms. **The CI workflow I read does not
  enforce this** (it builds and searches for `sorry`). Check it yourself with
  `#print axioms theorem_name` (see below) before relying on the claim.

### 7. Restyling the code

The Lean code was rewritten to be readable ("pythonic"). A restyle can change a statement by
accident. This repository guards against it with
`lean/SquigglyLine/Tests/StatementsUnchanged.lean` and `lean/tools/StatementFingerprint.lean`,
which hash every statement. These catch accidental changes in what was checked at the time.
They cannot say the original statement was the right one.

### 8. People and an LLM wrote this

The statements, definitions, proofs and prose were produced by a human and an LLM working
together. An LLM can write a plausible, wrong statement and a correct proof of it. Lean
rejects wrong proofs. It does not reject wrong statements. Human review of the statements is
the safeguard, and it is not complete.

## What is not Lean at all

Much of the repository is not proved:

- **Experiments** are **measured**: they show what happened in particular runs, not what must
  happen.
- **Cited results** marked **recalled** are written from memory of a paper, not checked
  against it. They may be wrong. An audit is planned, and the label is to be removed only
  when the paper has been read. Until then, treat every **recalled** claim as unverified.
- Claims marked **argued** have a reasoning but no proof. Claims marked **open** are not known.
- The plain-language text is not checked by anything.

The book labels each claim in this way (**proved**, **measured**, **recalled**, **argued**,
**open**). Read the label before relying on the claim.

## How much to trust it: by kind of claim

| What you read | How far to trust it |
|---|---|
| "Lean proves X follows from H" (and the build is green) | Very high: the derivation is sound, subject to the trusted base |
| "X is what the statement says" | High, if you have read the statement and its definitions. Lower if you only read the prose |
| "H is a reasonable description of real networks" | Not checked by Lean. A modelling judgement; see the experiments and the **open** items |
| "This was measured in a run" | Trust the run, not a general claim |
| "**recalled**, from a paper" | Low until audited |
| A plain-language explanation | As good as the author's reading, and checked by nothing |

Do not trust the whole thing blindly. Trust the derivation, check the statement, and treat
the link from model to real networks as a claim of a different kind.

## How to check for yourself

1. **Read the statement, not only the badge.** Open the theorem and read the hypotheses and
   the conclusion. Do the hypotheses fit your case?
2. **Read the definitions it uses.** Follow each capitalised name to where it is defined,
   and ask what each one assumes (the optimiser, the loss, linearity, the setting). These
   assumptions are not in the hypothesis list.
3. **Build it.** From `lean/`, run `lake build`. Search for `sorry`, `axiom`,
   `native_decide` and `unsafe` in `lean/SquigglyLine`.
4. **List the axioms a theorem uses.** Add `#print axioms SquigglyLine.theorem_name` to a
   scratch file importing `SquigglyLine`. Expect only `propext`, `Classical.choice` and
   `Quot.sound`. Anything else, or `sorryAx`, is a red flag.
5. **Look for an instance.** Can you find numbers that satisfy every hypothesis? If not, the
   theorem may be empty.
6. **Check against the experiments.** The notebooks under `experiments/` test the claims with
   numbers. A check that cannot fail would prove nothing, so they are written to be able to
   fail.
7. **Read the "What is not shown" section** of each chapter for what the theorem does not
   cover.

## What this repository does about it

- Builds on every push and fails on `sorry` (`.github/workflows/lean.yml`).
- Pins statements with `StatementsUnchanged` and a statement-fingerprint tool.
- Writes a "Python beside the Lean" version of each statement.
- Labels every claim by how it is known, and lists what is not shown in each chapter.
- Runs experiments for the claims, including outside the stated model, where it can.

What it does not yet do, and is listed as work to do: an automatic check of which axioms each
theorem uses; a standing audit of each theorem's hypotheses for satisfiability; checking each
**recalled** claim against its paper.

## If you find a problem

A mistaken statement, a definition that does not match its name, a hypothesis that cannot
hold, a **recalled** claim that does not match its paper: please open an issue. See
[CONTRIBUTING.md](CONTRIBUTING.md).

---

> "All models are wrong, but some are useful."
>
> George E. P. Box
