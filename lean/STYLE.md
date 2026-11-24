# How the Lean code is written

A proof is code. It is read more often than it is written. Every statement in
this project is written so that a reader with high-school mathematics and
good Python can follow what is claimed. The model file is
[`SquigglyLine/Theorem/SquigglyLineTheorem.lean`](SquigglyLine/Theorem/SquigglyLineTheorem.lean).
A file of definitions and small lemmas in the same style is
[`SquigglyLine/Theorem/Defs.lean`](SquigglyLine/Theorem/Defs.lean).

A restyle changes names and layout. It never changes the mathematics.

New proofs are found in typical Mathlib style first and then ported. The
standing brief for that port is [`PORTING.md`](PORTING.md).

## Names

| Kind | Case | Examples |
|---|---|---|
| a local name: a binder, a hypothesis, a `let`, a `have` | `snake_case` | `amplitude`, `learning_rate`, `slope_is_bounded` |
| a global function or constant | `SCREAMING_SNAKE_CASE` | `GET_NEAREST_DISTANCE`, `PI` |
| a type, or a type variable | `PascalCase` | `DataPoint`, `RealFunction`, `Weights` |
| a theorem | a `snake_case` sentence that says what is true | `nearest_distance_is_at_most_vertical_distance` |

- No single letters and no Greek, anywhere a reader has to read. `i`, `j`
  and `k` are allowed as indices of a sum, as in Python.
- A function is named as a verb. `GET_...` returns a value. `MAKE_...`
  builds an object. `TAKE_...`, `APPLY_...`, `RUN_...` do one step of
  something. `IS_...`, `HAS_...`, `ARE_...`, `HOLDS_...` answer yes or no.
- A hypothesis is named for what it says, not for what it is about:
  `frequency_pos`, `labels_in_band`, `slope_is_bounded`. Never `h`, `hf`,
  `hμ`.
- A theorem name is a sentence in `snake_case` that says what is true, with
  no clipped words: `distance`, not `dist`; `equals`, not `eq`. The signs are
  spelled `is_at_most` for `≤`, `is_less_than` for `<` and `equals` for `=`
  (decided by the author on 24 Nov 2026). By the same pattern `≥` is
  `is_at_least`, `>` is `is_greater_than` and `≠` is `is_not`; these three
  are not yet confirmed. A few short names that are known by now stay as
  they are: `squiggly_line_theorem`, `closer_but_no_better`.
- Notes, the book, the paper and the notebooks refer to theorems by name. So
  a rename goes through [`RENAMES-theorems.txt`](RENAMES-theorems.txt) and
  `scripts/rename_theorems.py`, which changes the name everywhere at once.
  The files of `Theorem/`, `Networks/`, `Connections/` and
  `Supporting/NewInputs/` follow the rule. The files of
  `Supporting/NetworkShape/` and `Supporting/Training/` still have their
  older, Mathlib-like names (`card_ge_of_zigzag`) until their turn comes.
- Names from Mathlib are not changed (`dist`, `Measurable`, `LipschitzWith`).
- The circle constant is `PI`. A bare `pi` is not a name Lean knows.

Names used across the project for the same thing:

| Was | Is |
|---|---|
| `f`, `g` (a function being fitted) | `model`, `other_model`; a fixed shape is `profile` |
| `p`, `q` (a data point) | `data_point`, `other_point` |
| `x`, `x'` | `input`, `other_input` |
| `y` (one label) / `y` (all labels) | `label` / `labels` |
| `θ`, `θ₀`, `θ₁` | `weights`, `start_weights`, `end_weights` |
| `A` (weights to predictions, linear) | `predict` |
| `A` (an amplitude) | `amplitude` |
| `w`, `w'` (a frequency) | `frequency`, `other_frequency` |
| `φ` (a phase) / `φ` (a feature map) | `phase` / `features` |
| `η` | `learning_rate` |
| `K` (a slope bound) | `slope_limit` |
| `ρ` | `reach` |
| `ℓ` | `loss_fn` |
| `μ` (a data distribution) | `data_distribution` |
| `n`, `m` (a count) | a name for what is counted: `step_count`, `layer_count` |
| `t` (a fraction along a path) | `fraction` |
| `ε` | `tolerance`, or `noise` when it is noise |
| `Θ`, `Y`, `X`, `E` (type variables) | `Weights`, `Outputs`, `Inputs`, `Space` |

## Types

No type inside a type in a signature. Give the inner type a name once, in
[`Style.lean`](SquigglyLine/Style.lean),
[`Vocabulary.lean`](SquigglyLine/Theorem/Vocabulary.lean) or at the top of
the file that needs it, and use the name: `RealFunction` for `ℝ → ℝ`,
`Model Inputs` for `Inputs → ℝ`, `DataDistribution` for
`Measure (DataPoint ℝ)`. A new name is an `abbrev`,
so every existing lemma still applies.

## Statements

1. One binder per line, each on its own line under the theorem name.
2. Each quantity in the statement gets a `let`. Each `let` is one line.
3. Each side of an "and", an "or" or an "if and only if" gets a name. So
   does the hypothesis of an "implies". The last line only combines names.
4. A quantity that several statements need is a global function, defined
   once above them and called. It is not repeated as a `let`.
5. This holds for one-line lemmas too. Lines are good: a reader takes a
   statement in small pieces.
6. Code stays within 80 columns. A comment at the end of a line may run
   past, to about 130.

```lean
/-- The line is never further away than the vertical error. -/
theorem nearest_distance_is_at_most_vertical_distance
    (model : Inputs → ℝ)
    (data_point : DataPoint Inputs) :
    let nearest_distance := GET_NEAREST_DISTANCE model data_point
    let vertical_error   := GET_VERTICAL_ERROR model data_point  -- straight up or down is one way to reach the line
    nearest_distance ≤ vertical_error := by
  unfold_named_pieces
  ...
```

## Comments

A comment at the end of a line says why that line is what it is. It explains
a number or a formula that would otherwise look like magic: where a `2`
comes from, why there is a square root, what a condition is for. A line that
explains itself gets no comment. About half the lines have none.

Every file opens with a summary in plain words. Every theorem has a
docstring in plain words. A definition's docstring ends with its Python
reading where one helps.

## Proofs

A statement is the interface and a proof is the implementation. Proofs keep
their tactics. What changes:

- The first line of a tactic proof is `unfold_named_pieces` (from
  [`Style.lean`](SquigglyLine/Style.lean)), which replaces each `let` of the
  statement by what it stands for. The rest of the proof then runs as
  before. A proof written as a single term needs no such line.
- `rw [some_lemma]` does not accept a lemma whose statement is an "if and
  only if" behind `let`s. Use `simp only [some_lemma]`, `(some_lemma ..).mp`
  or `rw [propext (some_lemma ..)]`.
- Hypotheses and local names follow the naming rules above.
- A step that carries the idea of the proof has a comment in plain words
  above it, and a `have` is named for what it establishes.

### When a `have` becomes a lemma

A `have` is a local lemma: it has its own stated type and its own proof, and it
exists only inside the proof around it. A `lemma` has a global name and can be
reused. Neither adds an assumption, so this is about reading and reuse, not
correctness. (Measured on 15 Nov 2026: about 550 `have`s, of which 47% are
three lines or fewer, 16% are eight lines or more, and only about 11% repeat
another `have`'s statement.)

Do not ban `have`. Promote a `have` to a top-level lemma when any one of these
holds:

1. **It repeats.** The same statement is proved twice or more, in one file or
   across files (for example, that the softmax denominator is positive).
2. **It is long.** Its proof runs to about eight lines or more. It is a lemma
   in disguise and makes the theorem hard to read.
3. **A reader would look it up by name.** It states a fact worth finding on
   its own.

Keep a short one-line fact that only this proof uses as a `have`. A promoted
lemma follows every rule above: a named statement, a plain-words docstring, and
its hypotheses spelled out, since it no longer sees the theorem's context.

## Checks

- Every push is built from scratch by CI, which fails on any `sorry`.
- A misspelt name is an error (`autoImplicit = false`).
- A restyle is checked by fingerprint: every theorem and definition is
  hashed before and after, ignoring names, `let`s and layout. A statement
  whose mathematics changed gets a different hash.
