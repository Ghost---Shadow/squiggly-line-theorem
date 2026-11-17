# Writing a chapter's notebook: the brief for helpers

Each chapter of the book gets **one Jupyter notebook** that checks the
chapter's claims with numbers. A notebook may hold several experiments.
Your prompt names your chapter. Everything else is here.

## Read first, once each

1. `experiments/part1/README.md`, `experiments/part1/common.py` and one
   finished notebook, `experiments/part1/ch04_nearness.ipynb`. Copy their
   form: what a cell explains, how a check is asserted, how a figure is
   drawn and saved.
2. Your chapter in `book/`, and its "Run it yourself" counterpart in
   `book/04-nearness.md`, to see how a chapter reports measured numbers.
3. The Lean file your chapter names, statements only, so that each
   experiment checks what the theorem says and nothing wider.

## What to make

- `experiments/partN/chNN_short_name.ipynb`, where `partN` is the part of
  the book your chapter is in: `part1` for chapters 1 to 7, `part2` for 8
  to 12, `part3` for 13 to 16, `part4` for 17 to 27, `part5` for 28 to 35,
  `part6` for 36 to 41, `part7` for 42 to 46. Create the folder if it is
  missing.
- Its figures, saved as PNG into `book/figures/NN-what-it-shows.png`.
  **Every chapter gets at least one figure** (see "Rules for figures").
- In your chapter file, each figure next to the claim it shows, and a section
  `## Run it yourself` just before `## What is not shown` (or before
  `## Check yourself` if the chapter has no such section): what the
  notebook checks, the measured numbers, and the command to run it.

## Rules for the notebook

- **One experiment per claim the chapter makes.** State the claim in a
  markdown cell, run the experiment, then `assert` the result and print a
  line starting `[PASS]`. A failed check must stop the notebook.
- **A check must be able to fail.** Ask of each one: would it fail if the
  claim were false? Do not loosen a threshold to make a check pass
  without saying so in the cell and in your report.
- **No check by construction.** A check that compares a formula with
  itself, or asserts something the code forces to be true, is not a check.
  Leave it out, or print it with the words "by construction, cannot fail"
  and do not count it as evidence in the chapter.
- **"Measured" means the model was run.** A number is measured only if it
  came out of a fit, a training run or a sampled model. A number that came
  from evaluating the chapter's formula is "from the formula". Say which.
- **Cite only what is printed.** Every number in the chapter's section
  appears in the notebook's stored output.
- **Seed everything.** Two runs must print identical `[PASS]` lines.
- **The right stand-in model.** Use the model the theorem is about. Where
  a proof assumes a model that is *linear in its weights*, train the sine
  and cosine coefficients of fixed frequencies, which is linear. Training
  an amplitude and a phase per term is not linear: use it only to show
  what changes when the features move, and say so. For folds use the tent
  layer and ReLU networks. Say in the first cell which model is used.
- **Cheap.** The whole notebook runs in under two minutes on a laptop CPU.
- **Names.** Locals are `snake_case`, constants are `SCREAMING_SNAKE_CASE`,
  functions are verbs (`measure_travel`, `draw_curve`). No single-letter
  names, in code or in prose.
- **Self-contained.** Helpers your chapter needs go in your notebook.
  Create no shared file.
- **Say what you expect before you run it.** The markdown cell that states
  a claim also says what number or shape is predicted, and what result
  would count against the claim. Write it before the code cell, not after
  seeing the output.
- **Print only what was computed.** No cell prints a conclusion as literal
  text. A summary line is built from the measured numbers.
- **Two distances.** Wherever a Euclidean (nearest) distance is reported,
  report the vertical error next to it. The loss sees only the vertical
  one.
- **Squiggliness alone.** When an experiment varies how squiggly a curve
  is, hold its amplitude fixed.
- **A control.** Where you can, add one case in which the hypothesis of the
  theorem is broken, and show that the conclusion then fails. Report the
  size of the failure.

## Rules for figures

- **At least one per chapter**, showing the mechanism the chapter proves.
  A second only if it shows something the first cannot. One good figure
  beats three.
- A figure shows one of these: the quantity the theorem is about against
  the quantity it depends on; the bound or the exact result on the same
  axes as what was measured; a case where the claim holds beside one where
  it breaks.
- Every number drawn comes from the notebook, from a seed. Do not draw a
  cartoon that looks like data. If a picture is a schematic, say so in its
  alt text.
- **Style.** Call `use_style()` from `experiments/part1/common.py` and use
  its colour constants and `save_figure`. That gives seaborn's default
  theme, the "deep" palette and the `paper` context. Do not edit
  `common.py`, and do not choose another style, palette or context.
  Colour follows the quantity: blue the nearest distance, orange the
  vertical error, green a bound, purple the model, grey "before" or
  "without".
- Every axis is labelled in plain words, with the unit where there is one.
  The title says what the figure shows. No label sits on a curve. With
  two or more curves there is a legend.
- The `paper` context makes text small. Keep figures about 5 to 7 inches
  wide so the text is legible on the site.
- In the chapter, the image link carries alt text that says what is shown
  and what differs between the curves:
  `![Error left against steps, for a strong and a weak direction, between the two bounds](figures/18-two-bounds.png)`.
  Put the label (**measured**, or **proved** for an exact curve) in the
  sentence before the figure.

## Rules for the chapter text

- Numbers in the chapter are copied from the notebook's output.
- Call them **measured**. An experiment is evidence, not a proof: say so
  once in the section.
- Change nothing else in the chapter, and do not touch quoted Lean.
- If your prompt points you at a section of `book/proposals/`, read those
  lines only. They say which experiments the author asked for.

## Before you report

```bash
jupyter nbconvert --to notebook --execute --inplace experiments/partN/chNN_*.ipynb
python book/tools/check_book.py NN
```

Run the notebook twice and compare the `[PASS]` lines. The checker must
end with `problems: 0`.

Write only your notebook, your figures and your chapter. If you make the
notebook with a script, name the script `experiments/partN/_build_chNN.py`
(your chapter number in the name, never a shared temporary folder: other
helpers use the same names there) and delete it before you report. Do not run git,
and do not run `lake`. Other helpers are working on other chapters at the
same time: do not touch their files, `common.py`, or `book/README.md`.

## Your report

Under 100 words: files written, the `[PASS]` count, any threshold you
changed after a failure and why, and any claim of the chapter that the
experiment did **not** bear out. That last item is the most useful thing
you can report.
