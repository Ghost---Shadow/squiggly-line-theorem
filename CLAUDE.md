# Notes for agents working in this repository

## The philosophy of the project

The owner is "investing" tokens in this repository. The goal is not citations, a paper
count or attention. The goal is for LLMs to become a better product.

> "All models are wrong, but some are useful." (George E. P. Box)

- **Product focus.** Ask of every piece of work whether it helps build a better product.
  Prefer what can be used (a rule that predicts a hyperparameter, a check that catches a
  mistake, an explanation a model gets right) over what is only interesting or impressive.
- **Utility is truth.** This is the owner's working stance. A theorem about a fixed-kernel
  model is a model, and it is worth what it is useful for: whether its numbers are a good
  guide for a real network, not whether it is exactly true of one. Judge work that way, not
  by how it would read in a paper.
- **Usefulness has to be shown.** "Useful" is a claim like any other: test it against real
  runs, and say where the model stops being a good guide. Say how each claim is known
  (**proved**, **measured**, **recalled**, **argued**, **open**), name what the model leaves
  out, and never present a recalled citation as checked or invent a reference. The labels are
  what let a reader know how far to rely on a model.
- Lean checks proofs, not whether the statement is the right one. See `DISCLAIMER.md`.

## Rules for experiments

These were in `handoff.md` (removed 15 Nov 2026; the text is in git history at `e69437f^`)
and still apply. They are what keeps a measured claim honest.

- **State the prediction and the stop rule before the run**, for any experiment that tests a
  hypothesis, and apply the same criterion to every curve or setting. A result that can only
  confirm is not evidence. (Thresholds of regression-style assertions in notebooks are set
  from measured numbers with a stated margin, as `experiments/WRITING.md` says.)
- **No hardcoded conclusion blocks.** Print only what the script computed. A "KEY FINDINGS"
  block of literal text is a conclusion written before the data. See `docs/EXPERIMENT_LOG.md`.
- **Report the vertical residual next to every Euclidean distance.** The loss only sees the
  vertical one.
- **Hold amplitude fixed when varying squiggliness.** Polynomial degree and unscaled width
  change the amplitude too.
- **Size the sample grid for the steepest slope**, or use `scripts/curves.py`. A fixed grid
  overestimates distance for steep curves.
- **Do not fix the legacy metrics.** They are the evidence behind
  `scripts/audit_legacy_metrics.py`.
- **Check a derived formula numerically before relying on it.** The first derivation of
  diminishing returns in this project had a sign error that a numerical check caught.

Where the rules for the work itself are kept: `lean/STYLE.md` and `lean/PORTING.md` for the
Lean code, `book/WRITING.md` for chapters, `experiments/WRITING.md` for notebooks and figures,
`docs/wishlist.md` for what to prove next, and `CONTRIBUTING.md` for contributors.
