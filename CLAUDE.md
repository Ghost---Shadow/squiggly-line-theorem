# Notes for agents working in this repository

> "All models are wrong, but some are useful." (George E. P. Box)

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
