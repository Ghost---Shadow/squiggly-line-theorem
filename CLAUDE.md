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

Where the rules for the work itself are kept: `lean/STYLE.md` and `lean/PORTING.md` for the
Lean code, `book/WRITING.md` for chapters, `experiments/WRITING.md` for notebooks and figures,
`docs/wishlist.md` for what to prove next, and `CONTRIBUTING.md` for contributors.
