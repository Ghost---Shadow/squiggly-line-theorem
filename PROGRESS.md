# Progress to the first full edition

This is the list behind the progress bar under the title of the
[README](README.md).

The bar is the share of the items below that are done. Each item counts the
same, so the number is rough. An item with a count, such as (16 of 34), counts
for that fraction. The list is what the first full edition needs: what stands
today, and the work planned for the existing book in
[the current plan](book/proposals/proposal-20261117.md). New projects in that
plan are not counted. To change the bar, tick an item here and run
[`scripts/readme_progress.py`](scripts/readme_progress.py).

## Proofs

- [x] The squiggly line theorem, checked by Lean and rebuilt on every push
- [x] Every Lean statement quoted in the book matches the sources
- [x] Chapter 18: strong directions first for any kernel, and the Fourier version
- [ ] Chapter 17: the two open items about plates (1 of 2)
- [ ] Chapter 5: a proof that standard initialisation gives the same loss at every width
- [ ] Theorem names in the same style as the rest of the code
- [ ] Long proof steps split into named lines, and long repeated steps made lemmas

## Book

- [x] All 47 chapters written
- [x] At least one figure in chapters 1 and 3 to 47
- [ ] Every "recalled" claim checked against its paper
- [ ] A "Preliminaries" section at the start of every chapter
- [ ] Under each open item, what stood in the way of a proof
- [ ] Units for the numbers in the worked examples
- [ ] One shared BibTeX file for the book and the paper
- [ ] The planned edits to chapters 2, 6, 7, 8, 17, 18 and 19
- [ ] The places where a measurement and a chapter differ, read and settled

## Experiments

- [x] A notebook for chapters 1 and 3 to 47
- [ ] The notebooks of chapters 14 to 47 read by a second reader (16 of 34)
- [ ] A test of whether the theory can guess hyperparameters

## Publishing

- [x] A PDF built on every push, and a web edition
- [x] A draft of the paper
- [x] Lean highlighting on the website, built and looked at
- [ ] Lean code blocks in `docs/` checked against the sources
