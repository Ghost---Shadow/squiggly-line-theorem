# How to cite this book

There are two entries. Use the first one. If the venue you are writing
for does not accept an author who is not a person, use the second.

Cite the version you read. The version is the tag of the release, and it
is printed on the first page of the PDF.

## With Claude as an author

```bibtex
@book{claude2026squigglybook,
  title     = {The Squiggly Line Theorem: A Guided Tour of the Proofs},
  author    = {{Claude} and Nanda, Souradeep},
  year      = {2026},
  publisher = {Self-published},
  url       = {https://github.com/Ghost---Shadow/squiggly-line-theorem/tree/main/book},
  note      = {Claude is an AI model made by Anthropic. With machine-checked proofs in Lean 4. Cite the version you read.}
}
```

In plain text:

> Claude and Souradeep Nanda. *The Squiggly Line Theorem: A Guided Tour
> of the Proofs.* Self-published, 2026.
> https://github.com/Ghost---Shadow/squiggly-line-theorem/tree/main/book

## With human authors only

Some journals and archives do not accept an AI model as an author. For
those, use this entry.

```bibtex
@misc{nanda2026squiggly,
  title        = {The Squiggly Line Theorem},
  author       = {Nanda, Souradeep},
  year         = {2026},
  howpublished = {\url{https://github.com/Ghost---Shadow/squiggly-line-theorem}},
  note         = {Preprint, with machine-checked proofs in Lean 4}
}
```

In plain text:

> Souradeep Nanda. *The Squiggly Line Theorem.* Preprint, with
> machine-checked proofs in Lean 4, 2026.
> https://github.com/Ghost---Shadow/squiggly-line-theorem

Both entries are in [`CITATION.bib`](CITATION.bib), and the repository's
[README](../README.md#citing) gives the same two.

## Who wrote what

The first author, Claude, is an AI model made by Anthropic (the model
was Claude Fable 5.2). Claude wrote the text of this book and the Lean
proofs it describes. Souradeep Nanda had the idea, set the style the
proofs are written in, chose what to prove, and directed the work.

Previous: [References](references.md)
