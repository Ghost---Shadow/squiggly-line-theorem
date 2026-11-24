# Position embeddings

**Proofs:** [`Positions.lean`](../../lean/SquigglyLine/Networks/Positions.lean).

Notes from 14 Nov 2026. Each statement is marked **proved**, **argued**,
**recalled** or **open**.

## The idea

Attention is an average, and an average does not know the order of what it
averages. A transformer has to be told where each token is. There are four
common ways. Three of them build in the fact that only the gap between two
positions should matter. The fourth has to learn it.

## The four

Proofs in
[`lean/SquigglyLine/Networks/Positions.lean`](../../lean/SquigglyLine/Networks/Positions.lean).

- **Sinusoidal, all frequencies together.** Give each position one cosine
  and one sine for every frequency. The overlap of the signals of two
  positions is a sum of cosines of the gap between them (**proved**:
  `position_overlap_equals_sum_of_cosines_of_the_gap`). So it depends only on the gap (**proved**:
  `position_overlap_does_not_change_under_a_shift`), and no two positions overlap more than a
  position does with itself (**proved**: `position_overlap_is_at_most_frequency_count`,
  `position_overlap_with_itself_equals_frequency_count`). This is the Fourier lift of `fourier-lift.md`, with
  many frequencies at once.
- **Rotary.** Do not add a signal. Turn the query and the key, each by an
  angle set by its position. The dot product of the two is that of the query
  turned by the difference of the angles, with the key left alone
  (**proved**: `dot_product_after_two_turns_depends_on_angle_gap`). So the score depends on the two
  positions only through their gap (**proved**: `rotary_score_depends_on_position_gap`),
  and no vector changes length (**proved**: `turning_keeps_the_length`). The
  proof is for one pair of coordinates; a real model turns every pair, each
  at its own frequency.
- **Relative position bias.** Add to each score a number looked up by the
  gap. Shifting the whole sequence changes no gap, so it changes no bias
  (**proved**: `relative_bias_does_not_change_under_a_shift`).
- **Learned table.** Give each position a free vector. Changing the vector
  of one position changes nothing at any other (**proved**:
  `learned_table_ties_no_two_positions`). The table is a lookup, a lift that can fit
  anything, and it says nothing about a position it has not seen.

The first three build in the fact that only the gap matters. The table has
to learn it from data, and cannot use it past the longest sequence it was
trained on (**argued**).

## How this meets the squiggly line

Through **the kernel and the lift**. A position signal is a lift of the
position, and what attention sees of two positions is the kernel of that
lift. For the sinusoidal and rotary kinds the kernel depends only on the
gap, which is the property `fourier-lift.md` proves for one frequency.

## What is not shown

- **Rotary positions in full.** The proof is for one pair of coordinates. A
  real model turns every pair, each at its own frequency.
- **Which kind trains best**, and how each behaves on sequences longer than
  those seen in training. The remark on the learned table is **argued**.
- **Other schemes**, such as a bias that grows with the gap.
