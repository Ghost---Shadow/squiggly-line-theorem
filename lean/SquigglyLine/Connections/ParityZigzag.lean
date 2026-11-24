/-
Parity is a zigzag: a first link to circuit lower bounds and P versus NP.

`docs/connections/p-versus-np.md` has the plain account. In short: the
parity of a string of bits is 0 when an even number of bits are on and 1
when an odd number are. Turn the bits on one at a time and the parity goes
0, 1, 0, 1, ... It is the squiggliest thing a function of bits can do.
Several known proofs that small circuits of a weak kind cannot compute some
function have a similar shape, and parity is their standard hard case.

This file proves five things.

* `flipping_any_bit_flips_parity`: every single bit changes the parity. No
  function of bits changes more often.
* `deep_narrow_network_computes_parity`: `layer_count` tent layers, two
  neurons each, compute the parity of `2 ^ layer_count` bits from the count
  of bits that are on.
* `shallow_network_needs_one_unit_per_two_bits`: a network with one hidden
  layer that reads the same count needs at least one unit for every two
  bits. This is `card_ge_of_zigzag` of `DepthSeparation.lean`, read for
  parity.
* `shallow_network_needs_one_unit_per_bit_less_one`: in fact it needs one
  unit for every bit, less one, and that cannot be improved. This is
  `card_ge_of_alternating_sides`, read for parity.

* `half_of_all_functions_change_at_any_flip`: among all functions of bits,
  exactly half change at any given flip. So being squiggly is common.

So for `2 ^ layer_count` bits a deep network uses `2 * layer_count`
neurons and a shallow one needs `2 ^ layer_count - 1` units.

Both networks see only how many bits are on, not which. That is a real
limit on the statement. Parity is easy to compute. Nothing here is about a
hard problem, and nothing here is a step towards P versus NP.

| Name         | Meaning                                              |
|--------------|------------------------------------------------------|
| `BitString`  | a string of bits, one for each position              |
| `COUNT_ONES` | how many of the bits are on                          |
| `GET_PARITY` | 0 if that count is even, 1 if it is odd              |

How to read the notation:

* `Fin bit_count` is the type of the positions `0, 1, ..., bit_count - 1`.
* `Function.update bits position new_bit` is `bits` with one bit replaced.
* `!bit` is the other bit: `!true = false` and `!false = true`.
* `APPLY_TENT^[layer_count]` is the tent layer applied that many times.

To do, not attempted:

* A shallow network that reads the bits themselves, not their count.
* The same count of squiggles for circuits of AND, OR and NOT gates of a
  fixed depth (Håstad's theorem). That needs the switching lemma, which
  Mathlib does not have.
-/
import SquigglyLine.Supporting.NetworkShape.DepthSeparation

namespace SquigglyLine

/-- A string of bits.
Python: `list[bool]` of length `bit_count`. -/
abbrev BitString (bit_count : ℕ) := Fin bit_count → Bool

/-- How many of the bits are on.
Python: `sum(1 for bit in bits if bit)`. -/
def COUNT_ONES
    {bit_count : ℕ}
    (bits : BitString bit_count) : ℕ :=
  ∑ position, if bits position then 1 else 0

/-- The parity of a string of bits: 0 if an even number are on, 1 if an odd
number are.
Python: `COUNT_ONES(bits) % 2`. -/
noncomputable def GET_PARITY
    {bit_count : ℕ}
    (bits : BitString bit_count) : ℝ :=
  if Even (COUNT_ONES bits) then 0 else 1

/-! ## Counting the bits that are on -/

/-- No more bits are on than there are bits. -/
theorem count_of_ones_is_at_most_bit_count
    {bit_count : ℕ}
    (bits : BitString bit_count) :
    let ones_count := COUNT_ONES bits
    ones_count ≤ bit_count := by
  unfold_named_pieces
  unfold COUNT_ONES
  calc ∑ position, (if bits position then 1 else 0)
      ≤ ∑ _position : Fin bit_count, 1 :=
        Finset.sum_le_sum fun position _ => by split_ifs <;> simp
    _ = bit_count := by simp

/-- Every count from 0 to `bit_count` is the count of some string: turn on
the first `ones_count` bits. -/
theorem some_bit_string_has_each_count
    {bit_count : ℕ}
    {ones_count : ℕ}
    (count_fits : ones_count ≤ bit_count) :
    ∃ bits : BitString bit_count, COUNT_ONES bits = ones_count := by
  refine ⟨fun position => decide (position.val < ones_count), ?_⟩
  unfold COUNT_ONES
  simp only [decide_eq_true_eq]
  -- A sum over positions is a sum over the numbers below `bit_count`.
  rw [Fin.sum_univ_eq_sum_range
    (fun position_number => if position_number < ones_count then 1 else 0)
    bit_count]
  -- A sum of ones over the positions that pass a test counts them.
  rw [Finset.sum_boole]
  have positions_that_are_on :
      (Finset.range bit_count).filter (fun position_number =>
        position_number < ones_count) = Finset.range ones_count := by
    ext position_number
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [positions_that_are_on]
  simp

/-! ## Parity changes at every step -/

/-- **Flipping any one bit flips the parity.** A function of bits cannot be
more sensitive than this: every neighbour of every input has the other
value. -/
theorem flipping_any_bit_flips_parity
    {bit_count : ℕ}
    (bits : BitString bit_count)
    (position : Fin bit_count) :
    let flipped_bits := Function.update bits position (!bits position)
    GET_PARITY flipped_bits = 1 - GET_PARITY bits := by
  unfold_named_pieces
  -- Split the count into the bit at `position` and all the other bits.
  have count_split : ∀ any_bits : BitString bit_count,
      COUNT_ONES any_bits
        = (if any_bits position then 1 else 0)
          + ∑ other ∈ Finset.univ.erase position,
              if any_bits other then 1 else 0 := by
    intro any_bits
    unfold COUNT_ONES
    exact (Finset.add_sum_erase Finset.univ
      (fun other => if any_bits other then 1 else 0)
      (Finset.mem_univ position)).symm
  -- The other bits are not touched by the flip.
  have other_bits_unchanged :
      ∑ other ∈ Finset.univ.erase position,
          (if Function.update bits position (!bits position) other
            then 1 else 0)
        = ∑ other ∈ Finset.univ.erase position,
            if bits other then 1 else 0 :=
    Finset.sum_congr rfl fun other other_in_rest => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase other_in_rest)]
  unfold GET_PARITY
  rw [count_split (Function.update bits position (!bits position)),
    count_split bits, other_bits_unchanged, Function.update_self]
  -- Call the count of the other bits `rest_count`.
  generalize (∑ other ∈ Finset.univ.erase position,
    if bits other then 1 else 0) = rest_count
  -- One more bit on swaps even and odd.
  have one_more_swaps : Even (1 + rest_count) ↔ ¬ Even rest_count := by
    rw [add_comm, Nat.even_add_one]
  -- Whichever way the bit was, the flip moves the count by one.
  cases bits position <;>
    by_cases rest_is_even : Even rest_count <;>
    simp [one_more_swaps, rest_is_even]

/-! ## Deep and narrow against shallow and wide -/

/-- **A deep narrow network computes parity.** For `2 ^ layer_count` bits,
feed the share of bits that are on into `layer_count` tent layers. The
output is the parity. Each tent layer has two neurons. -/
theorem deep_narrow_network_computes_parity
    (layer_count : ℕ)
    (bits : BitString (2 ^ layer_count)) :
    let share_of_ones : ℝ := (COUNT_ONES bits : ℝ) / 2 ^ layer_count
    let network_output := APPLY_TENT^[layer_count] share_of_ones
    network_output = GET_PARITY bits := by
  unfold_named_pieces
  -- The share is a grid point, and the tents zigzag along the grid.
  exact tent_layers_zigzag_on_the_grid layer_count (COUNT_ONES bits)
    (count_of_ones_is_at_most_bit_count bits)

/-- **A shallow network needs one unit for every two bits.** Take a network
with one hidden layer of ReLU units that reads the count of bits that are
on. If it is closer than one half to the parity for every string of
`bit_count` bits, it has at least `bit_count / 2` units (rounded down). The parity goes
up and down once for every two bits, and each up-and-down needs a unit. -/
theorem shallow_network_needs_one_unit_per_two_bits
    {Index : Type*}
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    (bit_count : ℕ)
    (computes_parity : ∀ bits : BitString bit_count,
      |EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          (COUNT_ONES bits : ℝ)
        - GET_PARITY bits| < 1 / 2) :
    let units_needed := bit_count / 2   -- whole-number division: one unit per two bits
    let unit_count   := units.card
    units_needed ≤ unit_count := by
  unfold_named_pieces
  -- At an even count the parity is 0, so the network is below one half ...
  have low_at_even : ∀ ones_count : ℕ, ones_count ≤ bit_count →
      Even ones_count →
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
        (ones_count : ℝ) < 1 / 2 := by
    intro ones_count count_fits count_is_even
    obtain ⟨bits, bits_have_count⟩ := some_bit_string_has_each_count count_fits
    have closeness := computes_parity bits
    unfold GET_PARITY at closeness
    rw [bits_have_count, ite_eq_left count_is_even, sub_zero] at closeness
    exact (abs_lt.mp closeness).2
  -- ... and at an odd count the parity is 1, so it is above one half.
  have high_at_odd : ∀ ones_count : ℕ, ones_count ≤ bit_count →
      ¬ Even ones_count →
      1 / 2 < EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
        (ones_count : ℝ) := by
    intro ones_count count_fits count_is_odd
    obtain ⟨bits, bits_have_count⟩ := some_bit_string_has_each_count count_fits
    have closeness := computes_parity bits
    unfold GET_PARITY at closeness
    rw [bits_have_count, ite_eq_right count_is_odd] at closeness
    have lower_side := (abs_lt.mp closeness).1
    linarith
  -- Along the counts 0, 1, 2, ... the network goes up and down once per
  -- two bits, and each up-and-down needs a unit.
  refine card_ge_of_zigzag units unit_gain unit_slope unit_bias
    (checkpoints := fun ones_count : ℕ => (ones_count : ℝ))
    Nat.strictMono_cast ?_
  intro turn turn_lt_turn_count
  have low_at_start := low_at_even (2 * turn) (by omega) (even_two_mul turn)
  have high_at_middle := high_at_odd (2 * turn + 1) (by omega)
    (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one turn)
  have low_at_end := low_at_even (2 * turn + 2) (by omega) ⟨turn + 1, by ring⟩
  exact ⟨low_at_start.trans high_at_middle, low_at_end.trans high_at_middle⟩

/-- **The same, asking less of the network.** It is enough that the output
is below one half at every even count and above one half at every odd
count. It need not be near 0 or near 1. The proof above uses only this. -/
theorem shallow_network_on_right_side_of_half_needs_one_unit_per_two_bits
    {Index : Type*}
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    (bit_count : ℕ)
    (is_low_at_even_counts : ∀ ones_count : ℕ, ones_count ≤ bit_count →
      Even ones_count →
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
        (ones_count : ℝ) < 1 / 2)
    (is_high_at_odd_counts : ∀ ones_count : ℕ, ones_count ≤ bit_count →
      ¬ Even ones_count →
      1 / 2 < EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
        (ones_count : ℝ)) :
    let units_needed := bit_count / 2   -- whole-number division: one unit per two bits
    let unit_count   := units.card
    units_needed ≤ unit_count := by
  unfold_named_pieces
  refine card_ge_of_zigzag units unit_gain unit_slope unit_bias
    (checkpoints := fun ones_count : ℕ => (ones_count : ℝ))
    Nat.strictMono_cast ?_
  intro turn turn_lt_turn_count
  have low_at_start :=
    is_low_at_even_counts (2 * turn) (by omega) (even_two_mul turn)
  have high_at_middle := is_high_at_odd_counts (2 * turn + 1) (by omega)
    (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one turn)
  have low_at_end :=
    is_low_at_even_counts (2 * turn + 2) (by omega) ⟨turn + 1, by ring⟩
  exact ⟨low_at_start.trans high_at_middle, low_at_end.trans high_at_middle⟩

/-- **A shallow network needs one unit for every bit, less one.** The same
network, with the same weak hypothesis, has at least `bit_count - 1` units.
This is about twice the bound above, and it cannot be improved: a zigzag
with a kink at each count from 1 to `bit_count - 1` computes the parity.
The proof counts the places where the network crosses one half, one in each
step from a count to the next, and finds a kink between every two crossings
next to each other (`card_ge_of_alternating_sides`). -/
theorem shallow_network_needs_one_unit_per_bit_less_one
    {Index : Type*}
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    (bit_count : ℕ)
    (is_low_at_even_counts : ∀ ones_count : ℕ, ones_count ≤ bit_count →
      Even ones_count →
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
        (ones_count : ℝ) < 1 / 2)
    (is_high_at_odd_counts : ∀ ones_count : ℕ, ones_count ≤ bit_count →
      ¬ Even ones_count →
      1 / 2 < EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
        (ones_count : ℝ)) :
    let units_needed := bit_count - 1   -- one unit for every count strictly between 0 and `bit_count`
    let unit_count   := units.card
    units_needed ≤ unit_count := by
  unfold_named_pieces
  exact card_ge_of_alternating_sides units unit_gain unit_slope unit_bias
    (checkpoints := fun ones_count : ℕ => (ones_count : ℝ))
    Nat.strictMono_cast is_low_at_even_counts is_high_at_odd_counts

/-! ## Being squiggly is common -/

/-- **Exactly half of all functions change at any given flip.** Fix a string
of bits and a position. Among all the functions from strings to a bit, as
many change their value when that bit is flipped as keep it. So a function
drawn at random changes at half of all flips: being squiggly is the usual
case, not a rare one.

The proof pairs the functions up. Change one function's value at the
string, and a function that changed at the flip becomes one that does not,
and the other way round. -/
theorem half_of_all_functions_change_at_any_flip
    {bit_count : ℕ}
    (bits : BitString bit_count)
    (position : Fin bit_count) :
    let flipped_bits := Function.update bits position (!bits position)
    let functions_that_change :=
      (Finset.univ : Finset (BitString bit_count → Bool)).filter
        (fun bit_function => bit_function flipped_bits ≠ bit_function bits)
    let functions_that_stay :=
      (Finset.univ : Finset (BitString bit_count → Bool)).filter
        (fun bit_function => bit_function flipped_bits = bit_function bits)
    functions_that_change.card = functions_that_stay.card := by
  unfold_named_pieces
  -- The flipped string is a different string.
  have flipped_is_different :
      Function.update bits position (!bits position) ≠ bits := by
    intro flipped_eq
    have same_at_position := congrFun flipped_eq position
    simp at same_at_position
  -- The pairing: change the value of the function at `bits`.
  let change_value_at_bits :
      (BitString bit_count → Bool) → (BitString bit_count → Bool) :=
    fun bit_function =>
      Function.update bit_function bits (!bit_function bits)
  have pairing_undoes_itself : ∀ bit_function,
      change_value_at_bits (change_value_at_bits bit_function)
        = bit_function := by
    intro bit_function
    simp [change_value_at_bits]
  have value_at_flipped_is_kept : ∀ bit_function,
      change_value_at_bits bit_function
          (Function.update bits position (!bits position))
        = bit_function (Function.update bits position (!bits position)) :=
    fun bit_function =>
      Function.update_of_ne flipped_is_different _ _
  have value_at_bits_is_changed : ∀ bit_function,
      change_value_at_bits bit_function bits = !bit_function bits :=
    fun bit_function => Function.update_self _ _ _
  refine Finset.card_nbij' change_value_at_bits change_value_at_bits
    ?_ ?_ (fun bit_function _ => pairing_undoes_itself bit_function)
    (fun bit_function _ => pairing_undoes_itself bit_function)
  · -- A function that changed at the flip no longer does.
    intro bit_function function_changes
    simp only [Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at function_changes ⊢
    rw [value_at_flipped_is_kept, value_at_bits_is_changed]
    cases value_at_flipped :
      bit_function (Function.update bits position (!bits position)) <;>
      cases value_at_bits : bit_function bits <;>
      simp_all
  · -- A function that did not change at the flip now does.
    intro bit_function function_stays
    simp only [Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at function_stays ⊢
    rw [value_at_flipped_is_kept, value_at_bits_is_changed, function_stays]
    cases bit_function bits <;> simp

end SquigglyLine
