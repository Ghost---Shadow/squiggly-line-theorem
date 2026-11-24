/-
Depth separation: a shallow network pays one unit per turn.

* `relu_unit_is_straight_away_from_its_kink` : a ReLU unit is a straight line on any stretch that
  does not contain its kink.
* `IS_AFFINE_ON.not_zigzag` : a straight line cannot be lower at both ends of
  a stretch than in the middle.
* `every_up_and_down_holds_a_kink` : so if a one-hidden-layer network goes up and comes
  back down, some unit has its kink in between.
* `one_unit_per_turn` : a zigzag with `turn_count` ups and downs needs
  `turn_count` units.
* `depth_separation` : `layer_count + 1` tent layers (`2 (layer_count + 1)`
  neurons) draw a zigzag that no one-hidden-layer network with fewer than
  `2 ^ layer_count` units can follow, even to within one half at the grid
  points.
* `one_unit_per_crossing_less_one` : a network that is below a level at every
  even checkpoint and above it at every odd one, over `step_count` steps,
  needs `step_count - 1` units. It counts crossings of the level, not tops.
* `depth_separation_one_unit_per_inner_grid_point` : so the shallow network needs
  `2 ^ (layer_count + 1) - 1` units, one for every grid point strictly
  inside. That is about twice `depth_separation`. That this many units are
  also enough is not proved here.

Definitions:

* `IS_AFFINE_ON`               a model is a straight line on a stretch;
* `EVALUATE_SHALLOW_NETWORK`   the value of a one-hidden-layer ReLU network.

Other lemmas: `IS_AFFINE_ON.const_mul`, `sum_of_straight_lines_is_a_straight_line` and
`line_crosses_zero_between_two_signs` are the small steps on the way.
-/
import Mathlib.Tactic.Choose
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import SquigglyLine.Networks.Depth

namespace SquigglyLine

/-! ### Straight lines -/

/-- `model` is a straight line on the set `stretch`.
Python: `all(model(x) == slope * x + intercept for x in stretch)` for some
`slope` and `intercept`. -/
def IS_AFFINE_ON
    (model : RealFunction)
    (stretch : Set ℝ) : Prop :=
  ∃ slope intercept : ℝ,
    ∀ input ∈ stretch, model input = slope * input + intercept

namespace IS_AFFINE_ON

variable {model : RealFunction} {stretch : Set ℝ}

/-- A multiple of a straight line is a straight line. -/
theorem const_mul
    (factor : ℝ)
    (is_line : IS_AFFINE_ON model stretch) :
    let scaled_is_line :=
      IS_AFFINE_ON (fun input => factor * model input) stretch
    scaled_is_line := by
  unfold_named_pieces
  obtain ⟨slope, intercept, line_formula⟩ := is_line
  refine ⟨factor * slope, factor * intercept, fun input input_in_stretch => ?_⟩
  show factor * model input = factor * slope * input + factor * intercept
  rw [line_formula input input_in_stretch]
  ring

/-- **A straight line cannot go up and come back down.** -/
theorem not_zigzag
    {left middle right : ℝ}
    (is_line : IS_AFFINE_ON model (Set.Icc left right))
    (left_lt_middle : left < middle)
    (middle_lt_right : middle < right)
    (left_below_middle : model left < model middle)
    (right_below_middle : model right < model middle) :
    False := by
  obtain ⟨slope, intercept, line_formula⟩ := is_line
  rw [line_formula left ⟨le_rfl, by linarith⟩,
    line_formula middle ⟨left_lt_middle.le, middle_lt_right.le⟩]
    at left_below_middle
  rw [line_formula right ⟨by linarith, le_rfl⟩,
    line_formula middle ⟨left_lt_middle.le, middle_lt_right.le⟩]
    at right_below_middle
  -- Lower on the left means the slope is positive ...
  have slope_pos : 0 < slope := by
    by_contra slope_nonpos
    push Not at slope_nonpos
    have drop_is_nonneg :=
      mul_nonneg (neg_nonneg.mpr slope_nonpos) (sub_pos.mpr left_lt_middle).le
    linarith
  -- ... which makes the right end higher than the middle.
  have rise_is_pos := mul_pos slope_pos (sub_pos.mpr middle_lt_right)
  linarith

end IS_AFFINE_ON

/-- A sum of straight lines is a straight line. -/
theorem sum_of_straight_lines_is_a_straight_line
    {Index : Type*}
    (indices : Finset Index)
    (summand : Index → RealFunction)
    {stretch : Set ℝ}
    (every_summand_is_line :
      ∀ j ∈ indices, IS_AFFINE_ON (summand j) stretch) :
    let sum_is_line :=
      IS_AFFINE_ON (fun input => ∑ j ∈ indices, summand j input) stretch
    sum_is_line := by
  unfold_named_pieces
  classical
  induction indices using Finset.induction_on with
  | empty => exact ⟨0, 0, fun input _ => by simp⟩
  | insert new_index rest new_index_not_in_rest rest_is_line =>
    obtain ⟨head_slope, head_intercept, head_formula⟩ :=
      every_summand_is_line new_index (Finset.mem_insert_self new_index rest)
    obtain ⟨rest_slope, rest_intercept, rest_formula⟩ :=
      rest_is_line (fun j j_in_rest =>
        every_summand_is_line j (Finset.mem_insert_of_mem j_in_rest))
    refine ⟨head_slope + rest_slope, head_intercept + rest_intercept,
      fun input input_in_stretch => ?_⟩
    have rest_sum_formula :
        ∑ j ∈ rest, summand j input = rest_slope * input + rest_intercept :=
      rest_formula input input_in_stretch
    show ∑ j ∈ insert new_index rest, summand j input
      = (head_slope + rest_slope) * input + (head_intercept + rest_intercept)
    rw [Finset.sum_insert new_index_not_in_rest,
      head_formula input input_in_stretch, rest_sum_formula]
    ring

/-! ### One ReLU unit bends once -/

/-- A line that is below zero at `input` and above zero at `middle` is zero
somewhere strictly inside any stretch that holds `input` and has `middle` in
its interior. -/
theorem line_crosses_zero_between_two_signs
    {weight bias left right input middle : ℝ}
    (left_le_input : left ≤ input)
    (input_le_right : input ≤ right)
    (left_lt_middle : left < middle)
    (middle_lt_right : middle < right)
    (line_negative_at_input : weight * input + bias < 0)
    (line_positive_at_middle : 0 < weight * middle + bias) :
    let is_after_left   := fun (crossing : ℝ) => left < crossing
    let is_before_right := fun (crossing : ℝ) => crossing < right
    let is_zero_of_line := fun (crossing : ℝ) => weight * crossing + bias = 0
    ∃ crossing, is_after_left crossing ∧ is_before_right crossing
      ∧ is_zero_of_line crossing := by
  unfold_named_pieces
  beta_reduce
  have gap_positive :
      0 < (weight * middle + bias) - (weight * input + bias) := by
    linarith
  -- How far along from `input` to `middle` the line reaches zero.
  obtain ⟨fraction, fraction_def⟩ :
      ∃ fraction, fraction = -(weight * input + bias)
        / ((weight * middle + bias) - (weight * input + bias)) :=
    ⟨_, rfl⟩
  have fraction_pos : 0 < fraction := by
    rw [fraction_def]
    exact div_pos (by linarith) gap_positive
  have fraction_lt_one : fraction < 1 := by
    rw [fraction_def, div_lt_one gap_positive]
    linarith
  have fraction_times_gap :
      fraction * ((weight * middle + bias) - (weight * input + bias))
        = -(weight * input + bias) := by
    rw [fraction_def, div_mul_cancel₀ _ gap_positive.ne']
  refine ⟨(1 - fraction) * input + fraction * middle, ?_, ?_, ?_⟩
  · have from_left :=
      mul_nonneg (sub_nonneg.mpr fraction_lt_one.le)
        (sub_nonneg.mpr left_le_input)
    have toward_middle := mul_pos fraction_pos (sub_pos.mpr left_lt_middle)
    nlinarith
  · have from_right :=
      mul_nonneg (sub_nonneg.mpr fraction_lt_one.le)
        (sub_nonneg.mpr input_le_right)
    have toward_middle := mul_pos fraction_pos (sub_pos.mpr middle_lt_right)
    nlinarith
  · linear_combination fraction_times_gap

/-- **A ReLU unit is straight away from its kink.** If `weight * point + bias`
is never zero strictly inside a stretch, the unit
`max (weight * input + bias) 0` is a straight line on the whole stretch. -/
theorem relu_unit_is_straight_away_from_its_kink
    {weight bias left right : ℝ}
    (left_lt_right : left < right)
    (no_zero_inside :
      ∀ point, left < point → point < right → weight * point + bias ≠ 0) :
    let unit_is_line :=
      IS_AFFINE_ON (fun input => max (weight * input + bias) 0)
        (Set.Icc left right)
    unit_is_line := by
  unfold_named_pieces
  have left_lt_midpoint : left < (left + right) / 2 := by linarith
  have midpoint_lt_right : (left + right) / 2 < right := by linarith
  rcases lt_or_gt_of_ne
      (no_zero_inside _ left_lt_midpoint midpoint_lt_right) with
    line_negative_inside | line_positive_inside
  · -- The line is below zero inside, so the unit is off: the zero line.
    refine ⟨0, 0, fun input input_in_stretch => ?_⟩
    have line_nonpos : weight * input + bias ≤ 0 := by
      by_contra line_positive
      push Not at line_positive
      obtain ⟨crossing, after_left, before_right, crossing_is_zero⟩ :=
        line_crosses_zero_between_two_signs (weight := -weight) (bias := -bias)
          input_in_stretch.1 input_in_stretch.2 left_lt_midpoint
          midpoint_lt_right (by linarith) (by linarith)
      exact no_zero_inside crossing after_left before_right
        (by linarith)
    show max (weight * input + bias) 0 = 0 * input + 0
    rw [max_eq_right line_nonpos]
    ring
  · -- The line is above zero inside, so the unit is on: the line itself.
    refine ⟨weight, bias, fun input input_in_stretch => ?_⟩
    have line_nonneg : 0 ≤ weight * input + bias := by
      by_contra line_negative
      push Not at line_negative
      obtain ⟨crossing, after_left, before_right, crossing_is_zero⟩ :=
        line_crosses_zero_between_two_signs input_in_stretch.1 input_in_stretch.2
          left_lt_midpoint midpoint_lt_right line_negative line_positive_inside
      exact no_zero_inside crossing after_left before_right crossing_is_zero
    exact max_eq_left line_nonneg

/-! ### A network with one hidden layer -/

section Shallow

variable {Index : Type*}

/-- A network with one hidden layer of ReLU units, indexed by `units`: unit `j`
has input weight `unit_slope j`, bias `unit_bias j` and output weight
`unit_gain j`.
Python: `sum(gain[j] * max(slope[j] * input + bias[j], 0) for j in units)`. -/
noncomputable def EVALUATE_SHALLOW_NETWORK
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    (input : ℝ) : ℝ :=
  ∑ j ∈ units, unit_gain j * max (unit_slope j * input + unit_bias j) 0

/-- **Every up-and-down holds a kink.** If the network is lower at both ends of
a stretch than at a point inside it, some unit has its kink strictly inside the
stretch. -/
theorem every_up_and_down_holds_a_kink
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    {left middle right : ℝ}
    (left_lt_middle : left < middle)
    (middle_lt_right : middle < right)
    (left_below_middle :
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias left
        < EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias middle)
    (right_below_middle :
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias right
        < EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          middle) :
    let is_after_left   := fun (crossing : ℝ) => left < crossing
    let is_before_right := fun (crossing : ℝ) => crossing < right
    let is_kink_of      := fun (unit : Index) (crossing : ℝ) =>
      unit_slope unit * crossing + unit_bias unit = 0  -- the unit switches on or off here
    let has_slope       := fun (unit : Index) => unit_slope unit ≠ 0
    let has_kink_inside := fun (unit : Index) =>
      ∃ crossing, is_after_left crossing ∧ is_before_right crossing
        ∧ is_kink_of unit crossing
    ∃ unit ∈ units, has_slope unit ∧ has_kink_inside unit := by
  unfold_named_pieces
  beta_reduce
  by_contra no_kink_inside
  push Not at no_kink_inside
  -- With no kink inside, every unit is straight on the stretch, and so is
  -- their sum. A straight line cannot zigzag.
  have network_is_line :
      IS_AFFINE_ON (EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope
        unit_bias) (Set.Icc left right) := by
    show IS_AFFINE_ON
      (fun input => ∑ j ∈ units,
        unit_gain j * max (unit_slope j * input + unit_bias j) 0)
      (Set.Icc left right)
    refine sum_of_straight_lines_is_a_straight_line units
      (fun j input => unit_gain j * max (unit_slope j * input + unit_bias j) 0)
      (fun j j_in_units => ?_)
    refine IS_AFFINE_ON.const_mul
      (model := fun input => max (unit_slope j * input + unit_bias j) 0)
      (unit_gain j) ?_
    by_cases slope_is_zero : unit_slope j = 0
    · exact ⟨0, max (unit_bias j) 0, fun input _ => by simp [slope_is_zero]⟩
    · exact relu_unit_is_straight_away_from_its_kink (left_lt_middle.trans middle_lt_right)
        (no_kink_inside j j_in_units slope_is_zero)
  exact network_is_line.not_zigzag left_lt_middle middle_lt_right
    left_below_middle right_below_middle

/-- **One unit per turn.** If the network goes up and comes back down
`turn_count` times along an increasing run of inputs, it has at least
`turn_count` units. -/
theorem one_unit_per_turn
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    {checkpoints : ℕ → ℝ}
    (checkpoints_increase : StrictMono checkpoints)
    {turn_count : ℕ}
    (zigzags_at_checkpoints : ∀ i < turn_count,
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          (checkpoints (2 * i))
        < EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          (checkpoints (2 * i + 1))
      ∧ EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          (checkpoints (2 * i + 2))
        < EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          (checkpoints (2 * i + 1))) :
    let unit_count := units.card
    turn_count ≤ unit_count := by
  unfold_named_pieces
  -- Each turn holds a kink, so there is a unit for it.
  have every_turn_has_kink : ∀ i ∈ Finset.range turn_count,
      ∃ j ∈ units, unit_slope j ≠ 0 ∧
        ∃ crossing, checkpoints (2 * i) < crossing
          ∧ crossing < checkpoints (2 * i + 2)
          ∧ unit_slope j * crossing + unit_bias j = 0 := by
    intro i i_in_range
    obtain ⟨goes_up, comes_down⟩ :=
      zigzags_at_checkpoints i (Finset.mem_range.mp i_in_range)
    exact every_up_and_down_holds_a_kink units unit_gain unit_slope unit_bias
      (checkpoints_increase (by omega)) (checkpoints_increase (by omega))
      goes_up comes_down
  rcases Nat.eq_zero_or_pos turn_count with rfl | turn_count_pos
  · exact Nat.zero_le _
  obtain ⟨first_unit, -⟩ :=
    every_turn_has_kink 0 (Finset.mem_range.mpr turn_count_pos)
  have : Nonempty Index := ⟨first_unit⟩
  choose! kink_unit kink_unit_spec using every_turn_has_kink
  -- Two different turns cannot share a unit: the stretches do not overlap and
  -- a unit has only one kink.
  have kink_unit_injective :
      Set.InjOn kink_unit (Finset.range turn_count : Set ℕ) := by
    intro turn turn_in_range other_turn other_turn_in_range same_unit
    obtain ⟨-, unit_slope_ne_zero, crossing, after_left, before_right,
        crossing_is_kink⟩ :=
      kink_unit_spec turn (Finset.mem_coe.mp turn_in_range)
    obtain ⟨-, -, other_crossing, other_after_left, other_before_right,
        other_crossing_is_kink⟩ :=
      kink_unit_spec other_turn (Finset.mem_coe.mp other_turn_in_range)
    rw [← same_unit] at other_crossing_is_kink
    have same_crossing : crossing = other_crossing :=
      mul_left_cancel₀ unit_slope_ne_zero (by linarith)
    by_contra turns_differ
    rcases Nat.lt_or_gt_of_ne turns_differ with turn_first | other_turn_first
    · have stretches_ordered :=
        checkpoints_increase.monotone
          (show 2 * turn + 2 ≤ 2 * other_turn by omega)
      linarith
    · have stretches_ordered :=
        checkpoints_increase.monotone
          (show 2 * other_turn + 2 ≤ 2 * turn by omega)
      linarith
  calc turn_count = (Finset.range turn_count).card :=
        (Finset.card_range turn_count).symm
    _ ≤ units.card :=
        Finset.card_le_card_of_injOn kink_unit
          (fun turn turn_in_range => (kink_unit_spec turn turn_in_range).1)
          kink_unit_injective

/-- **Depth separation.** `layer_count + 1` tent layers use
`2 (layer_count + 1)` neurons. A network with one hidden layer that stays
within one half of them at the `2 ^ (layer_count + 1) + 1` grid points has at
least `2 ^ layer_count` units. -/
theorem depth_separation
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    (layer_count : ℕ)
    (follows_zigzag : ∀ grid_index : ℕ, grid_index ≤ 2 ^ (layer_count + 1) →
      |EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          ((grid_index : ℝ) / 2 ^ (layer_count + 1))
        - APPLY_TENT^[layer_count + 1]
          ((grid_index : ℝ) / 2 ^ (layer_count + 1))|
        < 1 / 2) :
    let units_needed := 2 ^ layer_count  -- one unit per turn; the zigzag has 2 ^ layer_count turns
    let unit_count := units.card
    units_needed ≤ unit_count := by
  unfold_named_pieces
  -- At even grid points the tent is 0, so the network is below one half ...
  have low_at_even : ∀ grid_index : ℕ, grid_index ≤ 2 ^ (layer_count + 1) →
      Even grid_index →
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
        ((grid_index : ℝ) / 2 ^ (layer_count + 1)) < 1 / 2 := by
    intro grid_index index_on_grid index_even
    have closeness := follows_zigzag grid_index index_on_grid
    rw [tent_layers_zigzag_on_the_grid (layer_count + 1) grid_index index_on_grid,
      ite_eq_left index_even, sub_zero] at closeness
    exact (abs_lt.mp closeness).2
  -- ... and at odd grid points the tent is 1, so it is above one half.
  have high_at_odd : ∀ grid_index : ℕ, grid_index ≤ 2 ^ (layer_count + 1) →
      ¬ Even grid_index →
      1 / 2 < EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
        ((grid_index : ℝ) / 2 ^ (layer_count + 1)) := by
    intro grid_index index_on_grid index_odd
    have closeness := follows_zigzag grid_index index_on_grid
    rw [tent_layers_zigzag_on_the_grid (layer_count + 1) grid_index index_on_grid,
      ite_eq_right index_odd] at closeness
    have lower_side := (abs_lt.mp closeness).1
    linarith
  have two_pow_succ : 2 ^ (layer_count + 1) = 2 * 2 ^ layer_count := by
    rw [pow_succ, mul_comm]
  -- The grid points zigzag, so the network goes up and down once per pair.
  refine one_unit_per_turn units unit_gain unit_slope unit_bias
    (checkpoints := fun step : ℕ => (step : ℝ) / 2 ^ (layer_count + 1)) ?_ ?_
  · intro step other_step step_lt_other_step
    show (step : ℝ) / 2 ^ (layer_count + 1)
      < (other_step : ℝ) / 2 ^ (layer_count + 1)
    gcongr
  · intro i i_lt_turn_count
    have low_at_start := low_at_even (2 * i) (by omega) (even_two_mul i)
    have high_at_middle := high_at_odd (2 * i + 1) (by omega)
      (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one i)
    have low_at_end := low_at_even (2 * i + 2) (by omega) ⟨i + 1, by ring⟩
    exact ⟨low_at_start.trans high_at_middle, low_at_end.trans high_at_middle⟩

/-! ### One unit per crossing: a bound about twice as large

`one_unit_per_turn` counts the tops of a zigzag and finds one unit for each.
A zigzag that goes up and down `turn_count` times has about twice as many
bends as tops, so that bound is about half of what is needed. This section
counts the places where the network crosses a level instead. Between two
crossings next to each other the network leaves the level and comes back,
so it bends there, and these stretches do not overlap. -/

/-- Changing the sign of every output weight changes the sign of the
output. -/
theorem evaluate_shallow_network_with_negated_gains
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    (input : ℝ) :
    let negated_gain := fun unit => -unit_gain unit
    EVALUATE_SHALLOW_NETWORK units negated_gain unit_slope unit_bias input
      = -EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          input := by
  unfold_named_pieces
  simp [EVALUATE_SHALLOW_NETWORK, Finset.sum_neg_distrib]

/-- A network with one hidden layer is continuous: a small change of the
input makes a small change of the output. -/
theorem shallow_network_is_continuous
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ) :
    Continuous
      (EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias) := by
  unfold EVALUATE_SHALLOW_NETWORK
  refine continuous_finsetSum units fun unit _ => ?_
  exact continuous_const.mul
    (((continuous_const.mul continuous_id).add continuous_const).max
      continuous_const)

/-- **Between two crossings of a level there is a kink.** If the network is
at `level` at both ends of a stretch and off it at a point between, some
unit has its kink strictly inside the stretch. -/
theorem two_crossings_hold_a_kink_between_them
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    {left middle right level : ℝ}
    (left_lt_middle : left < middle)
    (middle_lt_right : middle < right)
    (left_is_at_level :
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias left
        = level)
    (right_is_at_level :
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias right
        = level)
    (middle_is_off_level :
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias middle
        ≠ level) :
    ∃ unit ∈ units, unit_slope unit ≠ 0 ∧
      ∃ crossing, left < crossing ∧ crossing < right
        ∧ unit_slope unit * crossing + unit_bias unit = 0 := by
  rcases lt_or_gt_of_ne middle_is_off_level with
    middle_is_below | middle_is_above
  · -- The network dips below the level. Turn it upside down: the same units,
    -- with the same kinks, now go up and come back down.
    have negated :=
      evaluate_shallow_network_with_negated_gains units unit_gain unit_slope
        unit_bias
    exact every_up_and_down_holds_a_kink units (fun unit => -unit_gain unit)
      unit_slope unit_bias left_lt_middle middle_lt_right
      (by rw [negated left, negated middle]; linarith)
      (by rw [negated right, negated middle]; linarith)
  · -- The network rises above the level and comes back down.
    exact every_up_and_down_holds_a_kink units unit_gain unit_slope unit_bias
      left_lt_middle middle_lt_right (by linarith) (by linarith)

/-- **One unit per crossing, less one.** Take an increasing run of inputs,
numbered from 0 to `step_count`. If the network is below `level` at every
even one and above it at every odd one, it has at least `step_count - 1`
units. The network crosses the level once in each of the `step_count`
steps, and between two crossings next to each other it has to bend. -/
theorem one_unit_per_crossing_less_one
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    {checkpoints : ℕ → ℝ}
    (checkpoints_increase : StrictMono checkpoints)
    {level : ℝ}
    {step_count : ℕ}
    (is_low_at_even : ∀ i ≤ step_count, Even i →
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
        (checkpoints i) < level)
    (is_high_at_odd : ∀ i ≤ step_count, ¬ Even i →
      level < EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
        (checkpoints i)) :
    let units_needed := step_count - 1
    let unit_count   := units.card
    units_needed ≤ unit_count := by
  unfold_named_pieces
  have network_is_continuous :=
    shallow_network_is_continuous units unit_gain unit_slope unit_bias
  -- The network is never exactly at the level at a checkpoint.
  have checkpoint_is_off_level : ∀ i ≤ step_count,
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
        (checkpoints i) ≠ level := by
    intro i i_le
    by_cases i_is_even : Even i
    · exact (is_low_at_even i i_le i_is_even).ne
    · exact (is_high_at_odd i i_le i_is_even).ne'
  -- In every step the network crosses the level, strictly inside the step.
  have every_step_has_crossing : ∀ i, i < step_count →
      ∃ crossing, checkpoints i < crossing ∧ crossing < checkpoints (i + 1)
        ∧ EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
            crossing = level := by
    intro i i_lt
    have step_is_ordered : checkpoints i ≤ checkpoints (i + 1) :=
      (checkpoints_increase (Nat.lt_succ_self i)).le
    -- A continuous function takes every value between two of its values.
    have level_is_taken :
        ∃ crossing ∈ Set.Icc (checkpoints i) (checkpoints (i + 1)),
          EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
            crossing = level := by
      by_cases i_is_even : Even i
      · have low_at_start := is_low_at_even i i_lt.le i_is_even
        have high_at_end := is_high_at_odd (i + 1) i_lt
          (by rw [Nat.even_add_one]; exact not_not.mpr i_is_even)
        exact intermediate_value_Icc step_is_ordered
          network_is_continuous.continuousOn
          ⟨low_at_start.le, high_at_end.le⟩
      · have high_at_start := is_high_at_odd i i_lt.le i_is_even
        have low_at_end := is_low_at_even (i + 1) i_lt
          (by rw [Nat.even_add_one]; exact i_is_even)
        exact intermediate_value_Icc' step_is_ordered
          network_is_continuous.continuousOn
          ⟨low_at_end.le, high_at_start.le⟩
    obtain ⟨crossing, ⟨after_start, before_end⟩, crossing_is_at_level⟩ :=
      level_is_taken
    -- The crossing is not at either end, where the network is off the level.
    have crossing_ne_start : crossing ≠ checkpoints i := by
      intro crossing_is_start
      rw [crossing_is_start] at crossing_is_at_level
      exact checkpoint_is_off_level i i_lt.le crossing_is_at_level
    have crossing_ne_end : crossing ≠ checkpoints (i + 1) := by
      intro crossing_is_end
      rw [crossing_is_end] at crossing_is_at_level
      exact checkpoint_is_off_level (i + 1) i_lt crossing_is_at_level
    exact ⟨crossing, lt_of_le_of_ne after_start (Ne.symm crossing_ne_start),
      lt_of_le_of_ne before_end crossing_ne_end, crossing_is_at_level⟩
  choose! crossing_of_step crossing_of_step_spec using every_step_has_crossing
  -- Between the crossings of two steps next to each other lies a
  -- checkpoint, where the network is off the level. So there is a kink
  -- between them.
  have every_gap_has_kink : ∀ i ∈ Finset.range (step_count - 1),
      ∃ unit ∈ units, unit_slope unit ≠ 0 ∧
        ∃ kink, crossing_of_step i < kink ∧ kink < crossing_of_step (i + 1)
          ∧ unit_slope unit * kink + unit_bias unit = 0 := by
    intro i i_in_range
    have i_lt : i + 1 < step_count := by
      have := Finset.mem_range.mp i_in_range
      omega
    obtain ⟨-, first_before_checkpoint, first_at_level⟩ :=
      crossing_of_step_spec i (by omega)
    obtain ⟨second_after_checkpoint, -, second_at_level⟩ :=
      crossing_of_step_spec (i + 1) i_lt
    exact two_crossings_hold_a_kink_between_them units unit_gain unit_slope
      unit_bias first_before_checkpoint second_after_checkpoint
      first_at_level second_at_level
      (checkpoint_is_off_level (i + 1) i_lt.le)
  rcases Nat.eq_zero_or_pos (step_count - 1) with no_gaps | some_gaps
  · rw [no_gaps]
    exact Nat.zero_le _
  obtain ⟨first_unit, -⟩ :=
    every_gap_has_kink 0 (Finset.mem_range.mpr some_gaps)
  have : Nonempty Index := ⟨first_unit⟩
  choose! kink_unit kink_unit_spec using every_gap_has_kink
  -- The crossings come in order, so the gaps between them do not overlap.
  have later_crossing_is_not_earlier : ∀ i k, i + 1 ≤ k → k < step_count →
      crossing_of_step (i + 1) ≤ crossing_of_step k := by
    intro i k i_succ_le_k k_lt
    rcases Nat.eq_or_lt_of_le i_succ_le_k with same_step | earlier_step
    · rw [same_step]
    · obtain ⟨-, before_next_checkpoint, -⟩ :=
        crossing_of_step_spec (i + 1) (by omega)
      obtain ⟨after_own_checkpoint, -, -⟩ := crossing_of_step_spec k k_lt
      have checkpoints_ordered :=
        checkpoints_increase.monotone (show i + 1 + 1 ≤ k by omega)
      linarith
  -- Two different gaps cannot share a unit: a unit has only one kink.
  have kink_unit_injective :
      Set.InjOn kink_unit (Finset.range (step_count - 1) : Set ℕ) := by
    intro gap gap_in_range other_gap other_gap_in_range same_unit
    have gap_lt := Finset.mem_range.mp (Finset.mem_coe.mp gap_in_range)
    have other_gap_lt :=
      Finset.mem_range.mp (Finset.mem_coe.mp other_gap_in_range)
    obtain ⟨-, unit_slope_ne_zero, kink, after_left, before_right,
        kink_is_zero⟩ :=
      kink_unit_spec gap (Finset.mem_coe.mp gap_in_range)
    obtain ⟨-, -, other_kink, other_after_left, other_before_right,
        other_kink_is_zero⟩ :=
      kink_unit_spec other_gap (Finset.mem_coe.mp other_gap_in_range)
    rw [← same_unit] at other_kink_is_zero
    have same_kink : kink = other_kink :=
      mul_left_cancel₀ unit_slope_ne_zero (by linarith)
    by_contra gaps_differ
    rcases Nat.lt_or_gt_of_ne gaps_differ with gap_first | other_gap_first
    · have gaps_ordered :=
        later_crossing_is_not_earlier gap other_gap (by omega) (by omega)
      linarith
    · have gaps_ordered :=
        later_crossing_is_not_earlier other_gap gap (by omega) (by omega)
      linarith
  calc step_count - 1 = (Finset.range (step_count - 1)).card :=
        (Finset.card_range (step_count - 1)).symm
    _ ≤ units.card :=
        Finset.card_le_card_of_injOn kink_unit
          (fun gap gap_in_range => (kink_unit_spec gap gap_in_range).1)
          kink_unit_injective

/-- **Depth separation, counted by crossings.** A network with one hidden
layer that stays within one half of `layer_count + 1` tent layers at the
grid points has at least `2 ^ (layer_count + 1) - 1` units. That is one for
every grid point strictly inside, twice the bound of `depth_separation` less
one. Whether this many units are also enough is not proved here: the network
has no constant added at its output, and that matters for small grids. -/
theorem depth_separation_one_unit_per_inner_grid_point
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    (layer_count : ℕ)
    (follows_zigzag : ∀ grid_index : ℕ, grid_index ≤ 2 ^ (layer_count + 1) →
      |EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          ((grid_index : ℝ) / 2 ^ (layer_count + 1))
        - APPLY_TENT^[layer_count + 1]
          ((grid_index : ℝ) / 2 ^ (layer_count + 1))|
        < 1 / 2) :
    let units_needed := 2 ^ (layer_count + 1) - 1   -- one unit for every grid point strictly inside
    let unit_count := units.card
    units_needed ≤ unit_count := by
  unfold_named_pieces
  refine one_unit_per_crossing_less_one units unit_gain unit_slope unit_bias
    (checkpoints := fun step : ℕ => (step : ℝ) / 2 ^ (layer_count + 1))
    (level := 1 / 2) ?_ ?_ ?_
  · intro step other_step step_lt_other_step
    show (step : ℝ) / 2 ^ (layer_count + 1)
      < (other_step : ℝ) / 2 ^ (layer_count + 1)
    gcongr
  · -- At even grid points the tent is 0, so the network is below one half.
    intro grid_index index_on_grid index_even
    have closeness := follows_zigzag grid_index index_on_grid
    rw [tent_layers_zigzag_on_the_grid (layer_count + 1) grid_index index_on_grid,
      ite_eq_left index_even, sub_zero] at closeness
    exact (abs_lt.mp closeness).2
  · -- At odd grid points the tent is 1, so it is above one half.
    intro grid_index index_on_grid index_odd
    have closeness := follows_zigzag grid_index index_on_grid
    rw [tent_layers_zigzag_on_the_grid (layer_count + 1) grid_index index_on_grid,
      ite_eq_right index_odd] at closeness
    have lower_side := (abs_lt.mp closeness).1
    linarith

end Shallow

end SquigglyLine
