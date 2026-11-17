/-
The trained path as a path of least action.

Through training (a model linear in its weights):
* `exists_iterate_gradientStep` : gradient descent moves only along the
  features. It never spends movement on a direction that leaves the outputs
  unchanged.
* `gradientDescent_fit_is_nearest` : so whenever it arrives at a fit, that fit
  is the nearest one to the start. Training takes the least travel.

Through the layers (the polarizer chain):
* `cos_mul_cos_le_cos_half_sq` : two turns `first_turn`, `second_turn` never
  keep more than two turns of their average. Evening out a pair of steps never
  loses.

Also here: `norm_sub_le_of_fit_along_features` (a fit reached along the
features is the nearest) and `even_turns_keep_more` (the same, with a length in
front).

* `prod_cos_le_cos_average_pow` : the same for any number of plates, each
  turning by at most a quarter turn either way. Together they never keep more
  than the same number of plates each turning by the average turn.
-/
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import SquigglyLine.Networks.Kernel

namespace SquigglyLine

/-! ### Through training: the nearest fit -/

section Training

open ContinuousLinearMap

variable {Weights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]

/-- **Moving only along the features is moving least.** A fit reached from
`start_weights` by a move of the form `A† vector` is at least as near to
`start_weights` as any other fit. -/
theorem norm_sub_le_of_fit_along_features
    (predict : Weights →L[ℝ] Outputs)
    {labels : Outputs}
    {start_weights : Weights}
    {weights : Weights}
    {other_weights : Weights}
    {vector : Outputs}
    (weights_move_along_features :
      weights = start_weights + adjoint predict vector)
    (weights_fit : predict weights = labels)
    (other_weights_fit : predict other_weights = labels) :
    let distance       := ‖weights - start_weights‖
    let other_distance := ‖other_weights - start_weights‖
    distance ≤ other_distance := by
  unfold_named_pieces
  have move_is_pullback : weights - start_weights = adjoint predict vector := by
    rw [weights_move_along_features, add_sub_cancel_left]
  have same_outputs :
      predict (weights - start_weights)
        = predict (other_weights - start_weights) := by
    rw [map_sub, map_sub, weights_fit, other_weights_fit]
  -- The move is a pullback, so it pairs with any other move through the
  -- outputs, which agree.
  have squared_eq : ‖weights - start_weights‖ ^ 2
      = inner ℝ (weights - start_weights) (other_weights - start_weights) := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 1 [move_is_pullback]
    rw [adjoint_inner_left, same_outputs, ← adjoint_inner_left,
      ← move_is_pullback]
  have product_le : ‖weights - start_weights‖ * ‖weights - start_weights‖
      ≤ ‖weights - start_weights‖ * ‖other_weights - start_weights‖ := by
    rw [← sq, squared_eq]
    exact real_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg (weights - start_weights))
    with zero | positive
  · rw [← zero]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left product_le positive

/-- **Gradient descent never wastes movement.** After any number of steps the
parameters differ from the start by a move along the features. -/
theorem exists_iterate_gradientStep
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (start_weights : Weights)
    (step_count : ℕ) :
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights
    ∃ vector : Outputs,
      let moved_weights := start_weights + adjoint predict vector
      trained_weights = moved_weights := by
  unfold_named_pieces
  induction step_count with
  | zero => exact ⟨0, by simp⟩
  | succ previous_count earlier_case =>
    obtain ⟨vector, vector_gives_weights⟩ := earlier_case
    -- One more step adds `learning_rate` times a residual, itself pulled back.
    refine ⟨vector + learning_rate • GET_RESIDUAL
      (predict : Weights →ₗ[ℝ] Outputs) labels
      ((TAKE_GRADIENT_STEP predict labels learning_rate)^[previous_count]
        start_weights), ?_⟩
    rw [Function.iterate_succ_apply', TAKE_GRADIENT_STEP, map_add, map_smul,
      ← add_assoc, ← vector_gives_weights]

/-- **Training takes the least travel.** If gradient descent arrives at a fit,
no other fit is nearer to the start. -/
theorem gradientDescent_fit_is_nearest
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (start_weights : Weights)
    (step_count : ℕ)
    (trained_weights_fit :
      predict ((TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights) = labels)
    {other_weights : Weights}
    (other_weights_fit : predict other_weights = labels) :
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights
    let trained_distance := ‖trained_weights - start_weights‖
    let other_distance   := ‖other_weights - start_weights‖
    trained_distance ≤ other_distance := by
  unfold_named_pieces
  obtain ⟨vector, vector_gives_weights⟩ :=
    exists_iterate_gradientStep predict labels learning_rate start_weights
      step_count
  exact norm_sub_le_of_fit_along_features predict vector_gives_weights
    trained_weights_fit other_weights_fit

end Training

/-! ### Through the layers: the evenest path -/

section Layers

open Real

/-- **Even steps lose least.** Two turns of `first_turn` and `second_turn`
never keep more than two turns of their average. -/
theorem cos_mul_cos_le_cos_half_sq
    (first_turn : ℝ)
    (second_turn : ℝ) :
    let kept_by_two_turns := cos first_turn * cos second_turn
    let average_turn      := (first_turn + second_turn) / 2
    let kept_by_average   := cos average_turn ^ 2
    kept_by_two_turns ≤ kept_by_average := by
  unfold_named_pieces
  have product_to_sum : cos first_turn * cos second_turn
      = (cos (first_turn - second_turn) + cos (first_turn + second_turn))
        / 2 := by
    rw [cos_sub, cos_add]
    ring
  have half_angle : cos ((first_turn + second_turn) / 2) ^ 2
      = 1 / 2 + cos (first_turn + second_turn) / 2 := by  -- cos² x = (1 + cos 2x) / 2
    rw [cos_sq, show 2 * ((first_turn + second_turn) / 2)
      = first_turn + second_turn by ring]
  rw [product_to_sum, half_angle]
  linarith [cos_le_one (first_turn - second_turn)]

/-- Evening out two neighbouring plates never loses length. -/
theorem even_turns_keep_more
    {length : ℝ}
    (length_nonneg : 0 ≤ length)
    (first_turn : ℝ)
    (second_turn : ℝ) :
    let kept_by_two_turns := length * (cos first_turn * cos second_turn)
    let average_turn      := (first_turn + second_turn) / 2
    let kept_by_average   := length * cos average_turn ^ 2
    kept_by_two_turns ≤ kept_by_average := by
  unfold_named_pieces
  have turns_le_average : cos first_turn * cos second_turn
      ≤ cos ((first_turn + second_turn) / 2) ^ 2 :=
    cos_mul_cos_le_cos_half_sq first_turn second_turn
  exact mul_le_mul_of_nonneg_left turns_le_average length_nonneg

open Finset in
/-- **Equal turns keep the most, for any number of plates.** Each plate turns
by at most a quarter turn either way. Together the plates never keep more
than the same number of plates keep when each turns by the average turn. -/
theorem prod_cos_le_cos_average_pow
    {Plates : Type*}
    (plates : Finset Plates)
    (plates_nonempty : plates.Nonempty)
    (turn : Plates → ℝ)
    (turns_within_quarter :
      ∀ plate ∈ plates, turn plate ∈ Set.Icc (-(PI / 2)) (PI / 2)) :
    let plate_count     := plates.card
    let kept_by_turns   := ∏ plate ∈ plates, cos (turn plate)
    let average_turn    := (∑ plate ∈ plates, turn plate) / plate_count
    let kept_by_average := cos average_turn ^ plate_count
    kept_by_turns ≤ kept_by_average := by
  unfold_named_pieces
  have count_pos : (0 : ℝ) < plates.card := by
    exact_mod_cast card_pos.mpr plates_nonempty
  have cos_nonneg : ∀ plate ∈ plates, 0 ≤ cos (turn plate) :=
    fun plate plate_in => cos_nonneg_of_mem_Icc
      (turns_within_quarter plate plate_in)
  have shares_sum_to_one : ∑ _plate ∈ plates, (plates.card : ℝ)⁻¹ = 1 := by
    rw [sum_const, nsmul_eq_mul, mul_inv_cancel₀ count_pos.ne']
  -- The geometric mean of the cosines is at most their arithmetic mean.
  have geometric_le_arithmetic := geom_mean_le_arith_mean plates
    (fun _ => (1 : ℝ)) (fun plate => cos (turn plate))
    (fun _ _ => zero_le_one) (by simpa using count_pos) cos_nonneg
  simp only [rpow_one, one_mul, sum_const, nsmul_eq_mul, mul_one]
    at geometric_le_arithmetic
  -- The cosine is concave on a half turn, so the mean of the cosines is at
  -- most the cosine of the mean (Jensen's inequality).
  have mean_cos_le_cos_mean :
      ∑ plate ∈ plates, (plates.card : ℝ)⁻¹ • cos (turn plate)
        ≤ cos (∑ plate ∈ plates, (plates.card : ℝ)⁻¹ • turn plate) :=
    strictConcaveOn_cos_Icc.concaveOn.le_map_sum (t := plates)
      (w := fun _ => (plates.card : ℝ)⁻¹) (p := turn)
      (fun _ _ => by positivity) shares_sum_to_one turns_within_quarter
  have product_nonneg : 0 ≤ ∏ plate ∈ plates, cos (turn plate) :=
    prod_nonneg cos_nonneg
  have mean_of_turns :
      ∑ plate ∈ plates, (plates.card : ℝ)⁻¹ • turn plate
        = (∑ plate ∈ plates, turn plate) / plates.card := by
    simp only [smul_eq_mul]
    rw [← mul_sum, div_eq_inv_mul]
  have mean_of_cos :
      ∑ plate ∈ plates, (plates.card : ℝ)⁻¹ • cos (turn plate)
        = (∑ plate ∈ plates, cos (turn plate)) / plates.card := by
    simp only [smul_eq_mul]
    rw [← mul_sum, div_eq_inv_mul]
  have root_le_cos_average :
      (∏ plate ∈ plates, cos (turn plate)) ^ ((plates.card : ℝ)⁻¹)
        ≤ cos ((∑ plate ∈ plates, turn plate) / plates.card) := by
    rw [← mean_of_turns]
    refine geometric_le_arithmetic.trans ?_
    rw [← mean_of_cos]
    exact mean_cos_le_cos_mean
  calc ∏ plate ∈ plates, cos (turn plate)
      = ((∏ plate ∈ plates, cos (turn plate))
          ^ ((plates.card : ℝ)⁻¹)) ^ plates.card := by
        rw [rpow_inv_natCast_pow product_nonneg
          (card_pos.mpr plates_nonempty).ne']
    _ ≤ cos ((∑ plate ∈ plates, turn plate) / plates.card)
          ^ plates.card :=
        pow_le_pow_left₀ (rpow_nonneg product_nonneg _)
          root_le_cos_average _

end Layers

end SquigglyLine
