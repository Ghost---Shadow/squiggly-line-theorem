/-
Averages: ensembles, weight averaging, and the ideal denoiser.

An average is never squigglier than what it averages, and never worse on
squared error than its members are on average.

Ensembles (`BLEND`):
* `error_of_the_average_equals_average_error_minus_spread` : the squared error of the average is the average squared
  error minus the spread of the members round the average.
* `ensemble_error_is_at_most_average_member_error` : so the average is at least as good as the members are
  on average.
* `average_slope_is_at_most_steepest_member` : and it is no steeper than the steepest member.

Weight averaging:
* `averaging_weights_is_averaging_lines` : for a model linear in its weights, averaging the
  weights is averaging the lines.
* `averaged_weights_error_is_at_most_average_member_error` : so the averaged weights are at least as good
  as the members are on average.

The ideal denoiser (`DENOISE_IDEALLY`):
* `weighted_squared_distance_splits_at_the_mean` : the weighted squared distance to any point is the
  weighted squared distance to the weighted mean plus the squared distance
  from the mean to the point.
* `weighted_mean_is_the_best_single_guess` : so the weighted mean is the best single guess.
* `ideal_denoiser_is_the_best_guess` : the ideal denoiser is that mean, with shares set
  by nearness to the noisy input. It is an attention head over the training
  examples.
* `ideal_denoiser_stays_inside_the_examples` : so it never leaves the region the training
  examples span.

Definitions: `BLEND`, `GET_WEIGHTED_MEAN`, `DENOISE_IDEALLY`.
Helper lemmas: `weighted_squared_distance_to_a_centre_expanded`, `offsets_from_the_weighted_mean_cancel`,
`ideal_denoiser_equals_weighted_mean_of_examples`.
-/
import SquigglyLine.Networks.Lift
import SquigglyLine.Supporting.NetworkShape.Attention

namespace SquigglyLine

open NNReal

/-! ### Ensembles -/

section Ensemble

variable {Members : Type*} (member_set : Finset Members)
  (shares predictions : Members → ℝ)

/-- The average of the predictions `predictions` with shares `shares`.
Python: `sum(shares[i] * predictions[i] for i in member_set)`. -/
def BLEND : ℝ :=
  ∑ i ∈ member_set, shares i * predictions i

/-- Expand the weighted squared distance of the predictions to a center. -/
theorem weighted_squared_distance_to_a_centre_expanded
    (center : ℝ) :
    let weighted_sq_error :=
      ∑ i ∈ member_set, shares i * (predictions i - center) ^ 2
    let sum_of_squares := ∑ i ∈ member_set, shares i * predictions i ^ 2
    let cross_term     :=
      2 * center * ∑ i ∈ member_set, shares i * predictions i  -- the middle term of (a - b)²
    let center_term    := center ^ 2 * ∑ i ∈ member_set, shares i
    weighted_sq_error = sum_of_squares - cross_term + center_term := by
  unfold_named_pieces
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The error of the average is the average error minus the spread.** -/
theorem error_of_the_average_equals_average_error_minus_spread
    (shares_sum_to_one : ∑ i ∈ member_set, shares i = 1)
    (label : ℝ) :
    let blend_error   := (BLEND member_set shares predictions - label) ^ 2
    let average_error :=
      ∑ i ∈ member_set, shares i * (predictions i - label) ^ 2
    let spread        :=
      ∑ i ∈ member_set, shares i *
        (predictions i - BLEND member_set shares predictions) ^ 2
    blend_error = average_error - spread := by
  unfold_named_pieces
  have expand (center : ℝ) :
      ∑ i ∈ member_set, shares i * (predictions i - center) ^ 2
        = ∑ i ∈ member_set, shares i * predictions i ^ 2
          - 2 * center * ∑ i ∈ member_set, shares i * predictions i
          + center ^ 2 * ∑ i ∈ member_set, shares i :=
    weighted_squared_distance_to_a_centre_expanded member_set shares predictions center
  rw [expand, expand, shares_sum_to_one]
  simp only [BLEND]
  ring

/-- **An ensemble is at least as good as its members are on average.** -/
theorem ensemble_error_is_at_most_average_member_error
    (shares_nonneg : ∀ i ∈ member_set, 0 ≤ shares i)
    (shares_sum_to_one : ∑ i ∈ member_set, shares i = 1)
    (label : ℝ) :
    let blend_error   := (BLEND member_set shares predictions - label) ^ 2
    let average_error :=
      ∑ i ∈ member_set, shares i * (predictions i - label) ^ 2
    blend_error ≤ average_error := by
  unfold_named_pieces
  -- The spread is a sum of non-negative terms, so subtracting it only helps.
  have spread_nonneg :
      0 ≤ ∑ i ∈ member_set, shares i *
        (predictions i - BLEND member_set shares predictions) ^ 2 :=
    Finset.sum_nonneg fun i member_in_set =>
      mul_nonneg (shares_nonneg i member_in_set) (sq_nonneg _)
  have blend_error_eq :
      (BLEND member_set shares predictions - label) ^ 2
        = ∑ i ∈ member_set, shares i * (predictions i - label) ^ 2
          - ∑ i ∈ member_set, shares i *
            (predictions i - BLEND member_set shares predictions) ^ 2 :=
    error_of_the_average_equals_average_error_minus_spread member_set shares predictions shares_sum_to_one label
  rw [blend_error_eq]
  linarith

/-- **An average is no steeper than its steepest member.** -/
theorem average_slope_is_at_most_steepest_member
    {Inputs : Type*} [PseudoMetricSpace Inputs]
    {slope_limit : SlopeLimit}
    {lines : Members → Inputs → ℝ}
    (lines_are_bounded : ∀ i ∈ member_set, LipschitzWith slope_limit (lines i))
    (shares_nonneg : ∀ i ∈ member_set, 0 ≤ shares i)
    (shares_sum_to_one : ∑ i ∈ member_set, shares i = 1) :
    LipschitzWith slope_limit fun input =>
      ∑ i ∈ member_set, shares i * lines i input := by
  refine LipschitzWith.of_dist_le_mul fun input other_input => ?_
  rw [Real.dist_eq, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ member_set,
        (shares i * lines i input - shares i * lines i other_input)|
      ≤ ∑ i ∈ member_set,
        |shares i * lines i input - shares i * lines i other_input| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ member_set, shares i * (slope_limit * dist input other_input) :=
        Finset.sum_le_sum fun i member_in_set => by
          have line_slope :=
            (lines_are_bounded i member_in_set).dist_le_mul input other_input
          rw [Real.dist_eq] at line_slope
          rw [← mul_sub, abs_mul,
            abs_of_nonneg (shares_nonneg i member_in_set)]
          exact mul_le_mul_of_nonneg_left line_slope
            (shares_nonneg i member_in_set)
    _ = slope_limit * dist input other_input := by
        rw [← Finset.sum_mul, shares_sum_to_one, one_mul]

end Ensemble

/-! ### Weight averaging -/

section Soup

variable {Inputs Weights Members : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]

/-- **Averaging weights is averaging lines**, for a model linear in its
weights. -/
theorem averaging_weights_is_averaging_lines
    (features : FeatureMap Inputs Weights)
    (member_set : Finset Members)
    (shares : Members → ℝ)
    (member_weights : Members → Weights)
    (input : Inputs) :
    let averaged_weights := ∑ i ∈ member_set, shares i • member_weights i
    let prediction_of_average :=
      EVALUATE_LIFTED_MODEL features averaged_weights input
    let average_of_predictions :=
      ∑ i ∈ member_set,
        shares i * EVALUATE_LIFTED_MODEL features (member_weights i) input
    prediction_of_average = average_of_predictions := by
  unfold_named_pieces
  simp only [EVALUATE_LIFTED_MODEL, sum_inner, inner_smul_left]
  rfl

/-- **Averaged weights are at least as good as the members are on
average.** -/
theorem averaged_weights_error_is_at_most_average_member_error
    (features : FeatureMap Inputs Weights)
    (member_set : Finset Members)
    {shares : Members → ℝ}
    (member_weights : Members → Weights)
    (shares_nonneg : ∀ i ∈ member_set, 0 ≤ shares i)
    (shares_sum_to_one : ∑ i ∈ member_set, shares i = 1)
    (input : Inputs)
    (label : ℝ) :
    let averaged_weights := ∑ i ∈ member_set, shares i • member_weights i
    let soup_error :=
      (EVALUATE_LIFTED_MODEL features averaged_weights input - label) ^ 2
    let average_member_error :=
      ∑ i ∈ member_set, shares i *
        (EVALUATE_LIFTED_MODEL features (member_weights i) input - label) ^ 2
    soup_error ≤ average_member_error := by
  unfold_named_pieces
  -- The soup predicts the blend of the members' predictions.
  have soup_is_blend :
      EVALUATE_LIFTED_MODEL features
          (∑ i ∈ member_set, shares i • member_weights i) input
        = ∑ i ∈ member_set,
            shares i *
              EVALUATE_LIFTED_MODEL features (member_weights i) input :=
    averaging_weights_is_averaging_lines features member_set shares member_weights input
  rw [soup_is_blend]
  exact ensemble_error_is_at_most_average_member_error member_set shares
    (fun i => EVALUATE_LIFTED_MODEL features (member_weights i) input)
    shares_nonneg shares_sum_to_one label

end Soup

/-! ### The ideal denoiser -/

section Denoiser

variable {Examples Space : Type*} [Fintype Examples]
  [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

/-- The mean of the points `points` with shares `shares`.
Python: `sum(shares[i] * points[i] for i in examples)`. -/
def GET_WEIGHTED_MEAN
    (shares : Examples → ℝ)
    (points : Examples → Space) : Space :=
  ∑ i, shares i • points i

/-- With shares that add to one, the points' offsets from their weighted mean
cancel out. -/
theorem offsets_from_the_weighted_mean_cancel
    {shares : Examples → ℝ}
    (shares_sum_to_one : ∑ i, shares i = 1)
    (points : Examples → Space) :
    let mean           := GET_WEIGHTED_MEAN shares points
    let weighted_offsets := ∑ i, shares i • (points i - mean)
    weighted_offsets = 0 := by
  unfold_named_pieces
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
    shares_sum_to_one, one_smul]
  exact sub_self _

/-- The weighted squared distance to any point `target` splits into the
weighted squared distance to the mean, plus the squared distance from the mean
to `target`. -/
theorem weighted_squared_distance_splits_at_the_mean
    {shares : Examples → ℝ}
    (shares_sum_to_one : ∑ i, shares i = 1)
    (points : Examples → Space)
    (target : Space) :
    let mean             := GET_WEIGHTED_MEAN shares points
    let spread_about_target := ∑ i, shares i * ‖points i - target‖ ^ 2
    let spread_about_mean   := ∑ i, shares i * ‖points i - mean‖ ^ 2
    let mean_offset         := ‖mean - target‖ ^ 2
    spread_about_target = spread_about_mean + mean_offset := by
  unfold_named_pieces
  -- The cross term vanishes because the offsets from the mean cancel.
  have cross_term_zero :
      ∑ i, shares i * inner ℝ (points i - GET_WEIGHTED_MEAN shares points)
        (GET_WEIGHTED_MEAN shares points - target) = 0 := by
    simp only [← real_inner_smul_left, ← sum_inner,
      offsets_from_the_weighted_mean_cancel shares_sum_to_one, inner_zero_left]
  have term_split (i : Examples) :
      shares i * ‖points i - target‖ ^ 2
        = shares i * ‖points i - GET_WEIGHTED_MEAN shares points‖ ^ 2
          + 2 * (shares i * inner ℝ
              (points i - GET_WEIGHTED_MEAN shares points)
              (GET_WEIGHTED_MEAN shares points - target))  -- the cross term of ‖a + b‖²
          + shares i * ‖GET_WEIGHTED_MEAN shares points - target‖ ^ 2 := by
    rw [show points i - target
        = points i - GET_WEIGHTED_MEAN shares points
          + (GET_WEIGHTED_MEAN shares points - target) by abel,
      norm_add_sq_real]
    ring
  rw [Finset.sum_congr rfl fun i _ => term_split i, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, cross_term_zero,
    ← Finset.sum_mul, shares_sum_to_one]
  ring

/-- **The weighted mean is the best single guess.** -/
theorem weighted_mean_is_the_best_single_guess
    {shares : Examples → ℝ}
    (shares_sum_to_one : ∑ i, shares i = 1)
    (points : Examples → Space)
    (target : Space) :
    let mean                := GET_WEIGHTED_MEAN shares points
    let spread_about_mean   := ∑ i, shares i * ‖points i - mean‖ ^ 2
    let spread_about_target := ∑ i, shares i * ‖points i - target‖ ^ 2
    spread_about_mean ≤ spread_about_target := by
  unfold_named_pieces
  have split_spread :
      ∑ i, shares i * ‖points i - target‖ ^ 2
        = ∑ i, shares i * ‖points i - GET_WEIGHTED_MEAN shares points‖ ^ 2
          + ‖GET_WEIGHTED_MEAN shares points - target‖ ^ 2 :=
    weighted_squared_distance_splits_at_the_mean shares_sum_to_one points target
  rw [split_spread]
  exact le_add_of_nonneg_right (sq_nonneg _)

variable [Nonempty Examples]

/-- The ideal denoiser for the training examples `examples` at noise level
`noise_level`. Given a noisy input `noisy_input`, each example gets a share
that falls with its squared distance from `noisy_input`, and the output is the
examples averaged with those shares. -/
noncomputable def DENOISE_IDEALLY
    (noise_level : ℝ)
    (examples : Examples → Space)
    (noisy_input : Space) : Space :=
  ATTEND (fun i => -‖noisy_input - examples i‖ ^ 2 / (2 * noise_level ^ 2))
    examples

omit [Nonempty Examples] in
/-- The ideal denoiser is the mean of the examples with softmax shares. -/
theorem ideal_denoiser_equals_weighted_mean_of_examples
    (noise_level : ℝ)
    (examples : Examples → Space)
    (noisy_input : Space) :
    let denoised := DENOISE_IDEALLY noise_level examples noisy_input
    let softmax_mean :=
      GET_WEIGHTED_MEAN
        (APPLY_SOFTMAX fun i =>
          -‖noisy_input - examples i‖ ^ 2 / (2 * noise_level ^ 2))
        examples
    denoised = softmax_mean := by
  unfold_named_pieces
  rfl

/-- **No other guess is better.** Among all outputs `other_output`, the ideal
denoiser has the least squared distance to the examples, weighted by how
likely each is to be the clean one. -/
theorem ideal_denoiser_is_the_best_guess
    (noise_level : ℝ)
    (examples : Examples → Space)
    (noisy_input : Space)
    (other_output : Space) :
    let shares :=
      APPLY_SOFTMAX fun j =>
        -‖noisy_input - examples j‖ ^ 2 / (2 * noise_level ^ 2)  -- Gaussian likelihood of each example
    let denoised := DENOISE_IDEALLY noise_level examples noisy_input
    let denoiser_spread := ∑ i, shares i * ‖examples i - denoised‖ ^ 2
    let other_spread    := ∑ i, shares i * ‖examples i - other_output‖ ^ 2
    denoiser_spread ≤ other_spread := by
  unfold_named_pieces
  exact weighted_mean_is_the_best_single_guess (softmax_shares_add_to_one _) examples other_output

/-- **The ideal denoiser only averages its training set.** Its output never
leaves the region the training examples span. -/
theorem ideal_denoiser_stays_inside_the_examples
    (noise_level : ℝ)
    (examples : Examples → Space)
    (noisy_input : Space) :
    let denoised := DENOISE_IDEALLY noise_level examples noisy_input
    let hull     := convexHull ℝ (Set.range examples)
    denoised ∈ hull := by
  unfold_named_pieces
  exact attention_output_lies_among_the_values _ examples

end Denoiser

end SquigglyLine
