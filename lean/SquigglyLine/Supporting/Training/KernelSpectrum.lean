/-
The whole error, in the kernel's own directions, and the Fourier case.

`SpectralBias.lean` follows one direction that the kernel only stretches.
This file does two more things.

**All the directions at once.** If the outputs have an orthonormal basis of
such directions, the error after `step_count` steps is the sum of its parts
along them, each part multiplied by its own factor:

* `residual_iterate_eq_sum`          the error after training, as that sum;
* `norm_sq_residual_iterate_eq_sum`  its squared length, one term per direction.

**The Fourier case.** Take `input_count` inputs evenly spaced over one period
and a lift whose kernel is a sum of cosines of the gap between two inputs, with
size `amplitude k` at frequency `k`, for frequencies up to `frequency_count`
with `2 * frequency_count < input_count`. Then the sampled wave of frequency
`frequency` is one of those directions, with strength
`input_count / 2 * amplitude frequency ^ 2`:

* `sum_cos_arith_eq_zero`            a wave sampled at evenly spaced points
                                     over whole turns sums to zero;
* `sum_cos_mul_cos`                  two sampled waves of different
                                     frequencies do not overlap;
* `sum_gapKernel_mul_wave`           the kernel sum stretches a sampled wave;
* `PREDICT_ON_EXAMPLES`              a lift on finitely many inputs, as a
                                     linear map from weights to outputs;
* `predictOnExamples_apply`          its output at one input;
* `adjoint_predictOnExamples`        its adjoint, as a weighted sum of lifts;
* `kernel_predictOnExamples_apply`   its kernel, in coordinates;
* `fourier_direction_is_stretched`   the sampled wave is stretched by
                                     `input_count / 2 * amplitude frequency ^ 2`;
* `fourier_spectral_bias`            so its error shrinks by
                                     `1 - learning_rate * (input_count / 2
                                     * amplitude frequency ^ 2)` each step.

A lift with that kernel:

* `LIFT_BY_FOURIER_SERIES`           the features of a Fourier series: for each
                                     frequency a cosine and a sine, times its
                                     amplitude;
* `inner_liftByFourierSeries`        its kernel is the sum of squared
                                     amplitudes times cosines of the gap;
* `fourierSeries_direction_is_stretched`
                                     so the Fourier version holds for it with
                                     nothing assumed about the kernel.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import SquigglyLine.Supporting.Training.SpectralBias

namespace SquigglyLine

/-! ### All the directions at once -/

section AllDirections

open ContinuousLinearMap

variable {Weights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]
  {Directions : Type*} [Fintype Directions]

/-- **The whole error.** If every vector of an orthonormal basis is stretched
by the kernel, the error after `step_count` steps is the sum of its parts along
the basis, each multiplied by its own factor
`(1 - learning_rate * strength i) ^ step_count`. -/
theorem residual_iterate_eq_sum
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (start_weights : Weights)
    (directions : OrthonormalBasis Directions ℝ Outputs)
    (strength : Directions → ℝ)
    (directions_are_stretched :
      ∀ i, predict (adjoint predict (directions i))
        = strength i • directions i)
    (step_count : ℕ) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights
    let start_error   := GET_RESIDUAL linear_predict labels start_weights
    let trained_error := GET_RESIDUAL linear_predict labels trained_weights
    let sum_of_parts  := ∑ i,
      ((1 - learning_rate * strength i) ^ step_count  -- one factor per step
        * inner ℝ (directions i) start_error) • directions i
    trained_error = sum_of_parts := by
  unfold_named_pieces
  -- Split the error into its parts along the basis, then shrink each part.
  conv_lhs => rw [← directions.sum_repr' (GET_RESIDUAL _ labels _)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [inner_residual_iterate_gradientStep predict labels learning_rate
      start_weights (directions_are_stretched i) step_count]

/-- **The whole loss.** The squared length of the error after `step_count`
steps is a sum with one term per direction, each shrinking on its own clock. -/
theorem norm_sq_residual_iterate_eq_sum
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (start_weights : Weights)
    (directions : OrthonormalBasis Directions ℝ Outputs)
    (strength : Directions → ℝ)
    (directions_are_stretched :
      ∀ i, predict (adjoint predict (directions i))
        = strength i • directions i)
    (step_count : ℕ) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights
    let start_error   := GET_RESIDUAL linear_predict labels start_weights
    let trained_error := GET_RESIDUAL linear_predict labels trained_weights
    let squared_loss  := ‖trained_error‖ ^ 2
    let sum_of_squares := ∑ i,
      ((1 - learning_rate * strength i) ^ step_count) ^ 2
        * inner ℝ (directions i) start_error ^ 2
    squared_loss = sum_of_squares := by
  unfold_named_pieces
  -- The squared length is the sum of the squared parts along the basis.
  rw [← directions.sum_sq_inner_right]
  exact Finset.sum_congr rfl fun i _ => by
    rw [inner_residual_iterate_gradientStep predict labels learning_rate
      start_weights (directions_are_stretched i) step_count, mul_pow]

end AllDirections

/-! ### The Fourier case -/

open Real Finset ContinuousLinearMap

/-- Waves sampled at evenly spaced points cancel: if `point_count` steps of
`angle_step` make a whole number `turn_count` of turns, then the cosines at
`start_angle + j * angle_step` sum to zero. -/
theorem sum_cos_arith_eq_zero
    (point_count : ℕ)
    (start_angle : ℝ)
    (angle_step : ℝ)
    (turn_count : ℤ)
    (half_step_sin_ne_zero : sin (angle_step / 2) ≠ 0)
    (whole_turns : point_count * angle_step = turn_count * (2 * PI)) :
    let angle_at := fun index : ℕ => start_angle + index * angle_step
    ∑ j ∈ range point_count, cos (angle_at j) = 0 := by
  unfold_named_pieces
  beta_reduce
  -- Multiplying by `2 * sin (angle_step / 2)` turns each cosine into a
  -- difference of two sines, so the sum telescopes.
  have cos_to_sine_difference : ∀ j : ℕ,
      2 * sin (angle_step / 2) * cos (start_angle + j * angle_step)
      = sin (start_angle + ((j + 1 : ℕ) : ℝ) * angle_step - angle_step / 2)
        - sin (start_angle + (j : ℝ) * angle_step - angle_step / 2) := by
    intro j
    have upper_angle :
        start_angle + ((j + 1 : ℕ) : ℝ) * angle_step - angle_step / 2
        = (start_angle + j * angle_step) + angle_step / 2 := by
      push_cast; ring
    have lower_angle :
        start_angle + (j : ℝ) * angle_step - angle_step / 2
        = (start_angle + j * angle_step) - angle_step / 2 := by ring
    rw [upper_angle, lower_angle, sin_add, sin_sub]; ring
  have telescoped :
      2 * sin (angle_step / 2)
        * ∑ j ∈ range point_count, cos (start_angle + j * angle_step) = 0 := by
    rw [mul_sum, sum_congr rfl fun j _ => cos_to_sine_difference j,
      sum_range_sub (fun j : ℕ =>
        sin (start_angle + (j : ℝ) * angle_step - angle_step / 2))]
    have end_angle :
        start_angle + (point_count : ℝ) * angle_step - angle_step / 2
        = (start_angle - angle_step / 2) + turn_count * (2 * PI) := by
      rw [whole_turns]; ring
    rw [end_angle, sin_add_int_mul_two_pi]; simp
  exact (mul_eq_zero.mp telescoped).resolve_left
    (mul_ne_zero two_ne_zero half_step_sin_ne_zero)

/-- Two sampled waves of different frequencies do not overlap; a wave
overlaps a shifted copy of itself by half the number of samples. -/
theorem sum_cos_mul_cos
    (input_count : ℕ)
    (first_frequency : ℕ)
    (second_frequency : ℕ)
    (phase : ℝ)
    (input_index : ℕ)
    (first_frequency_pos : 1 ≤ first_frequency)
    (second_frequency_pos : 1 ≤ second_frequency)
    (frequencies_below_count :
      first_frequency + second_frequency < input_count) :
    let input_at := fun index : ℕ => 2 * PI * index / input_count
    let overlap := ∑ i ∈ range input_count,
      cos (first_frequency * (input_at input_index - input_at i))
        * cos (second_frequency * input_at i - phase)
    let expected_overlap : ℝ :=
      if first_frequency = second_frequency
      then input_count / 2  -- half the samples, as `cos ^ 2` averages to `1 / 2`
        * cos (second_frequency * input_at input_index - phase)
      else 0
    overlap = expected_overlap := by
  unfold_named_pieces
  beta_reduce
  have count_pos : (0 : ℝ) < input_count := by
    exact_mod_cast (by omega : 0 < input_count)
  have count_ne_zero : (input_count : ℝ) ≠ 0 := count_pos.ne'
  have product_to_sum : ∀ angle other_angle : ℝ,
      cos angle * cos other_angle
      = (cos (angle + other_angle) + cos (angle - other_angle)) / 2 := by
    intro angle other_angle; rw [cos_add, cos_sub]; ring
  -- Each product of cosines is half a sum of two cosines: one at the
  -- difference of the frequencies, one at their sum.
  have split_product : ∀ i : ℕ,
      cos (first_frequency
          * (2 * PI * input_index / input_count - 2 * PI * i / input_count))
        * cos (second_frequency * (2 * PI * i / input_count) - phase)
      = (cos ((first_frequency * (2 * PI * input_index / input_count) - phase)
            + i * (2 * PI * ((second_frequency : ℝ) - first_frequency)
              / input_count))
        + cos ((first_frequency * (2 * PI * input_index / input_count) + phase)
            + i * (-(2 * PI * ((first_frequency : ℝ) + second_frequency)
              / input_count)))) / 2 := by
    intro i
    have difference_angle :
        (first_frequency * (2 * PI * input_index / input_count) - phase)
          + i * (2 * PI * ((second_frequency : ℝ) - first_frequency)
            / input_count)
        = first_frequency
            * (2 * PI * input_index / input_count - 2 * PI * i / input_count)
          + (second_frequency * (2 * PI * i / input_count) - phase) := by
      ring
    have sum_angle :
        (first_frequency * (2 * PI * input_index / input_count) + phase)
          + i * (-(2 * PI * ((first_frequency : ℝ) + second_frequency)
            / input_count))
        = first_frequency
            * (2 * PI * input_index / input_count - 2 * PI * i / input_count)
          - (second_frequency * (2 * PI * i / input_count) - phase) := by
      ring
    rw [difference_angle, sum_angle, product_to_sum]
  rw [sum_congr rfl fun i _ => split_product i, ← sum_div, sum_add_distrib]
  -- the sum-frequency part always cancels
  have sum_frequency_part_cancels : ∑ i ∈ range input_count,
      cos ((first_frequency * (2 * PI * input_index / input_count) + phase)
        + i * (-(2 * PI * ((first_frequency : ℝ) + second_frequency)
          / input_count))) = 0 := by
    apply sum_cos_arith_eq_zero input_count _ _
      (-((first_frequency : ℤ) + second_frequency))
    · have half_step :
          -(2 * PI * ((first_frequency : ℝ) + second_frequency) / input_count)
            / 2
          = -(PI * ((first_frequency : ℝ) + second_frequency) / input_count) :=
        by ring
      rw [half_step, sin_neg, neg_ne_zero]
      apply ne_of_gt
      apply sin_pos_of_pos_of_lt_pi
      · have frequencies_pos :
            (0 : ℝ) < (first_frequency : ℝ) + second_frequency := by
          positivity
        positivity
      · rw [mul_div_assoc]
        have ratio_lt_one :
            ((first_frequency : ℝ) + second_frequency) / input_count < 1 := by
          rw [div_lt_one count_pos]; exact_mod_cast frequencies_below_count
        nlinarith [pi_pos]
    · push_cast; field_simp
  rw [sum_frequency_part_cancels, add_zero]
  split_ifs with same_frequency
  · subst same_frequency
    simp only [sub_self, mul_zero, zero_div, add_zero, sum_const,
      card_range, nsmul_eq_mul]
    ring
  · -- different frequencies: the difference part cancels too
    have difference_part_cancels : ∑ i ∈ range input_count,
        cos ((first_frequency * (2 * PI * input_index / input_count) - phase)
          + i * (2 * PI * ((second_frequency : ℝ) - first_frequency)
            / input_count)) = 0 := by
      apply sum_cos_arith_eq_zero input_count _ _
        ((second_frequency : ℤ) - first_frequency)
      · have half_step :
            2 * PI * ((second_frequency : ℝ) - first_frequency) / input_count
              / 2
            = PI * (((second_frequency : ℝ) - first_frequency) / input_count) :=
          by ring
        rw [half_step]
        have gap_ne_zero :
            ((second_frequency : ℝ) - first_frequency) / input_count ≠ 0 := by
          apply div_ne_zero _ count_ne_zero
          rw [sub_ne_zero]; exact_mod_cast Ne.symm same_frequency
        have gap_abs_lt_one :
            |((second_frequency : ℝ) - first_frequency) / input_count| < 1 := by
          rw [abs_div, abs_of_pos count_pos, div_lt_one count_pos, abs_lt]
          have frequencies_lt_count :
              (first_frequency : ℝ) + second_frequency < input_count := by
            exact_mod_cast frequencies_below_count
          have first_nonneg : (0 : ℝ) ≤ first_frequency := by positivity
          have second_nonneg : (0 : ℝ) ≤ second_frequency := by positivity
          constructor <;> linarith
        rw [abs_lt] at gap_abs_lt_one
        intro sin_is_zero
        rw [sin_eq_zero_iff_of_lt_of_lt (by nlinarith [pi_pos])
          (by nlinarith [pi_pos])] at sin_is_zero
        exact gap_ne_zero
          ((mul_eq_zero.mp sin_is_zero).resolve_left pi_ne_zero)
      · push_cast; field_simp
    rw [difference_part_cancels, zero_div]

/-- **The kernel of evenly spaced inputs stretches each sampled wave.** -/
theorem sum_gapKernel_mul_wave
    (input_count : ℕ)
    (frequency_count : ℕ)
    (amplitude : ℕ → ℝ)
    (frequency : ℕ)
    (phase : ℝ)
    (input_index : ℕ)
    (frequencies_below_half_count : 2 * frequency_count < input_count)
    (frequency_pos : 1 ≤ frequency)
    (frequency_le_count : frequency ≤ frequency_count) :
    let input_at := fun index : ℕ => 2 * PI * index / input_count
    let kernel_sum := ∑ i ∈ range input_count,
      (∑ k ∈ Icc 1 frequency_count,
        amplitude k ^ 2 * cos (k * (input_at input_index - input_at i)))
        * cos (frequency * input_at i - phase)
    let stretched_wave :=
      (input_count / 2 * amplitude frequency ^ 2)  -- the strength of the direction
        * cos (frequency * input_at input_index - phase)
    kernel_sum = stretched_wave := by
  unfold_named_pieces
  beta_reduce
  -- Swap the sums: for each kernel frequency, a sum of two sampled waves.
  have swap_sums : ∑ i ∈ range input_count,
        (∑ k ∈ Icc 1 frequency_count, amplitude k ^ 2
          * cos (k * (2 * PI * input_index / input_count
            - 2 * PI * i / input_count)))
          * cos (frequency * (2 * PI * i / input_count) - phase)
      = ∑ k ∈ Icc 1 frequency_count, amplitude k ^ 2
        * ∑ i ∈ range input_count,
          cos (k * (2 * PI * input_index / input_count
            - 2 * PI * i / input_count))
            * cos (frequency * (2 * PI * i / input_count) - phase) := by
    simp_rw [sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun k _ => sum_congr rfl fun i _ => by ring
  -- Only the term at the wave's own frequency survives.
  rw [swap_sums, sum_eq_single frequency]
  · simp only [sum_cos_mul_cos input_count frequency frequency phase
      input_index frequency_pos frequency_pos (by omega), ↓reduceIte]
    ring
  · intro k k_in_range k_ne_frequency
    rw [mem_Icc] at k_in_range
    simp only [sum_cos_mul_cos input_count k frequency phase input_index
      k_in_range.1 frequency_pos (by omega), k_ne_frequency, ↓reduceIte,
      mul_zero]
  · intro frequency_not_in_range
    exact absurd (mem_Icc.mpr ⟨frequency_pos, frequency_le_count⟩)
      frequency_not_in_range

/-! ### From a lift on finitely many inputs to a predictor -/

section Predictor

variable {Weights : Type*} [NormedAddCommGroup Weights]
  [InnerProductSpace ℝ Weights] [CompleteSpace Weights]
variable {Examples : Type*} [Fintype Examples]

/-- The outputs of a lifted model on a finite list of inputs, as a linear
map of the weights.
Python: `lambda weights: [lifted_inputs[e] @ weights for e in examples]`. -/
noncomputable def PREDICT_ON_EXAMPLES (lifted_inputs : Examples → Weights) :
    Weights →L[ℝ] EuclideanSpace ℝ Examples :=
  (EuclideanSpace.equiv Examples ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun example_index =>
      innerSL ℝ (lifted_inputs example_index))

omit [CompleteSpace Weights] [Fintype Examples] in
/-- The output at one input is the inner product of its lift with the
weights. -/
theorem predictOnExamples_apply
    (lifted_inputs : Examples → Weights)
    (weights : Weights)
    (example_index : Examples) :
    let predicted := PREDICT_ON_EXAMPLES lifted_inputs weights example_index
    let inner_product := inner ℝ (lifted_inputs example_index) weights
    predicted = inner_product := by
  unfold_named_pieces
  rfl

/-- The adjoint of the predictor sends a vector to the sum of the lifts of the
inputs, each weighted by the matching entry of the vector. -/
theorem adjoint_predictOnExamples
    (lifted_inputs : Examples → Weights)
    (vector : EuclideanSpace ℝ Examples) :
    let predict := PREDICT_ON_EXAMPLES lifted_inputs
    let adjoint_image := adjoint predict vector
    let weighted_lifts := ∑ i, vector i • lifted_inputs i
    adjoint_image = weighted_lifts := by
  unfold_named_pieces
  apply ext_inner_right ℝ
  intro weights
  rw [adjoint_inner_left, sum_inner, PiLp.inner_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [predictOnExamples_apply, real_inner_smul_left]
  simp [mul_comm]

/-- The kernel, in coordinates: a sum of the lift kernel against the vector. -/
theorem kernel_predictOnExamples_apply
    (lifted_inputs : Examples → Weights)
    (vector : EuclideanSpace ℝ Examples)
    (output_index : Examples) :
    let predict := PREDICT_ON_EXAMPLES lifted_inputs
    let kernel_image := predict (adjoint predict vector) output_index
    let kernel_sum := ∑ i,
      inner ℝ (lifted_inputs output_index) (lifted_inputs i) * vector i
    kernel_image = kernel_sum := by
  unfold_named_pieces
  rw [predictOnExamples_apply, adjoint_predictOnExamples, inner_sum]
  exact sum_congr rfl fun i _ => by rw [real_inner_smul_right]; ring

end Predictor

/-- **The Fourier version.** `input_count` inputs evenly spaced over one
period, and a lift whose kernel is a sum of cosines of the gap with sizes
`amplitude k`. Then the sampled wave of frequency `frequency` is stretched by
`input_count / 2 * amplitude frequency ^ 2`. -/
theorem fourier_direction_is_stretched
    {Weights : Type*} [NormedAddCommGroup Weights]
    [InnerProductSpace ℝ Weights] [CompleteSpace Weights]
    (input_count : ℕ)
    (frequency_count : ℕ)
    (amplitude : ℕ → ℝ)
    (lifted_inputs : Fin input_count → Weights)
    (kernel_is_cosines :
      let input_at := fun index : ℕ => 2 * PI * index / input_count
      ∀ input_index other_index : Fin input_count,
        inner ℝ (lifted_inputs input_index) (lifted_inputs other_index)
        = ∑ k ∈ Icc 1 frequency_count, amplitude k ^ 2
            * cos (k * (input_at input_index - input_at other_index)))
    (frequency : ℕ)
    (phase : ℝ)
    (frequencies_below_half_count : 2 * frequency_count < input_count)
    (frequency_pos : 1 ≤ frequency)
    (frequency_le_count : frequency ≤ frequency_count) :
    let input_at := fun index : ℕ => 2 * PI * index / input_count
    let predict := PREDICT_ON_EXAMPLES lifted_inputs
    let wave : EuclideanSpace ℝ (Fin input_count) :=
      WithLp.toLp 2 fun i => cos (frequency * input_at (i : ℕ) - phase)
    let kernel_image := predict (adjoint predict wave)
    let stretched_wave :=
      (input_count / 2 * amplitude frequency ^ 2) • wave  -- the strength of the direction
    kernel_image = stretched_wave := by
  unfold_named_pieces
  beta_reduce
  ext input_index
  rw [kernel_predictOnExamples_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [kernel_is_cosines]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (∑ k ∈ Icc 1 frequency_count, amplitude k ^ 2
      * cos (k * (2 * PI * (input_index : ℕ) / input_count
        - 2 * PI * i / input_count)))
      * cos (frequency * (2 * PI * i / input_count) - phase)) input_count]
  exact sum_gapKernel_mul_wave input_count frequency_count amplitude frequency
    phase input_index frequencies_below_half_count frequency_pos
    frequency_le_count

/-- **Spectral bias, the Fourier version.** In the setting of
`fourier_direction_is_stretched`, the error along the sampled wave of
frequency `frequency` is multiplied by
`1 - learning_rate * (input_count / 2 * amplitude frequency ^ 2)` at every
step. -/
theorem fourier_spectral_bias
    {Weights : Type*} [NormedAddCommGroup Weights]
    [InnerProductSpace ℝ Weights] [CompleteSpace Weights]
    (input_count : ℕ)
    (frequency_count : ℕ)
    (amplitude : ℕ → ℝ)
    (lifted_inputs : Fin input_count → Weights)
    (kernel_is_cosines :
      let input_at := fun index : ℕ => 2 * PI * index / input_count
      ∀ input_index other_index : Fin input_count,
        inner ℝ (lifted_inputs input_index) (lifted_inputs other_index)
        = ∑ k ∈ Icc 1 frequency_count, amplitude k ^ 2
            * cos (k * (input_at input_index - input_at other_index)))
    (frequency : ℕ)
    (phase : ℝ)
    (frequencies_below_half_count : 2 * frequency_count < input_count)
    (frequency_pos : 1 ≤ frequency)
    (frequency_le_count : frequency ≤ frequency_count)
    (labels : EuclideanSpace ℝ (Fin input_count))
    (learning_rate : ℝ)
    (start_weights : Weights)
    (step_count : ℕ) :
    let input_at := fun index : ℕ => 2 * PI * index / input_count
    let predict := PREDICT_ON_EXAMPLES lifted_inputs
    let linear_predict :
        LinearPredictor Weights (EuclideanSpace ℝ (Fin input_count)) := predict
    let wave : EuclideanSpace ℝ (Fin input_count) :=
      WithLp.toLp 2 fun i => cos (frequency * input_at (i : ℕ) - phase)
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights
    let start_error   := inner ℝ wave
      (GET_RESIDUAL linear_predict labels start_weights)
    let trained_error := inner ℝ wave
      (GET_RESIDUAL linear_predict labels trained_weights)
    let share_left    :=
      (1 - learning_rate * (input_count / 2 * amplitude frequency ^ 2))
        ^ step_count  -- one factor per step, the strength is that of the wave
    trained_error = share_left * start_error := by
  unfold_named_pieces
  exact inner_residual_iterate_gradientStep (PREDICT_ON_EXAMPLES lifted_inputs)
    labels learning_rate start_weights
    (fourier_direction_is_stretched input_count frequency_count amplitude
      lifted_inputs kernel_is_cosines frequency phase
      frequencies_below_half_count frequency_pos frequency_le_count)
    step_count

section FourierSeries

open Real Finset ContinuousLinearMap

/-! ### A lift with this kernel: the Fourier series -/

/-- The features of a Fourier series with frequencies `1` to
`frequency_count`: for each frequency `k`, the pair
`amplitude k * cos (k * input)` and `amplitude k * sin (k * input)`.
Python: `[a[k] * cos(k * x) for k in ...] + [a[k] * sin(k * x) for k in ...]`. -/
noncomputable def LIFT_BY_FOURIER_SERIES
    (frequency_count : ℕ)
    (amplitude : ℕ → ℝ)
    (input : ℝ) :
    EuclideanSpace ℝ (↥(Icc 1 frequency_count) × Fin 2) :=
  WithLp.toLp 2 fun feature =>
    let frequency : ℕ := feature.1
    if feature.2 = 0
      then amplitude frequency * cos (frequency * input)   -- the cosine feature
      else amplitude frequency * sin (frequency * input)   -- the sine feature

/-- **The kernel of a Fourier series sees only the gap.** It is the sum, over
the frequencies, of the squared amplitude times the cosine of the frequency
times the gap. -/
theorem inner_liftByFourierSeries
    (frequency_count : ℕ)
    (amplitude : ℕ → ℝ)
    (input : ℝ)
    (other_input : ℝ) :
    let features := LIFT_BY_FOURIER_SERIES frequency_count amplitude
    let kernel   := inner ℝ (features input) (features other_input)
    let gap      := input - other_input
    let sum_of_cosines := ∑ k ∈ Icc 1 frequency_count,
      amplitude k ^ 2 * cos (k * gap)
    kernel = sum_of_cosines := by
  unfold_named_pieces
  rw [← sum_coe_sort (Icc 1 frequency_count)
    (fun k => amplitude k ^ 2 * cos (k * (input - other_input)))]
  simp only [LIFT_BY_FOURIER_SERIES, PiLp.inner_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  refine sum_congr rfl fun k _ => ?_
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, inner_apply]
  rw [mul_sub, cos_sub]
  ring

/-- **The Fourier version, with nothing assumed about the kernel.** For the
Fourier series on `input_count` evenly spaced inputs, the sampled wave of
frequency `frequency` is stretched by the kernel, by
`input_count / 2 * amplitude frequency ^ 2`. -/
theorem fourierSeries_direction_is_stretched
    (input_count : ℕ)
    (frequency_count : ℕ)
    (amplitude : ℕ → ℝ)
    (frequency : ℕ)
    (phase : ℝ)
    (frequencies_below_half_count : 2 * frequency_count < input_count)
    (frequency_pos : 1 ≤ frequency)
    (frequency_le_count : frequency ≤ frequency_count) :
    let input_at := fun index : ℕ => 2 * PI * index / input_count
    let lifted_inputs := fun index : Fin input_count =>
      LIFT_BY_FOURIER_SERIES frequency_count amplitude (input_at index)
    let predict := PREDICT_ON_EXAMPLES lifted_inputs
    let wave : EuclideanSpace ℝ (Fin input_count) :=
      WithLp.toLp 2 fun i => cos (frequency * input_at (i : ℕ) - phase)
    let kernel_image := predict (adjoint predict wave)
    let stretched_wave :=
      (input_count / 2 * amplitude frequency ^ 2) • wave  -- the strength of the direction
    kernel_image = stretched_wave := by
  intro input_at lifted_inputs
  exact fourier_direction_is_stretched input_count frequency_count amplitude
    lifted_inputs
    (fun input_index other_index =>
      inner_liftByFourierSeries frequency_count amplitude
        (input_at input_index) (input_at other_index))
    frequency phase frequencies_below_half_count frequency_pos
    frequency_le_count

end FourierSeries

end SquigglyLine
