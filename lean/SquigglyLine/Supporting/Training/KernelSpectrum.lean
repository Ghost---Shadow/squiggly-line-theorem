/-
The whole error, in the kernel's own directions, and the Fourier case.

`SpectralBias.lean` follows one direction that the kernel only stretches.
This file does two more things.

**All the directions at once.** If the outputs have an orthonormal basis of
such directions, the error after `step_count` steps is the sum of its parts
along them, each part multiplied by its own factor:

* `residual_iterate_eq_sum`          the error after training, as that sum;
* `norm_sq_residual_iterate_eq_sum`  its squared length, one term per direction.

**The Fourier case.** Take `N` inputs evenly spaced over one period and a lift
whose kernel is a sum of cosines of the gap between two inputs, with size
`a k` at frequency `k`, for frequencies up to `K` with `2 * K < N`. Then the
sampled wave of frequency `m` is one of those directions, with strength
`N / 2 * a m ^ 2`:

* `sum_cos_arith_eq_zero`            a wave sampled at evenly spaced points
                                     over whole turns sums to zero;
* `sum_cos_mul_cos`                  two sampled waves of different
                                     frequencies do not overlap;
* `sum_gapKernel_mul_wave`           the kernel sum stretches a sampled wave;
* `PREDICT_ON_EXAMPLES`              a lift on finitely many inputs, as a
                                     linear map from weights to outputs;
* `kernel_predictOnExamples_apply`   its kernel, in coordinates;
* `fourier_direction_is_stretched`   the sampled wave is stretched by
                                     `N / 2 * a m ^ 2`;
* `fourier_spectral_bias`            so its error shrinks by
                                     `1 - learning_rate * (N / 2 * a m ^ 2)`
                                     each step.

This file is in typical Mathlib style. It is to be ported (`lean/PORTING.md`).
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
  {ι : Type*} [Fintype ι]

/-- **The whole error.** If every vector of an orthonormal basis is stretched
by the kernel, the error after `t` steps is the sum of its parts along the
basis, each multiplied by its own factor `(1 - η * strength i) ^ t`. -/
theorem residual_iterate_eq_sum
    (predict : Weights →L[ℝ] Outputs) (labels : Outputs) (η : ℝ)
    (w₀ : Weights) (b : OrthonormalBasis ι ℝ Outputs) (strength : ι → ℝ)
    (h : ∀ i, predict (adjoint predict (b i)) = strength i • b i) (t : ℕ) :
    GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
        ((TAKE_GRADIENT_STEP predict labels η)^[t] w₀)
      = ∑ i, ((1 - η * strength i) ^ t
          * inner ℝ (b i)
              (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels w₀))
          • b i := by
  conv_lhs => rw [← b.sum_repr' (GET_RESIDUAL _ labels _)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [inner_residual_iterate_gradientStep predict labels η w₀ (h i) t]

/-- **The whole loss.** The squared length of the error after `t` steps is a
sum with one term per direction, each shrinking on its own clock. -/
theorem norm_sq_residual_iterate_eq_sum
    (predict : Weights →L[ℝ] Outputs) (labels : Outputs) (η : ℝ)
    (w₀ : Weights) (b : OrthonormalBasis ι ℝ Outputs) (strength : ι → ℝ)
    (h : ∀ i, predict (adjoint predict (b i)) = strength i • b i) (t : ℕ) :
    ‖GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
        ((TAKE_GRADIENT_STEP predict labels η)^[t] w₀)‖ ^ 2
      = ∑ i, ((1 - η * strength i) ^ t) ^ 2
          * inner ℝ (b i)
              (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels w₀) ^ 2 := by
  rw [← b.sum_sq_inner_right]
  exact Finset.sum_congr rfl fun i _ => by
    rw [inner_residual_iterate_gradientStep predict labels η w₀ (h i) t,
      mul_pow]

end AllDirections

/-! ### The Fourier case -/

open Real Finset ContinuousLinearMap

/-- Waves sampled at evenly spaced points cancel. -/
theorem sum_cos_arith_eq_zero (N : ℕ) (α θ : ℝ) (p : ℤ)
    (hθ : sin (θ / 2) ≠ 0) (hN : (N : ℝ) * θ = p * (2 * π)) :
    ∑ j ∈ range N, cos (α + j * θ) = 0 := by
  have key : ∀ j : ℕ, 2 * sin (θ / 2) * cos (α + j * θ)
      = sin (α + ((j + 1 : ℕ) : ℝ) * θ - θ / 2)
        - sin (α + (j : ℝ) * θ - θ / 2) := by
    intro j
    have h1 : α + ((j + 1 : ℕ) : ℝ) * θ - θ / 2 = (α + j * θ) + θ / 2 := by
      push_cast; ring
    have h2 : α + (j : ℝ) * θ - θ / 2 = (α + j * θ) - θ / 2 := by ring
    rw [h1, h2, sin_add, sin_sub]; ring
  have tele : 2 * sin (θ / 2) * ∑ j ∈ range N, cos (α + j * θ) = 0 := by
    rw [mul_sum, sum_congr rfl fun j _ => key j,
      sum_range_sub (fun j : ℕ => sin (α + (j : ℝ) * θ - θ / 2))]
    have h : α + (N : ℝ) * θ - θ / 2 = (α - θ / 2) + p * (2 * π) := by
      rw [hN]; ring
    rw [h, sin_add_int_mul_two_pi]; simp
  exact (mul_eq_zero.mp tele).resolve_left (mul_ne_zero two_ne_zero hθ)

/-- Two sampled waves of different frequencies do not overlap; a wave
overlaps a shifted copy of itself by half the number of samples. -/
theorem sum_cos_mul_cos (N k m : ℕ) (φ : ℝ) (j : ℕ)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k + m < N) :
    ∑ i ∈ range N,
        cos (k * (2 * π * j / N - 2 * π * i / N)) * cos (m * (2 * π * i / N) - φ)
      = if k = m then N / 2 * cos (m * (2 * π * j / N) - φ) else 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN' : (N : ℝ) ≠ 0 := hN.ne'
  have prod : ∀ A B : ℝ, cos A * cos B = (cos (A + B) + cos (A - B)) / 2 := by
    intro A B; rw [cos_add, cos_sub]; ring
  have split : ∀ i : ℕ,
      cos (k * (2 * π * j / N - 2 * π * i / N)) * cos (m * (2 * π * i / N) - φ)
        = (cos ((k * (2 * π * j / N) - φ) + i * (2 * π * ((m : ℝ) - k) / N))
          + cos ((k * (2 * π * j / N) + φ) + i * (-(2 * π * ((k : ℝ) + m) / N)))) / 2 := by
    intro i
    have hA : (k * (2 * π * j / N) - φ) + i * (2 * π * ((m : ℝ) - k) / N)
        = k * (2 * π * j / N - 2 * π * i / N) + (m * (2 * π * i / N) - φ) := by ring
    have hB : (k * (2 * π * j / N) + φ) + i * (-(2 * π * ((k : ℝ) + m) / N))
        = k * (2 * π * j / N - 2 * π * i / N) - (m * (2 * π * i / N) - φ) := by ring
    rw [hA, hB, prod]
  rw [sum_congr rfl fun i _ => split i, ← sum_div, sum_add_distrib]
  -- the sum-frequency part always cancels
  have second : ∑ i ∈ range N,
      cos ((k * (2 * π * j / N) + φ) + i * (-(2 * π * ((k : ℝ) + m) / N))) = 0 := by
    apply sum_cos_arith_eq_zero N _ _ (-((k : ℤ) + m))
    · have hx : -(2 * π * ((k : ℝ) + m) / N) / 2 = -(π * ((k : ℝ) + m) / N) := by ring
      rw [hx, sin_neg, neg_ne_zero]
      apply ne_of_gt
      apply sin_pos_of_pos_of_lt_pi
      · have : (0 : ℝ) < (k : ℝ) + m := by positivity
        positivity
      · rw [mul_div_assoc]
        have hlt : ((k : ℝ) + m) / N < 1 := by
          rw [div_lt_one hN]; exact_mod_cast hkm
        nlinarith [pi_pos]
    · push_cast; field_simp
  rw [second, add_zero]
  split_ifs with hkm'
  · subst hkm'
    simp only [sub_self, mul_zero, zero_div, add_zero, sum_const,
      card_range, nsmul_eq_mul]
    ring
  · have first : ∑ i ∈ range N,
        cos ((k * (2 * π * j / N) - φ) + i * (2 * π * ((m : ℝ) - k) / N)) = 0 := by
      apply sum_cos_arith_eq_zero N _ _ ((m : ℤ) - k)
      · have hx : 2 * π * ((m : ℝ) - k) / N / 2 = π * (((m : ℝ) - k) / N) := by ring
        rw [hx]
        have hne : ((m : ℝ) - k) / N ≠ 0 := by
          apply div_ne_zero _ hN'
          rw [sub_ne_zero]; exact_mod_cast Ne.symm hkm'
        have hlt : |((m : ℝ) - k) / N| < 1 := by
          rw [abs_div, abs_of_pos hN, div_lt_one hN, abs_lt]
          have h1 : (k : ℝ) + m < N := by exact_mod_cast hkm
          have h2 : (0 : ℝ) ≤ k := by positivity
          have h3 : (0 : ℝ) ≤ m := by positivity
          constructor <;> linarith
        rw [abs_lt] at hlt
        intro hsin
        rw [sin_eq_zero_iff_of_lt_of_lt (by nlinarith [pi_pos]) (by nlinarith [pi_pos])]
          at hsin
        exact hne ((mul_eq_zero.mp hsin).resolve_left pi_ne_zero)
      · push_cast; field_simp
    rw [first, zero_div]

/-- **The kernel of evenly spaced inputs stretches each sampled wave.** -/
theorem sum_gapKernel_mul_wave (N K : ℕ) (a : ℕ → ℝ) (m : ℕ) (φ : ℝ) (j : ℕ)
    (hK : 2 * K < N) (hm1 : 1 ≤ m) (hmK : m ≤ K) :
    ∑ i ∈ range N,
        (∑ k ∈ Icc 1 K, a k ^ 2 * cos (k * (2 * π * j / N - 2 * π * i / N)))
          * cos (m * (2 * π * i / N) - φ)
      = (N / 2 * a m ^ 2) * cos (m * (2 * π * j / N) - φ) := by
  have swap : ∑ i ∈ range N,
        (∑ k ∈ Icc 1 K, a k ^ 2 * cos (k * (2 * π * j / N - 2 * π * i / N)))
          * cos (m * (2 * π * i / N) - φ)
      = ∑ k ∈ Icc 1 K, a k ^ 2 * ∑ i ∈ range N,
          cos (k * (2 * π * j / N - 2 * π * i / N)) * cos (m * (2 * π * i / N) - φ) := by
    simp_rw [sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun k _ => sum_congr rfl fun i _ => by ring
  rw [swap, sum_eq_single m]
  · simp only [sum_cos_mul_cos N m m φ j hm1 hm1 (by omega), ↓reduceIte]; ring
  · intro k hk hkm
    rw [mem_Icc] at hk
    simp only [sum_cos_mul_cos N k m φ j hk.1 hm1 (by omega), hkm, ↓reduceIte,
      mul_zero]
  · intro hm; exact absurd (mem_Icc.mpr ⟨hm1, hmK⟩) hm

/-! ### From a lift on finitely many inputs to a predictor -/

section Predictor

variable {Weights : Type*} [NormedAddCommGroup Weights]
  [InnerProductSpace ℝ Weights] [CompleteSpace Weights]
variable {Examples : Type*} [Fintype Examples]

/-- The outputs of a lifted model on a finite list of inputs, as a linear
map of the weights. -/
noncomputable def PREDICT_ON_EXAMPLES (lifted : Examples → Weights) :
    Weights →L[ℝ] EuclideanSpace ℝ Examples :=
  (EuclideanSpace.equiv Examples ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun example_index => innerSL ℝ (lifted example_index))

omit [CompleteSpace Weights] [Fintype Examples] in
theorem predictOnExamples_apply (lifted : Examples → Weights) (w : Weights)
    (i : Examples) :
    PREDICT_ON_EXAMPLES lifted w i = inner ℝ (lifted i) w := rfl

theorem adjoint_predictOnExamples (lifted : Examples → Weights)
    (d : EuclideanSpace ℝ Examples) :
    adjoint (PREDICT_ON_EXAMPLES lifted) d = ∑ i, d i • lifted i := by
  apply ext_inner_right ℝ
  intro w
  rw [adjoint_inner_left, sum_inner, PiLp.inner_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [predictOnExamples_apply, real_inner_smul_left]
  simp [mul_comm]

/-- The kernel, in coordinates: a sum of the lift kernel against the vector. -/
theorem kernel_predictOnExamples_apply (lifted : Examples → Weights)
    (d : EuclideanSpace ℝ Examples) (j : Examples) :
    PREDICT_ON_EXAMPLES lifted (adjoint (PREDICT_ON_EXAMPLES lifted) d) j
      = ∑ i, inner ℝ (lifted j) (lifted i) * d i := by
  rw [predictOnExamples_apply, adjoint_predictOnExamples, inner_sum]
  exact sum_congr rfl fun i _ => by rw [real_inner_smul_right]; ring

end Predictor

/-- **The Fourier version.** `N` inputs evenly spaced over one period, and a
lift whose kernel is a sum of cosines of the gap with sizes `a k`. Then the
sampled wave of frequency `m` is stretched by `N / 2 * a m ^ 2`. -/
theorem fourier_direction_is_stretched
    {Weights : Type*} [NormedAddCommGroup Weights]
    [InnerProductSpace ℝ Weights] [CompleteSpace Weights]
    (N K : ℕ) (a : ℕ → ℝ) (lifted : Fin N → Weights)
    (hkernel : ∀ j i : Fin N, inner ℝ (lifted j) (lifted i)
      = ∑ k ∈ Icc 1 K, a k ^ 2
          * cos (k * (2 * π * (j : ℕ) / N - 2 * π * (i : ℕ) / N)))
    (m : ℕ) (φ : ℝ) (hK : 2 * K < N) (hm1 : 1 ≤ m) (hmK : m ≤ K) :
    let predict := PREDICT_ON_EXAMPLES lifted
    let wave : EuclideanSpace ℝ (Fin N) :=
      WithLp.toLp 2 fun i => cos (m * (2 * π * (i : ℕ) / N) - φ)
    predict (adjoint predict wave) = (N / 2 * a m ^ 2) • wave := by
  intro predict wave
  ext j
  rw [kernel_predictOnExamples_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [hkernel, wave]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (∑ k ∈ Icc 1 K, a k ^ 2 * cos (k * (2 * π * (j : ℕ) / N - 2 * π * i / N)))
      * cos (m * (2 * π * i / N) - φ)) N]
  exact sum_gapKernel_mul_wave N K a m φ j hK hm1 hmK

/-- **Spectral bias, the Fourier version.** In the setting of
`fourier_direction_is_stretched`, the error along the sampled wave of
frequency `m` is multiplied by `1 - η * (N / 2 * a m ^ 2)` at every step. -/
theorem fourier_spectral_bias
    {Weights : Type*} [NormedAddCommGroup Weights]
    [InnerProductSpace ℝ Weights] [CompleteSpace Weights]
    (N K : ℕ) (a : ℕ → ℝ) (lifted : Fin N → Weights)
    (hkernel : ∀ j i : Fin N, inner ℝ (lifted j) (lifted i)
      = ∑ k ∈ Icc 1 K, a k ^ 2
          * cos (k * (2 * π * (j : ℕ) / N - 2 * π * (i : ℕ) / N)))
    (m : ℕ) (φ : ℝ) (hK : 2 * K < N) (hm1 : 1 ≤ m) (hmK : m ≤ K)
    (labels : EuclideanSpace ℝ (Fin N)) (η : ℝ) (w₀ : Weights) (t : ℕ) :
    let predict := PREDICT_ON_EXAMPLES lifted
    let wave : EuclideanSpace ℝ (Fin N) :=
      WithLp.toLp 2 fun i => cos (m * (2 * π * (i : ℕ) / N) - φ)
    inner ℝ wave (GET_RESIDUAL (predict : Weights →ₗ[ℝ] _) labels
        ((TAKE_GRADIENT_STEP predict labels η)^[t] w₀))
      = (1 - η * (N / 2 * a m ^ 2)) ^ t
        * inner ℝ wave (GET_RESIDUAL (predict : Weights →ₗ[ℝ] _) labels w₀) := by
  intro predict wave
  exact inner_residual_iterate_gradientStep predict labels η w₀
    (fourier_direction_is_stretched N K a lifted hkernel m φ hK hm1 hmK) t

end SquigglyLine
