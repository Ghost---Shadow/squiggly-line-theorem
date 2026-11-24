/-
Waves of the primes: a first link to the Riemann zeta function.

`docs/connections/riemann-hypothesis.md` has the plain account. In short: at
height `height` on a vertical line, the prime `p` contributes the wave
`cos (height * log p)` to the zeta function. Its frequency is `log p`. So
the zeta function on a vertical line is a sum of waves, one squiggly line.

This file proves three things about the waves of two different primes.

* `ratio_of_prime_logs_is_irrational`: the two frequencies have no common
  period. This is unique factorisation: `p ^ a = q ^ b` is impossible.
* `two_prime_clocks_reach_every_pair_of_phases`: so the two waves can be
  brought as near as wanted to any pair of phases at the same height. This
  is Kronecker's theorem for two frequencies, and the first step in the
  proof of Voronin's universality theorem.
* `two_prime_wave_takes_every_label_inside_its_band`: so the sum of the two
  waves takes every label strictly inside its band. In the words of
  `Oscillation.lean`, it covers its band.

`commensurate_wave_misses_part_of_its_band` is the control. With
frequencies 1 and 2, which do have a common period, the sum never goes
below `-9/8`, though its band reaches down to `-2`.

Nothing here is about the zeros of the zeta function, and nothing here is a
step towards the Riemann hypothesis.

| Name                  | Meaning                                         |
|-----------------------|-------------------------------------------------|
| `MAKE_TWO_PRIME_WAVE` | the sum of the waves of two primes              |

How to read the notation:

* `Real.log p` is the natural logarithm of `p`. It is the frequency of the
  wave of the prime `p`.
* `Irrational x` says `x` is not a fraction of whole numbers.
* A phase is an angle in radians. Adding a whole number of turns,
  `turns * (2 * PI)`, does not change a wave.

To do, not attempted:

* The same for any finite number of primes. It needs Kronecker's theorem in
  several dimensions, which Mathlib does not have, and the fact that the
  logarithms of the primes have no rational relation.
* A finite reach: every label of a closed band strictly inside the full band
  is taken within a fixed distance of every height (`COVERS_WITHIN`).
* The slope limit of the wave, `first_amplitude * log p +
  second_amplitude * log q`, and with it the sandwich of `Sandwich.lean`.
-/
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import SquigglyLine.Theorem.SineCloser

namespace SquigglyLine

open Real

/-! ## The two frequencies have no common period -/

/-- **The frequencies of two different primes have an irrational ratio.**
If `log q / log p` were a fraction `a / b`, then `q ^ b = p ^ a`, and a
number would have two different factorisations into primes. -/
theorem ratio_of_prime_logs_is_irrational
    {first_prime second_prime : ℕ}
    (first_is_prime : first_prime.Prime)
    (second_is_prime : second_prime.Prime)
    (primes_differ : first_prime ≠ second_prime) :
    let first_frequency  := Real.log first_prime
    let second_frequency := Real.log second_prime
    Irrational (second_frequency / first_frequency) := by
  unfold_named_pieces
  have first_prime_gt_one : (1 : ℝ) < first_prime := by
    exact_mod_cast first_is_prime.one_lt
  have second_prime_gt_one : (1 : ℝ) < second_prime := by
    exact_mod_cast second_is_prime.one_lt
  have first_frequency_pos : 0 < Real.log first_prime :=
    Real.log_pos first_prime_gt_one
  have second_frequency_pos : 0 < Real.log second_prime :=
    Real.log_pos second_prime_gt_one
  -- Suppose the ratio is the fraction `ratio`.
  rintro ⟨ratio, ratio_eq⟩
  have ratio_pos_real : (0 : ℝ) < ratio := by
    rw [ratio_eq]
    exact div_pos second_frequency_pos first_frequency_pos
  have ratio_pos : 0 < ratio := by exact_mod_cast ratio_pos_real
  have numerator_pos : 0 < ratio.num := Rat.num_pos.mpr ratio_pos
  have denominator_ne_zero : (ratio.den : ℝ) ≠ 0 := by
    exact_mod_cast ratio.den_nz
  -- Clear the two divisions: `numerator * log p = denominator * log q`.
  rw [Rat.cast_def,
    div_eq_div_iff denominator_ne_zero first_frequency_pos.ne'] at ratio_eq
  -- The numerator is positive, so it is a natural number.
  obtain ⟨numerator, numerator_eq⟩ :
      ∃ numerator : ℕ, ratio.num = numerator :=
    ⟨ratio.num.toNat, (Int.toNat_of_nonneg numerator_pos.le).symm⟩
  rw [numerator_eq] at ratio_eq
  -- Logarithms of powers: `log (p ^ numerator) = log (q ^ denominator)`.
  have logs_of_powers_agree :
      Real.log ((first_prime : ℝ) ^ numerator)
        = Real.log ((second_prime : ℝ) ^ ratio.den) := by
    rw [Real.log_pow, Real.log_pow]
    push_cast at ratio_eq
    linarith
  -- So the powers agree, first as real numbers and then as whole numbers.
  have powers_agree_real :
      (first_prime : ℝ) ^ numerator = (second_prime : ℝ) ^ ratio.den :=
    Real.log_injOn_pos
      (Set.mem_Ioi.mpr (pow_pos (by linarith) _))
      (Set.mem_Ioi.mpr (pow_pos (by linarith) _))
      logs_of_powers_agree
  have powers_agree : first_prime ^ numerator = second_prime ^ ratio.den := by
    exact_mod_cast powers_agree_real
  -- The second prime divides its own power, so it divides a power of the
  -- first prime, so it divides the first prime, so they are equal.
  have second_divides_power : second_prime ∣ first_prime ^ numerator := by
    rw [powers_agree]
    exact dvd_pow_self second_prime ratio.den_nz
  have second_divides_first : second_prime ∣ first_prime :=
    second_is_prime.dvd_of_dvd_pow second_divides_power
  have primes_equal : second_prime = first_prime :=
    (Nat.prime_dvd_prime_iff_eq second_is_prime first_is_prime).mp
      second_divides_first
  exact primes_differ primes_equal.symm

/-! ## Two clocks reach every pair of phases -/

/-- **Two prime clocks reach every pair of phases.** Think of each wave as a
clock hand that turns at its own frequency. Pick any two positions for the
two hands. At some height the first hand is exactly at its position and the
second is within `tolerance` of its position.

This is Kronecker's theorem (1884) for two frequencies. -/
theorem two_prime_clocks_reach_every_pair_of_phases
    {first_prime second_prime : ℕ}
    (first_is_prime : first_prime.Prime)
    (second_is_prime : second_prime.Prime)
    (primes_differ : first_prime ≠ second_prime)
    (first_target_phase : ℝ)
    (second_target_phase : ℝ)
    {tolerance : ℝ}
    (tolerance_pos : 0 < tolerance) :
    let first_frequency  := Real.log first_prime
    let second_frequency := Real.log second_prime
    ∃ (height : ℝ) (first_turns : ℤ) (second_turns : ℤ),
      let first_phase     := height * first_frequency
      let second_phase    := height * second_frequency
      let first_is_exact  :=
        first_phase = first_target_phase + first_turns * (2 * PI)
      let second_is_close :=
        |second_phase - (second_target_phase + second_turns * (2 * PI))|
          < tolerance
      first_is_exact ∧ second_is_close := by
  unfold_named_pieces
  have first_prime_gt_one : (1 : ℝ) < first_prime := by
    exact_mod_cast first_is_prime.one_lt
  have first_frequency_pos : 0 < Real.log first_prime :=
    Real.log_pos first_prime_gt_one
  have first_frequency_ne_zero : Real.log first_prime ≠ 0 :=
    first_frequency_pos.ne'
  -- How far the second hand turns while the first makes one radian.
  set ratio := Real.log second_prime / Real.log first_prime with ratio_def
  have ratio_is_irrational : Irrational ratio :=
    ratio_of_prime_logs_is_irrational first_is_prime second_is_prime
      primes_differ
  -- Each full turn of the first hand moves the second by `2 * PI * ratio`.
  -- These steps come near every point of the circle, since the ratio is
  -- irrational.
  have step_over_turn : 2 * PI * ratio / (2 * PI) = ratio := by
    field_simp
  have steps_are_dense :=
    (AddCircle.denseRange_zsmul_coe_iff (a := 2 * PI * ratio)
      (p := 2 * PI)).mpr (by rw [step_over_turn]; exact ratio_is_irrational)
  -- Where the second hand still has to go, after the first is in place.
  obtain ⟨first_turns, steps_come_close⟩ :=
    steps_are_dense.exists_dist_lt
      ((second_target_phase - first_target_phase * ratio : ℝ) :
        AddCircle (2 * PI))
      tolerance_pos
  -- Read the distance on the circle as a distance between real numbers,
  -- up to a whole number of turns.
  rw [dist_eq_norm, ← AddCircle.coe_zsmul, ← AddCircle.coe_sub,
    AddCircle.norm_eq] at steps_come_close
  obtain ⟨turns_back, close_up_to_turns⟩ :
      ∃ turns_back : ℤ,
        |second_target_phase - first_target_phase * ratio
            - first_turns • (2 * PI * ratio) - turns_back * (2 * PI)|
          < tolerance :=
    ⟨_, steps_come_close⟩
  refine ⟨(first_target_phase + first_turns * (2 * PI))
      / Real.log first_prime, first_turns, -turns_back, ?_, ?_⟩
  · -- The first hand is exactly in place.
    field_simp
  · -- The second hand is where the steps put it.
    have second_phase_error :
        (first_target_phase + first_turns * (2 * PI))
            / Real.log first_prime * Real.log second_prime
          - (second_target_phase + ((-turns_back : ℤ) : ℝ) * (2 * PI))
        = -(second_target_phase - first_target_phase * ratio
            - first_turns • (2 * PI * ratio) - turns_back * (2 * PI)) := by
      rw [ratio_def, zsmul_eq_mul]
      push_cast
      field_simp
      ring
    rw [second_phase_error, abs_neg]
    exact close_up_to_turns

/-! ## The sum of two prime waves covers its band -/

/-- The sum of the waves of two primes, as a function of the height.

    def MAKE_TWO_PRIME_WAVE(first_prime, second_prime,
                            first_amplitude, second_amplitude):
        return lambda height: (
            first_amplitude * cos(height * log(first_prime))
            + second_amplitude * cos(height * log(second_prime)))

With amplitudes `p ^ (-σ)` and `q ^ (-σ)` this is the real part of the two
prime terms `p ^ (-s) + q ^ (-s)` at `s = σ + i * height`. -/
noncomputable def MAKE_TWO_PRIME_WAVE
    (first_prime : ℕ)
    (second_prime : ℕ)
    (first_amplitude : ℝ)
    (second_amplitude : ℝ) : RealFunction :=
  fun height =>
    first_amplitude * cos (height * Real.log first_prime)
      + second_amplitude * cos (height * Real.log second_prime)

/-- The wave never leaves its band: it stays between minus and plus the sum
of the two amplitudes. This needs nothing about primes. -/
theorem two_prime_wave_stays_inside_its_band
    (first_prime : ℕ)
    (second_prime : ℕ)
    {first_amplitude : ℝ}
    {second_amplitude : ℝ}
    (first_amplitude_nonneg : 0 ≤ first_amplitude)
    (second_amplitude_nonneg : 0 ≤ second_amplitude)
    (height : ℝ) :
    let wave :=
      MAKE_TWO_PRIME_WAVE first_prime second_prime
        first_amplitude second_amplitude
    let band_edge := first_amplitude + second_amplitude
    |wave height| ≤ band_edge := by
  unfold_named_pieces
  unfold MAKE_TWO_PRIME_WAVE
  have first_cos_le_one := abs_cos_le_one (height * Real.log first_prime)
  have second_cos_le_one := abs_cos_le_one (height * Real.log second_prime)
  calc |first_amplitude * cos (height * Real.log first_prime)
          + second_amplitude * cos (height * Real.log second_prime)|
      ≤ |first_amplitude * cos (height * Real.log first_prime)|
          + |second_amplitude * cos (height * Real.log second_prime)| :=
        abs_add_le _ _
    _ = first_amplitude * |cos (height * Real.log first_prime)|
          + second_amplitude * |cos (height * Real.log second_prime)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg first_amplitude_nonneg,
          abs_of_nonneg second_amplitude_nonneg]
    _ ≤ first_amplitude * 1 + second_amplitude * 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left first_cos_le_one first_amplitude_nonneg)
          (mul_le_mul_of_nonneg_left second_cos_le_one
            second_amplitude_nonneg)
    _ = first_amplitude + second_amplitude := by ring

/-- **The sum of two prime waves takes every label inside its band.** At
height 0 both waves are at their top. Because the two clocks reach every
pair of phases, at some height both are as near the bottom as wanted. The
wave is continuous, so on the way it passes through every label between. -/
theorem two_prime_wave_takes_every_label_inside_its_band
    {first_prime second_prime : ℕ}
    (first_is_prime : first_prime.Prime)
    (second_is_prime : second_prime.Prime)
    (primes_differ : first_prime ≠ second_prime)
    {first_amplitude : ℝ}
    {second_amplitude : ℝ}
    (second_amplitude_nonneg : 0 ≤ second_amplitude)
    {label : ℝ}
    (label_inside_band : |label| < first_amplitude + second_amplitude) :
    let wave :=
      MAKE_TWO_PRIME_WAVE first_prime second_prime
        first_amplitude second_amplitude
    ∃ height, wave height = label := by
  unfold_named_pieces
  obtain ⟨label_above_bottom, label_below_top⟩ := abs_lt.mp label_inside_band
  -- How far the label is above the bottom of the band.
  set room := label + (first_amplitude + second_amplitude) with room_def
  have room_pos : 0 < room := by linarith
  have denominator_pos : 0 < second_amplitude + 1 := by linarith
  -- Bring the first wave exactly to its bottom (phase `PI`) and the second
  -- to within `tolerance` of its bottom.
  obtain ⟨low_height, first_turns, second_turns, first_is_exact,
      second_is_close⟩ :=
    two_prime_clocks_reach_every_pair_of_phases first_is_prime
      second_is_prime primes_differ PI PI
      (div_pos room_pos denominator_pos)
  -- The first wave is at -1.
  have first_cos_is_bottom :
      cos (low_height * Real.log first_prime) = -1 := by
    rw [first_is_exact, cos_add_int_mul_two_pi, cos_pi]
  -- The second wave is within `tolerance` of -1.
  have second_cos_near_bottom :
      cos (low_height * Real.log second_prime)
        ≤ -1 + room / (second_amplitude + 1) := by
    have cos_moves_less_than_phase :=
      abs_cos_sub_cos_le (low_height * Real.log second_prime)
        (PI + second_turns * (2 * PI))
    rw [cos_add_int_mul_two_pi, cos_pi] at cos_moves_less_than_phase
    have := (abs_le.mp
      (cos_moves_less_than_phase.trans second_is_close.le)).2
    linarith
  -- So at that height the wave is at or below the label.
  have amplitude_share_le_one :
      second_amplitude * (room / (second_amplitude + 1)) ≤ room := by
    rw [mul_div_assoc', div_le_iff₀ denominator_pos]
    nlinarith
  have wave_is_low :
      MAKE_TWO_PRIME_WAVE first_prime second_prime first_amplitude
        second_amplitude low_height ≤ label := by
    unfold MAKE_TWO_PRIME_WAVE
    rw [first_cos_is_bottom]
    have second_term_is_low :=
      mul_le_mul_of_nonneg_left second_cos_near_bottom
        second_amplitude_nonneg
    linarith
  -- At height 0 the wave is at the top of its band, above the label.
  have wave_is_high :
      label ≤ MAKE_TWO_PRIME_WAVE first_prime second_prime first_amplitude
        second_amplitude 0 := by
    unfold MAKE_TWO_PRIME_WAVE
    simp only [zero_mul, cos_zero, mul_one]
    linarith
  -- A continuous function takes every value between two of its values.
  have wave_is_continuous :
      Continuous (MAKE_TWO_PRIME_WAVE first_prime second_prime
        first_amplitude second_amplitude) := by
    unfold MAKE_TWO_PRIME_WAVE
    fun_prop
  have label_is_between :
      label ∈ Set.uIcc
        (MAKE_TWO_PRIME_WAVE first_prime second_prime first_amplitude
          second_amplitude low_height)
        (MAKE_TWO_PRIME_WAVE first_prime second_prime first_amplitude
          second_amplitude 0) :=
    Set.mem_uIcc.mpr (Or.inl ⟨wave_is_low, wave_is_high⟩)
  obtain ⟨height, -, height_hits_label⟩ :=
    intermediate_value_uIcc wave_is_continuous.continuousOn label_is_between
  exact ⟨height, height_hits_label⟩

/-! ## The control: frequencies with a common period -/

/-- **A wave whose two frequencies have a common period misses part of its
band.** With frequencies 1 and 2 and both amplitudes 1, the band is from -2
to 2, and the sum never goes below `-9/8`. So the theorem above does need
the two frequencies to be those of different primes. -/
theorem commensurate_wave_misses_part_of_its_band
    (height : ℝ) :
    let slow_wave := cos height
    let fast_wave := cos (2 * height)   -- twice the frequency: a common period of `2 * PI`
    let lowest_value : ℝ := -9 / 8
    lowest_value ≤ slow_wave + fast_wave := by
  unfold_named_pieces
  -- `cos (2 * x) = 2 * cos x ^ 2 - 1`, and then the sum is
  -- `2 * (cos x + 1/4) ^ 2 - 9/8`.
  rw [cos_two_mul]
  nlinarith [sq_nonneg (cos height + 1 / 4)]

end SquigglyLine
