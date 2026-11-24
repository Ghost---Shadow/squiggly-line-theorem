/-
Waves of the primes: a first link to the Riemann zeta function.

`docs/connections/riemann-hypothesis.md` has the plain account. In short: at
height `height` on a vertical line, the prime `p` contributes the wave
`cos (height * log p)` to the zeta function. Its frequency is `log p`. So
the zeta function on a vertical line is a sum of waves, one squiggly line.

This file proves seven things about the waves of two different primes.

* `ratio_of_prime_logs_is_irrational`: the two frequencies have no common
  period. This is unique factorisation: `p ^ a = q ^ b` is impossible.
* `two_prime_clocks_reach_every_pair_of_phases`: so the two waves can be
  brought as near as wanted to any pair of phases at the same height. This
  is Kronecker's theorem for two frequencies, and the first step in the
  proof of Voronin's universality theorem.
* `two_prime_wave_takes_every_label_inside_its_band`: so the sum of the two
  waves takes every label strictly inside its band. In the words of
  `Oscillation.lean`, it covers its band.

* `two_prime_wave_covers_a_narrower_band`: and it does so with a finite
  reach. Within a fixed distance of every height it takes every label of
  any band strictly inside its own. This is `COVERS_WITHIN`.
* `two_prime_wave_fits_any_target_after_a_bounded_warp`: so the warp theorem
  of `Oscillation.lean` applies. Any target in the narrower band is fitted
  exactly after moving each input by at most the reach.

* `two_prime_wave_slope_is_at_most_amplitudes_times_frequencies`: the slope
  of the wave is at most `|A| * log p + |B| * log q`.
* `two_prime_wave_is_near_the_data_and_pays_the_slope_tax`: so both bounds
  of the squiggly line theorem hold for it: near the data, and steep.

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
* A number for the reach. The proof gets the reach from compactness, which
  gives no number.
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

/-! ## A finite reach -/

/-- **Steps of an irrational size come near every point of the circle within
a fixed number of steps.** The circle is compact, so finitely many of the
steps already come within `tolerance` of every point. -/
theorem irrational_steps_come_near_every_point_in_bounded_time
    {ratio : ℝ}
    (ratio_is_irrational : Irrational ratio)
    {tolerance : ℝ}
    (tolerance_pos : 0 < tolerance) :
    ∃ step_limit : ℕ, ∀ target : ℝ,
      ∃ (step_count : ℤ) (turns_back : ℤ),
        let uses_few_steps := step_count.natAbs ≤ step_limit
        let step_size      := 2 * PI * ratio
        let is_close       :=
          |target - step_count * step_size - turns_back * (2 * PI)|
            < tolerance
        uses_few_steps ∧ is_close := by
  unfold_named_pieces
  have circle_has_positive_length : Fact ((0 : ℝ) < 2 * PI) :=
    ⟨by positivity⟩
  have step_over_turn : 2 * PI * ratio / (2 * PI) = ratio := by
    field_simp
  have steps_are_dense :=
    (AddCircle.denseRange_zsmul_coe_iff (a := 2 * PI * ratio)
      (p := 2 * PI)).mpr (by rw [step_over_turn]; exact ratio_is_irrational)
  -- Put an open ball of radius `tolerance` round every step. The balls
  -- cover the circle, so finitely many of them do.
  obtain ⟨chosen_steps, chosen_steps_cover⟩ :=
    isCompact_univ.elim_finite_subcover
      (fun step_count : ℤ =>
        Metric.ball
          (step_count • ((2 * PI * ratio : ℝ) : AddCircle (2 * PI)))
          tolerance)
      (fun _ => Metric.isOpen_ball)
      (fun point _ => by
        obtain ⟨step_count, step_is_close⟩ :=
          steps_are_dense.exists_dist_lt point tolerance_pos
        exact Set.mem_iUnion.mpr
          ⟨step_count, Metric.mem_ball.mpr step_is_close⟩)
  -- The largest of the chosen step counts is the limit.
  refine ⟨chosen_steps.sup Int.natAbs, fun target => ?_⟩
  have target_is_covered :=
    chosen_steps_cover (Set.mem_univ ((target : ℝ) : AddCircle (2 * PI)))
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop]
    at target_is_covered
  obtain ⟨step_count, step_is_chosen, step_is_close⟩ := target_is_covered
  rw [dist_eq_norm, ← AddCircle.coe_zsmul, ← AddCircle.coe_sub,
    AddCircle.norm_eq, zsmul_eq_mul] at step_is_close
  exact ⟨step_count, _, Finset.le_sup (f := Int.natAbs) step_is_chosen,
    step_is_close⟩

/-- **Two prime clocks reach every pair of phases within a fixed distance of
every height.** The same as `two_prime_clocks_reach_every_pair_of_phases`,
with a bound: there is a `reach`, depending only on the two primes and the
tolerance, such that a good height lies within `reach` of any height you
start from. -/
theorem two_prime_clocks_reach_every_pair_of_phases_within_a_fixed_distance
    {first_prime second_prime : ℕ}
    (first_is_prime : first_prime.Prime)
    (second_is_prime : second_prime.Prime)
    (primes_differ : first_prime ≠ second_prime)
    {tolerance : ℝ}
    (tolerance_pos : 0 < tolerance) :
    let first_frequency  := Real.log first_prime
    let second_frequency := Real.log second_prime
    ∃ reach : ℝ,
      ∀ (start_height first_target_phase second_target_phase : ℝ),
        ∃ (height : ℝ) (first_turns : ℤ) (second_turns : ℤ),
          let is_near_the_start := |height - start_height| ≤ reach
          let first_is_exact    :=
            height * first_frequency
              = first_target_phase + first_turns * (2 * PI)
          let second_is_close   :=
            |height * second_frequency
                - (second_target_phase + second_turns * (2 * PI))|
              < tolerance
          is_near_the_start ∧ first_is_exact ∧ second_is_close := by
  unfold_named_pieces
  have first_prime_gt_one : (1 : ℝ) < first_prime := by
    exact_mod_cast first_is_prime.one_lt
  have first_frequency_pos : 0 < Real.log first_prime :=
    Real.log_pos first_prime_gt_one
  have first_frequency_ne_zero : Real.log first_prime ≠ 0 :=
    first_frequency_pos.ne'
  have two_pi_pos : (0 : ℝ) < 2 * PI := by positivity
  set ratio := Real.log second_prime / Real.log first_prime with ratio_def
  have ratio_is_irrational : Irrational ratio :=
    ratio_of_prime_logs_is_irrational first_is_prime second_is_prime
      primes_differ
  obtain ⟨step_limit, steps_reach⟩ :=
    irrational_steps_come_near_every_point_in_bounded_time
      ratio_is_irrational tolerance_pos
  refine ⟨(2 * PI + 2 * PI * step_limit) / Real.log first_prime,
    fun start_height first_target_phase second_target_phase => ?_⟩
  -- How far the first hand still has to turn, less whole turns: a number
  -- from 0 up to one turn.
  obtain ⟨first_left, first_left_def⟩ :
      ∃ first_left : ℝ, first_left
        = first_target_phase - start_height * Real.log first_prime :=
    ⟨_, rfl⟩
  obtain ⟨whole_turns, whole_turns_def⟩ :
      ∃ whole_turns : ℤ, whole_turns = ⌊first_left / (2 * PI)⌋ := ⟨_, rfl⟩
  obtain ⟨first_left_reduced, reduced_def⟩ :
      ∃ first_left_reduced : ℝ, first_left_reduced
        = first_left - whole_turns * (2 * PI) := ⟨_, rfl⟩
  have reduced_nonneg : 0 ≤ first_left_reduced := by
    have floor_le := Int.floor_le (first_left / (2 * PI))
    rw [← whole_turns_def, le_div_iff₀ two_pi_pos] at floor_le
    linarith
  have reduced_lt_one_turn : first_left_reduced < 2 * PI := by
    have lt_floor_add_one := Int.lt_floor_add_one (first_left / (2 * PI))
    rw [← whole_turns_def, div_lt_iff₀ two_pi_pos] at lt_floor_add_one
    linarith
  -- Full turns of the first hand bring the second hand where it must go.
  obtain ⟨step_count, turns_back, uses_few_steps, is_close⟩ :=
    steps_reach (second_target_phase
      - start_height * Real.log second_prime - first_left_reduced * ratio)
  have step_abs_le : |(step_count : ℝ)| ≤ step_limit := by
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast uses_few_steps
  refine ⟨start_height
      + (first_left_reduced + step_count * (2 * PI)) / Real.log first_prime,
    step_count - whole_turns, -turns_back, ?_, ?_, ?_⟩
  · -- The height moved by less than one turn plus `step_limit` turns.
    have numerator_bound :
        |first_left_reduced + step_count * (2 * PI)|
          ≤ 2 * PI + 2 * PI * step_limit :=
      calc |first_left_reduced + step_count * (2 * PI)|
          ≤ |first_left_reduced| + |(step_count : ℝ) * (2 * PI)| :=
            abs_add_le _ _
        _ = first_left_reduced + |(step_count : ℝ)| * (2 * PI) := by
            rw [abs_of_nonneg reduced_nonneg, abs_mul, abs_of_pos two_pi_pos]
        _ ≤ 2 * PI + 2 * PI * step_limit := by
            have steps_bound :=
              mul_le_mul_of_nonneg_right step_abs_le two_pi_pos.le
            linarith
    rw [add_sub_cancel_left, abs_div, abs_of_pos first_frequency_pos]
    exact div_le_div_of_nonneg_right numerator_bound first_frequency_pos.le
  · -- The first hand is exactly in place.
    rw [reduced_def, first_left_def]
    push_cast
    field_simp
    ring
  · -- The second hand is where the steps put it.
    have second_phase_error :
        (start_height + (first_left_reduced + step_count * (2 * PI))
            / Real.log first_prime) * Real.log second_prime
          - (second_target_phase + ((-turns_back : ℤ) : ℝ) * (2 * PI))
        = -(second_target_phase - start_height * Real.log second_prime
            - first_left_reduced * ratio
            - step_count * (2 * PI * ratio) - turns_back * (2 * PI)) := by
      rw [ratio_def]
      push_cast
      field_simp
      ring
    rw [second_phase_error, abs_neg]
    exact is_close

/-- **The sum of two prime waves covers a narrower band, with a finite
reach.** Take any band strictly inside the full band of the wave. There is a
`reach` such that within `reach` of every height the wave takes every label
of the narrower band. This is `COVERS_WITHIN` of `Oscillation.lean`, the
hypothesis of the covering bound and of the warp theorem. -/
theorem two_prime_wave_covers_a_narrower_band
    {first_prime second_prime : ℕ}
    (first_is_prime : first_prime.Prime)
    (second_is_prime : second_prime.Prime)
    (primes_differ : first_prime ≠ second_prime)
    {first_amplitude : ℝ}
    {second_amplitude : ℝ}
    (second_amplitude_nonneg : 0 ≤ second_amplitude)
    {inner_edge : ℝ}
    (inner_edge_inside : inner_edge < first_amplitude + second_amplitude) :
    let wave :=
      MAKE_TWO_PRIME_WAVE first_prime second_prime
        first_amplitude second_amplitude
    let narrower_band := Set.Icc (-inner_edge) inner_edge
    ∃ reach : ℝ, COVERS_WITHIN wave reach narrower_band := by
  unfold_named_pieces
  -- How much narrower the band is than the full band.
  obtain ⟨room, room_def⟩ :
      ∃ room : ℝ, room = first_amplitude + second_amplitude - inner_edge :=
    ⟨_, rfl⟩
  have room_pos : 0 < room := by linarith
  have denominator_pos : 0 < second_amplitude + 1 := by linarith
  have amplitude_share_le_room :
      second_amplitude * (room / (second_amplitude + 1)) ≤ room := by
    rw [mul_div_assoc', div_le_iff₀ denominator_pos]
    nlinarith
  obtain ⟨reach, clocks_reach⟩ :=
    two_prime_clocks_reach_every_pair_of_phases_within_a_fixed_distance
      first_is_prime second_is_prime primes_differ
      (div_pos room_pos denominator_pos)
  refine ⟨reach, fun input label label_in_band => ?_⟩
  obtain ⟨label_above_inner_bottom, label_below_inner_top⟩ :=
    Set.mem_Icc.mp label_in_band
  -- A height near `input` where both waves are at or near the bottom ...
  obtain ⟨low_height, low_first_turns, low_second_turns, low_is_near,
      low_first_is_exact, low_second_is_close⟩ :=
    clocks_reach input PI PI
  -- ... and one where both are at or near the top.
  obtain ⟨high_height, high_first_turns, high_second_turns, high_is_near,
      high_first_is_exact, high_second_is_close⟩ :=
    clocks_reach input 0 0
  have wave_is_low :
      MAKE_TWO_PRIME_WAVE first_prime second_prime first_amplitude
        second_amplitude low_height ≤ label := by
    have first_cos_is_bottom :
        cos (low_height * Real.log first_prime) = -1 := by
      rw [low_first_is_exact, cos_add_int_mul_two_pi, cos_pi]
    have cos_moves_less_than_phase :=
      abs_cos_sub_cos_le (low_height * Real.log second_prime)
        (PI + low_second_turns * (2 * PI))
    rw [cos_add_int_mul_two_pi, cos_pi] at cos_moves_less_than_phase
    have second_cos_near_bottom := (abs_le.mp
      (cos_moves_less_than_phase.trans low_second_is_close.le)).2
    have second_term_is_low :=
      mul_le_mul_of_nonneg_left
        (show cos (low_height * Real.log second_prime)
            ≤ -1 + room / (second_amplitude + 1) by linarith)
        second_amplitude_nonneg
    unfold MAKE_TWO_PRIME_WAVE
    rw [first_cos_is_bottom]
    linarith
  have wave_is_high :
      label ≤ MAKE_TWO_PRIME_WAVE first_prime second_prime first_amplitude
        second_amplitude high_height := by
    have first_cos_is_top :
        cos (high_height * Real.log first_prime) = 1 := by
      rw [high_first_is_exact, cos_add_int_mul_two_pi, cos_zero]
    have cos_moves_less_than_phase :=
      abs_cos_sub_cos_le (high_height * Real.log second_prime)
        (0 + high_second_turns * (2 * PI))
    rw [cos_add_int_mul_two_pi, cos_zero] at cos_moves_less_than_phase
    have second_cos_near_top := (abs_le.mp
      (cos_moves_less_than_phase.trans high_second_is_close.le)).1
    have second_term_is_high :=
      mul_le_mul_of_nonneg_left
        (show 1 - room / (second_amplitude + 1)
            ≤ cos (high_height * Real.log second_prime) by linarith)
        second_amplitude_nonneg
    unfold MAKE_TWO_PRIME_WAVE
    rw [first_cos_is_top]
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
          second_amplitude high_height) :=
    Set.mem_uIcc.mpr (Or.inl ⟨wave_is_low, wave_is_high⟩)
  obtain ⟨height, height_is_between, height_hits_label⟩ :=
    intermediate_value_uIcc wave_is_continuous.continuousOn label_is_between
  -- That height lies between two heights that are both near `input`.
  refine ⟨height, ?_, height_hits_label⟩
  obtain ⟨low_from_below, low_from_above⟩ := abs_le.mp low_is_near
  obtain ⟨high_from_below, high_from_above⟩ := abs_le.mp high_is_near
  rw [Real.dist_eq, abs_le]
  rcases Set.mem_uIcc.mp height_is_between with
    ⟨low_le_height, height_le_high⟩ | ⟨high_le_height, height_le_low⟩
  · constructor <;> linarith
  · constructor <;> linarith

/-- **Any target in the narrower band is fitted exactly after a bounded
warp.** This is `exists_warp_of_coversWithin` for the sum of two prime
waves: move each input by at most `reach`, and the wave has exactly the
target's value there. It is this project's small counterpart of
universality: the nearness is used by moving the input. -/
theorem two_prime_wave_fits_any_target_after_a_bounded_warp
    {first_prime second_prime : ℕ}
    (first_is_prime : first_prime.Prime)
    (second_is_prime : second_prime.Prime)
    (primes_differ : first_prime ≠ second_prime)
    {first_amplitude : ℝ}
    {second_amplitude : ℝ}
    (second_amplitude_nonneg : 0 ≤ second_amplitude)
    {inner_edge : ℝ}
    (inner_edge_inside : inner_edge < first_amplitude + second_amplitude) :
    let wave :=
      MAKE_TWO_PRIME_WAVE first_prime second_prime
        first_amplitude second_amplitude
    let narrower_band := Set.Icc (-inner_edge) inner_edge
    ∃ reach : ℝ, ∀ target : RealFunction,
      (∀ input, target input ∈ narrower_band) →
      ∃ warp : WarpOver ℝ,
        let moves_each_input_a_little :=
          ∀ input, dist input (warp input) ≤ reach
        let hits_the_target :=
          ∀ input, wave (warp input) = target input
        moves_each_input_a_little ∧ hits_the_target := by
  unfold_named_pieces
  obtain ⟨reach, wave_covers⟩ :=
    two_prime_wave_covers_a_narrower_band first_is_prime second_is_prime
      primes_differ second_amplitude_nonneg inner_edge_inside
  exact ⟨reach, fun target target_in_band =>
    exists_warp_of_coversWithin wave_covers target target_in_band⟩

/-! ## The slope of the wave, and the sandwich -/

/-- **The wave of a prime is as steep as its frequency.** The sum of the two
waves has slope at most `|first_amplitude| * log p + |second_amplitude| *
log q`. A larger prime has a larger frequency `log p`, so its wave is
squigglier. -/
theorem two_prime_wave_slope_is_at_most_amplitudes_times_frequencies
    (first_prime : ℕ)
    (second_prime : ℕ)
    (first_amplitude : ℝ)
    (second_amplitude : ℝ) :
    let wave :=
      MAKE_TWO_PRIME_WAVE first_prime second_prime
        first_amplitude second_amplitude
    let first_slope  := ‖first_amplitude‖₊ * ‖Real.log first_prime‖₊    -- `‖x‖₊` is `|x|`, as a number that is never negative
    let second_slope := ‖second_amplitude‖₊ * ‖Real.log second_prime‖₊
    let slope_limit : SlopeLimit := first_slope + second_slope
    LipschitzWith slope_limit wave := by
  unfold_named_pieces
  refine LipschitzWith.of_dist_le_mul fun height other_height => ?_
  -- `cos` never changes faster than its angle.
  have first_cos_gap :=
    abs_cos_sub_cos_le (height * Real.log first_prime)
      (other_height * Real.log first_prime)
  have second_cos_gap :=
    abs_cos_sub_cos_le (height * Real.log second_prime)
      (other_height * Real.log second_prime)
  have first_angle_gap :
      height * Real.log first_prime - other_height * Real.log first_prime
        = Real.log first_prime * (height - other_height) := by ring
  have second_angle_gap :
      height * Real.log second_prime - other_height * Real.log second_prime
        = Real.log second_prime * (height - other_height) := by ring
  rw [first_angle_gap, abs_mul] at first_cos_gap
  rw [second_angle_gap, abs_mul] at second_cos_gap
  simp only [Real.dist_eq, NNReal.coe_add, NNReal.coe_mul, coe_nnnorm,
    Real.norm_eq_abs]
  unfold MAKE_TWO_PRIME_WAVE
  calc |first_amplitude * cos (height * Real.log first_prime)
          + second_amplitude * cos (height * Real.log second_prime)
        - (first_amplitude * cos (other_height * Real.log first_prime)
          + second_amplitude * cos (other_height * Real.log second_prime))|
      = |first_amplitude * (cos (height * Real.log first_prime)
            - cos (other_height * Real.log first_prime))
          + second_amplitude * (cos (height * Real.log second_prime)
            - cos (other_height * Real.log second_prime))| := by
        congr 1
        ring
    _ ≤ |first_amplitude * (cos (height * Real.log first_prime)
            - cos (other_height * Real.log first_prime))|
          + |second_amplitude * (cos (height * Real.log second_prime)
            - cos (other_height * Real.log second_prime))| :=
        abs_add_le _ _
    _ = |first_amplitude| * |cos (height * Real.log first_prime)
            - cos (other_height * Real.log first_prime)|
          + |second_amplitude| * |cos (height * Real.log second_prime)
            - cos (other_height * Real.log second_prime)| := by
        rw [abs_mul, abs_mul]
    _ ≤ |first_amplitude|
            * (|Real.log first_prime| * |height - other_height|)
          + |second_amplitude|
            * (|Real.log second_prime| * |height - other_height|) :=
        add_le_add
          (mul_le_mul_of_nonneg_left first_cos_gap
            (abs_nonneg first_amplitude))
          (mul_le_mul_of_nonneg_left second_cos_gap
            (abs_nonneg second_amplitude))
    _ = (|first_amplitude| * |Real.log first_prime|
          + |second_amplitude| * |Real.log second_prime|)
          * |height - other_height| := by ring

/-- **The squiggly line sandwich for the sum of two prime waves.** For data
whose labels lie in a band strictly inside the band of the wave, the wave
passes within `reach` of every data point, and the vertical error is at most
`√(1 + slope_limit²)` times that nearest distance. Near, and steep by the
same token: the two bounds of `Oscillation.lean` and `Sandwich.lean`, for
the primes. -/
theorem two_prime_wave_is_near_the_data_and_pays_the_slope_tax
    {first_prime second_prime : ℕ}
    (first_is_prime : first_prime.Prime)
    (second_is_prime : second_prime.Prime)
    (primes_differ : first_prime ≠ second_prime)
    {first_amplitude : ℝ}
    {second_amplitude : ℝ}
    (second_amplitude_nonneg : 0 ≤ second_amplitude)
    {inner_edge : ℝ}
    (inner_edge_inside : inner_edge < first_amplitude + second_amplitude) :
    let wave :=
      MAKE_TWO_PRIME_WAVE first_prime second_prime
        first_amplitude second_amplitude
    let narrower_band := Set.Icc (-inner_edge) inner_edge
    let first_slope  := ‖first_amplitude‖₊ * ‖Real.log first_prime‖₊
    let second_slope := ‖second_amplitude‖₊ * ‖Real.log second_prime‖₊
    let slope_limit : SlopeLimit := first_slope + second_slope
    let stretch := √(1 + (slope_limit : ℝ) ^ 2)   -- Pythagoras: 1 across, slope_limit up
    ∃ reach : ℝ, ∀ data_point : DataPoint ℝ,
      GET_LABEL data_point ∈ narrower_band →
        let nearest_distance := GET_NEAREST_DISTANCE wave data_point
        let vertical_error   := GET_VERTICAL_ERROR wave data_point
        nearest_distance ≤ reach
          ∧ vertical_error ≤ stretch * nearest_distance := by
  unfold_named_pieces
  obtain ⟨reach, wave_covers⟩ :=
    two_prime_wave_covers_a_narrower_band first_is_prime second_is_prime
      primes_differ second_amplitude_nonneg inner_edge_inside
  have slope_is_bounded :=
    two_prime_wave_slope_is_at_most_amplitudes_times_frequencies
      first_prime second_prime first_amplitude second_amplitude
  exact ⟨reach, fun data_point label_in_band =>
    ⟨nearestDist_le_of_coversWithin wave_covers data_point label_in_band,
      verticalDist_le_of_lipschitz slope_is_bounded data_point⟩⟩

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
