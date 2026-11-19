/-
Light that travels: what a gap can and cannot do.

`TrainedPlate.lean` says what one point of a plate does. Between the plates
and the screen the light travels across a gap. This file assumes two things
about a gap and nothing else: it is linear (the light of two sources is the
sum of their lights), and it is the same at every place (move the light one
point sideways, and what arrives moves one point sideways). The gap of the
simulation in `experiments/optics/optics.py` has both properties.

* `wave_keeps_its_direction`: a wave that enters such a gap leaves as the
  same wave, multiplied by one number. A gap never turns one wave into
  another.
* `beams_stay_beams`: so light made of several waves leaves as the same
  waves, each multiplied by its own number. The beams that a plate makes
  stay beams.
* `brighter_lamp_scales_every_window`,
  `brighter_lamp_keeps_the_brightest_window`: whatever the plates and gaps
  are, a lamp `lamp_factor` times stronger puts `lamp_factor ^ 2` times the
  light in every window. So the brightest window stays the brightest.
* `one_plate_only_dims_a_glowing_point`,
  `one_plate_cannot_steer_a_glowing_point`: under an ordinary lamp each
  point of the picture glows on its own. One plate changes the light of a
  glowing point by one factor, the same in every window. So one plate
  cannot send that light to one window and away from another.

| Name                     | Meaning                                          |
|--------------------------|--------------------------------------------------|
| `LightOnLine`            | light along a line of points: a complex number at each |
| `SHIFT_BY_ONE_POINT`     | the same light, moved one point sideways         |
| `IS_SAME_AT_EVERY_PLACE` | a gap that does not care where the light is      |
| `MAKE_WAVE`              | a wave: each point is `step` times the one before |
| `GET_LIGHT_IN_WINDOW`    | the brightness added up over a window            |

How to read the notation:

* `A →ₗ[ℂ] B` is a linear map from `A` to `B`. Python: a matrix.
* `Complex.normSq z` is the brightness of light of size `z`: the square of
  its length.
* `Pi.single source 1` is light of size 1 at the point `source` and none
  anywhere else. Python: a one-hot list.
* A wave with `step = exp(i * k)` leaves a plate at the angle whose sine is
  `k * wavelength / (2 * PI * pixel)`. A different `step` is a different
  direction.
-/
import SquigglyLine.Networks.TrainedPlate
import Mathlib.Algebra.BigOperators.Pi

namespace SquigglyLine

open Finset

/-! ## A gap keeps each wave -/

/-- Light along a line of points: one complex number at every point.
Python: `dict[int, complex]`. -/
abbrev LightOnLine := ℤ → ℂ

/-- The same light, moved one point sideways.
Python: `lambda point: light[point + 1]`. -/
def SHIFT_BY_ONE_POINT
    (light : LightOnLine) : LightOnLine :=
  fun point => light (point + 1)

/-- A gap is the same at every place: moving the light sideways before the
gap is the same as moving it after.

    def IS_SAME_AT_EVERY_PLACE(gap):
        return all(gap(SHIFT_BY_ONE_POINT(light))
                   == SHIFT_BY_ONE_POINT(gap(light)) for light in all_lights)
-/
def IS_SAME_AT_EVERY_PLACE
    (gap : LightOnLine →ₗ[ℂ] LightOnLine) : Prop :=
  ∀ light : LightOnLine,
    gap (SHIFT_BY_ONE_POINT light) = SHIFT_BY_ONE_POINT (gap light)

/-- A wave across the line: the light at each point is `step` times the
light at the point before. Python: `lambda point: step ** point`. -/
noncomputable def MAKE_WAVE
    (step : ℂ) : LightOnLine :=
  fun point => step ^ point

/-- **A gap keeps each wave.** A wave that crosses a gap arrives as the same
wave, multiplied by one number. -/
theorem wave_keeps_its_direction
    (gap : LightOnLine →ₗ[ℂ] LightOnLine)
    (gap_is_same_at_every_place : IS_SAME_AT_EVERY_PLACE gap)
    (step : ℂ)
    (step_ne_zero : step ≠ 0) :
    let wave           := MAKE_WAVE step
    let wave_after_gap := gap wave
    let gap_factor     := wave_after_gap 0                   -- what arrives at point 0 sets the factor for every point
    wave_after_gap = gap_factor • wave := by
  unfold_named_pieces
  -- Moving a wave one point sideways multiplies it by `step`.
  have shifted_wave_is_scaled_wave :
      SHIFT_BY_ONE_POINT (MAKE_WAVE step) = step • MAKE_WAVE step := by
    funext point
    simp only [SHIFT_BY_ONE_POINT, MAKE_WAVE, Pi.smul_apply, smul_eq_mul]
    rw [zpow_add_one₀ step_ne_zero, mul_comm]
  -- So what arrives has the same property: each point is `step` times the
  -- one before.
  have next_point_is_step_times :
      ∀ point : ℤ,
        gap (MAKE_WAVE step) (point + 1)
          = step * gap (MAKE_WAVE step) point := by
    intro point
    have moved_before_or_after :=
      congrFun (gap_is_same_at_every_place (MAKE_WAVE step)) point
    rw [shifted_wave_is_scaled_wave, map_smul] at moved_before_or_after
    simp only [SHIFT_BY_ONE_POINT, Pi.smul_apply, smul_eq_mul]
      at moved_before_or_after
    exact moved_before_or_after.symm
  -- Walk from point 0 to any point, to the right and to the left.
  have every_point_from_point_zero :
      ∀ point : ℤ,
        gap (MAKE_WAVE step) point
          = step ^ point * gap (MAKE_WAVE step) 0 := by
    intro point
    refine Int.induction_on point ?_ ?_ ?_
    · simp
    · intro steps_right holds_before
      rw [next_point_is_step_times, holds_before,
        zpow_add_one₀ step_ne_zero]
      ring
    · intro steps_left holds_before
      have one_step_back := next_point_is_step_times (-(steps_left : ℤ) - 1)
      rw [sub_add_cancel, holds_before] at one_step_back
      have undo_one_step :
          gap (MAKE_WAVE step) (-(steps_left : ℤ) - 1)
            = step⁻¹ * (step * gap (MAKE_WAVE step) (-(steps_left : ℤ) - 1)) := by
        rw [← mul_assoc, inv_mul_cancel₀ step_ne_zero, one_mul]
      rw [undo_one_step, ← one_step_back, zpow_sub_one₀ step_ne_zero]
      ring
  funext point
  rw [every_point_from_point_zero point]
  simp only [Pi.smul_apply, smul_eq_mul, MAKE_WAVE]
  ring

/-- **Beams stay beams.** Light made of several waves crosses a gap and
arrives as the same waves, each multiplied by its own number. No new wave
appears, so no new direction appears. -/
theorem beams_stay_beams
    {Beams : Type*}
    (gap : LightOnLine →ₗ[ℂ] LightOnLine)
    (gap_is_same_at_every_place : IS_SAME_AT_EVERY_PLACE gap)
    (beams : Finset Beams)
    (step : Beams → ℂ)
    (steps_ne_zero : ∀ beam, step beam ≠ 0)
    (strength : Beams → ℂ) :
    let light_before :=
      ∑ beam ∈ beams, strength beam • MAKE_WAVE (step beam)
    let light_after := gap light_before
    let gap_factor  := fun beam => gap (MAKE_WAVE (step beam)) 0   -- one number per beam, from `wave_keeps_its_direction`
    let same_beams_rescaled :=
      ∑ beam ∈ beams,
        (strength beam * gap_factor beam) • MAKE_WAVE (step beam)
    light_after = same_beams_rescaled := by
  unfold_named_pieces
  rw [map_sum]
  refine Finset.sum_congr rfl fun beam _ => ?_
  have beam_is_kept :
      gap (MAKE_WAVE (step beam))
        = gap (MAKE_WAVE (step beam)) 0 • MAKE_WAVE (step beam) :=
    wave_keeps_its_direction gap gap_is_same_at_every_place
      (step beam) (steps_ne_zero beam)
  rw [map_smul]
  conv_lhs => rw [beam_is_kept]
  rw [smul_smul]

/-! ## The screen -/

/-- The brightness on the screen, added up over one window.
Python: `sum(abs(light_on_screen[point]) ** 2 for point in window)`. -/
noncomputable def GET_LIGHT_IN_WINDOW
    {Screen : Type*}
    (window : Finset Screen)
    (light_on_screen : Screen → ℂ) : ℝ :=
  ∑ point ∈ window, Complex.normSq (light_on_screen point)

/-- **A brighter lamp scales every window alike.** Let `travel` be anything
linear from the picture to the screen: plates, gaps, any number of them.
A lamp `lamp_factor` times stronger puts `lamp_factor ^ 2` times the light in
the window. -/
theorem brighter_lamp_scales_every_window
    {Pixels Screen : Type*}
    (travel : (Pixels → ℂ) →ₗ[ℂ] (Screen → ℂ))
    (window : Finset Screen)
    (picture : Pixels → ℂ)
    (lamp_factor : ℝ) :
    let brighter_picture := (lamp_factor : ℂ) • picture
    let light_before := GET_LIGHT_IN_WINDOW window (travel picture)
    let light_after  :=
      GET_LIGHT_IN_WINDOW window (travel brighter_picture)
    light_after = lamp_factor ^ 2 * light_before := by       -- brightness is the square of the size
  unfold_named_pieces
  simp only [GET_LIGHT_IN_WINDOW, map_smul, Pi.smul_apply, smul_eq_mul,
    Complex.normSq_mul, Complex.normSq_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun point _ => ?_
  ring

/-- **The answer does not depend on the lamp.** If one window holds at least
as much light as another, it still does under a stronger or a weaker lamp. -/
theorem brighter_lamp_keeps_the_brightest_window
    {Pixels Screen : Type*}
    (travel : (Pixels → ℂ) →ₗ[ℂ] (Screen → ℂ))
    (window : Finset Screen)
    (other_window : Finset Screen)
    (picture : Pixels → ℂ)
    (lamp_factor : ℝ)
    (window_is_brighter :
      GET_LIGHT_IN_WINDOW other_window (travel picture)
        ≤ GET_LIGHT_IN_WINDOW window (travel picture)) :
    let brighter_picture := (lamp_factor : ℂ) • picture
    let light_in_window :=
      GET_LIGHT_IN_WINDOW window (travel brighter_picture)
    let light_in_other_window :=
      GET_LIGHT_IN_WINDOW other_window (travel brighter_picture)
    light_in_other_window ≤ light_in_window := by
  unfold_named_pieces
  have scaled_window :=
    brighter_lamp_scales_every_window travel window picture lamp_factor
  have scaled_other_window :=
    brighter_lamp_scales_every_window travel other_window picture lamp_factor
  simp only at scaled_window scaled_other_window
  rw [scaled_window, scaled_other_window]
  exact mul_le_mul_of_nonneg_left window_is_brighter (sq_nonneg lamp_factor)

/-! ## An ordinary lamp and one plate -/

/-- **One plate only dims a glowing point.** A point of the picture glows on
its own. A plate multiplies the light at each point by its mask value there.
Then the light travels, by any linear rule. In every window the plate changes
that light by the same factor, the brightness of the mask at the glowing
point. -/
theorem one_plate_only_dims_a_glowing_point
    {Pixels Screen : Type*} [DecidableEq Pixels]
    (travel : (Pixels → ℂ) →ₗ[ℂ] (Screen → ℂ))
    (window : Finset Screen)
    (mask : Pixels → ℂ)
    (source : Pixels) :
    let glowing_point : Pixels → ℂ := Pi.single source 1     -- light of size 1 at `source`, none elsewhere
    let after_plate : Pixels → ℂ :=
      fun pixel => mask pixel * glowing_point pixel
    let light_with_plate :=
      GET_LIGHT_IN_WINDOW window (travel after_plate)
    let light_without_plate :=
      GET_LIGHT_IN_WINDOW window (travel glowing_point)
    let dimming := Complex.normSq (mask source)              -- one number, the same for every window
    light_with_plate = dimming * light_without_plate := by
  unfold_named_pieces
  -- The plate meets the light at one point only, so it can only scale it.
  have plate_only_scales :
      (fun pixel => mask pixel * (Pi.single source 1 : Pixels → ℂ) pixel)
        = mask source • (Pi.single source 1 : Pixels → ℂ) := by
    funext pixel
    by_cases is_source : pixel = source
    · subst is_source
      simp
    · simp [is_source]
  rw [plate_only_scales]
  simp only [GET_LIGHT_IN_WINDOW, map_smul, Pi.smul_apply, smul_eq_mul,
    Complex.normSq_mul, Finset.mul_sum]

/-- **One plate cannot steer lamp light.** How the light of a glowing point
is split between two windows is the same with the plate as without it. -/
theorem one_plate_cannot_steer_a_glowing_point
    {Pixels Screen : Type*} [DecidableEq Pixels]
    (travel : (Pixels → ℂ) →ₗ[ℂ] (Screen → ℂ))
    (window : Finset Screen)
    (other_window : Finset Screen)
    (mask : Pixels → ℂ)
    (source : Pixels) :
    let glowing_point : Pixels → ℂ := Pi.single source 1     -- light of size 1 at `source`, none elsewhere
    let after_plate : Pixels → ℂ :=
      fun pixel => mask pixel * glowing_point pixel
    let with_plate    := GET_LIGHT_IN_WINDOW window (travel after_plate)
    let without_plate := GET_LIGHT_IN_WINDOW window (travel glowing_point)
    let other_with_plate :=
      GET_LIGHT_IN_WINDOW other_window (travel after_plate)
    let other_without_plate :=
      GET_LIGHT_IN_WINDOW other_window (travel glowing_point)
    with_plate * other_without_plate
      = other_with_plate * without_plate := by                -- the same split, written without dividing
  unfold_named_pieces
  have dimmed := one_plate_only_dims_a_glowing_point travel window mask source
  have other_dimmed :=
    one_plate_only_dims_a_glowing_point travel other_window mask source
  simp only at dimmed other_dimmed
  rw [dimmed, other_dimmed]
  ring

end SquigglyLine
