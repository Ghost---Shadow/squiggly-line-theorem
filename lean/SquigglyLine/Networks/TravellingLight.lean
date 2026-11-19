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
* `turning_plate_makes_three_waves`,
  `turning_plate_makes_one_wave_of_circular_light`: a plate is what makes
  the waves. A plate whose axis turns steadily makes three waves from
  horizontal light (straight on and one to each side) and a single wave
  from circular light.
* `three_waves_arrive_as_three_waves`: and after any gap that is the same
  at every place, the light of the turning plate is still those three waves.
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
| `GET_GRATING_STEP`       | the step of the wave a turning plate makes       |
| `GET_LIGHT_IN_WINDOW`    | the brightness added up over a window            |

What is planned and not done is listed at the end of the file, under
"To do".

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

open Finset Real

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
    -- At each point: `step ^ (point + 1)` is `step * step ^ point`.
    simp only [SHIFT_BY_ONE_POINT, MAKE_WAVE, Pi.smul_apply, smul_eq_mul]
    rw [zpow_add_one₀ step_ne_zero, mul_comm]
  -- So what arrives has the same property: each point is `step` times the
  -- one before.
  have next_point_is_step_times :
      ∀ point : ℤ,
        gap (MAKE_WAVE step) (point + 1)
          = step * gap (MAKE_WAVE step) point := by
    intro point
    -- Moving the wave before the gap or after it gives the same light.
    have moved_before_or_after :=
      congrFun (gap_is_same_at_every_place (MAKE_WAVE step)) point
    -- Moved before the gap, the wave is `step` times the wave, and a gap is
    -- linear, so `step` comes out of the gap.
    rw [shifted_wave_is_scaled_wave, map_smul] at moved_before_or_after
    -- Read both sides at `point`.
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
    · -- At point 0 the claim is `x = 1 * x`.
      simp
    · -- One more point to the right: multiply by `step` once more.
      intro steps_right holds_before
      rw [next_point_is_step_times, holds_before,
        zpow_add_one₀ step_ne_zero]
      ring
    · -- One more point to the left: the point after it is the one we know,
      -- and the point after is `step` times it, so divide by `step`.
      intro steps_left holds_before
      have one_step_back := next_point_is_step_times (-(steps_left : ℤ) - 1)
      rw [sub_add_cancel, holds_before] at one_step_back
      have undo_one_step :
          gap (MAKE_WAVE step) (-(steps_left : ℤ) - 1)
            = step⁻¹ * (step
                * gap (MAKE_WAVE step) (-(steps_left : ℤ) - 1)) := by
        rw [← mul_assoc, inv_mul_cancel₀ step_ne_zero, one_mul]
      rw [undo_one_step, ← one_step_back, zpow_sub_one₀ step_ne_zero]
      ring
  -- Compare the two lights at every point: both are `step ^ point` times
  -- what arrives at point 0.
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
  -- A gap is linear, so it can be applied to each beam separately.
  rw [map_sum]
  -- Then it is enough to compare one beam at a time.
  refine Finset.sum_congr rfl fun beam _ => ?_
  -- Each wave crosses the gap as itself times one number.
  have beam_is_kept :
      gap (MAKE_WAVE (step beam))
        = gap (MAKE_WAVE (step beam)) 0 • MAKE_WAVE (step beam) :=
    wave_keeps_its_direction gap gap_is_same_at_every_place
      (step beam) (steps_ne_zero beam)
  -- The strength of the beam also comes out of the gap.
  rw [map_smul]
  -- Replace the wave that crossed the gap by the kept wave.
  conv_lhs => rw [beam_is_kept]
  -- Two numbers in a row multiply into one.
  rw [smul_smul]

/-! ## A plate makes the waves -/

/-- The step of the wave made by a plate whose axis turns half a turn every
`period` points: a full turn of the wave every `period` points.
Python: `cmath.exp(2j * pi / period)`. -/
noncomputable def GET_GRATING_STEP
    (period : ℝ) : ℂ :=
  Complex.exp ((2 * PI / period : ℝ) * Complex.I)

/-- **A turning plate makes three waves.** Let the axis of a plate turn
steadily, half a turn every `period` points. `plate_on_horizontal_light`
gives the across part of the light behind it, `1/2 + cos(2θ)/2` at each
point. That is one half of the wave that goes straight on, a quarter of a
wave to one side and a quarter of its mirror image to the other side. -/
theorem turning_plate_makes_three_waves
    (period : ℝ) :
    let axis_angle := fun point : ℤ => PI * point / period   -- half a turn every `period` points
    let across_part : LightOnLine :=
      fun point => ((1 / 2 + Real.cos (2 * axis_angle point) / 2 : ℝ) : ℂ)
    let step        := GET_GRATING_STEP period
    let straight_on := MAKE_WAVE 1                           -- the same at every point
    let to_one_side := MAKE_WAVE step
    let to_the_other_side := MAKE_WAVE step⁻¹
    let three_waves : LightOnLine :=
      (1 / 2 : ℂ) • straight_on
        + (1 / 4 : ℂ) • to_one_side
        + (1 / 4 : ℂ) • to_the_other_side
    across_part = three_waves := by
  unfold_named_pieces
  funext point
  -- A cosine is half of a wave plus half of its mirror image.
  have cos_as_two_waves :
      ∀ angle : ℝ,
        ((1 / 2 + Real.cos angle / 2 : ℝ) : ℂ)
          = 1 / 2 + 1 / 4 * Complex.exp ((angle : ℂ) * Complex.I)
            + 1 / 4 * Complex.exp (-(angle : ℂ) * Complex.I) := by
    intro angle
    push_cast
    rw [Complex.cos]
    ring
  -- The wave at a point is `exp` of that point's angle.
  have wave_at_point :
      GET_GRATING_STEP period ^ point
        = Complex.exp
            (((2 * (PI * point / period) : ℝ) : ℂ) * Complex.I) := by
    rw [GET_GRATING_STEP, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  -- Its mirror image has the opposite angle.
  have mirror_wave_at_point :
      (GET_GRATING_STEP period)⁻¹ ^ point
        = Complex.exp
            (-((2 * (PI * point / period) : ℝ) : ℂ) * Complex.I) := by
    rw [inv_zpow, wave_at_point, ← Complex.exp_neg, ← neg_mul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, MAKE_WAVE, one_zpow,
    wave_at_point, mirror_wave_at_point, cos_as_two_waves]
  ring

/-- **With circular light a turning plate makes one wave.**
`plate_on_circular_light` gives the phase shift `exp(2θ i)` of the half of
the light that changes handedness. Across a plate whose axis turns steadily
that is a single wave, to one side only. -/
theorem turning_plate_makes_one_wave_of_circular_light
    (period : ℝ) :
    let axis_angle := fun point : ℤ => PI * point / period   -- half a turn every `period` points
    let phase_shift : LightOnLine :=
      fun point =>
        Complex.exp (2 * ((axis_angle point : ℝ) : ℂ) * Complex.I)
    let to_one_side := MAKE_WAVE (GET_GRATING_STEP period)
    phase_shift = to_one_side := by
  unfold_named_pieces
  funext point
  -- The wave at a point is `exp` of that point's angle.
  simp only [MAKE_WAVE]
  rw [GET_GRATING_STEP, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- **The three waves arrive as three waves.** The light behind a turning
plate crosses any gap that is the same at every place, and what arrives is
the same three waves, each multiplied by its own number. The plate made the
three directions and the gap adds none. -/
theorem three_waves_arrive_as_three_waves
    (gap : LightOnLine →ₗ[ℂ] LightOnLine)
    (gap_is_same_at_every_place : IS_SAME_AT_EVERY_PLACE gap)
    (period : ℝ) :
    let step := GET_GRATING_STEP period
    let light_behind_plate : LightOnLine :=                  -- from `turning_plate_makes_three_waves`
      (1 / 2 : ℂ) • MAKE_WAVE 1
        + (1 / 4 : ℂ) • MAKE_WAVE step
        + (1 / 4 : ℂ) • MAKE_WAVE step⁻¹
    let light_on_screen   := gap light_behind_plate
    let straight_factor   := gap (MAKE_WAVE 1) 0             -- one number per wave, from `wave_keeps_its_direction`
    let side_factor       := gap (MAKE_WAVE step) 0
    let other_side_factor := gap (MAKE_WAVE step⁻¹) 0
    let same_three_waves : LightOnLine :=
      (1 / 2 * straight_factor) • MAKE_WAVE 1
        + (1 / 4 * side_factor) • MAKE_WAVE step
        + (1 / 4 * other_side_factor) • MAKE_WAVE step⁻¹
    light_on_screen = same_three_waves := by
  unfold_named_pieces
  -- The step of a wave is never zero.
  have step_ne_zero : GET_GRATING_STEP period ≠ 0 := by
    rw [GET_GRATING_STEP]
    exact Complex.exp_ne_zero _
  -- Each of the three waves crosses the gap and stays itself.
  have straight_is_kept :=
    wave_keeps_its_direction gap gap_is_same_at_every_place 1 one_ne_zero
  have side_is_kept :=
    wave_keeps_its_direction gap gap_is_same_at_every_place
      (GET_GRATING_STEP period) step_ne_zero
  have other_side_is_kept :=
    wave_keeps_its_direction gap gap_is_same_at_every_place
      (GET_GRATING_STEP period)⁻¹ (inv_ne_zero step_ne_zero)
  simp only at straight_is_kept side_is_kept other_side_is_kept
  -- The gap is linear, so it acts on the three waves one at a time.
  rw [map_add, map_add, map_smul, map_smul, map_smul]
  conv_lhs => rw [straight_is_kept, side_is_kept, other_side_is_kept]
  simp only [smul_smul]

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
  -- Travel is linear, so the factor comes out of the light at each point.
  -- The brightness of a product is the product of the brightnesses, and a
  -- real factor `r` has brightness `r * r`. Move the factor into the sum.
  simp only [GET_LIGHT_IN_WINDOW, map_smul, Pi.smul_apply, smul_eq_mul,
    Complex.normSq_mul, Complex.normSq_ofReal, Finset.mul_sum]
  -- Each point of the window: `r * r * x = r ^ 2 * x`.
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
  -- Each window holds `lamp_factor ^ 2` times what it held before.
  have scaled_window :=
    brighter_lamp_scales_every_window travel window picture lamp_factor
  have scaled_other_window :=
    brighter_lamp_scales_every_window travel other_window picture lamp_factor
  simp only at scaled_window scaled_other_window
  rw [scaled_window, scaled_other_window]
  -- Multiplying both sides of the old inequality by a square keeps it.
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
    · -- At the glowing point both sides are `mask source`.
      subst is_source
      simp
    · -- Elsewhere there is no light, and both sides are 0.
      simp [is_source]
  rw [plate_only_scales]
  -- Now the same steps as for a brighter lamp, with the complex factor
  -- `mask source`, whose brightness is `dimming`.
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
  -- In each window the plate multiplies the light by the same `dimming`.
  have dimmed := one_plate_only_dims_a_glowing_point travel window mask source
  have other_dimmed :=
    one_plate_only_dims_a_glowing_point travel other_window mask source
  simp only at dimmed other_dimmed
  rw [dimmed, other_dimmed]
  -- Both sides are `dimming * without * other_without`.
  ring

/-! ## To do

Written on 19 Nov 2026. These were planned and not done, because the usage
limit of the week was nearly reached and each needs more than one attempt.
None of them is proved anywhere in this project yet. In rough order of
value for `docs/networks/polarizer-classifier.md`:

1. **The second pass.** `turning_plate_makes_three_waves`,
   `turning_plate_makes_one_wave_of_circular_light` and
   `three_waves_arrive_as_three_waves` were written straight into this file
   and have not had the port and second pass of `lean/PORTING.md`.
2. **The up part.** `plate_on_horizontal_light` also gives an up part,
   `sin(2θ)/2`. Show that across a turning plate it is two waves, to the two
   sides, with no wave straight on. With the across part that gives the
   whole light behind the plate.
3. **The shares of light.** For a gap that loses no light (each
   `gap_factor` has length 1), show the brightness of the waves is 1/4
   straight on and 1/8 to each side of what came in, and 1/2 is absorbed.
   The note has these as derived and checked. It needs a definition of the
   brightness of a wave, per point of the line.
4. **Circular light, whole statement.** Join `plate_on_circular_light`, a
   circular analyzer and `turning_plate_makes_one_wave_of_circular_light`:
   behind the analyzer there is one wave, with 1/4 of the brightness.
5. **A lamp gives a linear classifier.** Define lamp light (each point
   glows on its own, brightness adds) and show the light in a window is a
   sum over the points of `weight × strength ^ 2` with every weight at least
   zero. `one_plate_only_dims_a_glowing_point` is the one-plate case of the
   weights.
6. **Scores are sums of squares.** For light from one source, the light in
   a window is a sum of squares of linear readings of the picture, at most
   four per screen point. `GET_LIGHT_IN_WINDOW` is already that sum; the
   count of readings is not stated.
7. **No gap, no mixing.** With no gap, plates act on each point alone, so
   the light at a screen point depends on one point of the picture.
8. **Light is never gained.** For plates (each a projection) and a gap that
   gains no light, the light on the screen is at most the light of the
   picture.
9. **The gap of the simulation.** Everything above holds for any gap. The
   simulation uses one: the wave with `step = exp(i k)` is multiplied by
   `exp(2 PI i d √(1 − f²))`, with `f` its spatial frequency. Define it,
   show it is linear, the same at every place and loses no light, and then
   the grating rule `sin φ = λ/Λ` and the length of gap that a sideways
   move needs. This is the large one.
10. **The pixel limit.** An angle that changes by less than a quarter turn
    per pixel bends light by at most `sin φ = λ / (2 × pixel)`.
11. **Two directions.** This file has light along a line. The plates are
    surfaces, so the points should be pairs. The proofs should go through
    with a shift in each direction.
12. **A line that closes on itself.** The simulation works on a grid that
    wraps around. `wave_keeps_its_direction` on `ZMod point_count` is the
    statement that matches the code exactly.
-/

end SquigglyLine
