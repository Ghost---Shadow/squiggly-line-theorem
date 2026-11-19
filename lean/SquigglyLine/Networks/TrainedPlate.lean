/-
A plate whose angle is chosen at each point: what one point of it does.

`docs/networks/polarizer-classifier.md` lets the middle plate of the
three-polarizer experiment have a different angle at every point and trains
those angles. This file proves what the plate does at one point, for the two
kinds of light the note uses.

* `plate_on_horizontal_light`: horizontal light through a plate at angle
  `axis_angle` comes out as `(1/2 + cos(2 * axis_angle) / 2,
  sin(2 * axis_angle) / 2)` times its strength. Where the axis turns steadily
  across the plate, these are waves across the plate, and the plate is a
  grating.
* `plate_between_crossed_polarizers`: with a vertical plate after it, what
  is left is `sin(2 * axis_angle) / 2` of the strength, pointing up. The
  three plates are a mask with a value between `-1/2` and `1/2`.
* `plate_on_circular_light`: circular light through the plate comes out as
  half of itself plus half of the opposite circular light, and the second
  half is multiplied by `exp(2 * axis_angle * i)`. For that half the plate is
  a phase plate, and the angle is the phase.

| Name                             | Meaning                                    |
|----------------------------------|--------------------------------------------|
| `ComplexLight`                   | light with a phase: a pair of complex numbers |
| `PASS_COMPLEX_LIGHT_THROUGH_POLARIZER` | the shadow of such light on one direction |
| `LEFT_CIRCULAR_LIGHT`            | `(1, i)`: up lags across by a quarter wave |
| `RIGHT_CIRCULAR_LIGHT`           | `(1, -i)`: the opposite handedness         |

How to read the notation:

* `Complex.I` is the number `i`. Multiplying light by `exp(phase * i)` shifts
  its wave by `phase` and does not change its brightness.
* `(x : ℂ)` is the real number `x` seen as a complex number.
* The circular lights are not scaled to length 1. Divide by `√2` for that; it
  changes nothing in the statement.
-/
import SquigglyLine.Networks.ThreePolarizers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace SquigglyLine

open Real

/-! ## Linear light -/

/-- **A plate on horizontal light.** The light that leaves has an across part
`1/2 + cos(2θ)/2` and an up part `sin(2θ)/2` of the strength. -/
theorem plate_on_horizontal_light
    (amplitude : ℝ)
    (axis_angle : ℝ) :
    let incoming_light := MAKE_LIGHT amplitude 0             -- pointing across
    let outgoing_light := PASS_THROUGH_POLARIZER axis_angle incoming_light
    let across_part    := 1 / 2 + cos (2 * axis_angle) / 2   -- a steady part and a wave: cos(θ) ^ 2
    let up_part        := sin (2 * axis_angle) / 2           -- a wave only: cos(θ) * sin(θ)
    let expected_light : LightArrow :=
      (amplitude * across_part, amplitude * up_part)
    outgoing_light = expected_light := by
  unfold_named_pieces
  -- Write the shadow out in coordinates. With the angle of the light 0,
  -- the double-angle formulas turn `cos θ ^ 2` and `cos θ * sin θ` into the
  -- two parts named above, and `ring` checks the rest.
  ext <;>
    simp only [PASS_THROUGH_POLARIZER, MAKE_LIGHT, cos_zero, sin_zero,
      cos_two_mul, sin_two_mul] <;>
    ring

/-- **The trained three-polarizer experiment, at one point.** Horizontal
light, a plate at `axis_angle`, then a vertical plate: what leaves points up
and has `sin(2θ)/2` of the strength. At 45° that is one half, as in
`three_polarizers`. -/
theorem plate_between_crossed_polarizers
    (amplitude : ℝ)
    (axis_angle : ℝ) :
    let incoming_light := MAKE_LIGHT amplitude 0             -- pointing across
    let after_plate    := PASS_THROUGH_POLARIZER axis_angle incoming_light
    let vertical_axis  := PI / 2                             -- 90°: at right angles to the light that came in
    let outgoing_light := PASS_THROUGH_POLARIZER vertical_axis after_plate
    let mask_value     := sin (2 * axis_angle) / 2           -- between -1/2 and 1/2, set by the angle of the plate
    let expected_light : LightArrow := (0, amplitude * mask_value)
    outgoing_light = expected_light := by
  unfold_named_pieces
  -- First plate: use what it does to horizontal light.
  rw [plate_on_horizontal_light]
  -- The vertical plate keeps the up part of the light and nothing else:
  -- `cos (PI / 2) = 0` and `sin (PI / 2) = 1`.
  ext <;>
    simp only [PASS_THROUGH_POLARIZER, cos_pi_div_two, sin_pi_div_two] <;>
    ring

/-! ## Circular light -/

/-- Light with a phase: an across part and an up part, each a complex number.
Python: `tuple[complex, complex]`. -/
abbrev ComplexLight := ℂ × ℂ

/-- A polarizer acting on light with a phase: the shadow on the axis, as for
`PASS_THROUGH_POLARIZER`.

    def PASS_COMPLEX_LIGHT_THROUGH_POLARIZER(axis_angle, light):
        shadow_length = (
            light[0] * cos(axis_angle) + light[1] * sin(axis_angle))
        return (shadow_length * cos(axis_angle),
                shadow_length * sin(axis_angle))
-/
noncomputable def PASS_COMPLEX_LIGHT_THROUGH_POLARIZER
    (axis_angle : ℝ)
    (light : ComplexLight) : ComplexLight :=
  let shadow_length : ℂ :=
    light.1 * (cos axis_angle : ℝ) + light.2 * (sin axis_angle : ℝ)   -- the dot product of the light with the axis direction
  (shadow_length * (cos axis_angle : ℝ),
   shadow_length * (sin axis_angle : ℝ))

/-- Circular light: the up part is the across part a quarter wave late.
Python: `(1, 1j)`. -/
noncomputable abbrev LEFT_CIRCULAR_LIGHT : ComplexLight := (1, Complex.I)

/-- Circular light of the opposite handedness. Python: `(1, -1j)`. -/
noncomputable abbrev RIGHT_CIRCULAR_LIGHT : ComplexLight := (1, -Complex.I)

/-- **A plate on circular light.** Half of the light keeps its handedness.
The other half has the opposite handedness and its wave is shifted by twice
the angle of the plate. So for that half the plate is a phase plate, and the
angle of the plate is the weight. -/
theorem plate_on_circular_light
    (axis_angle : ℝ) :
    let outgoing_light :=
      PASS_COMPLEX_LIGHT_THROUGH_POLARIZER axis_angle LEFT_CIRCULAR_LIGHT
    let phase_shift : ℂ :=
      Complex.exp (2 * axis_angle * Complex.I)               -- a shift of the wave by twice the angle of the plate
    let unchanged_half : ComplexLight :=
      (1 / 2 : ℂ) • LEFT_CIRCULAR_LIGHT
    let shifted_half : ComplexLight :=
      (1 / 2 * phase_shift) • RIGHT_CIRCULAR_LIGHT
    outgoing_light = unchanged_half + shifted_half := by
  unfold_named_pieces
  -- The phase shift written with real parts: `exp(2θi) = cos(2θ) + sin(2θ) i`,
  -- then the double-angle formulas in terms of `cos θ` and `sin θ`.
  have exp_as_cos_sin :
      Complex.exp (2 * axis_angle * Complex.I)
        = (2 * (cos axis_angle : ℝ) ^ 2 - 1)
          + 2 * (sin axis_angle : ℝ) * (cos axis_angle : ℝ)
            * Complex.I := by
    -- Put the angle in the form `(real number) * i`.
    rw [show (2 * axis_angle * Complex.I : ℂ)
          = ((2 * axis_angle : ℝ) : ℂ) * Complex.I by push_cast; ring,
      -- `exp (x * i) = cos x + sin x * i`, with `cos` and `sin` of a real.
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      cos_two_mul, sin_two_mul]
    push_cast
    ring
  -- The one fact about the angle that is used: `sin θ ^ 2 + cos θ ^ 2 = 1`.
  have sin_sq_add_cos_sq_complex :
      ((sin axis_angle : ℝ) : ℂ) ^ 2
        + ((cos axis_angle : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast sin_sq_add_cos_sq axis_angle
  ext
  · -- The across part: both sides are polynomials in `cos θ` and `sin θ`.
    simp only [PASS_COMPLEX_LIGHT_THROUGH_POLARIZER, Prod.fst_add,
      Prod.smul_fst, smul_eq_mul, exp_as_cos_sin]
    ring
  · -- The up part: equal once `sin θ ^ 2 + cos θ ^ 2 = 1` is used, and
    -- `I * I = -1`.
    simp only [PASS_COMPLEX_LIGHT_THROUGH_POLARIZER, Prod.snd_add,
      Prod.smul_snd, smul_eq_mul, exp_as_cos_sin]
    linear_combination
      (Complex.I : ℂ) * sin_sq_add_cos_sq_complex
      + ((sin axis_angle : ℝ) : ℂ) * ((cos axis_angle : ℝ) : ℂ)
          * Complex.I_mul_I

end SquigglyLine
