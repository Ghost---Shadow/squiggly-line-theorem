/-
Standard initialisation: the squared loss at the start does not see the width.

Chapter 5 of the book measures that a network's loss at the start is the
same at every width, and says that this is not proved. This file proves it
for squared error and one hidden layer.

The network is

    output = sum over the hidden units of outer_weight * hidden_value

Draw the outer weights independently of each other and of everything in the
first layer, each with mean zero and mean square `outer_scale / width`.
This is what the standard schemes do ("variance one over fan-in"). Then

* the mean of the output is zero, and
* the mean of the squared output is `outer_scale * hidden_mean_square`,
  where `hidden_mean_square` is the mean square of one hidden unit.

The width has cancelled: there are `width` units, and each outer weight has
mean square `outer_scale / width`. Squared error reads only these two
numbers, so the expected squared error at the start is
`label ^ 2 + outer_scale * hidden_mean_square` at every width.

What is assumed and not proved:

* every hidden unit has the same mean square at the input, and that number
  is the same at every width. It is so when the incoming weights of each
  unit are drawn in the same way at every width, because a hidden unit does
  not know how many other units there are.
* nothing is said about the shape of the distribution of the output. It is
  not the same at every width. Only its mean and its mean square are.

Nothing here needs the weights to be Gaussian or the activation to be ReLU.

Theorems:

* `mean_of_one_outer_weight_equals_weight_mean`
* `mean_of_two_outer_weights_multiplied`
* `output_and_squared_output_have_means`
* `output_mean_is_zero_and_mean_square_has_no_width`
* `expected_squared_error_at_start_has_no_width`
* `expected_squared_error_at_start_is_same_at_two_widths`

How to read the notation:

* `Measure.pi (fun _ => weight_distribution)` draws one weight for each
  hidden unit, independently, all from `weight_distribution`.
* `first.prod second` draws a pair, the two parts independently.
* `∫ weight, weight ^ 2 ∂weight_distribution` is the mean of the squared
  weight.
* `MemLp function 2 distribution` says the square of the function has a
  finite mean.
* `Integrable function distribution` says the function has a finite mean.
* `Fintype.card Units` is the number of hidden units: the width.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Pi
import SquigglyLine.Style

namespace SquigglyLine

open MeasureTheory

variable {Units : Type*} [Fintype Units] [DecidableEq Units]

/-! ## One outer weight, and two of them multiplied -/

/-- One outer weight, written as a product over all the units: the weight
itself for the chosen unit, and 1 for every other unit. -/
theorem one_outer_weight_as_product
    (chosen_unit : Units)
    (outer_weights : Units → ℝ) :
    ∏ unit, (if unit = chosen_unit then outer_weights unit else 1)
      = outer_weights chosen_unit := by
  rw [Finset.prod_ite_eq' Finset.univ chosen_unit outer_weights]
  simp

/-- Two outer weights multiplied, written as a product over all the units. -/
theorem two_outer_weights_as_product
    (first_unit : Units)
    (second_unit : Units)
    (outer_weights : Units → ℝ) :
    ∏ unit,
        ((if unit = first_unit then outer_weights unit else 1)
          * (if unit = second_unit then outer_weights unit else 1))
      = outer_weights first_unit * outer_weights second_unit := by
  rw [Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ first_unit outer_weights,
    Finset.prod_ite_eq' Finset.univ second_unit outer_weights]
  simp

/-- The mean of one outer weight, when all are drawn independently from the
same distribution, is the mean of that distribution. -/
theorem mean_of_one_outer_weight_equals_weight_mean
    (weight_distribution : Measure ℝ)
    [IsProbabilityMeasure weight_distribution]
    (chosen_unit : Units) :
    let outer_weight_distribution :=
      Measure.pi (fun _ : Units => weight_distribution)
    let mean_of_chosen_weight :=
      ∫ outer_weights : Units → ℝ, outer_weights chosen_unit
        ∂outer_weight_distribution
    let weight_mean := ∫ weight, weight ∂weight_distribution
    mean_of_chosen_weight = weight_mean := by
  unfold_named_pieces
  simp_rw [← one_outer_weight_as_product chosen_unit]
  -- The mean of a product of independent pieces is the product of the means.
  rw [integral_fintype_prod_eq_prod
    (fun unit weight => if unit = chosen_unit then weight else 1)]
  -- Every factor is 1 except the one for the chosen unit.
  rw [Finset.prod_eq_single chosen_unit]
  · simp
  · intro other_unit _ other_is_not_chosen
    simp [other_is_not_chosen]
  · intro chosen_not_in_all
    exact absurd (Finset.mem_univ chosen_unit) chosen_not_in_all

/-- **Two outer weights multiplied.** For two different units the mean of
the product is zero, because the weights are independent and have mean zero.
For one unit taken twice it is the mean square of a weight. -/
theorem mean_of_two_outer_weights_multiplied
    (weight_distribution : Measure ℝ)
    [IsProbabilityMeasure weight_distribution]
    (weight_mean_is_zero : ∫ weight, weight ∂weight_distribution = 0)
    (first_unit : Units)
    (second_unit : Units) :
    let outer_weight_distribution :=
      Measure.pi (fun _ : Units => weight_distribution)
    let mean_of_product :=
      ∫ outer_weights : Units → ℝ,
        outer_weights first_unit * outer_weights second_unit
        ∂outer_weight_distribution
    let weight_mean_square := ∫ weight, weight ^ 2 ∂weight_distribution
    mean_of_product
      = if first_unit = second_unit then weight_mean_square else 0 := by
  unfold_named_pieces
  simp_rw [← two_outer_weights_as_product first_unit second_unit]
  rw [integral_fintype_prod_eq_prod
    (fun unit weight =>
      (if unit = first_unit then weight else 1)
        * (if unit = second_unit then weight else 1))]
  by_cases units_are_same : first_unit = second_unit
  · -- One unit taken twice: its factor is the mean square, the others are 1.
    subst units_are_same
    simp only [↓reduceIte]
    rw [Finset.prod_eq_single first_unit]
    · simp [pow_two]
    · intro other_unit _ other_is_not_first
      simp [other_is_not_first]
    · intro first_not_in_all
      exact absurd (Finset.mem_univ first_unit) first_not_in_all
  · -- Two different units: the factor of the first unit is the mean of one
    -- weight, which is zero.
    simp only [units_are_same, ↓reduceIte]
    refine Finset.prod_eq_zero (Finset.mem_univ first_unit) ?_
    simp [units_are_same, weight_mean_is_zero]

/-! ## What has a mean -/

/-- The output of the network and its square both have a finite mean. This
is bookkeeping: it lets the next theorems take sums out of means. -/
theorem output_and_squared_output_have_means
    {FirstLayer : Type*} [MeasurableSpace FirstLayer]
    (weight_distribution : Measure ℝ)
    [IsProbabilityMeasure weight_distribution]
    (first_layer_distribution : Measure FirstLayer)
    [IsProbabilityMeasure first_layer_distribution]
    (hidden : Units → FirstLayer → ℝ)
    (weight_is_square_integrable :
      MemLp (fun weight : ℝ => weight) 2 weight_distribution)
    (hidden_is_square_integrable :
      ∀ unit, MemLp (hidden unit) 2 first_layer_distribution) :
    let prior :=
      (Measure.pi (fun _ : Units => weight_distribution)).prod
        first_layer_distribution
    let one_term_has_a_mean := ∀ unit : Units,
      Integrable
        (fun parameters : (Units → ℝ) × FirstLayer =>
          parameters.1 unit * hidden unit parameters.2)
        prior
    let one_pair_term_has_a_mean := ∀ first_unit second_unit : Units,
      Integrable
        (fun parameters : (Units → ℝ) × FirstLayer =>
          (parameters.1 first_unit * parameters.1 second_unit)
            * (hidden first_unit parameters.2
                * hidden second_unit parameters.2))
        prior
    one_term_has_a_mean ∧ one_pair_term_has_a_mean := by
  unfold_named_pieces
  have weight_is_integrable :
      Integrable (fun weight : ℝ => weight) weight_distribution :=
    weight_is_square_integrable.integrable one_le_two
  have weight_square_is_integrable :
      Integrable (fun weight : ℝ => weight * weight) weight_distribution :=
    weight_is_square_integrable.integrable_mul weight_is_square_integrable
  -- A factor that is the weight or 1, times another such factor.
  have factor_is_integrable :
      ∀ (is_first is_second : Prop) [Decidable is_first] [Decidable is_second],
        Integrable
          (fun weight : ℝ =>
            (if is_first then weight else 1)
              * (if is_second then weight else 1))
          weight_distribution := by
    intro is_first is_second _ _
    by_cases first_holds : is_first <;> by_cases second_holds : is_second <;>
      simp only [first_holds, second_holds, ite_true, ite_false, mul_one,
        one_mul]
    exacts [weight_square_is_integrable, weight_is_integrable,
      weight_is_integrable, integrable_const 1]
  have one_outer_weight_is_integrable : ∀ chosen_unit : Units,
      Integrable (fun outer_weights : Units → ℝ => outer_weights chosen_unit)
        (Measure.pi (fun _ : Units => weight_distribution)) := by
    intro chosen_unit
    have product_is_integrable :=
      Integrable.fintype_prod (μ := fun _ : Units => weight_distribution)
        (f := fun unit weight =>
          (if unit = chosen_unit then weight else 1)
            * (if False then weight else 1))
        (fun unit => factor_is_integrable (unit = chosen_unit) False)
    refine product_is_integrable.congr (Filter.Eventually.of_forall ?_)
    intro outer_weights
    simp only [ite_false, mul_one]
    exact one_outer_weight_as_product chosen_unit outer_weights
  have two_outer_weights_are_integrable : ∀ first_unit second_unit : Units,
      Integrable
        (fun outer_weights : Units → ℝ =>
          outer_weights first_unit * outer_weights second_unit)
        (Measure.pi (fun _ : Units => weight_distribution)) := by
    intro first_unit second_unit
    have product_is_integrable :=
      Integrable.fintype_prod (μ := fun _ : Units => weight_distribution)
        (f := fun unit weight =>
          (if unit = first_unit then weight else 1)
            * (if unit = second_unit then weight else 1))
        (fun unit =>
          factor_is_integrable (unit = first_unit) (unit = second_unit))
    refine product_is_integrable.congr (Filter.Eventually.of_forall ?_)
    intro outer_weights
    exact two_outer_weights_as_product first_unit second_unit outer_weights
  have hidden_is_integrable : ∀ unit,
      Integrable (hidden unit) first_layer_distribution :=
    fun unit => (hidden_is_square_integrable unit).integrable one_le_two
  have two_hidden_are_integrable : ∀ first_unit second_unit,
      Integrable
        (fun first_layer =>
          hidden first_unit first_layer * hidden second_unit first_layer)
        first_layer_distribution :=
    fun first_unit second_unit =>
      (hidden_is_square_integrable first_unit).integrable_mul
        (hidden_is_square_integrable second_unit)
  exact ⟨fun unit =>
      (one_outer_weight_is_integrable unit).mul_prod
        (hidden_is_integrable unit),
    fun first_unit second_unit =>
      (two_outer_weights_are_integrable first_unit second_unit).mul_prod
        (two_hidden_are_integrable first_unit second_unit)⟩

omit [DecidableEq Units] in
/-- The square of the output is a sum over pairs of hidden units. -/
theorem squared_output_as_sum_over_pairs
    {FirstLayer : Type*}
    (hidden : Units → FirstLayer → ℝ)
    (parameters : (Units → ℝ) × FirstLayer) :
    (∑ unit, parameters.1 unit * hidden unit parameters.2) ^ 2
      = ∑ first_unit, ∑ second_unit,
          (parameters.1 first_unit * parameters.1 second_unit)
            * (hidden first_unit parameters.2
                * hidden second_unit parameters.2) := by
  rw [pow_two, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun first_unit _ =>
    Finset.sum_congr rfl fun second_unit _ => ?_
  ring

/-! ## The output of the network at the start -/

/-- **At the start, the mean output is zero and the mean squared output has
no width in it.** One hidden layer; the outer weights independent of each
other and of the first layer, with mean zero and mean square
`outer_scale / width`; every hidden unit with the same mean square. -/
theorem output_mean_is_zero_and_mean_square_has_no_width
    {FirstLayer : Type*} [MeasurableSpace FirstLayer]
    [Nonempty Units]
    (weight_distribution : Measure ℝ)
    [IsProbabilityMeasure weight_distribution]
    (first_layer_distribution : Measure FirstLayer)
    [IsProbabilityMeasure first_layer_distribution]
    (hidden : Units → FirstLayer → ℝ)                 -- the value of each hidden unit at the input, for each draw of the first layer
    {outer_scale : ℝ}
    {hidden_mean_square : ℝ}
    (weight_is_square_integrable :
      MemLp (fun weight : ℝ => weight) 2 weight_distribution)
    (weight_mean_is_zero : ∫ weight, weight ∂weight_distribution = 0)
    (weight_mean_square_is_scale_over_width :
      ∫ weight, weight ^ 2 ∂weight_distribution
        = outer_scale / Fintype.card Units)
    (hidden_is_square_integrable :
      ∀ unit, MemLp (hidden unit) 2 first_layer_distribution)
    (hidden_mean_square_is_same :
      ∀ unit, ∫ first_layer, hidden unit first_layer ^ 2
        ∂first_layer_distribution = hidden_mean_square) :
    let prior :=
      (Measure.pi (fun _ : Units => weight_distribution)).prod
        first_layer_distribution                      -- outer weights and first layer, drawn independently
    let output := fun parameters : (Units → ℝ) × FirstLayer =>
      ∑ unit, parameters.1 unit * hidden unit parameters.2
    let mean_output        := ∫ parameters, output parameters ∂prior
    let mean_square_output := ∫ parameters, output parameters ^ 2 ∂prior
    mean_output = 0
      ∧ mean_square_output = outer_scale * hidden_mean_square := by
  unfold_named_pieces
  obtain ⟨one_term_has_a_mean, one_pair_term_has_a_mean⟩ :=
    output_and_squared_output_have_means weight_distribution
      first_layer_distribution hidden weight_is_square_integrable
      hidden_is_square_integrable
  have width_ne_zero : (Fintype.card Units : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  constructor
  · -- The mean. Take the sum out, then split each term into the mean of the
    -- outer weight times the mean of the hidden unit. The first is zero.
    rw [integral_finsetSum _ fun unit _ => one_term_has_a_mean unit]
    refine Finset.sum_eq_zero fun unit _ => ?_
    rw [integral_prod_mul
        (fun outer_weights : Units → ℝ => outer_weights unit) (hidden unit),
      mean_of_one_outer_weight_equals_weight_mean weight_distribution unit,
      weight_mean_is_zero, zero_mul]
  · -- The mean square. The square of a sum is a sum over pairs of units.
    simp_rw [squared_output_as_sum_over_pairs hidden]
    -- Take both sums out of the mean.
    rw [integral_finsetSum _ fun first_unit _ =>
      integrable_finsetSum _ fun second_unit _ =>
        one_pair_term_has_a_mean first_unit second_unit]
    simp_rw [integral_finsetSum _ fun second_unit _ =>
      one_pair_term_has_a_mean _ second_unit]
    -- Each term splits into a mean over the outer weights times a mean over
    -- the first layer. The first is zero unless the two units are the same.
    have term_value : ∀ first_unit second_unit : Units,
        ∫ parameters : (Units → ℝ) × FirstLayer,
            (parameters.1 first_unit * parameters.1 second_unit)
              * (hidden first_unit parameters.2
                  * hidden second_unit parameters.2)
          ∂(Measure.pi (fun _ : Units => weight_distribution)).prod
            first_layer_distribution
        = if first_unit = second_unit
            then outer_scale / Fintype.card Units * hidden_mean_square
            else 0 := by
      intro first_unit second_unit
      rw [integral_prod_mul
          (fun outer_weights : Units → ℝ =>
            outer_weights first_unit * outer_weights second_unit)
          (fun first_layer =>
            hidden first_unit first_layer * hidden second_unit first_layer),
        mean_of_two_outer_weights_multiplied weight_distribution
          weight_mean_is_zero first_unit second_unit]
      by_cases units_are_same : first_unit = second_unit
      · subst units_are_same
        simp only [↓reduceIte]
        rw [weight_mean_square_is_scale_over_width,
          ← hidden_mean_square_is_same first_unit]
        simp_rw [pow_two]
      · simp only [units_are_same, ↓reduceIte, zero_mul]
    simp_rw [term_value]
    -- Only the pairs of one unit with itself are left: `width` equal terms.
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

/-- **The expected squared error at the start has no width in it.** For any
label, it is `label ^ 2 + outer_scale * hidden_mean_square`. -/
theorem expected_squared_error_at_start_has_no_width
    {FirstLayer : Type*} [MeasurableSpace FirstLayer]
    [Nonempty Units]
    (weight_distribution : Measure ℝ)
    [IsProbabilityMeasure weight_distribution]
    (first_layer_distribution : Measure FirstLayer)
    [IsProbabilityMeasure first_layer_distribution]
    (hidden : Units → FirstLayer → ℝ)
    {outer_scale : ℝ}
    {hidden_mean_square : ℝ}
    (weight_is_square_integrable :
      MemLp (fun weight : ℝ => weight) 2 weight_distribution)
    (weight_mean_is_zero : ∫ weight, weight ∂weight_distribution = 0)
    (weight_mean_square_is_scale_over_width :
      ∫ weight, weight ^ 2 ∂weight_distribution
        = outer_scale / Fintype.card Units)
    (hidden_is_square_integrable :
      ∀ unit, MemLp (hidden unit) 2 first_layer_distribution)
    (hidden_mean_square_is_same :
      ∀ unit, ∫ first_layer, hidden unit first_layer ^ 2
        ∂first_layer_distribution = hidden_mean_square)
    (label : ℝ) :
    let prior :=
      (Measure.pi (fun _ : Units => weight_distribution)).prod
        first_layer_distribution
    let output := fun parameters : (Units → ℝ) × FirstLayer =>
      ∑ unit, parameters.1 unit * hidden unit parameters.2
    let expected_squared_error :=
      ∫ parameters, (label - output parameters) ^ 2 ∂prior
    expected_squared_error
      = label ^ 2 + outer_scale * hidden_mean_square := by
  unfold_named_pieces
  obtain ⟨mean_is_zero, mean_square_has_no_width⟩ :=
    output_mean_is_zero_and_mean_square_has_no_width weight_distribution
      first_layer_distribution hidden weight_is_square_integrable
      weight_mean_is_zero weight_mean_square_is_scale_over_width
      hidden_is_square_integrable hidden_mean_square_is_same
  obtain ⟨one_term_has_a_mean, one_pair_term_has_a_mean⟩ :=
    output_and_squared_output_have_means weight_distribution
      first_layer_distribution hidden weight_is_square_integrable
      hidden_is_square_integrable
  beta_reduce at mean_is_zero mean_square_has_no_width
  -- The output and its square have means, because every term does.
  have output_is_integrable :
      Integrable
        (fun parameters : (Units → ℝ) × FirstLayer =>
          ∑ unit, parameters.1 unit * hidden unit parameters.2)
        ((Measure.pi (fun _ : Units => weight_distribution)).prod
          first_layer_distribution) :=
    integrable_finsetSum _ fun unit _ => one_term_has_a_mean unit
  have output_square_is_integrable :
      Integrable
        (fun parameters : (Units → ℝ) × FirstLayer =>
          (∑ unit, parameters.1 unit * hidden unit parameters.2) ^ 2)
        ((Measure.pi (fun _ : Units => weight_distribution)).prod
          first_layer_distribution) := by
    simp_rw [squared_output_as_sum_over_pairs hidden]
    exact integrable_finsetSum _ fun first_unit _ =>
      integrable_finsetSum _ fun second_unit _ =>
        one_pair_term_has_a_mean first_unit second_unit
  have twice_label_times_output_is_integrable :
      Integrable
        (fun parameters : (Units → ℝ) × FirstLayer =>
          2 * label * ∑ unit, parameters.1 unit * hidden unit parameters.2)
        ((Measure.pi (fun _ : Units => weight_distribution)).prod
          first_layer_distribution) :=
    output_is_integrable.const_mul (2 * label)
  have first_two_terms_are_integrable :
      Integrable
        (fun parameters : (Units → ℝ) × FirstLayer =>
          label ^ 2
            - 2 * label * ∑ unit, parameters.1 unit * hidden unit parameters.2)
        ((Measure.pi (fun _ : Units => weight_distribution)).prod
          first_layer_distribution) :=
    (integrable_const (label ^ 2)).sub twice_label_times_output_is_integrable
  -- Expand the square: label ^ 2 - 2 * label * output + output ^ 2.
  have expand_square : ∀ parameters : (Units → ℝ) × FirstLayer,
      (label - ∑ unit, parameters.1 unit * hidden unit parameters.2) ^ 2
        = label ^ 2
          - 2 * label * (∑ unit, parameters.1 unit * hidden unit parameters.2)
          + (∑ unit, parameters.1 unit * hidden unit parameters.2) ^ 2 := by
    intro parameters
    ring
  simp_rw [expand_square]
  rw [integral_add first_two_terms_are_integrable output_square_is_integrable,
    integral_sub (integrable_const (label ^ 2))
      twice_label_times_output_is_integrable,
    integral_const_mul, mean_is_zero, mean_square_has_no_width]
  simp

/-- **The same at two widths.** Take two networks of this kind with
different numbers of hidden units. If the outer weights of each have mean
square `outer_scale` over its own width, and the hidden units of both have
the same mean square, then the expected squared error at the start is the
same for both, for every label. -/
theorem expected_squared_error_at_start_is_same_at_two_widths
    {OtherUnits : Type*} [Fintype OtherUnits] [DecidableEq OtherUnits]
    {FirstLayer OtherFirstLayer : Type*}
    [MeasurableSpace FirstLayer] [MeasurableSpace OtherFirstLayer]
    [Nonempty Units] [Nonempty OtherUnits]
    (weight_distribution other_weight_distribution : Measure ℝ)
    [IsProbabilityMeasure weight_distribution]
    [IsProbabilityMeasure other_weight_distribution]
    (first_layer_distribution : Measure FirstLayer)
    (other_first_layer_distribution : Measure OtherFirstLayer)
    [IsProbabilityMeasure first_layer_distribution]
    [IsProbabilityMeasure other_first_layer_distribution]
    (hidden : Units → FirstLayer → ℝ)
    (other_hidden : OtherUnits → OtherFirstLayer → ℝ)
    {outer_scale : ℝ}
    {hidden_mean_square : ℝ}
    (weight_is_square_integrable :
      MemLp (fun weight : ℝ => weight) 2 weight_distribution)
    (other_weight_is_square_integrable :
      MemLp (fun weight : ℝ => weight) 2 other_weight_distribution)
    (weight_mean_is_zero : ∫ weight, weight ∂weight_distribution = 0)
    (other_weight_mean_is_zero :
      ∫ weight, weight ∂other_weight_distribution = 0)
    (weight_mean_square_is_scale_over_width :
      ∫ weight, weight ^ 2 ∂weight_distribution
        = outer_scale / Fintype.card Units)
    (other_weight_mean_square_is_scale_over_width :
      ∫ weight, weight ^ 2 ∂other_weight_distribution
        = outer_scale / Fintype.card OtherUnits)
    (hidden_is_square_integrable :
      ∀ unit, MemLp (hidden unit) 2 first_layer_distribution)
    (other_hidden_is_square_integrable :
      ∀ unit, MemLp (other_hidden unit) 2 other_first_layer_distribution)
    (hidden_mean_square_is_same :
      ∀ unit, ∫ first_layer, hidden unit first_layer ^ 2
        ∂first_layer_distribution = hidden_mean_square)
    (other_hidden_mean_square_is_same :
      ∀ unit, ∫ first_layer, other_hidden unit first_layer ^ 2
        ∂other_first_layer_distribution = hidden_mean_square)
    (label : ℝ) :
    let prior :=
      (Measure.pi (fun _ : Units => weight_distribution)).prod
        first_layer_distribution
    let other_prior :=
      (Measure.pi (fun _ : OtherUnits => other_weight_distribution)).prod
        other_first_layer_distribution
    let output := fun parameters : (Units → ℝ) × FirstLayer =>
      ∑ unit, parameters.1 unit * hidden unit parameters.2
    let other_output :=
      fun parameters : (OtherUnits → ℝ) × OtherFirstLayer =>
        ∑ unit, parameters.1 unit * other_hidden unit parameters.2
    let expected_squared_error :=
      ∫ parameters, (label - output parameters) ^ 2 ∂prior
    let other_expected_squared_error :=
      ∫ parameters, (label - other_output parameters) ^ 2 ∂other_prior
    expected_squared_error = other_expected_squared_error := by
  unfold_named_pieces
  rw [expected_squared_error_at_start_has_no_width weight_distribution
      first_layer_distribution hidden weight_is_square_integrable
      weight_mean_is_zero weight_mean_square_is_scale_over_width
      hidden_is_square_integrable hidden_mean_square_is_same label,
    expected_squared_error_at_start_has_no_width other_weight_distribution
      other_first_layer_distribution other_hidden
      other_weight_is_square_integrable other_weight_mean_is_zero
      other_weight_mean_square_is_scale_over_width
      other_hidden_is_square_integrable other_hidden_mean_square_is_same label]

end SquigglyLine
