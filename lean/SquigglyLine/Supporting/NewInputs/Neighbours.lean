/-
Nearest neighbours, k-means and contrastive learning: three uses of nearness.

* **Nearest neighbours.** Copying the label of the nearest training input is
  wrong by at most the slope of the truth times the distance to that input.
* **k-means.** Each half of a step lowers the cost or leaves it: moving every
  point to its nearest centre, and moving every centre to the mean of its
  points.
* **Contrastive learning.** For vectors of length one, the dot product is one
  minus half the squared distance. So a softmax over cosine similarity at
  temperature `temperature` is a softmax over squared distance: the same
  weights as the ideal denoiser of `Averaging.lean` with noise level
  `√temperature`.

Theorems:
* `nearest_neighbour_error_is_at_most_slope_times_distance`                  nearest-neighbour error is at most
                                        slope times distance;
* `reassigning_points_does_not_raise_the_cost`                  k-means, first half: moving points to
                                        a no-further centre does not raise the
                                        cost;
* `mean_is_the_best_centre_of_a_cluster`                      k-means, second half: the mean is the
                                        best centre;
* `softmax_ignores_a_constant_added_to_every_score`                   shifting every score changes no share;
* `overlap_of_unit_vectors_equals_one_minus_half_squared_distance`            dot product against distance, for unit
                                        vectors;
* `softmax_of_overlap_equals_softmax_of_distance`  the same for keys of one
                                        common length and a query of any
                                        length;
* `softmax_of_cosine_equals_softmax_of_distance_for_unit_vectors`  contrastive scoring is scoring by
                                        nearness.
-/
import SquigglyLine.Supporting.NewInputs.Averaging

namespace SquigglyLine

open Real NNReal

variable {Examples Space : Type*} [NormedAddCommGroup Space]
  [InnerProductSpace ℝ Space]

omit [InnerProductSpace ℝ Space] in
/-- **Nearest neighbours.** If the truth `model` has slope at most
`slope_limit`, then copying the label of the nearest training input
`inputs nearest` is wrong by at most `slope_limit` times the distance from the
query to any training input, and so to the nearest. -/
theorem nearest_neighbour_error_is_at_most_slope_times_distance
    {model : Model Space}
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit model)
    (query : Space)
    (inputs : Examples → Space)
    {nearest : Examples}
    (nearest_is_nearest :
      ∀ other, dist query (inputs nearest) ≤ dist query (inputs other))
    (other : Examples) :
    let copy_error := |model query - model (inputs nearest)|
    let bound      := slope_limit * dist query (inputs other)
    copy_error ≤ bound := by
  unfold_named_pieces
  have slope_step := slope_is_bounded.dist_le_mul query (inputs nearest)
  rw [Real.dist_eq] at slope_step
  exact slope_step.trans (mul_le_mul_of_nonneg_left
    (nearest_is_nearest other) slope_limit.coe_nonneg)

variable {Centres : Type*} [Fintype Examples]

omit [InnerProductSpace ℝ Space] in
/-- **k-means, first half.** Give every point a centre that is no further than
the one it had. The cost does not rise. -/
theorem reassigning_points_does_not_raise_the_cost
    (points : Examples → Space)
    (centres : Centres → Space)
    (old_centre_of new_centre_of : Examples → Centres)
    (new_is_no_further :
      ∀ i, ‖points i - centres (new_centre_of i)‖
        ≤ ‖points i - centres (old_centre_of i)‖) :
    let new_cost := ∑ i, ‖points i - centres (new_centre_of i)‖ ^ 2
    let old_cost := ∑ i, ‖points i - centres (old_centre_of i)‖ ^ 2
    new_cost ≤ old_cost := by
  unfold_named_pieces
  exact Finset.sum_le_sum fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (new_is_no_further i) 2

/-- **k-means, second half.** For the points of one cluster, no centre has a
lower cost than their mean. -/
theorem mean_is_the_best_centre_of_a_cluster [Nonempty Examples]
    (points : Examples → Space)
    (other_centre : Space) :
    let mean :=
      GET_WEIGHTED_MEAN (fun _ => (Fintype.card Examples : ℝ)⁻¹) points  -- equal shares: 1 / count
    let mean_cost  := ∑ i, ‖points i - mean‖ ^ 2
    let other_cost := ∑ i, ‖points i - other_centre‖ ^ 2
    mean_cost ≤ other_cost := by
  unfold_named_pieces
  have count_pos : (0 : ℝ) < Fintype.card Examples := by
    exact_mod_cast Fintype.card_pos
  have shares_sum_to_one :
      ∑ _i : Examples, (Fintype.card Examples : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ count_pos.ne']
  -- With equal shares, the weighted best-guess bound is the plain one, up to
  -- the common factor `1 / count`.
  have weighted_bound :
      ∑ i, (Fintype.card Examples : ℝ)⁻¹
          * ‖points i
            - GET_WEIGHTED_MEAN (fun _ => (Fintype.card Examples : ℝ)⁻¹)
              points‖ ^ 2
        ≤ ∑ i, (Fintype.card Examples : ℝ)⁻¹
          * ‖points i - other_centre‖ ^ 2 :=
    weighted_mean_is_the_best_single_guess shares_sum_to_one points other_centre
  simp only [← Finset.mul_sum] at weighted_bound
  exact le_of_mul_le_mul_left weighted_bound (inv_pos.mpr count_pos)

/-- Adding the same number to every score changes no share of the softmax. -/
theorem softmax_ignores_a_constant_added_to_every_score
    (scores : Examples → ℝ)
    (shift : ℝ) :
    let shifted_shares := APPLY_SOFTMAX (fun i => scores i + shift)
    let shares         := APPLY_SOFTMAX scores
    shifted_shares = shares := by
  unfold_named_pieces
  funext i
  simp only [APPLY_SOFTMAX, exp_add, ← Finset.sum_mul]
  rw [mul_div_mul_right _ _ (exp_pos shift).ne']

/-- For two vectors of length one, the dot product is one minus half the
squared distance. -/
theorem overlap_of_unit_vectors_equals_one_minus_half_squared_distance
    {vector other_vector : Space}
    (vector_is_unit : ‖vector‖ = 1)
    (other_vector_is_unit : ‖other_vector‖ = 1) :
    let dot_product := inner ℝ vector other_vector
    let from_distance := 1 - ‖vector - other_vector‖ ^ 2 / 2  -- ‖a - b‖² = 2 - 2 a·b for unit a, b
    dot_product = from_distance := by
  unfold_named_pieces
  have expansion := norm_sub_sq_real vector other_vector
  rw [vector_is_unit, other_vector_is_unit] at expansion
  linarith

/-- **Contrastive learning scores by nearness.** For vectors of length one, the
softmax over cosine similarity at temperature `temperature` is the softmax over
minus the squared distance, divided by `2 * temperature`. -/
theorem softmax_of_cosine_equals_softmax_of_distance_for_unit_vectors
    {query : Space}
    {keys : Examples → Space}
    (query_is_unit : ‖query‖ = 1)
    (keys_are_unit : ∀ i, ‖keys i‖ = 1)
    (temperature : ℝ) :
    let cosine_shares :=
      APPLY_SOFTMAX (fun i => inner ℝ query (keys i) / temperature)
    let distance_shares :=
      APPLY_SOFTMAX fun i => -‖query - keys i‖ ^ 2 / (2 * temperature)
    cosine_shares = distance_shares := by
  unfold_named_pieces
  -- The two scores differ by the same constant for every key.
  have scores_differ_by_const :
      (fun i => inner ℝ query (keys i) / temperature)
        = fun i => -‖query - keys i‖ ^ 2 / (2 * temperature)
            + 1 / temperature := by
    funext i
    have dot_product_eq :
        inner ℝ query (keys i) = 1 - ‖query - keys i‖ ^ 2 / 2 :=
      overlap_of_unit_vectors_equals_one_minus_half_squared_distance query_is_unit (keys_are_unit i)
    rw [dot_product_eq]
    ring
  have shift_invariant :
      APPLY_SOFTMAX
          (fun i => -‖query - keys i‖ ^ 2 / (2 * temperature)
            + 1 / temperature)
        = APPLY_SOFTMAX fun i => -‖query - keys i‖ ^ 2 / (2 * temperature) :=
    softmax_ignores_a_constant_added_to_every_score _ _
  rw [scores_differ_by_const, shift_invariant]

/-- **The same without vectors of length one.** It is enough that the keys
all have the same length, whatever that length is. The query may have any
length. The two scores still differ by the same constant for every key, and
a softmax does not see a constant added to every score. -/
theorem softmax_of_overlap_equals_softmax_of_distance
    {query : Space}
    {keys : Examples → Space}
    {key_length : ℝ}
    (keys_have_same_length : ∀ i, ‖keys i‖ = key_length)
    (temperature : ℝ) :
    let overlap_shares :=
      APPLY_SOFTMAX (fun i => inner ℝ query (keys i) / temperature)
    let distance_shares :=
      APPLY_SOFTMAX fun i => -‖query - keys i‖ ^ 2 / (2 * temperature)
    overlap_shares = distance_shares := by
  unfold_named_pieces
  -- The two scores differ by the same constant for every key.
  have scores_differ_by_const :
      (fun i => inner ℝ query (keys i) / temperature)
        = fun i => -‖query - keys i‖ ^ 2 / (2 * temperature)
            + (‖query‖ ^ 2 + key_length ^ 2) / (2 * temperature) := by
    funext i
    -- The squared distance written out: two squared lengths, minus twice
    -- the overlap.
    have expansion := norm_sub_sq_real query (keys i)
    rw [keys_have_same_length i] at expansion
    have dot_product_eq :
        inner ℝ query (keys i)
          = (‖query‖ ^ 2 + key_length ^ 2 - ‖query - keys i‖ ^ 2) / 2 := by
      linarith
    rw [dot_product_eq]
    ring
  rw [scores_differ_by_const]
  exact softmax_ignores_a_constant_added_to_every_score _ _

end SquigglyLine
