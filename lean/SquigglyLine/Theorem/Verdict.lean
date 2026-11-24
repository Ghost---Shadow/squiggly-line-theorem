/-
The verdict on the learning claim.

If every member of a family has the same one-point marginals, then no member
starts closer than another, for any regression loss and any data.
Random-phase waves of different frequencies are such a family. This is the
flat "vertical error" column of the experiment, as a theorem.

Theorems:

* `shared_marginals_never_start_closer`    shared marginals: nobody starts closer;
* `higher_frequency_never_starts_closer`   so not for random-phase waves;
* `learning_claim_fails_for_random_phase_waves`  so the learning claim fails for them;
* `learning_claim_fails_for_random_phase_sines`         and for sines in particular.
-/
import SquigglyLine.Theorem.Conjecture
import SquigglyLine.Theorem.Marginal
import SquigglyLine.Theorem.RandomPhase

namespace SquigglyLine

open MeasureTheory

variable {Size Inputs : Type*} [Preorder Size] [MeasurableSpace Inputs]
  {loss_fn : RealFunction}

/-- A family with shared one-point marginals never starts closer in a
regression loss. -/
theorem shared_marginals_never_start_closer
    {model_family : ModelFamily Size Inputs}
    (loss_is_measurable : Measurable loss_fn)
    (all_marginals_agree :
      ∀ size other_size,
        (model_family size).marginal = (model_family other_size).marginal)
    {smaller bigger : Size}
    (smaller_lt_bigger : smaller < bigger)  -- the family has two different sizes to compare
    (data_distribution : DataDistributionOver Inputs) :
    let bigger_starts_closer :=
      STARTS_CLOSER (GET_RESIDUAL_LOSS loss_fn) model_family data_distribution
    ¬ bigger_starts_closer :=
  -- "Starts closer" would make the two expected losses different, and
  -- equal marginals make them equal.
  fun starts_closer =>
    (starts_closer smaller_lt_bigger).ne
      (equal_marginals_give_equal_expected_loss loss_is_measurable
        (all_marginals_agree bigger smaller) data_distribution)

/-- **Squiggliness does not lower the training loss.** Raising the frequency
of a random-phase wave never lowers its expected regression loss. -/
theorem higher_frequency_never_starts_closer
    {period : ℝ} [Fact (0 < period)]
    {profile : Profile period}
    (profile_is_measurable : Measurable profile)
    (loss_is_measurable : Measurable loss_fn)
    (frequency_of : Size → ℝ)
    {smaller bigger : Size}
    (smaller_lt_bigger : smaller < bigger)
    (data_distribution : DataDistribution) :
    let wave_family := fun size =>
      MAKE_RANDOM_PHASE_WAVE profile profile_is_measurable (frequency_of size)
    let bigger_starts_closer :=
      STARTS_CLOSER (GET_RESIDUAL_LOSS loss_fn) wave_family data_distribution
    ¬ bigger_starts_closer :=
  shared_marginals_never_start_closer loss_is_measurable
    (fun _ _ => frequency_does_not_change_the_marginals_of_a_random_phase_wave profile_is_measurable _ _)
    smaller_lt_bigger data_distribution

/-- The learning claim fails for random-phase waves whose frequency grows
with size. -/
theorem learning_claim_fails_for_random_phase_waves
    {period : ℝ} [Fact (0 < period)]
    {profile : Profile period}
    (profile_is_measurable : Measurable profile)
    (loss_is_measurable : Measurable loss_fn)
    (frequency_of : ℕ → ℝ)
    (data_distribution : DataDistribution) :
    let wave_family := fun size =>
      MAKE_RANDOM_PHASE_WAVE profile profile_is_measurable (frequency_of size)
    let learning_claim :=
      LEARNING_CLAIM_HOLDS loss_fn wave_family data_distribution
    ¬ learning_claim :=
  higher_frequency_never_starts_closer profile_is_measurable loss_is_measurable
    frequency_of Nat.zero_lt_one data_distribution  -- sizes 0 and 1 are enough to compare

/-- The experiment of `scripts/frequency_isolation.py`, as a theorem: for
sines of any amplitude and any frequencies, the learning claim fails for
every regression loss on every data distribution. -/
theorem learning_claim_fails_for_random_phase_sines
    (amplitude : ℝ)
    (loss_is_measurable : Measurable loss_fn)
    (frequency_of : ℕ → ℝ)
    (data_distribution : DataDistribution) :
    let sine_family := fun size =>
      MAKE_RANDOM_PHASE_SINE amplitude (frequency_of size)
    let learning_claim :=
      LEARNING_CLAIM_HOLDS loss_fn sine_family data_distribution
    ¬ learning_claim :=
  shared_marginals_never_start_closer loss_is_measurable
    (fun _ _ => frequency_does_not_change_the_marginals_of_a_random_phase_sine amplitude _ _)
    Nat.zero_lt_one data_distribution  -- sizes 0 and 1 are enough to compare

end SquigglyLine
