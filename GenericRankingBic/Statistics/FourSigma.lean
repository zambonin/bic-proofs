import GenericRankingBic.Statistics.RealBand

private theorem example_card : (BoundedCompAcc 1 20 1 0).card = 20 := by
  decide +kernel

private theorem example_mean : compPartialMean 1 20 1 1 = 1 / 20 := by
  decide +kernel

private theorem example_variance : compPartialVariance 1 20 1 1 = 19 / 400 := by
  decide +kernel

private theorem example_in_band_zero :
    inStatisticalBand (compPartialMean 1 20 1) (compPartialVariance 1 20 1)
      4 1 0 = true := by
  rw [inStatisticalBand_iff, example_mean, example_variance]
  norm_num

private theorem example_out_band_one :
    inStatisticalBand (compPartialMean 1 20 1) (compPartialVariance 1 20 1)
      4 1 1 = false := by
  simp only [Bool.eq_false_iff, inStatisticalBand]
  rw [example_mean, example_variance]
  norm_num

private theorem example_retained_card :
    ((BoundedCompAcc 1 20 1 0).filter fun z =>
      (z ⟨0, by decide⟩ : Rat) = 0).card = 19 := by
  decide +kernel

private theorem example_coord_le :
    ∀ z ∈ BoundedCompAcc 1 20 1 0, z ⟨0, by decide⟩ ≤ 1 := by
  decide +kernel

private theorem example_band_iff_zero (j : Nat) (hj : j ≤ 1) :
    inStatisticalBand (compPartialMean 1 20 1) (compPartialVariance 1 20 1)
      4 1 j = true ↔ j = 0 := by
  interval_cases j
  · simp [example_in_band_zero]
  · simp [example_out_band_one]

/-- Exactly 19 of the 20 bounded compositions lie inside the four-sigma band
for their first partial sum. Thus the finite coverage is exactly 95%. -/
theorem fourSigma_counterexample_retained_fraction :
    (((BoundedCompAcc 1 20 1 0).filter fun z =>
      inStatisticalBand (compPartialMean 1 20 1) (compPartialVariance 1 20 1)
        4 1 (z ⟨0, by decide⟩) = true).card : Rat) /
      (BoundedCompAcc 1 20 1 0).card = 19 / 20 := by
  have hfilter :
      ((BoundedCompAcc 1 20 1 0).filter fun z =>
        inStatisticalBand (compPartialMean 1 20 1) (compPartialVariance 1 20 1)
          4 1 (z ⟨0, by decide⟩) = true) =
      ((BoundedCompAcc 1 20 1 0).filter fun z =>
        (z ⟨0, by decide⟩ : Rat) = 0) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, hband⟩
      exact ⟨hz, by exact_mod_cast (example_band_iff_zero _ (example_coord_le z hz)).mp hband⟩
    · rintro ⟨hz, hzero⟩
      refine ⟨hz, (example_band_iff_zero _ (example_coord_le z hz)).mpr ?_⟩
      exact_mod_cast hzero
  rw [hfilter, example_retained_card, example_card]
  norm_num

/-- The exact finite coverage can fall below the paper's Gaussian 99.993%
figure, so that figure cannot be a universal finite-parameter theorem. -/
theorem fourSigma_counterexample_below_gaussian_figure :
    (((BoundedCompAcc 1 20 1 0).filter fun z =>
      inStatisticalBand (compPartialMean 1 20 1) (compPartialVariance 1 20 1)
        4 1 (z ⟨0, by decide⟩) = true).card : Rat) /
      (BoundedCompAcc 1 20 1 0).card < 99993 / 100000 := by
  rw [fourSigma_counterexample_retained_fraction]
  norm_num

/-- The sum of squared deviations is the sample size times the rational
variance. This finite identity is the input to Chebyshev's inequality. -/
private theorem centered_sq_sum_eq_card_mul_variance {α : Type*} (S : Finset α)
    (f : α → Rat) (hS : 0 < S.card) :
    (∑ z ∈ S, (f z - finiteMean S f) ^ 2) =
      (S.card : Rat) * finiteVariance S f := by
  have hcard : (S.card : Rat) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS
  let μ := finiteMean S f
  have hcenter :
      (∑ z ∈ S, (f z - μ) ^ 2) =
        (∑ z ∈ S, (f z) ^ 2) - 2 * μ * (∑ z ∈ S, f z) + S.card * μ ^ 2 := by
    calc
      _ = ∑ z ∈ S, ((f z) ^ 2 - 2 * μ * f z + μ ^ 2) := by
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_const]
        ring
  rw [hcenter]
  dsimp [μ, finiteMean, finiteVariance]
  field_simp
  ring

/-- At most one sixteenth of any nonempty finite uniform sample lies strictly
outside its four-standard-deviation band when the variance is positive. -/
theorem finite_fourSigma_outside_le {α : Type*} (S : Finset α) (f : α → Rat)
    (hS : 0 < S.card) (hv : 0 < finiteVariance S f) :
    (((S.filter fun z =>
      16 * finiteVariance S f < (f z - finiteMean S f) ^ 2).card : Rat) /
        S.card) ≤ 1 / 16 := by
  classical
  let μ := finiteMean S f
  let v := finiteVariance S f
  let bad := S.filter fun z => 16 * v < (f z - μ) ^ 2
  have hcard : (0 : Rat) < S.card := by exact_mod_cast hS
  have hbad_sum : (bad.card : Rat) * (16 * v) ≤
      ∑ z ∈ bad, (f z - μ) ^ 2 := by
    simpa only [nsmul_eq_mul] using
      (Finset.card_nsmul_le_sum bad (fun z => (f z - μ) ^ 2) (16 * v)
        (by intro z hz; exact le_of_lt (Finset.mem_filter.mp hz).2))
  have hsum_le : (∑ z ∈ bad, (f z - μ) ^ 2) ≤
      ∑ z ∈ S, (f z - μ) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro z _ _
      exact sq_nonneg _
  have hsum : (∑ z ∈ S, (f z - μ) ^ 2) = (S.card : Rat) * v :=
    centered_sq_sum_eq_card_mul_variance S f hS
  have hcount : (bad.card : Rat) * 16 ≤ S.card := by
    have hmul : ((bad.card : Rat) * 16) * v ≤ (S.card : Rat) * v := by
      calc
        _ = (bad.card : Rat) * (16 * v) := by ring
        _ ≤ ∑ z ∈ bad, (f z - μ) ^ 2 := hbad_sum
        _ ≤ ∑ z ∈ S, (f z - μ) ^ 2 := hsum_le
        _ = (S.card : Rat) * v := hsum
    exact (mul_le_mul_iff_left₀ hv).mp hmul
  dsimp [bad, μ, v] at hcount ⊢
  apply (div_le_iff₀ hcard).mpr
  nlinarith

/-- The finite Chebyshev bound also covers zero variance: in that case every
sample is exactly at the mean. -/
theorem finite_fourSigma_outside_le_general {α : Type*} (S : Finset α)
    (f : α → Rat) (hS : 0 < S.card) :
    (((S.filter fun z =>
      16 * finiteVariance S f < (f z - finiteMean S f) ^ 2).card : Rat) /
        S.card) ≤ 1 / 16 := by
  classical
  rcases lt_or_eq_of_le (finiteVariance_nonneg S f) with hv | hv
  · exact finite_fourSigma_outside_le S f hS hv
  · have hv0 : finiteVariance S f = 0 := hv.symm
    have hsum : (∑ z ∈ S, (f z - finiteMean S f) ^ 2) = 0 := by
      rw [centered_sq_sum_eq_card_mul_variance S f hS, hv0, mul_zero]
    have hpoint : ∀ z ∈ S, (f z - finiteMean S f) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun z _ => sq_nonneg (f z - finiteMean S f))).mp hsum
    have hfilter :
        (S.filter fun z =>
          16 * finiteVariance S f < (f z - finiteMean S f) ^ 2) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro z hz
      rw [hv0, mul_zero, hpoint z hz]
      exact lt_irrefl 0
    rw [hfilter]
    norm_num

/-- Uniform finite-sample coverage of the inclusive four-sigma band is at
least `15/16`. This is the unconditional Chebyshev guarantee. -/
theorem finite_fourSigma_inside_ge {α : Type*} (S : Finset α)
    (f : α → Rat) (hS : 0 < S.card) :
    (15 / 16 : Rat) ≤
      (((S.filter fun z =>
        (f z - finiteMean S f) ^ 2 ≤ 16 * finiteVariance S f).card : Rat) /
          S.card) := by
  classical
  let bad := S.filter fun z =>
    16 * finiteVariance S f < (f z - finiteMean S f) ^ 2
  let good := S.filter fun z =>
    (f z - finiteMean S f) ^ 2 ≤ 16 * finiteVariance S f
  have hcard : (0 : Rat) < S.card := by exact_mod_cast hS
  have hparts : bad.card + good.card = S.card := by
    simpa only [bad, good, not_lt] using
      (Finset.card_filter_add_card_filter_not
        (s := S) (p := fun z =>
          16 * finiteVariance S f < (f z - finiteMean S f) ^ 2))
  have hpartsq : (bad.card : Rat) + good.card = S.card := by exact_mod_cast hparts
  have hbad : ((bad.card : Rat) / S.card) ≤ 1 / 16 :=
    finite_fourSigma_outside_le_general S f hS
  have hbadcount : (bad.card : Rat) * 16 ≤ S.card := by
    have h := (div_le_iff₀ hcard).mp hbad
    nlinarith
  apply (le_div_iff₀ hcard).mpr
  nlinarith

/-- The unconditional finite-sample coverage guarantee for the exact
partial-sum mean and variance of bounded compositions. -/
theorem composition_fourSigma_inside_ge (n k d i : Nat)
    (hS : 0 < (BoundedCompAcc n k d 0).card) :
    (15 / 16 : Rat) ≤
      ((((BoundedCompAcc n k d 0).filter fun z =>
        (partialSumQ z i - compPartialMean n k d i) ^ 2 ≤
          16 * compPartialVariance n k d i).card : Rat) /
        (BoundedCompAcc n k d 0).card) := by
  exact finite_fourSigma_inside_ge (BoundedCompAcc n k d 0)
    (fun z => partialSumQ z i) hS
