import GenericRankingBic.Statistics.Variance
import Mathlib.Data.Real.Sqrt

/-- The rational squared band is exactly the paper's real-valued band when
the variance at the selected row is nonnegative. -/
theorem inStatisticalBand_iff_abs_le_sqrt (mean variance : Nat → Rat) (c i j : Nat)
    (hvariance : 0 ≤ variance i) :
    inStatisticalBand mean variance c i j = true ↔
      |(j : Real) - (mean i : Real)| ≤
        (c : Real) * Real.sqrt (variance i : Real) := by
  rw [inStatisticalBand_iff]
  have hvarianceReal : 0 ≤ (variance i : Real) := by exact_mod_cast hvariance
  have hnonneg : 0 ≤ (c : Real) * Real.sqrt (variance i : Real) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hsquare : ((c : Real) * Real.sqrt (variance i : Real)) ^ 2 =
      (c : Real) ^ 2 * (variance i : Real) := by
    rw [mul_pow, Real.sq_sqrt hvarianceReal]
  rw [← (sq_le_sq₀ (abs_nonneg _) hnonneg), sq_abs, hsquare]
  exact_mod_cast (Iff.rfl :
    ((j : Rat) - mean i) ^ 2 ≤ (c : Rat) ^ 2 * variance i ↔
      ((j : Rat) - mean i) ^ 2 ≤ (c : Rat) ^ 2 * variance i)

/-- A composition's statistical band agrees with the literal real band,
provided its finite-sample variance is nonnegative. -/
theorem compositionBand_iff_abs_le_sqrt_of_nonneg (n k d c i j : Nat)
    (hvariance : 0 ≤ compPartialVariance n k d i) :
    inStatisticalBand (compPartialMean n k d) (compPartialVariance n k d) c i j = true ↔
      |(j : Real) - (compPartialMean n k d i : Real)| ≤
        (c : Real) * Real.sqrt (compPartialVariance n k d i : Real) := by
  exact inStatisticalBand_iff_abs_le_sqrt _ _ c i j hvariance

/-- The exact composition variance is always nonnegative, so the table's
Boolean predicate agrees unconditionally with the paper's real band. -/
theorem compositionBand_iff_abs_le_sqrt (n k d c i j : Nat) :
    inStatisticalBand (compPartialMean n k d) (compPartialVariance n k d) c i j = true ↔
      |(j : Real) - (compPartialMean n k d i : Real)| ≤
        (c : Real) * Real.sqrt (compPartialVariance n k d i : Real) := by
  exact compositionBand_iff_abs_le_sqrt_of_nonneg n k d c i j
    (compPartialVariance_nonneg n k d i)

/-- The literal band with Proposition 5's closed-form partial-sum mean and
variance. The nonempty sample space and `k > 1` assumptions are those of the
normalized variance identity. -/
theorem compositionBand_eq_prop5_real (n k d c i j : Nat) (hk : 1 < k) (hi : i ≤ k)
    (hS : 0 < (BoundedCompAcc n k d 0).card) :
    inStatisticalBand (compPartialMean n k d) (compPartialVariance n k d) c i j = true ↔
      |(j : Real) - ((i : Rat) * n / k : Rat)| ≤
        (c : Real) * Real.sqrt
          (((i : Rat) * (k - i) / (k - 1) *
            finiteVariance (BoundedCompAcc n k d 0)
              (fun z => (z ⟨0, by omega⟩ : Rat))) : Rat) := by
  rw [compositionBand_iff_abs_le_sqrt,
    compPartialMean_eq n k d i (by omega) hi hS,
    compPartialVariance_eq n k d i hk hi hS]
