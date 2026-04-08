import GenericRankingBic.Tables.Probabilistic
import Mathlib.Algebra.Order.Chebyshev

/-- Finite rational variance is nonnegative, including its empty-space value zero. -/
theorem finiteVariance_nonneg {α : Type*} (S : Finset α) (f : α → ℚ) :
    0 ≤ finiteVariance S f := by
  unfold finiteVariance finiteMean
  exact sub_nonneg.mpr sum_div_card_sq_le_sum_sq_div_card

/-- The exact variance of a composition partial sum is nonnegative. -/
theorem compPartialVariance_nonneg (n k d i : Nat) :
    0 ≤ compPartialVariance n k d i := by
  exact finiteVariance_nonneg _ _
