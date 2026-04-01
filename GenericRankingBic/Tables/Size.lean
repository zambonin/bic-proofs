import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Finset Nat

/-- Number of scalar entries in the accumulated table when `d ≤ n`.
Each cell has `min j d + 2` entries, including its leading zero. -/
theorem accumulatedTableSize (n k d : ℕ) (h_dn : d ≤ n) :
    ∑ _i ∈ range (k + 1), ∑ j ∈ range (n + 1), (min j d + 2) =
    (k + 1) * (d * (d + 1) / 2 + 2 * (d + 1) + (n - d) * (d + 2)) := by
  have h_inner : ∑ j ∈ Finset.range (n + 1), (min j d + 2) =
      (∑ j ∈ Finset.range (d + 1), (j + 2)) + (∑ j ∈ Finset.range (n - d), (d + 2)) := by
    rw [← Finset.sum_range_add_sum_Ico _ (by linarith : d + 1 ≤ n + 1)]
    simp +arith +decide [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun x hx => by rw [min_eq_left (Finset.mem_range_succ_iff.mp hx)]
  simp_all +decide [Finset.sum_add_distrib]
  simp +arith +decide [mul_comm, Finset.sum_range_id]
