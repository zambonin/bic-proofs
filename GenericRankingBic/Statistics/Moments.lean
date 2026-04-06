import GenericRankingBic.Counting.AccumulatedCardinality
import GenericRankingBic.Statistics.PartialSums

open Finset Nat

private theorem totalSumQ_of_mem_BoundedComp (r k d : ℕ)
    (z : Fin k → ℕ) (hz : z ∈ BoundedComp r k d) : totalSumQ z = r := by
  have hsum : ∑ i : Fin k, z i = r :=
    mem_antidiagonalTuple.mp (Finset.mem_filter.mp hz).1
  simpa only [totalSumQ, Nat.cast_sum] using
    congrArg (fun x : ℕ => (x : ℚ)) hsum

/-- `rawMoment p` is the unnormalized `p`-th moment of the total sum on the
finite accumulated composition set. In particular, `rawMoment 0` is its size. -/
theorem rawMoment_eq_sum_totalSumQ_pow (p n k d l : ℕ) (hk : 0 < k) :
    (rawMoment p n k d l : ℚ) =
      ∑ z ∈ BoundedCompAcc n k d l, (totalSumQ z) ^ p := by
  rw [BoundedCompAcc_eq_clipped]
  unfold BoundedCompAcc
  have hdisj :
      ((Finset.range (min l n + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun j => BoundedComp (n - j) k d) := by
    intro i hi j hj hij
    apply BoundedComp_disjoint
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    omega
  rw [Finset.sum_biUnion hdisj]
  rw [rawMoment_eq_sum_clipped p n k d l hk]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  have hfixed : ∀ z ∈ BoundedComp (n - j) k d,
      (totalSumQ z) ^ p = ((n - j : ℕ) : ℚ) ^ p := by
    intro z hz
    rw [totalSumQ_of_mem_BoundedComp (n - j) k d z hz]
  rw [Finset.sum_congr rfl hfixed]
  simp [compCount, mul_comm]

/-- The mean of `R` is `μ₁ / μ₀`. For its probabilistic interpretation,
the accumulated set must be nonempty. -/
theorem finiteMean_totalSumQ_eq_rawMoments (n k d l : ℕ) (hk : 0 < k) :
    finiteMean (BoundedCompAcc n k d l) totalSumQ =
      (rawMoment 1 n k d l : ℚ) / (rawMoment 0 n k d l : ℚ) := by
  rw [finiteMean]
  have hraw := rawMoment_eq_sum_totalSumQ_pow 1 n k d l hk
  simp only [pow_one] at hraw
  rw [← hraw]
  rw [rawMoment_zero_eq_BoundedCompAcc_card n k d l hk]
  norm_num

/-- The totalized second moment of `R` is `μ₂ / μ₀`; a probability
interpretation requires a nonempty accumulated set. -/
theorem finiteMean_totalSumQ_sq_eq_rawMoments (n k d l : ℕ) (hk : 0 < k) :
    finiteMean (BoundedCompAcc n k d l) (fun z => (totalSumQ z) ^ 2) =
      (rawMoment 2 n k d l : ℚ) / (rawMoment 0 n k d l : ℚ) := by
  rw [finiteMean, ← rawMoment_eq_sum_totalSumQ_pow 2 n k d l hk]
  rw [rawMoment_zero_eq_BoundedCompAcc_card n k d l hk]
  norm_num

/-- Finite variance of `R` is `μ₂ / μ₀ - (μ₁ / μ₀)²`, with the
totalized value zero on the empty accumulated set. -/
theorem finiteVariance_totalSumQ_eq_rawMoments (n k d l : ℕ) (hk : 0 < k) :
    finiteVariance (BoundedCompAcc n k d l) totalSumQ =
      (rawMoment 2 n k d l : ℚ) / (rawMoment 0 n k d l : ℚ) -
        ((rawMoment 1 n k d l : ℚ) / (rawMoment 0 n k d l : ℚ)) ^ 2 := by
  rw [finiteVariance, ← finiteMean_totalSumQ_eq_rawMoments n k d l hk]
  rw [← finiteMean_totalSumQ_sq_eq_rawMoments n k d l hk]
  rfl

/-- Proposition 5's displayed formula for the variance of the first part,
with the fiber counts and the mean both written using raw moments. -/
theorem variance_single_part_eq_rawMoments (n k d l : ℕ) (hk : 1 < k)
    (hS : 0 < (BoundedCompAcc n k d l).card) :
    finiteVariance (BoundedCompAcc n k d l)
        (fun z => (z ⟨0, by omega⟩ : ℚ)) =
      (∑ y ∈ Finset.range (min n d + 1),
          (y : ℚ) ^ 2 * (rawMoment 0 (n - y) (k - 1) d l : ℚ)) /
          (rawMoment 0 n k d l : ℚ) -
        (((rawMoment 1 n k d l : ℚ) /
          (rawMoment 0 n k d l : ℚ)) / k) ^ 2 := by
  rw [variance_single_part_normalized n k d l hk hS]
  rw [finiteMean_totalSumQ_eq_rawMoments n k d l (by omega)]
  rw [rawMoment_zero_eq_BoundedCompAcc_card n k d l (by omega)]
  congr 2
  apply Finset.sum_congr rfl
  intro y hy
  rw [rawMoment_zero_eq_BoundedCompAcc_card (n - y) (k - 1) d l (by omega)]
  norm_num
