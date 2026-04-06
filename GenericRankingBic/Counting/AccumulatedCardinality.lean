import GenericRankingBic.Counting.AccumulatedSet
import GenericRankingBic.Counting.RawMoment
import Mathlib.Tactic

open Finset Nat

/-- Natural subtraction repeats zero after `j = n`, so the accumulated set is
already complete when the window reaches `n`. -/
theorem BoundedCompAcc_eq_clipped (n k d l : ℕ) :
    BoundedCompAcc n k d l = BoundedCompAcc n k d (min l n) := by
  ext z
  simp only [BoundedCompAcc, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, hz⟩
    refine ⟨min j n, by omega, ?_⟩
    have hsub : n - min j n = n - j := by omega
    simpa only [hsub] using hz
  · rintro ⟨j, hj, hz⟩
    exact ⟨j, by omega, hz⟩

/-- For a positive number of parts, the accumulated set has cardinality `compCountAcc`. -/
theorem BoundedCompAcc_card_eq_compCountAcc (n k d l : ℕ) (hk : 0 < k) :
    ((BoundedCompAcc n k d l).card : ℤ) = compCountAcc n k d l := by
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
  rw [Finset.card_biUnion hdisj]
  simp only [Nat.cast_sum]
  exact (compCountAcc_eq_partial_sum_clipped n k d l hk).symm

/-- The zeroth unnormalized moment counts accumulated compositions. -/
theorem rawMoment_zero_eq_BoundedCompAcc_card (n k d l : ℕ) (hk : 0 < k) :
    rawMoment 0 n k d l = ((BoundedCompAcc n k d l).card : ℤ) := by
  rw [rawMoment_zero_eq_compCountAcc]
  exact (BoundedCompAcc_card_eq_compCountAcc n k d l hk).symm
