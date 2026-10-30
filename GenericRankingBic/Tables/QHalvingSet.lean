import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open Finset

/-- The largest exponent whose power divides `k`, bounded by its logarithm.
For `q ≥ 2` and `k > 0`, the bound excludes no divisor power. -/
def qValuation (q k : ℕ) : ℕ :=
  Nat.findGreatest (fun p => q ^ p ∣ k) (Nat.log q k)

/-- The floor/ceiling pair at one level. -/
def qHalvingLevel (q k p : ℕ) : Finset ℕ :=
  {k / q ^ p, k ⌈/⌉ q ^ p}

/-- Literal union of levels `1,...,floor(log_q k)`.
This set does not specify the complete row trace of a q-way ranking algorithm. -/
def qHalvingSet (q k : ℕ) : Finset ℕ :=
  (Icc 1 (Nat.log q k)).biUnion (qHalvingLevel q k)

/-- The defined valuation is the greatest dividing exponent, also for composite `q`. -/
theorem pow_dvd_iff_le_qValuation (q k p : ℕ) (hq : 2 ≤ q) (hk : 0 < k) :
    q ^ p ∣ k ↔ p ≤ qValuation q k := by
  constructor
  · intro hp
    apply Nat.le_findGreatest
    · exact Nat.le_log_of_pow_le (by omega) (Nat.le_of_dvd hk hp)
    · exact hp
  · intro hp
    have hd : q ^ qValuation q k ∣ k := by
      unfold qValuation
      apply Nat.findGreatest_spec (P := fun p => q ^ p ∣ k) (m := 0) (Nat.zero_le (Nat.log q k))
      simp
    exact (Nat.pow_dvd_pow q hp).trans hd

private theorem ceilDiv_eq_div_add (k b : ℕ) (hb : 0 < b) :
    k ⌈/⌉ b = k / b + if b ∣ k then 0 else 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have hpred : k + b - 1 + 1 = k + b := by omega
  have hlo := Nat.div_mul_le_self k b
  have hhi := Nat.lt_mul_div_succ k hb
  by_cases hd : b ∣ k
  · have heq : k / b * b = k := Nat.div_mul_cancel hd
    simp only [hd, if_true, add_zero]
    apply Nat.div_eq_of_lt_le <;> nlinarith
  · have hne : k / b * b ≠ k := by
      intro heq
      exact hd ⟨k / b, by nlinarith [heq]⟩
    have hstrict : k / b * b < k := by omega
    simp only [hd, if_false]
    apply Nat.div_eq_of_lt_le <;> nlinarith

/-- A level has one value if `q^p` divides `k`, and two otherwise. -/
theorem qHalvingLevel_card_add (q k p : ℕ) (hq : 0 < q) :
    (qHalvingLevel q k p).card + (if q ^ p ∣ k then 1 else 0) = 2 := by
  unfold qHalvingLevel
  rw [ceilDiv_eq_div_add k (q ^ p) (pow_pos hq _)]
  split_ifs with hd <;> simp

private theorem qHalvingLevel_separated (q k p t : ℕ) (hq : 3 ≤ q)
    (hk : 0 < k) (hpt : p < t) (ht : t ≤ Nat.log q k) :
    k ⌈/⌉ q ^ t < k / q ^ p := by
  have hqpos : 0 < q := by omega
  have hpow : q * q ^ p ≤ q ^ t := by
    simpa [pow_succ, Nat.mul_comm] using
      Nat.pow_le_pow_right hqpos (Nat.succ_le_of_lt hpt)
  have hfloor : 1 ≤ k / q ^ t := by
    apply (Nat.le_div_iff_mul_le (pow_pos hqpos _)).2
    simpa using Nat.pow_le_of_le_log (Nat.ne_of_gt hk) ht
  have hmul : q * (k / q ^ t) ≤ k / q ^ p := by
    apply (Nat.le_div_iff_mul_le (pow_pos hqpos _)).2
    calc
      q * (k / q ^ t) * q ^ p = (k / q ^ t) * (q * q ^ p) := by ring
      _ ≤ (k / q ^ t) * q ^ t := Nat.mul_le_mul_left _ hpow
      _ ≤ k := Nat.div_mul_le_self _ _
  rw [ceilDiv_eq_div_add k (q ^ t) (pow_pos hqpos _)]
  split_ifs <;> nlinarith

/-- Distinct levels are disjoint for `q ≥ 3` and `k > 0`. -/
theorem qHalvingLevel_pairwiseDisjoint (q k : ℕ) (hq : 3 ≤ q) (hk : 0 < k) :
    (↑(Icc 1 (Nat.log q k)) : Set ℕ).PairwiseDisjoint (qHalvingLevel q k) := by
  intro p hp t ht hne
  have hp' := (mem_Icc.mp (show p ∈ Icc 1 (Nat.log q k) from hp)).2
  have ht' := (mem_Icc.mp (show t ∈ Icc 1 (Nat.log q k) from ht)).2
  have hlow (a : ℕ) : k / q ^ a ≤ k ⌈/⌉ q ^ a := by
    change k ⌊/⌋ q ^ a ≤ k ⌈/⌉ q ^ a
    exact floorDiv_le_ceilDiv
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [qHalvingLevel, mem_insert, mem_singleton] at hx hy
  rcases lt_or_gt_of_ne hne with hpt | htp
  · have hsep := qHalvingLevel_separated q k p t hq hk hpt ht'
    rcases hx with rfl | rfl <;> rcases hy with hy | hy <;>
      have := hlow p <;> have := hlow t <;> omega
  · have hsep := qHalvingLevel_separated q k t p hq hk htp hp'
    rcases hx with rfl | rfl <;> rcases hy with hy | hy <;>
      have := hlow p <;> have := hlow t <;> omega

/-- There are exactly `v_q(k)` dividing positive levels. -/
theorem qHalving_dividing_levels_card (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k) :
    ((Icc 1 (Nat.log q k)).filter fun p => q ^ p ∣ k).card = qValuation q k := by
  have hv : qValuation q k ≤ Nat.log q k := Nat.findGreatest_le _
  have hset : (Icc 1 (Nat.log q k)).filter (fun p => q ^ p ∣ k) =
      Icc 1 (qValuation q k) := by
    ext p
    simp only [mem_filter, mem_Icc, pow_dvd_iff_le_qValuation q k p hq hk]
    omega
  rw [hset, Nat.card_Icc]
  omega

/-- Exact literal-set cardinality for every positive `k` and integer base `q ≥ 3`. -/
theorem qHalvingSet_card (q k : ℕ) (hq : 3 ≤ q) (hk : 0 < k) :
    (qHalvingSet q k).card = 2 * Nat.log q k - qValuation q k := by
  have hsum : (qHalvingSet q k).card + qValuation q k = 2 * Nat.log q k := by
    unfold qHalvingSet
    rw [Finset.card_biUnion (qHalvingLevel_pairwiseDisjoint q k hq hk)]
    rw [← qHalving_dividing_levels_card q k (by omega) hk, Finset.card_filter]
    rw [← Finset.sum_add_distrib]
    simp only [qHalvingLevel_card_add q k _ (by omega)]
    simp
    omega
  omega

/-- The literal union is empty when `k < q`. -/
theorem qHalvingSet_eq_empty_of_lt (q k : ℕ) (hkq : k < q) :
    qHalvingSet q k = ∅ := by
  simp [qHalvingSet, Nat.log_of_lt hkq]

example : qHalvingSet 3 8 = {2, 3} := by decide
example : (qHalvingSet 4 64).card = 3 := by decide
example : qValuation 4 64 = 3 := by decide
