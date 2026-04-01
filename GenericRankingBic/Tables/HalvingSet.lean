import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Finset Nat

/-- Distinct positive child lengths obtained by repeated binary halving, excluding the root. -/
def halvingSet (k : ℕ) : Finset ℕ :=
  if k ≤ 1 then ∅
  else {k / 2, k - k / 2} ∪ halvingSet (k / 2) ∪ halvingSet (k - k / 2)
termination_by k
decreasing_by
  · exact Nat.div_lt_self (by omega) (by omega)
  · exact Nat.sub_lt_self (by omega) (by omega)

/-- The halving set of a power of 2 contains only smaller powers of 2. -/
theorem halvingSet_pow (m : ℕ) :
    halvingSet (2^m) = (range m).image (2^·) := by
  induction' m with m ih <;> simp_all +decide [pow_succ']
  · simp [halvingSet]
  · unfold halvingSet; grind

/-- Recursive characterization of H(k) for even k. -/
lemma halvingSet_even (k : ℕ) (hk : k > 0) :
    halvingSet (2 * k) = insert k (halvingSet k) := by
  rw [halvingSet]; split_ifs with h
  <;> [omega; simp [show 2 * k / 2 = k by omega, show 2 * k - k = k by omega]]

/-- Recursive characterization of H(k) for odd k. -/
lemma halvingSet_odd (k : ℕ) (hk : k > 0) :
    halvingSet (2 * k + 1) =
      {k, k + 1} ∪ halvingSet k ∪ halvingSet (k + 1) := by
  rw [halvingSet]; split_ifs with h
  <;> [omega;
    simp [show (2 * k + 1) / 2 = k by omega,
      show 2 * k + 1 - k = k + 1 by omega]]

/-- Every child length is smaller than the root. -/
lemma halvingSet_max_lt (k : ℕ) (hk : k > 1) :
    ∀ x ∈ halvingSet k, x < k := by
  induction' k using Nat.strong_induction_on with k ih
  rcases Nat.even_or_odd' k with ⟨c, rfl | rfl⟩
  · rw [halvingSet_even]
    · rcases c with (_ | _ | c) <;> simp_all +arith +decide
      · simp [halvingSet]
      · grind +ring
    · linarith
  · unfold halvingSet
    rcases c with (_ | _ | c) <;>
      simp +arith +decide [Nat.add_div] at *
    · grind +locals
    · grind +ring

/-- The root is excluded from its halving set. -/
lemma not_mem_halvingSet (k : ℕ) :
    k ∉ halvingSet k := by
  by_cases hk : k > 1
  · exact fun h => by have := halvingSet_max_lt k hk k h; linarith
  · rw [halvingSet, if_pos (by omega)]
    simp

/-- Cardinality recursion: |H(2k)| = |H(k)| + 1 for k > 0. -/
theorem halvingSet_card_even (k : ℕ) (hk : k > 0) :
    (halvingSet (2 * k)).card = (halvingSet k).card + 1 := by
  rw [halvingSet_even k hk,
    Finset.card_insert_of_notMem (not_mem_halvingSet k)]

/-- Size of the halving set for powers of 2: |H(2^m)| = m. -/
theorem halvingSet_card_pow (m : ℕ) :
    (halvingSet (2^m)).card = m := by
  rw [halvingSet_pow,
    card_image_of_injective _
      (Nat.pow_right_injective (by omega : 2 ≤ 2)),
    card_range]

/-- `H(2j) ⊆ H(2j+1)`. -/
lemma halvingSet_even_subset (j : ℕ) (hj : j ≥ 1) :
    halvingSet (2 * j) ⊆ halvingSet (2 * j + 1) := by
  rw [halvingSet_even]
  · rw [halvingSet_odd]
    · grind
    · linarith
  · linarith

/-- `H(2j+2) ⊆ H(2j+1)`. -/
lemma halvingSet_succ_even_subset (j : ℕ) (hj : j ≥ 1) :
    halvingSet (2 * j + 2) ⊆ halvingSet (2 * j + 1) := by
  rw [show 2 * j + 2 = 2 * (j + 1) by ring, halvingSet_even]
  · rw [halvingSet_odd]
    · grind
    · linarith
  · grind

/-- For even m ≥ 4, m ∉ H(m+1). -/
lemma even_not_mem_halvingSet_succ (m : ℕ) (hm : m ≥ 4)
    (heven : Even m) : m ∉ halvingSet (m + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j := even_iff_two_dvd.mp heven
  rw [halvingSet_odd]
  · simp +zetaDelta at *
    exact ⟨by linarith, by linarith,
      fun h => by linarith [halvingSet_max_lt j (by linarith) _ h],
      fun h => by
        linarith [halvingSet_max_lt (j + 1) (by linarith) _ h]⟩
  · linarith

/-- Cardinality recursion for odd k with odd half:
|H(2m+1)| = |H(m)| + 2 for odd m ≥ 1. -/
lemma halvingSet_card_odd_odd (m : ℕ) (hm : m ≥ 1)
    (hodd : ¬Even m) :
    (halvingSet (2 * m + 1)).card =
      (halvingSet m).card + 2 := by
  have h_not_mem_m : m ∉ halvingSet m :=
    not_mem_halvingSet m
  have h_not_mem_m1 : m + 1 ∉ halvingSet m := by
    intro h_mem_m1
    have h_mem_m1_lt_m : m + 1 < m := by
      apply halvingSet_max_lt m (by
        contrapose! hodd; interval_cases m; simp_all +decide
        exact absurd h_mem_m1 (by simp [halvingSet])) (m + 1) h_mem_m1
    linarith [h_mem_m1_lt_m]
  have h_halvingSet :
      halvingSet (2 * m + 1) = {m, m + 1} ∪ halvingSet m := by
    rw [halvingSet_odd]
    · rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩ <;>
        simp_all +arith +decide [parity_simps]
      rcases k with (_ | k) <;> simp_all +arith +decide
      · ext x; simp [halvingSet, or_comm]
      · have h_subset :
            halvingSet (2 * k + 4) ⊆ halvingSet (2 * k + 3) := by
          exact halvingSet_succ_even_subset (k + 1) (by linarith)
        grind
    · linarith
  grind

/-- Cardinality recursion for odd k with even half:
|H(2m+1)| = |H(m+1)| + 2 for even m ≥ 4. -/
lemma halvingSet_card_odd_even (m : ℕ) (hm : m ≥ 4)
    (heven : Even m) :
    (halvingSet (2 * m + 1)).card =
      (halvingSet (m + 1)).card + 2 := by
  have h_def :
      halvingSet (2 * m + 1) =
        {m, m + 1} ∪ halvingSet m ∪ halvingSet (m + 1) := by
    convert halvingSet_odd m (by linarith) using 1
  have h_even_subset :
      halvingSet m ⊆ halvingSet (m + 1) := by
    grind +suggestions
  have h_not_mem :
      m + 1 ∉ halvingSet (m + 1) ∧ m ∉ halvingSet (m + 1) := by
    exact ⟨not_mem_halvingSet _,
      even_not_mem_halvingSet_succ _ (by linarith)
        (by simpa using heven)⟩
  rw [h_def, Finset.union_assoc]
  rw [Finset.union_eq_right.mpr h_even_subset]; aesop

/-- Closed expression for the cardinality of `halvingSet` at `k ≥ 2`. -/
def halvingCardFormula (k : ℕ) : ℕ :=
  let ℓ := Nat.log 2 k
  2 * ℓ - padicValNat 2 k -
    (if 2 ^ ℓ < k ∧ k < 2 ^ ℓ + 2 ^ (ℓ - 1) then 1 else 0)

/-- Formula recursion: even case. -/
lemma halvingCardFormula_even (m : ℕ) (hm : m ≥ 1) :
    halvingCardFormula (2 * m) = halvingCardFormula m + 1 := by
  unfold halvingCardFormula
  rw [padicValNat.mul] <;> simp +arith +decide
  · rw [show log 2 (2 * m) = log 2 m + 1 from ?_, Nat.mul_succ]
    · split_ifs <;> simp_all +decide [pow_succ']
      · rw [tsub_tsub, tsub_add_eq_add_tsub]
        · grind +splitImp
        · have h_padic : padicValNat 2 m ≤ log 2 m := by
            exact Nat.le_log_of_pow_le (by decide)
              (Nat.le_of_dvd hm (Nat.ordProj_dvd _ _))
          linarith [show log 2 m > 0 from
            Nat.log_pos (by decide) (by linarith)]
      · grind +suggestions
      · rcases k : Nat.log 2 m with (_ | k) <;>
          simp_all +arith +decide [Nat.pow_succ']
        · linarith
        · omega
      · rw [tsub_add_eq_add_tsub]
        have := Nat.ordProj_dvd m 2
        have := Nat.le_of_dvd hm this
        have := Nat.le_log_of_pow_le (by decide) this
        exact le_trans this (by linarith)
    · rw [mul_comm, Nat.log_mul_base] <;> norm_num [hm]
      linarith
  · linarith

/-- Formula recursion: odd case with odd half. -/
lemma halvingCardFormula_odd_odd (m : ℕ) (hm : m ≥ 1)
    (hodd : ¬Even m) :
    halvingCardFormula (2 * m + 1) =
      halvingCardFormula m + 2 := by
  unfold halvingCardFormula
  have h_log : Nat.log 2 (2 * m + 1) = Nat.log 2 m + 1 := by
    rw [Nat.log_eq_iff] <;> norm_num
    exact ⟨by rw [pow_succ']
              linarith [Nat.pow_log_le_self 2
                (by linarith : m ≠ 0)],
           by rw [pow_succ']
              linarith [Nat.lt_pow_of_log_lt one_lt_two
                (by linarith :
                  Nat.log 2 m < Nat.log 2 m + 1)]⟩
  simp_all +decide [Nat.even_iff,
    padicValNat.eq_zero_of_not_dvd]
  rcases k : Nat.log 2 m with (_ | k) <;>
    simp_all +decide [pow_succ']
  · interval_cases m; trivial
  · grind

/-- Formula recursion: odd case with even half (m ≥ 4). -/
lemma halvingCardFormula_odd_even (m : ℕ) (hm : m ≥ 4)
    (heven : Even m) :
    halvingCardFormula (2 * m + 1) =
      halvingCardFormula (m + 1) + 2 := by
  unfold halvingCardFormula
  rw [show Nat.log 2 (2 * m + 1) = Nat.log 2 (m + 1) + 1
        from ?_,
    padicValNat.eq_zero_of_not_dvd,
    padicValNat.eq_zero_of_not_dvd]
  · rcases k : Nat.log 2 (m + 1) with (_ | _ | k) <;>
      simp_all +arith +decide [Nat.pow_succ']
    · grind
    · grind
  · grind
  · lia
  · nontriviality
    rw [Nat.log_eq_iff] <;> norm_num
    have := Nat.pow_log_le_self 2 (by linarith : m + 1 ≠ 0)
    have := Nat.lt_pow_succ_log_self (by decide : 1 < 2)
      (m + 1)
    (rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩ <;>
      ring_nf at * <;> norm_num at *)
    · rcases Nat.even_or_odd' (2 ^ log 2 (1 + k * 2)) with
        ⟨c, d | d⟩ <;> push_cast [*] at * <;>
        ring_nf at * <;> norm_num at *
      · grind
      · have := congr_arg Even d
        norm_num [Nat.even_add, Nat.even_mul,
          Nat.even_pow] at this
        grind
    · simp_all +decide [parity_simps]

/-- Cardinality of the iterated binary halving set for `k ≥ 2`. -/
theorem halvingSet_card (k : ℕ) (hk : k ≥ 2) :
    (halvingSet k).card = halvingCardFormula k := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk_small : k = 2 ∨ k = 3 ∨ k = 5
    · -- The three seeds not covered by a recurrence with a smaller valid argument.
      rcases hk_small with h | h | h
      · subst k
        calc
          (halvingSet 2).card = 1 := by
            rw [halvingSet_card_even 1 (by omega)]
            simp [halvingSet]
          _ = halvingCardFormula 2 := by norm_num [halvingCardFormula]
      · subst k
        calc
          (halvingSet 3).card = 2 := by
            rw [halvingSet_odd 1 (by omega)]
            simp [halvingSet]
          _ = halvingCardFormula 3 := by
            norm_num [halvingCardFormula, padicValNat.eq_zero_of_not_dvd]
      · subst k
        calc
          (halvingSet 5).card = 3 := by
            rw [halvingSet_odd 2 (by omega)]
            simp [halvingSet]
          _ = halvingCardFormula 5 := by
            norm_num [halvingCardFormula, padicValNat.eq_zero_of_not_dvd]
    · -- All other cases follow from the even or odd recurrence.
      push_neg at hk_small
      rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
      · -- Even case: k = 2m
        rw [halvingSet_card_even m (by omega),
          ih m (by omega) (by omega),
          halvingCardFormula_even m (by omega)]
      · -- Odd case: k = 2m + 1
        by_cases hm_even : Even m
        · -- m even, m ≥ 4
          have hm_ge4 : m ≥ 4 := by
            rcases hm_even with ⟨t, ht⟩
            omega
          rw [halvingSet_card_odd_even m hm_ge4 hm_even,
            ih (m + 1) (by omega) (by omega),
            halvingCardFormula_odd_even m hm_ge4 hm_even]
        · -- m odd, m ≥ 1
          rw [halvingSet_card_odd_odd m (by omega) hm_even,
            ih m (by omega) (by omega),
            halvingCardFormula_odd_odd m (by omega) hm_even]
