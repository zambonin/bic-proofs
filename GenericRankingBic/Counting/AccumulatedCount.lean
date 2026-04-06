import GenericRankingBic.Counting.InclusionExclusion
import GenericRankingBic.Counting.WeightedSum
import Mathlib.Tactic

open Finset Polynomial Nat

/-- Closed accumulated-count expression for the window `[n-l,n]`, clipped at zero,
for a positive number of parts. -/
def compCountAcc (n k d l : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (inclExclBound n k d + 1),
    (-1 : ℤ) ^ i * (k.choose i : ℤ) *
      binomSumZ (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) l

lemma binomSumZ_eq (c : ℕ) (m : ℤ) (l : ℕ) :
    binomSumZ c m l = if m < 0 then 0
      else (((m.toNat + 1).choose (c + 1) : ℤ) -
        ((m.toNat - l).choose (c + 1) : ℤ)) := by
  unfold binomSumZ weightedBinomSumZ
  split_ifs with hm
  · rfl
  · rw [weightedBinomSum_base c m.toNat l]
    have h_le : (m.toNat - l).choose (c + 1) ≤ (m.toNat + 1).choose (c + 1) := by
      exact Nat.choose_le_choose _ (by omega)
    rw [Int.ofNat_sub h_le]

/-- A zero-length window selects the coefficient at `m`; negative upper indices give zero. -/
@[simp]
lemma binomSumZ_zero (c : ℕ) (m : ℤ) :
    binomSumZ c m 0 = if m < 0 then 0 else (m.toNat.choose c : ℤ) := by
  rw [binomSumZ_eq]
  split_ifs with hm
  · rfl
  · have hzero : m.toNat - 0 = m.toNat := by omega
    rw [hzero, Nat.choose_succ_succ m.toNat c, add_comm]
    simp

/-- Extending the window adds the coefficient at its new nonnegative left endpoint. -/
lemma binomSumZ_step_large (c l : ℕ) (m : ℤ) (hm : m ≥ ↑l + 1) :
    binomSumZ c m (l + 1) - binomSumZ c m l =
      (Nat.choose (m.toNat - l - 1) c : ℤ) := by
  rw [binomSumZ_eq, binomSumZ_eq]
  split_ifs with h_m
  · exact False.elim (by omega)
  · have hp : m.toNat - l = m.toNat - l - 1 + 1 := by omega
    have hq : m.toNat - (l + 1) = m.toNat - l - 1 := by omega
    conv =>
      lhs
      rw [hp, Nat.choose_succ_succ (m.toNat - l - 1) c]
      rw [hq]
    push_cast
    ring

/-- Extending a window that already reaches zero adds no terms. -/
lemma binomSumZ_step_small (c l : ℕ) (m : ℤ) (hm0 : m ≥ 0) (hml : m ≤ ↑l) :
    binomSumZ c m (l + 1) - binomSumZ c m l = 0 := by
  rw [binomSumZ_eq, binomSumZ_eq]
  split_ifs with h_m
  · omega
  · have hp : m.toNat - l = 0 := by omega
    have hq : m.toNat - (l + 1) = 0 := by omega
    rw [hp, hq]
    ring

lemma inclExclBound_mono_sub (n k d l : ℕ) (hl : l + 1 ≤ n) :
    inclExclBound (n - 1 - l) k d ≤ inclExclBound n k d := by
  exact min_le_min_left _ (Nat.div_le_div_right (Nat.sub_le_of_le_add <| by omega))

lemma compCountAcc_extra_terms_vanish (n k d l i : ℕ) (hk : 0 < k)
    (hi_lo : inclExclBound (n - 1 - l) k d < i) (hi_hi : i ≤ inclExclBound n k d) :
    (-1 : ℤ) ^ i * (k.choose i : ℤ) *
      (binomSumZ (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) (l + 1) -
       binomSumZ (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) l) = 0 := by
  by_cases hi : inclExclBound (n - 1 - l) k d < i <;> simp_all +decide [inclExclBound]
  rcases hi_lo with (hi_lo | hi_lo)
  · linarith
  · by_cases h_case : (n - 1 - l : ℤ) < (d + 1) * i
    · by_cases h_case2 : (n - (d + 1) * i + k - 1 : ℤ) ≤ l
      · exact Or.inr (binomSumZ_step_small _ _ _
          (by nlinarith [Nat.div_mul_le_self n (d + 1)]) h_case2)
      · have h_binom_zero :
            Nat.choose (Int.toNat (n - (d + 1) * i + k - 1 - l - 1))
              (k - 1) = 0 := by
          rw [Nat.choose_eq_zero_of_lt]
          omega
        have := binomSumZ_step_large (k - 1) l (n - (d + 1) * i + k - 1)
          (by linarith)
        aesop
    · contrapose! hi_lo
      exact Nat.le_div_iff_mul_le (Nat.succ_pos _) |>.2
        (Nat.le_sub_of_add_le <| Nat.le_sub_of_add_le <| by linarith)

lemma compCountAcc_main_term (n k d l i : ℕ) (hk : 0 < k) (hl : l + 1 ≤ n)
    (hi : i ≤ inclExclBound (n - 1 - l) k d) :
    binomSumZ (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) (l + 1) -
    binomSumZ (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) l =
      ((n - 1 - l + k - 1 - (d + 1) * i).choose (k - 1) : ℤ) := by
  convert binomSumZ_step_large _ _ _ _ using 1
  · grind
  · contrapose! hi
    refine lt_of_le_of_lt (min_le_right _ _) ?_
    rw [Nat.div_lt_iff_lt_mul <| Nat.succ_pos _]
    grind

/-- Extending the window adds the count at its new nonnegative left endpoint. -/
lemma compCountAcc_step (n k d l : ℕ) (hk : 0 < k) (hl : l + 1 ≤ n) :
    compCountAcc n k d (l + 1) - compCountAcc n k d l =
      (compCount (n - 1 - l) k d : ℤ) := by
  have h_eq :
      ∑ i ∈ Finset.range (inclExclBound n k d + 1), (-1 : ℤ) ^ i * (k.choose i : ℤ) *
            (binomSumZ (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) (l + 1) -
             binomSumZ (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) l) =
        (compCount (n - 1 - l) k d : ℤ) := by
          rw [compCount_inclExcl]
          · rw [← Finset.sum_subset (Finset.range_mono
              (Nat.succ_le_succ (inclExclBound_mono_sub n k d l hl)))]
            · refine Finset.sum_congr rfl fun i hi => ?_
              rw [compCountAcc_main_term n k d l i hk hl
                (Finset.mem_range_succ_iff.mp hi)]
            · exact fun x hx₁ hx₂ =>
                compCountAcc_extra_terms_vanish n k d l x hk
                  (by simpa using hx₂)
                  (Finset.mem_range_succ_iff.mp hx₁)
          · linarith
  convert h_eq using 1
  unfold compCountAcc
  rw [← Finset.sum_sub_distrib]
  congr
  ext
  ring

/-- The analytical expression sums composition counts over `[n-l,n]` when `l ≤ n`. -/
theorem compCountAcc_eq_partial_sum (n k d l : ℕ) (hk : 0 < k) (hl : l ≤ n) :
    compCountAcc n k d l =
      ∑ j ∈ Finset.range (l + 1), (compCount (n - j) k d : ℤ) := by
  induction l generalizing n k d with
  | zero =>
    simp
    unfold compCountAcc
    rw [compCount_inclExcl _ _ _ hk]
    apply sum_congr rfl; intro i _
    rw [binomSumZ_zero]
    split_ifs with hm
    · have hi_bound : i ∈ Finset.range (inclExclBound n k d + 1) := by assumption
      have h1 : i ≤ inclExclBound n k d := Nat.le_of_lt_succ (Finset.mem_range.mp hi_bound)
      have h_div : i ≤ n / (d + 1) := le_trans h1 (min_le_right k (n / (d + 1)))
      have h4 : i * (d + 1) ≤ n / (d + 1) * (d + 1) :=
        Nat.mul_le_mul_right (d + 1) h_div
      have h5 : n / (d + 1) * (d + 1) ≤ n := Nat.div_mul_le_self n (d + 1)
      have hi_le : (d + 1) * i ≤ n := by
        rw [Nat.mul_comm]
        exact le_trans h4 h5
      have hz : (↑((d + 1) * i) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hi_le
      have hkz : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
      linarith
    · congr 2
      congr 1
      omega
  | succ l ih =>
    rw [Finset.sum_range_succ]
    rw [← ih n k d hk (by omega)]
    have h_step :
        compCountAcc n k d (l + 1) - compCountAcc n k d l =
          (compCount (n - 1 - l) k d : ℤ) :=
      compCountAcc_step n k d l hk (by omega)
    have h_idx : n - 1 - l = n - (l + 1) := by omega
    rw [h_idx] at h_step
    linarith

/-- Once the window reaches zero, extending it adds no new composition count. -/
lemma compCountAcc_step_stable (n k d l : ℕ) (hk : 0 < k) (hl : n ≤ l) :
    compCountAcc n k d (l + 1) = compCountAcc n k d l := by
  unfold compCountAcc
  apply Finset.sum_congr rfl
  intro i hi
  have hm : (n : ℤ) - ((d + 1) * i : ℕ) + k - 1 ≤
        (l : ℤ) + (k - 1 : ℕ) := by
      omega
  by_cases hsmall : (n : ℤ) - ((d + 1) * i : ℕ) + k - 1 ≤ (l : ℤ)
  · rw [show binomSumZ (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) (l + 1) =
          binomSumZ (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) l from ?_]
    · by_cases hneg : (n : ℤ) - ((d + 1) * i : ℕ) + k - 1 < 0
      · have hz (v : ℕ) :
            binomSumZ (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) v = 0 := by
          unfold binomSumZ weightedBinomSumZ
          rw [if_pos hneg]
        rw [hz (l + 1), hz l]
      · exact sub_eq_zero.mp (binomSumZ_step_small (k - 1) l _ (by omega) hsmall)
  · have hlarge : (l : ℤ) + 1 ≤ (n : ℤ) - ((d + 1) * i : ℕ) + k - 1 := by omega
    have hzero : Nat.choose ((↑n - ↑((d + 1) * i) + ↑k - 1 : ℤ).toNat - l - 1) (k - 1) = 0 := by
      apply Nat.choose_eq_zero_of_lt
      omega
    have hdiff := binomSumZ_step_large (k - 1) l
      (↑n - ↑((d + 1) * i) + ↑k - 1) hlarge
    rw [hzero] at hdiff
    have hdiff0 :
        binomSumZ (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) (l + 1) -
          binomSumZ (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) l = 0 := by
      simpa using hdiff
    rw [sub_eq_zero.mp hdiff0]

/-- The analytical expression is constant after its window covers all nonnegative sums. -/
theorem compCountAcc_eq_at_n (n k d l : ℕ) (hk : 0 < k) (hl : n ≤ l) :
    compCountAcc n k d l = compCountAcc n k d n := by
  induction l, hl using Nat.le_induction with
  | base => rfl
  | succ l hle ih =>
    rw [compCountAcc_step_stable n k d l hk hle, ih]

/-- Accumulated counts over the interval `[n-l,n]`, clipped at zero. -/
theorem compCountAcc_eq_partial_sum_clipped (n k d l : ℕ) (hk : 0 < k) :
    compCountAcc n k d l =
      ∑ j ∈ Finset.range (min l n + 1), (compCount (n - j) k d : ℤ) := by
  by_cases h : l ≤ n
  · simpa [min_eq_left h] using compCountAcc_eq_partial_sum n k d l hk h
  · have hle : n ≤ l := by omega
    rw [compCountAcc_eq_at_n n k d l hk hle]
    simpa [min_eq_right hle] using compCountAcc_eq_partial_sum n k d n hk le_rfl
