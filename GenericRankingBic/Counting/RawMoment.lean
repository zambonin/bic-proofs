import GenericRankingBic.Counting.AccumulatedCount
import GenericRankingBic.Counting.InclusionExclusion
import GenericRankingBic.Counting.WeightedSum
import Mathlib.Tactic

open Finset Polynomial Nat

/-- Integer shift of the inclusion–exclusion binomial index. -/
def inclExclShift (d k i : ℕ) : ℤ := (d + 1 : ℤ) * i - k + 1

/-- Inclusion–exclusion expression for the unnormalized `p`th power sum
over a window ending at `n`, for a positive number of parts. -/
def rawMoment (p n k d l : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (inclExclBound n k d + 1),
    (-1 : ℤ) ^ i * (k.choose i : ℤ) *
      ∑ s ∈ Finset.range (p + 1),
        (p.choose s : ℤ) * (inclExclShift d k i) ^ (p - s) *
          weightedBinomSumZ s (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) l

lemma choose_recurrence (a k' : ℕ) :
    (k' : ℤ) * (a.choose k' : ℤ) +
      (↑(k' + 1) : ℤ) * (a.choose (k' + 1) : ℤ) =
      (a : ℤ) * (a.choose k' : ℤ) := by
  have h := Nat.add_one_mul_choose_eq a k'
  have := Nat.choose_succ_succ a k'
  push_cast at *
  nlinarith

/-- Once the window reaches zero, its natural interval stops changing. -/
private lemma weightedBinomSum_eq_of_le (s k' y l : ℕ) (hyl : y ≤ l) :
    weightedBinomSum s k' y (l + 1) = weightedBinomSum s k' y l := by
  unfold weightedBinomSum
  rw [Nat.sub_eq_zero_of_le (by linarith), Nat.sub_eq_zero_of_le (by linarith)]

/-- Extending a window that already reaches zero adds no weighted terms. -/
lemma weightedBinomSum_diff_small (s k' l y : ℕ) (hyl : y ≤ l) :
    (weightedBinomSum s k' y (l + 1) : ℤ) - (weightedBinomSum s k' y l : ℤ) = 0 := by
  rw [weightedBinomSum_eq_of_le s k' y l hyl, sub_self]

/-- The exponent recurrence cast to `ℤ`. -/
private lemma weightedBinomSum_succ_cast (s k' y l : ℕ) :
    (weightedBinomSum (s + 1) k' y l : ℤ) =
      ↑k' * ↑(weightedBinomSum s k' y l) + ↑(k' + 1) * ↑(weightedBinomSum s (k' + 1) y l) := by
  have := weightedBinomSum_succ s k' y l
  norm_cast

/-- Extending the window adds the weighted coefficient at the new endpoint `y-l-1`. -/
lemma weightedBinomSum_diff_power (s k' l y : ℕ) (hyl : y ≥ l + 1) :
    (weightedBinomSum s k' y (l + 1) : ℤ) - (weightedBinomSum s k' y l : ℤ) =
      (↑(y - l - 1) : ℤ) ^ s * (Nat.choose (y - l - 1) k' : ℤ) := by
  induction s generalizing k' l y with
  | zero =>
    convert binomSumZ_step_large k' l y (by linarith) using 1
    grind
  | succ s ih =>
    convert congr_arg₂ (· + ·) (congr_arg (fun x : ℤ => k' * x) (ih k' l y hyl))
      (congr_arg (fun x : ℤ => (k' + 1) * x) (ih (k' + 1) l y hyl)) using 1
    · convert congr_arg₂ (· - ·) (weightedBinomSum_succ_cast s k' y (l + 1))
        (weightedBinomSum_succ_cast s k' y l) using 1
      push_cast
      ring
    · have := choose_recurrence (y - l - 1) k'
      simp_all +decide [pow_succ, mul_assoc, mul_comm]
      grind

lemma weightedBinomSumZ_diff_small (s k' l : ℕ) (m : ℤ) (hml : m ≤ ↑l) :
    weightedBinomSumZ s k' m (l + 1) - weightedBinomSumZ s k' m l = 0 := by
  unfold weightedBinomSumZ
  split_ifs <;> simp_all +decide [weightedBinomSum_eq_of_le]

lemma weightedBinomSumZ_diff_power (s k' l : ℕ) (m : ℤ) (hm : m ≥ ↑l + 1) :
    weightedBinomSumZ s k' m (l + 1) - weightedBinomSumZ s k' m l =
      (↑(m.toNat - l - 1) : ℤ) ^ s * (Nat.choose (m.toNat - l - 1) k' : ℤ) := by
  convert weightedBinomSum_diff_power s k' l m.toNat
    (by linarith [Int.toNat_of_nonneg (by linarith : 0 ≤ m)]) using 1
  unfold weightedBinomSumZ
  split_ifs <;> norm_num
  linarith

lemma weightedBinomSumZ_zero (s c : ℕ) (m : ℤ) :
    weightedBinomSumZ s c m 0 =
      if m < 0 then 0
      else (m.toNat ^ s * m.toNat.choose c : ℤ) := by
  unfold weightedBinomSumZ
  unfold weightedBinomSum
  aesop

lemma rawMoment_step (p n k d l : ℕ) (hk : 0 < k)
    (hl : l + 1 ≤ n) :
    rawMoment p n k d (l + 1) - rawMoment p n k d l =
      (↑(n - l - 1) : ℤ) ^ p * (compCount (n - l - 1) k d : ℤ) := by
  rw [compCount_inclExcl]
  · -- Apply the difference formula to each term in the sum
    have h_diff : ∀ i ∈ Finset.range (inclExclBound n k d + 1),
        ∑ s ∈ Finset.range (p + 1),
          (Nat.choose p s : ℤ) * (inclExclShift d k i) ^ (p - s) *
            (weightedBinomSumZ s (k - 1) (n - ((d + 1) * i) + k - 1) (l + 1) -
              weightedBinomSumZ s (k - 1) (n - ((d + 1) * i) + k - 1) l) =
        if (n : ℤ) - ((d + 1) * i) + k - 1 ≥ l + 1
        then (n - l - 1 : ℤ) ^ p * (Nat.choose (n - l - 1 + k - 1 - (d + 1) * i) (k - 1))
        else 0 := by
      intro i hi
      split_ifs <;> simp_all +decide
      · rw [Finset.sum_congr rfl fun s hs => by rw [weightedBinomSumZ_diff_power]; linarith]
        have h_binom : (n - l - 1 : ℤ) ^ p =
            ∑ s ∈ Finset.range (p + 1), (p.choose s : ℤ) * (inclExclShift d k i) ^ (p - s) *
              ((n - (d + 1) * i + k - 1 - l - 1 : ℤ) ^ s) := by
          rw [show (n - l - 1 : ℤ) = (inclExclShift d k i) + (n - (d + 1) * i + k - 1 - l - 1)
            by unfold inclExclShift; ring]
          rw [add_comm, add_pow]
          congr; ext; ring
        rw [h_binom, Finset.sum_mul _ _ _]
        grind +splitImp
      · refine Finset.sum_eq_zero fun s hs => ?_
        rw [weightedBinomSumZ_diff_small] <;> norm_num
        linarith
    -- Apply the difference formula to each term in the sum and simplify
    have h_sum_diff :
        ∑ i ∈ Finset.range (inclExclBound n k d + 1),
          (-1 : ℤ) ^ i * (k.choose i : ℤ) *
            (if (n : ℤ) - ((d + 1) * i) + k - 1 ≥ l + 1
             then (n - l - 1 : ℤ) ^ p * (Nat.choose (n - l - 1 + k - 1 - (d + 1) * i) (k - 1))
             else 0) =
        (n - l - 1 : ℤ) ^ p *
          ∑ i ∈ Finset.range (inclExclBound (n - l - 1) k d + 1),
            (-1 : ℤ) ^ i * (k.choose i : ℤ) *
              (Nat.choose (n - l - 1 + k - 1 - (d + 1) * i) (k - 1)) := by
      rw [Finset.mul_sum _ _ _, ← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ
        (show inclExclBound (n - l - 1) k d ≤ inclExclBound n k d from _)))]
      · refine Finset.sum_congr rfl fun i hi => ?_
        split_ifs <;> simp_all +decide [mul_assoc, mul_comm, mul_left_comm]
        contrapose! hi
        unfold inclExclBound
        rw [min_lt_iff]
        apply Or.inr
        exact Nat.div_lt_of_lt_mul (by
          rw [mul_comm (d + 1) i]
          zify at *
          rw [Nat.cast_sub (show 1 ≤ n - l by omega)]
          rw [Nat.cast_sub (show l ≤ n by omega)]
          push_cast at *
          omega
        )
      · simp +zetaDelta at *
        intro x hx₁ hx₂ hx₃
        contrapose! hx₂
        simp_all +decide [inclExclBound]
        rw [Nat.le_div_iff_mul_le] <;> norm_num
        by_cases h_case : n - l - 1 + k - 1 - (d + 1) * x ≥ k - 1
        · grind
        · exact False.elim <| hx₂.2.2 <| Nat.choose_eq_zero_of_lt <| lt_of_not_ge h_case
      · exact min_le_min le_rfl (Nat.div_le_div_right (by omega))
    convert h_sum_diff using 1
    · rw [← Finset.sum_congr rfl fun i hi => by rw [← h_diff i hi]]
      simp +decide [rawMoment, mul_sub, Finset.sum_sub_distrib]
    · rw [Nat.cast_sub <| Nat.le_sub_of_add_le <| by linarith, Nat.cast_sub <| by linarith]
      push_cast
      ring
  · grind

/-- Unnormalized power sum over `[n-l,n]` when the window stays nonnegative. -/
theorem rawMoment_eq_sum (p n k d l : ℕ) (hk : 0 < k)
    (hl : l ≤ n) :
    rawMoment p n k d l =
      ∑ j ∈ Finset.range (l + 1), (↑(n - j) : ℤ) ^ p * (compCount (n - j) k d : ℤ) := by
  induction l with
  | zero =>
    unfold rawMoment
    simp +decide [weightedBinomSumZ_zero]
    rw [compCount_inclExcl n k d hk]
    rw [Finset.mul_sum _ _ _]
    refine Finset.sum_congr rfl fun i hi => ?_
    rcases le_or_gt ((d + 1) * i) (n + k - 1) with h | h <;>
      simp_all +decide [Nat.sub_sub, add_comm]
    · split_ifs <;> simp_all +decide
      · grind +qlia
      · rw [show (k + (n - (d + 1) * i) : ℤ).toNat - 1 = n + k - (1 + (d + 1) * i) from ?_]
        · rw [show (n : ℤ) = (n + k - (1 + (d + 1) * i)) + (inclExclShift d k i)
            by unfold inclExclShift; ring]
          rw [add_pow]
          simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _]
          exact Finset.sum_congr rfl fun x hx => by
            rw [Nat.cast_sub (by nlinarith [Nat.sub_add_cancel (by nlinarith : 1 ≤ n + k)])]
            push_cast
            ring
        · grind
    · contrapose! h
      simp only [inclExclBound] at hi
      exact Nat.le_sub_one_of_lt (by
        nlinarith [Nat.div_mul_le_self n (d + 1), min_le_right k (n / (d + 1)),
                   Nat.mul_le_mul_right (d + 1)
                     (Nat.le_trans hi (min_le_right k (n / (d + 1))))])
  | succ l ih =>
    rw [Finset.sum_range_succ, ← ih (Nat.le_of_lt (Nat.lt_of_succ_le hl))]
    convert eq_add_of_sub_eq' (rawMoment_step p n k d l hk (by linarith)) using 1

/-- Weighted binomial windows are stable once the new endpoint lies below the
    binomial coefficient's lower index. -/
private lemma weightedBinomSumZ_step_stable (s c l : ℕ) (m : ℤ)
    (hm : m ≤ (l : ℤ) + c) :
    weightedBinomSumZ s c m (l + 1) = weightedBinomSumZ s c m l := by
  by_cases hsmall : m ≤ (l : ℤ)
  · exact sub_eq_zero.mp (weightedBinomSumZ_diff_small s c l m hsmall)
  · have hlarge : (l : ℤ) + 1 ≤ m := by omega
    have hzero : Nat.choose (m.toNat - l - 1) c = 0 := by
      apply Nat.choose_eq_zero_of_lt
      omega
    have hdiff := weightedBinomSumZ_diff_power s c l m hlarge
    rw [hzero] at hdiff
    simpa using sub_eq_zero.mp hdiff

/-- The raw-moment analytical expression stabilizes after the window reaches zero. -/
lemma rawMoment_step_stable (p n k d l : ℕ) (hk : 0 < k) (hl : n ≤ l) :
    rawMoment p n k d (l + 1) = rawMoment p n k d l := by
  unfold rawMoment
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hm : (n : ℤ) - ((d + 1) * i : ℕ) + k - 1 ≤
      (l : ℤ) + (k - 1 : ℕ) := by omega
  rw [weightedBinomSumZ_step_stable s (k - 1) l _ hm]

theorem rawMoment_eq_at_n (p n k d l : ℕ) (hk : 0 < k) (hl : n ≤ l) :
    rawMoment p n k d l = rawMoment p n k d n := by
  induction l, hl using Nat.le_induction with
  | base => rfl
  | succ l hle ih => rw [rawMoment_step_stable p n k d l hk hle, ih]

/-- Unnormalized power sum over `[n-l,n]`, clipped at zero. -/
theorem rawMoment_eq_sum_clipped (p n k d l : ℕ) (hk : 0 < k) :
    rawMoment p n k d l =
      ∑ j ∈ Finset.range (min l n + 1),
        (↑(n - j) : ℤ) ^ p * (compCount (n - j) k d : ℤ) := by
  by_cases h : l ≤ n
  · simpa [min_eq_left h] using rawMoment_eq_sum p n k d l hk h
  · have hle : n ≤ l := by omega
    rw [rawMoment_eq_at_n p n k d l hk hle]
    simpa [min_eq_right hle] using rawMoment_eq_sum p n k d n hk le_rfl

private def scaledStep (d i : ℕ) : ℤ := ↑((d + 1) * i)

/-- Closed expression for the first unnormalized moment. -/
theorem rawMoment_one (n k d l : ℕ) (hk : 0 < k) :
    rawMoment 1 n k d l =
      ∑ i ∈ Finset.range (inclExclBound n k d + 1),
        (-1 : ℤ) ^ i * (k.choose i : ℤ) *
          (scaledStep d i * binomSumZ (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) l +
           ↑k * binomSumZ k (↑n - ↑((d + 1) * i) + ↑k - 1) l) := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [inclExclShift, scaledStep]
  rcases k with (_ | k) <;> simp_all +decide [range_add_one, mul_assoc, mul_comm]
  rw [weightedBinomSumZ_succ]
  ring_nf
  exact Or.inl (by push_cast [add_comm, binomSumZ]; ring)

/-- Closed expression for the second unnormalized moment. -/
theorem rawMoment_two (n k d l : ℕ) (hk : 0 < k) :
    rawMoment 2 n k d l =
      ∑ i ∈ Finset.range (inclExclBound n k d + 1),
        (-1 : ℤ) ^ i * (k.choose i : ℤ) *
          (scaledStep d i ^ 2 * binomSumZ (k - 1) (↑n - ↑((d + 1) * i) + ↑k - 1) l +
           ↑k * (2 * scaledStep d i + 1) * binomSumZ k (↑n - ↑((d + 1) * i) + ↑k - 1) l +
           ↑k * (↑k + 1) * binomSumZ (k + 1) (↑n - ↑((d + 1) * i) + ↑k - 1) l) := by
  simp +decide [rawMoment, scaledStep, binomSumZ]
  refine Finset.sum_congr rfl fun x hx => congr_arg₂ _ rfl ?_
  norm_num [Finset.sum_range_succ', inclExclShift]
  rcases k with (_ | k) <;> simp_all +decide [weightedBinomSumZ_succ]; ring

/-- The zeroth power-sum expression equals the accumulated-count expression. -/
theorem rawMoment_zero_eq_compCountAcc (n k d l : ℕ) :
    rawMoment 0 n k d l = compCountAcc n k d l := by
  exact Finset.sum_congr rfl fun i hi => by simp +decide [binomSumZ]
