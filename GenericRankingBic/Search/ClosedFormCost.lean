import GenericRankingBic.Search.ColexThreshold
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Asymptotics.Defs

section ClosedFormCost

/-- The inclusion–exclusion formula for an accumulated count. Each outer
summand contains a constant number of binomial expressions. -/
def closedFormAcc (n k d l : Nat) : Int :=
  ∑ i ∈ Finset.range (inclExclBound n k d + 1),
    (-1 : Int) ^ i * (k.choose i : Int) *
      (let m : Int := (n : Int) - ((d + 1) * i : Nat) + (k : Int) - 1
       if m < 0 then 0 else
         ((m.toNat + 1).choose (k - 1 + 1) : Int) -
           ((m.toNat - l).choose (k - 1 + 1) : Int))

/-- The closed expression computes the accumulated count already verified
against the partial sum of composition counts. -/
theorem closedFormAcc_eq_compCountAcc (n k d l : Nat) :
    closedFormAcc n k d l = compCountAcc n k d l := by
  unfold closedFormAcc compCountAcc
  apply Finset.sum_congr rfl
  intro i _
  rw [binomSumZ_eq]

/-- The paper's accumulated sequence starts with zero. Its entry at positive
index `q` is the accumulated count through part `q - 1`. -/
def closedFormPrefix (n k d q : Nat) : Int :=
  if q = 0 then 0 else closedFormAcc n k d (q - 1)

theorem closedFormPrefix_eq (n k d q : Nat) :
    closedFormPrefix n k d q =
      if q = 0 then 0 else compCountAcc n k d (q - 1) := by
  simp [closedFormPrefix, closedFormAcc_eq_compCountAcc]

/-- Adjacent entries in the paper's accumulated sequence are ordered. -/
theorem closedFormPrefix_step (n k d q : Nat) (hk : 0 < k)
    (hq : q < min n d + 1) :
    closedFormPrefix n k d q ≤ closedFormPrefix n k d (q + 1) := by
  cases q with
  | zero =>
      have hzero := compCountAcc_eq_partial_sum n k d 0 hk (Nat.zero_le n)
      simp [closedFormPrefix_eq, hzero]
  | succ l =>
      have hstep := compCountAcc_step n k d l hk (by omega)
      have hnonneg : (0 : Int) ≤ (compCount (n - 1 - l) k d : Int) :=
        Int.natCast_nonneg _
      have hle : compCountAcc n k d l ≤ compCountAcc n k d (l + 1) := by omega
      rw [closedFormPrefix_eq, closedFormPrefix_eq]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      simpa [Nat.succ_eq_add_one] using hle

/-- Monotonicity of the closed-form accumulated sequence on its valid index
range, obtained from the already verified partial-sum identity. -/
theorem closedFormPrefix_mono (n k d a b : Nat) (hk : 0 < k)
    (hab : a ≤ b) (hb : b ≤ min n d + 1) :
    closedFormPrefix n k d a ≤ closedFormPrefix n k d b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ b _ ih =>
      exact (ih (by omega)).trans (closedFormPrefix_step n k d b hk (by omega))

/-- The executable prefix agrees with the colex prefix of the finite-set
counting instance throughout the admissible part range. -/
theorem closedFormPrefix_eq_colexPrefix (n i d p : Nat)
    (hi : 0 < i) (hp : p ≤ min n d + 1) :
    closedFormPrefix n i d p =
      ((colexPrefix (C := finsetInstance) n i d p : Nat) : Int) := by
  cases p with
  | zero => simp [closedFormPrefix, colexPrefix]
  | succ p =>
      have hpn : p ≤ n := by omega
      rw [closedFormPrefix_eq]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel_right]
      exact (colexPrefix_succ_eq_compCountAcc n i d p hi hpn).symm

/-- The number of outer inclusion–exclusion summands evaluated to obtain one
entry of the accumulated sequence. The zero sentinel needs none. -/
def closedFormPrefixTerms (n k d q : Nat) : Nat :=
  if q = 0 then 0 else inclExclBound n k d + 1

/-- Search result, decisions and outer inclusion–exclusion summand evaluations.
The summand count excludes work inside `Nat.choose`, big-integer arithmetic
and list operations; decisions are counted separately. -/
structure ClosedFormRun where
  /-- Selected prefix index. -/
  index : Nat
  /-- Number of midpoint decisions. -/
  decisions : Nat
  /-- Outer inclusion-exclusion summands evaluated at the midpoints. -/
  summandEvaluations : Nat

/-- Binary search for the greatest index `q` with `A(q) ≤ rank` in `[lo, hi)`.
The upper endpoint is a sentinel with `rank < A(hi)`. On an eligible midpoint,
the recursive interval retains that midpoint. The fuel only makes the
recursion structural; the public entry point supplies the initial span. -/
def closedFormSearchFuel (n k d : Nat) (rank : Int) :
    Nat → Nat → Nat → ClosedFormRun
  | 0, lo, _hi => ⟨lo, 0, 0⟩
  | fuel + 1, lo, hi =>
    if hi - lo ≤ 1 then ⟨lo, 0, 0⟩
    else
      let mid := lo + (hi - lo) / 2
      if closedFormPrefix n k d mid ≤ rank then
        let continuation := closedFormSearchFuel n k d rank fuel mid hi
        ⟨continuation.index, continuation.decisions + 1,
          continuation.summandEvaluations + closedFormPrefixTerms n k d mid⟩
      else
        let continuation := closedFormSearchFuel n k d rank fuel lo mid
        ⟨continuation.index, continuation.decisions + 1,
          continuation.summandEvaluations + closedFormPrefixTerms n k d mid⟩

/-- Search the paper's `0, A₀, …, A_(min(n,d))` sequence. The caller's
valid-rank assumption must imply `rank < A_(min(n,d))`. -/
def closedFormSearch (n k d : Nat) (rank : Int) : ClosedFormRun :=
  closedFormSearchFuel n k d rank (min n d + 1) 0 (min n d + 1)

theorem closedFormPrefixTerms_le (n k d q : Nat) :
    closedFormPrefixTerms n k d q ≤ k + 1 := by
  unfold closedFormPrefixTerms
  split_ifs
  · omega
  · have h := min_le_left k (n / (d + 1))
    simp [inclExclBound, Nat.add_le_add_right h 1]

/-- Every decision incurs at most `k + 1` binomial-summand evaluations. -/
theorem closedFormSearchFuel_terms_le_decisions (n k d fuel : Nat)
    (rank : Int) (lo hi : Nat) :
    (closedFormSearchFuel n k d rank fuel lo hi).summandEvaluations ≤
      (k + 1) * (closedFormSearchFuel n k d rank fuel lo hi).decisions := by
  induction fuel generalizing lo hi with
  | zero => simp [closedFormSearchFuel]
  | succ fuel ih =>
    by_cases hspan : hi - lo ≤ 1
    · simp [closedFormSearchFuel, hspan]
    · let mid := lo + (hi - lo) / 2
      by_cases hprobe : closedFormPrefix n k d mid ≤ rank
      · have hrec := ih mid hi
        have hterm := closedFormPrefixTerms_le n k d mid
        have hsum :
            (closedFormSearchFuel n k d rank fuel mid hi).summandEvaluations +
                closedFormPrefixTerms n k d mid ≤
              (k + 1) * ((closedFormSearchFuel n k d rank fuel mid hi).decisions + 1) := by
          calc
            _ ≤ (k + 1) * (closedFormSearchFuel n k d rank fuel mid hi).decisions +
                (k + 1) := Nat.add_le_add hrec hterm
            _ = _ := by ring
        simpa [closedFormSearchFuel, hspan, hprobe, mid] using hsum
      · have hrec := ih lo mid
        have hterm := closedFormPrefixTerms_le n k d mid
        have hsum :
            (closedFormSearchFuel n k d rank fuel lo mid).summandEvaluations +
                closedFormPrefixTerms n k d mid ≤
              (k + 1) * ((closedFormSearchFuel n k d rank fuel lo mid).decisions + 1) := by
          calc
            _ ≤ (k + 1) * (closedFormSearchFuel n k d rank fuel lo mid).decisions +
                (k + 1) := Nat.add_le_add hrec hterm
            _ = _ := by ring
        simpa [closedFormSearchFuel, hspan, hprobe, mid] using hsum

/-- Binary search makes at most `⌈log₂(hi-lo)⌉` decisions. -/
theorem closedFormSearchFuel_decisions_le_clog (n k d fuel : Nat)
    (rank : Int) (lo hi : Nat) :
    (closedFormSearchFuel n k d rank fuel lo hi).decisions ≤
      Nat.clog 2 (hi - lo) := by
  induction fuel generalizing lo hi with
  | zero => simp [closedFormSearchFuel]
  | succ fuel ih =>
    by_cases hspan : hi - lo ≤ 1
    · simp [closedFormSearchFuel, hspan]
    · let mid := lo + (hi - lo) / 2
      have hlog := Nat.clog_of_one_lt (b := 2) (n := hi - lo)
        (by omega) (by omega)
      by_cases hprobe : closedFormPrefix n k d mid ≤ rank
      · have hhalf : hi - mid ≤ (hi - lo + 1) / 2 := by
          dsimp [mid]
          omega
        have hrec := (ih mid hi).trans (Nat.clog_monotone 2 hhalf)
        simpa [closedFormSearchFuel, hspan, hprobe, hlog, mid] using
          Nat.add_le_add_right hrec 1
      · have hhalf : mid - lo ≤ (hi - lo + 1) / 2 := by
          dsimp [mid]
          omega
        have hrec := (ih lo mid).trans (Nat.clog_monotone 2 hhalf)
        simpa [closedFormSearchFuel, hspan, hprobe, hlog, mid] using
          Nat.add_le_add_right hrec 1

/-- Concrete per-part cost: at most `(k + 1) * ⌈log₂(min(n,d)+1)⌉`
outer inclusion–exclusion summands. -/
theorem closedFormSearch_terms_le (n k d : Nat) (rank : Int) :
    (closedFormSearch n k d rank).summandEvaluations ≤
      (k + 1) * Nat.clog 2 (min n d + 1) := by
  have hterms := closedFormSearchFuel_terms_le_decisions n k d
    (min n d + 1) rank 0 (min n d + 1)
  have hdecisions := closedFormSearchFuel_decisions_le_clog n k d
    (min n d + 1) rank 0 (min n d + 1)
  simpa [closedFormSearch] using
    hterms.trans (Nat.mul_le_mul_left (k + 1) hdecisions)

/-- With a valid bracket and enough fuel, the search returns the exact
adjacent threshold: `A(q) ≤ rank < A(q+1)`. The induction uses no monotonicity;
it preserves the two endpoint inequalities directly. -/
theorem closedFormSearchFuel_boundary (n k d fuel lo hi : Nat) (rank : Int)
    (hlo : lo < hi) (hspan : hi - lo ≤ fuel)
    (hloValue : closedFormPrefix n k d lo ≤ rank)
    (hhiValue : rank < closedFormPrefix n k d hi) :
    let q := (closedFormSearchFuel n k d rank fuel lo hi).index
    lo ≤ q ∧ q < hi ∧
      closedFormPrefix n k d q ≤ rank ∧
      rank < closedFormPrefix n k d (q + 1) := by
  induction fuel generalizing lo hi with
  | zero => omega
  | succ fuel ih =>
    by_cases hsmall : hi - lo ≤ 1
    · have hnext : hi = lo + 1 := by omega
      simp only [closedFormSearchFuel, if_pos hsmall]
      exact ⟨Nat.le_refl _, hlo, hloValue, by simpa [hnext] using hhiValue⟩
    · let mid := lo + (hi - lo) / 2
      have hmidlo : lo < mid := by dsimp [mid]; omega
      have hmidhi : mid < hi := by dsimp [mid]; omega
      by_cases hprobe : closedFormPrefix n k d mid ≤ rank
      · have hfuel : hi - mid ≤ fuel := by dsimp [mid] at *; omega
        have hrec := ih mid hi hmidhi hfuel hprobe hhiValue
        rcases hrec with ⟨hql, hqh, hqValue, hqNext⟩
        have hlow : lo ≤ (closedFormSearchFuel n k d rank fuel mid hi).index :=
          le_trans (Nat.le_of_lt hmidlo) hql
        simpa [closedFormSearchFuel, hsmall, hprobe, mid] using
          (show lo ≤ (closedFormSearchFuel n k d rank fuel mid hi).index ∧
            (closedFormSearchFuel n k d rank fuel mid hi).index < hi ∧
            closedFormPrefix n k d (closedFormSearchFuel n k d rank fuel mid hi).index ≤ rank ∧
            rank < closedFormPrefix n k d
              ((closedFormSearchFuel n k d rank fuel mid hi).index + 1)
            from ⟨hlow, hqh, hqValue, hqNext⟩)
      · have hfuel : mid - lo ≤ fuel := by dsimp [mid] at *; omega
        have hrec := ih lo mid hmidlo hfuel hloValue (lt_of_not_ge hprobe)
        rcases hrec with ⟨hql, hqh, hqValue, hqNext⟩
        have hhigh : (closedFormSearchFuel n k d rank fuel lo mid).index < hi :=
          lt_trans hqh hmidhi
        simpa [closedFormSearchFuel, hsmall, hprobe, mid] using
          (show lo ≤ (closedFormSearchFuel n k d rank fuel lo mid).index ∧
            (closedFormSearchFuel n k d rank fuel lo mid).index < hi ∧
            closedFormPrefix n k d (closedFormSearchFuel n k d rank fuel lo mid).index ≤ rank ∧
            rank < closedFormPrefix n k d
              ((closedFormSearchFuel n k d rank fuel lo mid).index + 1)
            from ⟨hql, hhigh, hqValue, hqNext⟩)

/-- A valid rank is bracketed by the zero sentinel and the final accumulated
count. The computed part is precisely the boundary between eligible and
ineligible accumulated entries. -/
theorem closedFormSearch_boundary (n k d : Nat) (rank : Int)
    (hrank : 0 ≤ rank)
    (hvalid : rank < closedFormPrefix n k d (min n d + 1)) :
    let q := (closedFormSearch n k d rank).index
    q < min n d + 1 ∧
      closedFormPrefix n k d q ≤ rank ∧
      rank < closedFormPrefix n k d (q + 1) := by
  have h := closedFormSearchFuel_boundary n k d (min n d + 1) 0
    (min n d + 1) rank (by omega) (by simp)
    (by simpa [closedFormPrefix] using hrank) hvalid
  simpa [closedFormSearch] using h

/-- When the accumulated entries are monotone, the boundary returned by the
search is the greatest entry no larger than the rank. -/
theorem closedFormSearch_maximal (n k d : Nat) (rank : Int)
    (hrank : 0 ≤ rank)
    (hvalid : rank < closedFormPrefix n k d (min n d + 1))
    (hmono : ∀ a b, a ≤ b → b ≤ min n d + 1 →
      closedFormPrefix n k d a ≤ closedFormPrefix n k d b) :
    let q := (closedFormSearch n k d rank).index
    q < min n d + 1 ∧
      closedFormPrefix n k d q ≤ rank ∧
      (∀ j ≤ min n d + 1,
        closedFormPrefix n k d j ≤ rank → j ≤ q) := by
  obtain ⟨hq, hqValue, hnext⟩ :=
    closedFormSearch_boundary n k d rank hrank hvalid
  refine ⟨hq, hqValue, ?_⟩
  intro j hj hjValue
  by_contra hnot
  have hle : (closedFormSearch n k d rank).index + 1 ≤ j := by omega
  have hmonoval := hmono _ _ hle hj
  omega

/-- For a positive number of parts and a rank below the final accumulated
count, the executable closed-form search returns the paper's maximal prefix
threshold. The monotonicity premise of the generic theorem is discharged by
the accumulated-count partial-sum identity. -/
theorem closedFormSearch_maximal_of_accBound (n k d : Nat) (rank : Int)
    (hk : 0 < k) (hrank : 0 ≤ rank)
    (hvalid : rank < compCountAcc n k d (min n d)) :
    let q := (closedFormSearch n k d rank).index
    q < min n d + 1 ∧
      closedFormPrefix n k d q ≤ rank ∧
      (∀ j ≤ min n d + 1,
        closedFormPrefix n k d j ≤ rank → j ≤ q) := by
  apply closedFormSearch_maximal n k d rank hrank
  · simpa [closedFormPrefix_eq] using hvalid
  · intro a b hab hb
    exact closedFormPrefix_mono n k d a b hk hab hb

/-- For every valid colex rank, the costed closed-form search selects the
same last part as the generic colex block search. -/
theorem closedFormSearch_eq_colex_lastPart (n i d r : Nat)
    (hi : 0 < i) (hr : r < compCount n (i + 1) d) :
    (closedFormSearch n i d (r : Int)).index =
      n - (findBlock (C := finsetInstance) n i 1 d (pathDecreasing n) r).1 := by
  obtain ⟨p, r', hp, hfind, hlo, hhi, _⟩ :=
    exists_colex_prefix_threshold (C := finsetInstance) n i d r hr
  have hpp : p + 1 ≤ min n d + 1 := by omega
  have hpValue : closedFormPrefix n i d p ≤ (r : Int) := by
    rw [closedFormPrefix_eq_colexPrefix n i d p hi (by omega)]
    exact_mod_cast hlo
  have hpNext : (r : Int) < closedFormPrefix n i d (p + 1) := by
    rw [closedFormPrefix_eq_colexPrefix n i d (p + 1) hi hpp]
    exact_mod_cast hhi
  have hfinal : (r : Int) < closedFormPrefix n i d (min n d + 1) :=
    lt_of_lt_of_le hpNext
      (closedFormPrefix_mono n i d (p + 1) (min n d + 1) hi hpp (le_refl _))
  obtain ⟨hqBound, hqValue, hmax⟩ :=
    closedFormSearch_maximal n i d (r : Int) (Int.natCast_nonneg _) hfinal
      (fun a b hab hb => closedFormPrefix_mono n i d a b hi hab hb)
  have hp_le_q : p ≤ (closedFormSearch n i d (r : Int)).index :=
    hmax p (by omega) hpValue
  have hq_le_p : (closedFormSearch n i d (r : Int)).index ≤ p := by
    by_contra h
    have hpq : p + 1 ≤ (closedFormSearch n i d (r : Int)).index := by omega
    have hvalue := closedFormPrefix_mono n i d (p + 1)
      (closedFormSearch n i d (r : Int)).index hi hpq (by omega)
    omega
  have hq : (closedFormSearch n i d (r : Int)).index = p := by omega
  rw [hq, hfind]
  omega

open Asymptotics Filter

/-- For `n = d` and fixed positive `k` and rank, the summand count is
`O(k log d)`. The concrete bound above holds uniformly in `n`, `k` and `d`. -/
theorem closedFormSearch_terms_isBigO (k : Nat) (hk : 0 < k) (rank : Int) :
    (fun d : Nat => ((closedFormSearch d k d rank).summandEvaluations : Real))
      =O[atTop] (fun d : Nat => ((k * Nat.clog 2 (d + 2) : Nat) : Real)) := by
  apply isBigO_of_le' (c := 2) atTop
  intro d
  have h := closedFormSearch_terms_le d k d rank
  have htotal : (closedFormSearch d k d rank).summandEvaluations ≤
      2 * (k * Nat.clog 2 (d + 2)) := by
    have hk2 : k + 1 ≤ 2 * k := by omega
    have hprod := Nat.mul_le_mul_right (Nat.clog 2 (d + 2)) hk2
    simp only [min_self] at h
    have hmono : Nat.clog 2 (d + 1) ≤ Nat.clog 2 (d + 2) :=
      Nat.clog_monotone 2 (by omega)
    calc
      _ ≤ (k + 1) * Nat.clog 2 (d + 1) := h
      _ ≤ (k + 1) * Nat.clog 2 (d + 2) := Nat.mul_le_mul_left _ hmono
      _ ≤ (2 * k) * Nat.clog 2 (d + 2) := hprod
      _ = 2 * (k * Nat.clog 2 (d + 2)) := by ring
  simpa using (show
    ((closedFormSearch d k d rank).summandEvaluations : Real) ≤
      2 * ((k * Nat.clog 2 (d + 2) : Nat) : Real) by exact_mod_cast htotal)

end ClosedFormCost
