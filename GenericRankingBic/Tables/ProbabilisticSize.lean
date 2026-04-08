import GenericRankingBic.Statistics.Variance
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Asymptotics.Defs

/-- A bounded rational statistic has variance at most the square of its bound. -/
theorem finiteVariance_le_sq_of_bdd {α : Type*} (S : Finset α) (f : α → ℚ)
    (d : ℕ) (hf : ∀ z ∈ S, 0 ≤ f z ∧ f z ≤ d) :
    finiteVariance S f ≤ (d : ℚ) ^ 2 := by
  classical
  have hsumsq : (∑ z ∈ S, (f z) ^ 2) ≤ (S.card : ℚ) * (d : ℚ) ^ 2 := by
    calc
      _ ≤ ∑ z ∈ S, (d : ℚ) ^ 2 := by
        apply Finset.sum_le_sum
        intro z hz
        have h := hf z hz
        nlinarith
      _ = (S.card : ℚ) * (d : ℚ) ^ 2 := by simp
  by_cases hS : S.card = 0
  · simp [finiteVariance, finiteMean, hS]
  · have hcard : 0 < (S.card : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hS
    have hdiv : (∑ z ∈ S, (f z) ^ 2) / (S.card : ℚ) ≤ (d : ℚ) ^ 2 := by
      apply (div_le_iff₀ hcard).2
      nlinarith [hsumsq]
    unfold finiteVariance
    nlinarith [sq_nonneg (finiteMean S f)]

/-- The exact variance of the first part is bounded by `d²`. -/
theorem compFirstVariance_le_sq (n k d : ℕ) (hk : 0 < k) :
    finiteVariance (BoundedCompAcc n k d 0)
      (fun z => (z ⟨0, hk⟩ : ℚ)) ≤ (d : ℚ) ^ 2 := by
  apply finiteVariance_le_sq_of_bdd
  intro z hz
  have hz' : z ∈ BoundedComp n k d := by simpa [BoundedCompAcc] using hz
  have hzd : z ⟨0, hk⟩ ≤ d := (Finset.mem_filter.mp hz').2 _
  exact ⟨by positivity, by exact_mod_cast hzd⟩

/-- Every partial-sum variance is bounded by `k d²` in a nonempty
`k`-part composition class. -/
theorem compPartialVariance_le_card_mul_sq (n k d i : ℕ) (hk : 1 < k)
    (hi : i ≤ k) (hS : 0 < (BoundedCompAcc n k d 0).card) :
    compPartialVariance n k d i ≤ (k : ℚ) * (d : ℚ) ^ 2 := by
  let v : ℚ := finiteVariance (BoundedCompAcc n k d 0)
    (fun z => (z ⟨0, by omega⟩ : ℚ))
  have hv0 : 0 ≤ v := finiteVariance_nonneg _ _
  have hvd : v ≤ (d : ℚ) ^ 2 := compFirstVariance_le_sq n k d (by omega)
  rw [compPartialVariance_eq n k d i hk hi hS]
  have hiq : (i : ℚ) ≤ k := by exact_mod_cast hi
  have hkq : (0 : ℚ) < (k : ℚ) - 1 := by
    have : (1 : ℚ) < k := by exact_mod_cast hk
    linarith
  have hki : 0 ≤ (k : ℚ) - i := by linarith
  have hcoef0 : 0 ≤ (i : ℚ) * (k - i) / (k - 1) := by
    apply div_nonneg
    · exact mul_nonneg (by positivity) hki
    · linarith
  have hcoef : (i : ℚ) * (k - i) / (k - 1) ≤ k := by
    by_cases hzero : i = 0
    · simp [hzero]
    · have hi1 : (1 : ℚ) ≤ i := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
      have hsub : (k : ℚ) - i ≤ k - 1 := by linarith
      have hprod : (i : ℚ) * ((k : ℚ) - i) ≤ k * ((k : ℚ) - 1) := by
        calc
          _ ≤ (k : ℚ) * (k - i) := mul_le_mul_of_nonneg_right hiq hki
          _ ≤ (k : ℚ) * (k - 1) := mul_le_mul_of_nonneg_left hsub (by positivity)
      rw [div_le_iff₀ hkq]
      exact hprod
  nlinarith [mul_le_mul_of_nonneg_left hvd hcoef0,
    mul_le_mul_of_nonneg_right hcoef hv0]

/-- The same variance bound holds for an empty composition class, where the
finite-sample statistic is defined to be zero. -/
theorem compPartialVariance_le_card_mul_sq_all (n k d i : ℕ) (hk : 1 < k)
    (hi : i ≤ k) :
    compPartialVariance n k d i ≤ (k : ℚ) * (d : ℚ) ^ 2 := by
  by_cases hS : 0 < (BoundedCompAcc n k d 0).card
  · exact compPartialVariance_le_card_mul_sq n k d i hk hi hS
  · have hempty : BoundedCompAcc n k d 0 = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hS)
    simp [compPartialVariance, finiteVariance, finiteMean, hempty]
    positivity

/-- Number of cells satisfying the exact statistical predicate in one row. -/
def retainedBandRow (n k d c i : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter
    (fun j => inStatisticalBand (compPartialMean n k d)
      (compPartialVariance n k d) c i j)

/-- Number of retained count values in the exact statistical band. This
counts values independently of any Gaussian approximation or coverage rate. -/
def retainedBandCells (n k d c : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), (retainedBandRow n k d c i).card

/-- Membership in the counted set is exactly presence of an entry in the
reference count table. The table's outer list still allocates every slot. -/
theorem mem_retainedBandRow_iff_present (n k d c i j : ℕ) (hi : i ≤ k) (hj : j ≤ n) :
    j ∈ retainedBandRow n k d c i ↔
      probCombLookup (probCombTableFromCompositions n k d c) i j ≠ none := by
  rw [probCombTableFromCompositions_lookup n k d c i j hi hj]
  simp [retainedBandRow, hj]

/-- The accumulated table retains precisely the same cell positions. Its
present values are complete accumulated sequences rather than single counts. -/
theorem mem_retainedBandRow_iff_acc_present (n k d c i j : ℕ) (hi : i ≤ k)
    (hj : j ≤ n) :
    j ∈ retainedBandRow n k d c i ↔
      probAccLookup (probAccTableFromCompositions n k d c) i j ≠ none := by
  rw [probAccTableFromCompositions_lookup n k d c i j hi hj]
  simp [retainedBandRow, hj]

/-- An integer finite set of diameter at most `w` has at most `w+1` elements. -/
private theorem card_le_diameter_add_one (s : Finset ℕ) (w : ℕ)
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≤ b + w ∧ b ≤ a + w) :
    s.card ≤ w + 1 := by
  classical
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    have ha : a ∈ s := Finset.min'_mem s hs
    have hsubset : s ⊆ Finset.Icc a (a + w) := by
      intro b hb
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le s b hb, (h a ha b hb).2⟩
    have hc := Finset.card_le_card hsubset
    simp only [Nat.card_Icc] at hc
    omega
  · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [this]

/-- The integer square root rounded upward has square at least `k`. -/
private theorem le_sqrt_add_one_sq (k : ℕ) :
    k ≤ (Nat.sqrt k + 1) ^ 2 := by
  have h := Nat.sqrt_le_add k
  nlinarith

/-- A retained row has width at most a constant times `sqrt k`, uniformly in
the total `n`. The constant depends only on fixed `c` and `d`. -/
theorem retainedBandRow_card_le (n k d c i : ℕ) (hk : 1 < k) (hi : i ≤ k) :
    (retainedBandRow n k d c i).card ≤
      2 * c * d * (Nat.sqrt k + 1) + 1 := by
  let R : ℕ := c * d * (Nat.sqrt k + 1)
  have hvar := compPartialVariance_le_card_mul_sq_all n k d i hk hi
  have hkroot : (k : ℚ) ≤ (((Nat.sqrt k + 1 : ℕ) : ℚ)) ^ 2 := by
    exact_mod_cast le_sqrt_add_one_sq k
  have hbound : (c : ℚ) ^ 2 * compPartialVariance n k d i ≤ (R : ℚ) ^ 2 := by
    calc
      _ ≤ (c : ℚ) ^ 2 * ((k : ℚ) * (d : ℚ) ^ 2) :=
        mul_le_mul_of_nonneg_left hvar (sq_nonneg _)
      _ ≤ (c : ℚ) ^ 2 *
          ((((Nat.sqrt k + 1 : ℕ) : ℚ)) ^ 2 * (d : ℚ) ^ 2) := by
        gcongr
      _ = (R : ℚ) ^ 2 := by dsimp [R]; push_cast; ring
  have hmem (j : ℕ) (hj : j ∈ retainedBandRow n k d c i) :
      |(j : ℚ) - compPartialMean n k d i| ≤ R := by
    have hj' : inStatisticalBand (compPartialMean n k d)
        (compPartialVariance n k d) c i j = true :=
      (Finset.mem_filter.mp hj).2
    have hsq := (inStatisticalBand_iff _ _ c i j).mp hj'
    have hsq' : ((j : ℚ) - compPartialMean n k d i) ^ 2 ≤ (R : ℚ) ^ 2 :=
      hsq.trans hbound
    rw [← sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _), sq_abs]
    exact hsq'
  have hdiam : ∀ a ∈ retainedBandRow n k d c i,
      ∀ b ∈ retainedBandRow n k d c i,
        a ≤ b + 2 * R ∧ b ≤ a + 2 * R := by
    intro a ha b hb
    have h₁ := abs_le.mp (hmem a ha)
    have h₂ := abs_le.mp (hmem b hb)
    constructor
    · have hq : (a : ℚ) ≤ b + 2 * (R : ℚ) := by linarith
      exact_mod_cast hq
    · have hq : (b : ℚ) ≤ a + 2 * (R : ℚ) := by linarith
      exact_mod_cast hq
  have hc := card_le_diameter_add_one _ (2 * R) hdiam
  convert hc using 1
  dsimp [R]
  ring

/-- For `k ≥ 2`, the count of retained entries is bounded uniformly in `n`.
The outer dense `List (List (Option Nat))` still has `(k+1)(n+1)` slots. -/
theorem retainedBandCells_le (n k d c : ℕ) (hk : 1 < k) :
    retainedBandCells n k d c ≤
      (k + 1) * (2 * c * d * (Nat.sqrt k + 1) + 1) := by
  unfold retainedBandCells
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        (2 * c * d * (Nat.sqrt k + 1) + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact retainedBandRow_card_le n k d c i hk (by simpa using hi)
    _ = (k + 1) * (2 * c * d * (Nat.sqrt k + 1) + 1) := by simp

/-- A real square-root bound with a constant depending only on `c` and `d`. -/
theorem retainedBandCells_le_real (n k d c : ℕ) (hk : 1 < k) :
    (retainedBandCells n k d c : ℝ) ≤
      (4 * (2 * c * d + 1 : ℕ) : ℝ) * (k : ℝ) * Real.sqrt k := by
  have hrow : 2 * c * d * (Nat.sqrt k + 1) + 1 ≤
      (2 * c * d + 1) * (Nat.sqrt k + 1) := by
    have ht : 1 ≤ Nat.sqrt k + 1 := by omega
    calc
      _ ≤ 2 * c * d * (Nat.sqrt k + 1) + (Nat.sqrt k + 1) := by omega
      _ = (2 * c * d + 1) * (Nat.sqrt k + 1) := by ring
  have hnat : retainedBandCells n k d c ≤
      (k + 1) * (2 * c * d + 1) * (Nat.sqrt k + 1) := by
    calc
      _ ≤ (k + 1) * (2 * c * d * (Nat.sqrt k + 1) + 1) :=
        retainedBandCells_le n k d c hk
      _ ≤ (k + 1) * ((2 * c * d + 1) * (Nat.sqrt k + 1)) :=
        Nat.mul_le_mul_left _ hrow
      _ = _ := by ring
  have hcast : (retainedBandCells n k d c : ℝ) ≤
      (k + 1 : ℕ) * (2 * c * d + 1 : ℕ) * (Nat.sqrt k + 1 : ℕ) := by
    exact_mod_cast hnat
  have hk2 : ((k + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
    exact_mod_cast (show k + 1 ≤ 2 * k by omega)
  have hroot : (((Nat.sqrt k + 1 : ℕ) : ℝ)) ≤ 2 * Real.sqrt k := by
    have hs := Real.nat_sqrt_le_real_sqrt (a := k)
    have hs1 : (1 : ℝ) ≤ Real.sqrt k := by
      calc
        (1 : ℝ) = Real.sqrt 1 := by simp
        _ ≤ Real.sqrt k := Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ k by omega))
    push_cast
    linarith
  calc
    _ ≤ ((k + 1 : ℕ) : ℝ) * ((2 * c * d + 1 : ℕ) : ℝ) *
        (((Nat.sqrt k + 1 : ℕ) : ℝ)) := hcast
    _ ≤ (2 * (k : ℝ)) * ((2 * c * d + 1 : ℕ) : ℝ) *
        (2 * Real.sqrt k) := by gcongr
    _ = (4 * (2 * c * d + 1 : ℕ) : ℝ) * (k : ℝ) * Real.sqrt k := by
      push_cast
      ring

open Asymptotics Filter

/-- The number of retained values is `O(k sqrt k)` as `k → ∞`, uniformly
for any choice of total `n(k)`, with `d` and `c` fixed. This is not an
allocated-memory bound for the dense list-of-options representation. -/
theorem retainedBandCells_isBigO (nSeq : ℕ → ℕ) (d c : ℕ) :
    (fun k : ℕ => (retainedBandCells (nSeq k) k d c : ℝ))
      =O[atTop] (fun k : ℕ => (k : ℝ) * Real.sqrt k) := by
  apply IsBigO.of_bound (4 * ((2 * c * d + 1 : ℕ) : ℝ))
  filter_upwards [eventually_ge_atTop 2] with k hk
  have h := retainedBandCells_le_real (nSeq k) k d c hk
  have hleft : 0 ≤ (retainedBandCells (nSeq k) k d c : ℝ) := Nat.cast_nonneg _
  have hright : 0 ≤ (k : ℝ) * Real.sqrt k :=
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright,
    mul_assoc] using h
