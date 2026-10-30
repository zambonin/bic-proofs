import GenericRankingBic.Tables.AccumulatedStorage
import GenericRankingBic.Counting.AccumulatedCount

open Finset

/-- The number of integers in a scalar slice, zero for a reversed interval. -/
def scalarSliceLength (lower upper : ℕ) : ℕ := upper + 1 - lower

theorem scalarSliceLength_eq_conditional (lower upper : ℕ) :
    scalarSliceLength lower upper =
      if lower ≤ upper then upper - lower + 1 else 0 := by
  unfold scalarSliceLength
  split_ifs <;> omega

/-- The C metadata test `base <= total < base+length` is exactly membership
in the represented inclusive interval, in non-overflowing integer arithmetic. -/
theorem scalarSlice_contains_iff (lower upper total : ℕ) :
    lower ≤ total ∧ total < lower + scalarSliceLength lower upper ↔
      total ∈ Icc lower upper := by
  simp only [scalarSliceLength, mem_Icc]
  omega

/-- Each tag identifies a distinct scalar, even when different slices share a total. -/
def packedScalarSlots (rows windows : Finset ℕ) (lower upper : ℕ → ℕ → ℕ) :
    Finset (Σ _i : ℕ, Σ _l : ℕ, ℕ) :=
  rows.sigma fun i => windows.sigma fun l => Icc (lower i l) (upper i l)

/-- Exact scalar allocation count for supplied integer metadata endpoints. -/
theorem packedScalarSlots_card (rows windows : Finset ℕ) (lower upper : ℕ → ℕ → ℕ) :
    (packedScalarSlots rows windows lower upper).card =
      ∑ i ∈ rows, ∑ l ∈ windows, scalarSliceLength (lower i l) (upper i l) := by
  simp [packedScalarSlots, card_sigma, Nat.card_Icc, scalarSliceLength]

/-- C-grid allocation: `(k+1)*d` metadata records, scalar rows `1,...,k`,
columns `0,...,d-1`, and a one-word minimum allocation when empty. Byte sizes
are parameters; allocator overhead and allocation failure are excluded. -/
def smallAccAllocatedBytes (k d headerBytes metadataBytes scalarBytes : ℕ)
    (lower upper : ℕ → ℕ → ℕ) : ℕ :=
  headerBytes + (k + 1) * d * metadataBytes +
    max 1 (packedScalarSlots (Icc 1 k) (range d) lower upper).card * scalarBytes

/-- A deterministic endpoint certificate bounds a slice. A rounding/error
allowance can be included in `R`; its validity must be checked separately. -/
theorem scalarSliceLength_le_of_endpoints (lower upper R : ℕ) (μ : ℚ)
    (hlo : μ - R ≤ lower) (hhi : (upper : ℚ) ≤ μ + R) :
    scalarSliceLength lower upper ≤ 2 * R + 1 := by
  have hq : (upper : ℚ) ≤ lower + 2 * (R : ℚ) := by linarith
  have hn : upper ≤ lower + 2 * R := by exact_mod_cast hq
  unfold scalarSliceLength
  omega

/-- Bound allocated scalars from certified integer endpoints. Applying this
to floating C endpoints requires a separate arithmetic/error certificate. -/
theorem packedScalarSlots_card_le_of_endpoints (rows windows : Finset ℕ)
    (lower upper : ℕ → ℕ → ℕ) (mean : ℕ → ℕ → ℚ) (R : ℕ)
    (hlo : ∀ i ∈ rows, ∀ l ∈ windows, mean i l - R ≤ lower i l)
    (hhi : ∀ i ∈ rows, ∀ l ∈ windows, (upper i l : ℚ) ≤ mean i l + R) :
    (packedScalarSlots rows windows lower upper).card ≤
      rows.card * windows.card * (2 * R + 1) := by
  rw [packedScalarSlots_card]
  calc
    _ ≤ ∑ _i ∈ rows, ∑ _l ∈ windows, (2 * R + 1) := by
      apply sum_le_sum; intro i hi
      apply sum_le_sum; intro l hl
      exact scalarSliceLength_le_of_endpoints _ _ R (mean i l)
        (hlo i hi l hl) (hhi i hi l hl)
    _ = _ := by simp [Nat.mul_assoc, Nat.mul_comm]

/-- Value of the C `compute_dir` sum with exclusive length `len`. For a
positive column `len`, its inclusive count window is `len-1`, while the
constructor calls the moment routines with inclusive window `len`. -/
def exclusiveAccumulatedCount (n k d len : ℕ) : ℤ :=
  ∑ a ∈ range (min len (n + 1)), (compCount (n - a) k d : ℤ)

@[simp] theorem exclusiveAccumulatedCount_zero (n k d : ℕ) :
    exclusiveAccumulatedCount n k d 0 = 0 := by
  simp [exclusiveAccumulatedCount]

/-- Exclusive length `l+1` corresponds to inclusive window `l`, not `l+1`. -/
theorem exclusiveAccumulatedCount_succ (n k d l : ℕ) (hk : 0 < k) :
    exclusiveAccumulatedCount n k d (l + 1) = compCountAcc n k d l := by
  rw [compCountAcc_eq_partial_sum_clipped n k d l hk]
  unfold exclusiveAccumulatedCount
  have h : min (l + 1) (n + 1) = min l n + 1 := by omega
  rw [h]

/-- Exact accumulated-window four-sigma coverage, before metadata clipping. -/
theorem accumulated_fourSigma_inside_ge (n k d l i : ℕ)
    (hS : 0 < (BoundedCompAcc n k d l).card) :
    (15 / 16 : ℚ) ≤
      (((BoundedCompAcc n k d l).filter fun z =>
        (partialSumQ z i - accPartialMean n k d l i) ^ 2 ≤
          16 * accPartialVariance n k d l i).card : ℚ) /
        (BoundedCompAcc n k d l).card := by
  exact finite_fourSigma_inside_ge (BoundedCompAcc n k d l)
    (fun z => partialSumQ z i) hS

/-- A stored slice has four-sigma marginal coverage when it contains every
band-selected sample value. Clipping and admissibility must satisfy this
condition; a lower/upper endpoint computation alone does not establish it. -/
theorem accumulated_stored_coverage_of_contains (n k d l i lower upper : ℕ)
    (hS : 0 < (BoundedCompAcc n k d l).card)
    (hcontains : ∀ z ∈ BoundedCompAcc n k d l,
      (partialSumQ z i - accPartialMean n k d l i) ^ 2 ≤
        16 * accPartialVariance n k d l i →
      (lower : ℚ) ≤ partialSumQ z i ∧ partialSumQ z i ≤ upper) :
    (15 / 16 : ℚ) ≤
      (((BoundedCompAcc n k d l).filter fun z =>
        (lower : ℚ) ≤ partialSumQ z i ∧ partialSumQ z i ≤ upper).card : ℚ) /
        (BoundedCompAcc n k d l).card := by
  apply (accumulated_fourSigma_inside_ge n k d l i hS).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_le_card (show
    ((BoundedCompAcc n k d l).filter fun z =>
      (partialSumQ z i - accPartialMean n k d l i) ^ 2 ≤
        16 * accPartialVariance n k d l i) ⊆
    ((BoundedCompAcc n k d l).filter fun z =>
      (lower : ℚ) ≤ partialSumQ z i ∧ partialSumQ z i ≤ upper) from by
      intro z hz
      exact mem_filter.mpr ⟨(mem_filter.mp hz).1,
        hcontains z (mem_filter.mp hz).1 (mem_filter.mp hz).2⟩)

/-- Joint coverage from two marginals on the same sample space, with no
independence assumption. Applying this to cache reads requires their actual
query events under a common law. -/
theorem finite_two_read_coverage {α : Type*} (S : Finset α)
    (A B : α → Prop) [DecidablePred A] [DecidablePred B]
    (hS : 0 < S.card) (pA pB : ℚ)
    (hA : pA ≤ ((S.filter A).card : ℚ) / S.card)
    (hB : pB ≤ ((S.filter B).card : ℚ) / S.card) :
    pA + pB - 1 ≤ ((S.filter fun z => A z ∧ B z).card : ℚ) / S.card := by
  classical
  have hc : (0 : ℚ) < S.card := by exact_mod_cast hS
  have hu : ((S.filter A) ∪ (S.filter B)).card ≤ S.card :=
    card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  have heq := card_union_add_card_inter (S.filter A) (S.filter B)
  have hinter : (S.filter A) ∩ (S.filter B) = (S.filter fun z => A z ∧ B z) := by
    ext z
    simp only [mem_inter, mem_filter]
    tauto
  rw [hinter] at heq
  have hn : (S.filter A).card + (S.filter B).card ≤
      S.card + (S.filter fun z => A z ∧ B z).card := by omega
  have hq : ((S.filter A).card : ℚ) + (S.filter B).card ≤
      S.card + (S.filter fun z => A z ∧ B z).card := by exact_mod_cast hn
  have hAc := (le_div_iff₀ hc).mp hA
  have hBc := (le_div_iff₀ hc).mp hB
  apply (le_div_iff₀ hc).mpr
  nlinarith

/-- An adjacent-prefix pair has coverage at least `7/8` when each read has
marginal coverage at least `15/16` under the same sampling experiment. -/
theorem adjacentPrefix_coverage_of_marginals {α : Type*} (S : Finset α)
    (leftHit rightHit : α → Prop) [DecidablePred leftHit] [DecidablePred rightHit]
    (hS : 0 < S.card)
    (hleft : (15 / 16 : ℚ) ≤ ((S.filter leftHit).card : ℚ) / S.card)
    (hright : (15 / 16 : ℚ) ≤ ((S.filter rightHit).card : ℚ) / S.card) :
    (7 / 8 : ℚ) ≤
      ((S.filter fun z => leftHit z ∧ rightHit z).card : ℚ) / S.card := by
  have h := finite_two_read_coverage S leftHit rightHit hS (15/16) (15/16) hleft hright
  norm_num at h ⊢
  exact h

/-- The inclusive window used by C column 2 has these exact moments at (2,2,3). -/
theorem accumulated_clipping_example_moments :
    (BoundedCompAcc 2 2 3 2).card = 6 ∧
    accPartialMean 2 2 3 2 1 = 2 / 3 ∧
    accPartialVariance 2 2 3 2 1 = 5 / 9 := by decide +kernel

/-- Every sample lies in the exact four-sigma band in this example. -/
theorem accumulated_clipping_example_full_band :
    ((BoundedCompAcc 2 2 3 2).filter fun z =>
      (partialSumQ z 1 - accPartialMean 2 2 3 2 1)^2 ≤
        16 * accPartialVariance 2 2 3 2 1).card = 6 := by decide +kernel

/-- Clipping this slice by `column <= total+1` retains mass `1/2` of the
unconditioned moment law in `[1,2]`. Admissible queries exclude total zero,
and missing entries still use exact fallback, so band mass alone does not
determine the cache-hit rate. -/
theorem accumulated_clipping_example_stored_fraction :
    (((BoundedCompAcc 2 2 3 2).filter fun z =>
      (1 : ℚ) ≤ partialSumQ z 1 ∧ partialSumQ z 1 ≤ 2).card : ℚ) /
      (BoundedCompAcc 2 2 3 2).card = 1 / 2 := by decide +kernel
