import GenericRankingBic.Statistics.Conditional
import GenericRankingBic.Statistics.RealBand
import Mathlib.Tactic

/-- First nonnegative integer at or above the real lower endpoint. -/
noncomputable def naturalLowerCut (lower : ℝ) : ℕ := (⌈lower⌉ : ℤ).toNat

/-- First nonnegative integer strictly above the real upper endpoint. -/
noncomputable def naturalUpperCut (upper : ℝ) : ℕ := ((⌊upper⌋ : ℤ) + 1).toNat

theorem naturalLowerCut_le_iff (lower : ℝ) (s : ℕ) :
    naturalLowerCut lower ≤ s ↔ lower ≤ (s : ℝ) := by
  rw [naturalLowerCut, Int.toNat_le, Int.ceil_le]
  norm_cast

theorem lt_naturalUpperCut_iff (upper : ℝ) (s : ℕ) :
    s < naturalUpperCut upper ↔ (s : ℝ) ≤ upper := by
  rw [naturalUpperCut, Int.lt_toNat]
  have h : (s : ℤ) < ⌊upper⌋ + 1 ↔ (s : ℤ) ≤ ⌊upper⌋ := by omega
  rw [h, Int.le_floor]
  norm_cast

theorem naturalLowerCut_le_naturalUpperCut
    (lower upper : ℝ) (h : lower ≤ upper) :
    naturalLowerCut lower ≤ naturalUpperCut upper := by
  apply Int.toNat_le_toNat
  apply Int.ceil_le.mpr
  have hu := Int.lt_floor_add_one upper
  norm_cast at hu ⊢
  linarith

/-- Real radius of the paper's `c = 4` partial-sum band. -/
noncomputable def fourSigmaRadius (n k d i : ℕ) : ℝ :=
  4 * Real.sqrt (compPartialVariance n k d i : ℝ)

/-- First retained integer in the paper's closed real band, clipped at zero. -/
noncomputable def fourSigmaLowerCut (n k d i : ℕ) : ℕ :=
  naturalLowerCut ((compPartialMean n k d i : ℝ) - fourSigmaRadius n k d i)

/-- Exclusive upper cut for the paper's closed real band. -/
noncomputable def fourSigmaUpperCut (n k d i : ℕ) : ℕ :=
  naturalUpperCut ((compPartialMean n k d i : ℝ) + fourSigmaRadius n k d i)

theorem fourSigmaLowerCut_le_upperCut (n k d i : ℕ) :
    fourSigmaLowerCut n k d i ≤ fourSigmaUpperCut n k d i := by
  unfold fourSigmaLowerCut fourSigmaUpperCut
  apply naturalLowerCut_le_naturalUpperCut
  have hr : 0 ≤ fourSigmaRadius n k d i := by
    unfold fourSigmaRadius
    positivity
  linarith

/-- Exactly the retained integer cells of the table's squared predicate. -/
theorem compositionFourSigmaBand_iff_interval (n k d i s : ℕ) :
    inStatisticalBand (compPartialMean n k d) (compPartialVariance n k d)
      4 i s = true ↔
      fourSigmaLowerCut n k d i ≤ s ∧ s < fourSigmaUpperCut n k d i := by
  rw [compositionBand_iff_abs_le_sqrt]
  have hlow := naturalLowerCut_le_iff
    ((compPartialMean n k d i : ℝ) - fourSigmaRadius n k d i) s
  have hhigh := lt_naturalUpperCut_iff
    ((compPartialMean n k d i : ℝ) + fourSigmaRadius n k d i) s
  change fourSigmaLowerCut n k d i ≤ s ↔
      (compPartialMean n k d i : ℝ) - fourSigmaRadius n k d i ≤ s at hlow
  change s < fourSigmaUpperCut n k d i ↔
      (s : ℝ) ≤ (compPartialMean n k d i : ℝ) + fourSigmaRadius n k d i at hhigh
  constructor
  · intro h
    have habs := (abs_le.mp h)
    simp only [Nat.cast_ofNat] at habs
    constructor
    · apply hlow.mpr
      unfold fourSigmaRadius
      linarith [habs.1]
    · apply hhigh.mpr
      unfold fourSigmaRadius
      linarith [habs.2]
  · rintro ⟨hlo, hhi⟩
    apply abs_le.mpr
    have hl := hlow.mp hlo
    have hh := hhigh.mp hhi
    constructor <;> unfold fourSigmaRadius at * <;>
      simp only [Nat.cast_ofNat] <;> linarith

/-- All retained integer values in the `c = 4` row. The upper cut itself is
excluded, because the paper's band has an inclusive real upper endpoint. -/
noncomputable def fourSigmaRetainedValues (n k d i : ℕ) : Finset ℕ :=
  (Finset.range (fourSigmaUpperCut n k d i)).filter
    (fun s => inStatisticalBand (compPartialMean n k d)
      (compPartialVariance n k d) 4 i s = true)

theorem fourSigmaRetainedValues_eq_Ico (n k d i : ℕ) :
    fourSigmaRetainedValues n k d i =
      Finset.Ico (fourSigmaLowerCut n k d i)
        (fourSigmaUpperCut n k d i) := by
  ext s
  simp only [fourSigmaRetainedValues, Finset.mem_filter, Finset.mem_range,
    Finset.mem_Ico, compositionFourSigmaBand_iff_interval]
  tauto

/-- Exact probability mass retained by the paper's `c = 4` row, using the
conditional partial-sum law on uniform fixed-total compositions. -/
noncomputable def conditionalFourSigmaMass (n j t d : ℕ)
    (hcount : 0 < compCount n (j + t) d) : ℝ :=
  ∑ s ∈ fourSigmaRetainedValues n (j + t) d j,
    conditionalPartialSumMassReal n j t d hcount s

theorem conditionalFourSigmaMass_eq_interval (n j t d : ℕ)
    (hcount : 0 < compCount n (j + t) d) :
    conditionalFourSigmaMass n j t d hcount =
      conditionalPartialSumBandMass n j t d hcount
        (fourSigmaLowerCut n (j + t) d j)
        (fourSigmaUpperCut n (j + t) d j) := by
  rw [conditionalFourSigmaMass, fourSigmaRetainedValues_eq_Ico]
  rfl

/-- The Gaussian reference uses the very same finite-sample variance as the
four-sigma radius. -/
noncomputable def fourSigmaVarianceNNReal (n k d i : ℕ) : NNReal :=
  ⟨(compPartialVariance n k d i : ℝ), by
    exact_mod_cast compPartialVariance_nonneg n k d i⟩

theorem fourSigmaVarianceNNReal_coe (n k d i : ℕ) :
    (fourSigmaVarianceNNReal n k d i : ℝ) =
      (compPartialVariance n k d i : ℝ) := rfl

/-- The Gaussian CDF transfer theorem applies directly to the paper's
retained `c = 4` cells. Both endpoint approximation bounds and the Gaussian
reference-band mass remain explicit premises. -/
theorem conditionalFourSigmaMass_coverage_of_gaussian_approx (n j t d : ℕ)
    (hcount : 0 < compCount n (j + t) d) (ε : ℝ)
    (hlo : |conditionalPartialSumCDFCut n j t d hcount
      (fourSigmaLowerCut n (j + t) d j) -
      gaussianCDFCut (compPartialMean n (j + t) d j : ℝ)
        (fourSigmaVarianceNNReal n (j + t) d j)
        (fourSigmaLowerCut n (j + t) d j)| ≤ ε)
    (hhi : |conditionalPartialSumCDFCut n j t d hcount
      (fourSigmaUpperCut n (j + t) d j) -
      gaussianCDFCut (compPartialMean n (j + t) d j : ℝ)
        (fourSigmaVarianceNNReal n (j + t) d j)
        (fourSigmaUpperCut n (j + t) d j)| ≤ ε)
    (hgauss : (99993 : ℝ) / 100000 ≤
      gaussianCDFCut (compPartialMean n (j + t) d j : ℝ)
        (fourSigmaVarianceNNReal n (j + t) d j)
        (fourSigmaUpperCut n (j + t) d j) -
      gaussianCDFCut (compPartialMean n (j + t) d j : ℝ)
        (fourSigmaVarianceNNReal n (j + t) d j)
        (fourSigmaLowerCut n (j + t) d j)) :
    (99993 : ℝ) / 100000 - 2 * ε ≤
      conditionalFourSigmaMass n j t d hcount := by
  rw [conditionalFourSigmaMass_eq_interval]
  exact conditionalPartialSumBand_99993_of_gaussian_approx n j t d
    hcount (compPartialMean n (j + t) d j : ℝ)
    (fourSigmaVarianceNNReal n (j + t) d j)
    (fourSigmaLowerCut n (j + t) d j)
    (fourSigmaUpperCut n (j + t) d j)
    (fourSigmaLowerCut_le_upperCut n (j + t) d j)
    ε hlo hhi hgauss
