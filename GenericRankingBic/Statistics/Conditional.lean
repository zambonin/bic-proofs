import GenericRankingBic.Counting.Convolution
import GenericRankingBic.Statistics.PartialSums
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

private theorem mem_boundedComp_iff (n k d : ℕ) (z : Fin k → ℕ) :
    z ∈ BoundedComp n k d ↔
      (∑ a, z a) = n ∧ ∀ a, z a ≤ d := by
  simp [BoundedComp, Finset.Nat.mem_antidiagonalTuple]

/-- Compositions whose first `j` parts sum to `s`. -/
def partialSumFiber (n j t d s : ℕ) : Finset (Fin (j + t) → ℕ) :=
  (BoundedComp n (j + t) d).filter
    (fun z => ∑ a : Fin j, z (Fin.castAdd t a) = s)

private theorem append_pair_injective (j t : ℕ) :
    Function.Injective (fun z : (Fin j → ℕ) × (Fin t → ℕ) =>
      Fin.append z.1 z.2) := by
  intro a b h
  have hleft : a.1 = b.1 := by
    funext i
    have h' := congrFun h (Fin.castAdd t i)
    simpa using h'
  have hright : a.2 = b.2 := by
    funext i
    have h' := congrFun h (Fin.natAdd j i)
    simpa using h'
  exact Prod.ext hleft hright

private theorem append_restrict (j t : ℕ) (z : Fin (j + t) → ℕ) :
    Fin.append (fun a : Fin j => z (Fin.castAdd t a))
      (fun a : Fin t => z (Fin.natAdd j a)) = z := by
  funext a
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;> simp

/-- `partialSumQ` agrees with the sum over the first `j` coordinates. -/
theorem partialSumQ_eq_firstSum (j t : ℕ) (z : Fin (j + t) → ℕ) :
    partialSumQ z j =
      ∑ i : Fin j, (z (Fin.castAdd t i) : ℚ) := by
  unfold partialSumQ
  refine Finset.sum_bij
    (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin j))
    ?_ ?_ ?_ ?_
  · intro i hi
    simp
  · intro i hi i' hi' heq
    exact Fin.ext (congrArg (fun x : Fin j => x.val) heq)
  · intro b hb
    refine ⟨Fin.castAdd t b, ?_, ?_⟩
    · simp
    · apply Fin.ext
      rfl
  · intro i hi
    congr 1

theorem partialSumFiber_card (n j t d s : ℕ) (hs : s ≤ n) :
    (partialSumFiber n j t d s).card =
      compCount s j d * compCount (n - s) t d := by
  have hset : partialSumFiber n j t d s =
      ((BoundedComp s j d).product (BoundedComp (n - s) t d)).image
        (fun z => Fin.append z.1 z.2) := by
    ext z
    simp only [partialSumFiber, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hz, hfirst⟩
      let a : Fin j → ℕ := fun i => z (Fin.castAdd t i)
      let b : Fin t → ℕ := fun i => z (Fin.natAdd j i)
      have hzb := (mem_boundedComp_iff n (j + t) d z).mp hz
      have hsum : (∑ i, b i) = n - s := by
        have hsplit : (∑ i, a i) + (∑ i, b i) = n := by
          rw [← Fin.sum_univ_add]
          exact hzb.1
        have ha_sum : (∑ i, a i) = s := hfirst
        omega
      refine ⟨(a, b), ?_, ?_⟩
      · apply Finset.mem_product.mpr
        constructor
        · apply (mem_boundedComp_iff s j d a).mpr
          exact ⟨hfirst, fun i => hzb.2 (Fin.castAdd t i)⟩
        · apply (mem_boundedComp_iff (n - s) t d b).mpr
          exact ⟨hsum, fun i => hzb.2 (Fin.natAdd j i)⟩
      · exact append_restrict j t z
    · rintro ⟨⟨a, b⟩, hpair, rfl⟩
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hpair
      have ha' := (mem_boundedComp_iff s j d a).mp ha
      have hb' := (mem_boundedComp_iff (n - s) t d b).mp hb
      constructor
      · apply (mem_boundedComp_iff n (j + t) d (Fin.append a b)).mpr
        constructor
        · rw [Fin.sum_univ_add]
          simp only [Fin.append_left, Fin.append_right]
          omega
        · intro i
          refine Fin.addCases (fun x => ?_) (fun x => ?_) i <;> simp [ha'.2, hb'.2]
      · simpa using ha'.1
  rw [hset, Finset.card_image_of_injective _ (append_pair_injective j t)]
  simp [compCount, Finset.card_product]

/-- Partial-sum law of a uniform bounded composition conditioned on total `n`.
The positive count supplies a nonempty sample space. -/
noncomputable def conditionalPartialSumLaw (n j t d : ℕ)
    (hcount : 0 < compCount n (j + t) d) : PMF ℕ :=
  (PMF.uniformOfFinset (BoundedComp n (j + t) d)
    (Finset.card_pos.mp hcount)).map
      (fun z => ∑ a : Fin j, z (Fin.castAdd t a))

theorem conditionalPartialSumLaw_apply (n j t d s : ℕ)
    (hcount : 0 < compCount n (j + t) d) (hs : s ≤ n) :
    conditionalPartialSumLaw n j t d hcount s =
      (compCount s j d * compCount (n - s) t d : ENNReal) /
        (compCount n (j + t) d : ENNReal) := by
  unfold conditionalPartialSumLaw
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  change (↑(partialSumFiber n j t d s).card : ENNReal) /
      (compCount n (j + t) d : ENNReal) = _
  rw [partialSumFiber_card n j t d s hs]
  norm_cast

theorem conditionalPartialSumLaw_apply_gt (n j t d s : ℕ)
    (hcount : 0 < compCount n (j + t) d) (hs : n < s) :
    conditionalPartialSumLaw n j t d hcount s = 0 := by
  unfold conditionalPartialSumLaw
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  have hempty : partialSumFiber n j t d s = ∅ := by
    ext z
    constructor
    · intro hz
      have h := (mem_boundedComp_iff n (j + t) d z).mp
        (Finset.mem_filter.mp hz).1
      have hsplit := Fin.sum_univ_add z
      have hfirst := (Finset.mem_filter.mp hz).2
      omega
    · intro hz
      simp at hz
  change (↑(partialSumFiber n j t d s).card : ENNReal) /
      (compCount n (j + t) d : ENNReal) = 0
  rw [hempty]
  simp

/-- The real mass of the exact conditional law. -/
noncomputable def conditionalPartialSumMassReal (n j t d : ℕ)
    (hcount : 0 < compCount n (j + t) d) (s : ℕ) : ℝ :=
  (conditionalPartialSumLaw n j t d hcount s).toReal

/-- Exact CDF at an integer cut: probability that `S_j < cut`. -/
noncomputable def conditionalPartialSumCDFCut (n j t d : ℕ)
    (hcount : 0 < compCount n (j + t) d) (cut : ℕ) : ℝ :=
  ∑ s ∈ Finset.range cut, conditionalPartialSumMassReal n j t d hcount s

/-- Exact mass of the integer band `[lo, hi)`. -/
noncomputable def conditionalPartialSumBandMass (n j t d : ℕ)
    (hcount : 0 < compCount n (j + t) d) (lo hi : ℕ) : ℝ :=
  ∑ s ∈ Finset.Ico lo hi, conditionalPartialSumMassReal n j t d hcount s

theorem conditionalPartialSumBandMass_eq_cdf_sub (n j t d : ℕ)
    (hcount : 0 < compCount n (j + t) d)
    (lo hi : ℕ) (hlohi : lo ≤ hi) :
    conditionalPartialSumBandMass n j t d hcount lo hi =
      conditionalPartialSumCDFCut n j t d hcount hi -
        conditionalPartialSumCDFCut n j t d hcount lo := by
  exact Finset.sum_Ico_eq_sub _ hlohi

/-- Gaussian CDF at a cut between adjacent integers, using the usual
half-integer continuity correction. A positive variance is needed for the
Gaussian interpretation of this expression. -/
noncomputable def gaussianCDFCut (mean : ℝ) (variance : NNReal) (cut : ℕ) : ℝ :=
  ((ProbabilityTheory.gaussianReal mean variance)
    (Set.Iio ((cut : ℝ) - 1 / 2))).toReal

/-- Two endpoint CDF errors of at most `ε` give a band-mass error of at most
`2ε`. The approximation bounds are premises, not a conditional limit theorem. -/
theorem conditionalPartialSumBand_gaussian_error_le (n j t d : ℕ)
    (hcount : 0 < compCount n (j + t) d)
    (mean : ℝ) (variance : NNReal) (lo hi : ℕ) (hlohi : lo ≤ hi)
    (ε : ℝ)
    (hlo : |conditionalPartialSumCDFCut n j t d hcount lo -
      gaussianCDFCut mean variance lo| ≤ ε)
    (hhi : |conditionalPartialSumCDFCut n j t d hcount hi -
      gaussianCDFCut mean variance hi| ≤ ε) :
    |conditionalPartialSumBandMass n j t d hcount lo hi -
      (gaussianCDFCut mean variance hi - gaussianCDFCut mean variance lo)| ≤
        2 * ε := by
  rw [conditionalPartialSumBandMass_eq_cdf_sub n j t d hcount lo hi hlohi]
  calc
    |(conditionalPartialSumCDFCut n j t d hcount hi -
       conditionalPartialSumCDFCut n j t d hcount lo) -
       (gaussianCDFCut mean variance hi - gaussianCDFCut mean variance lo)| =
      |(conditionalPartialSumCDFCut n j t d hcount hi - gaussianCDFCut mean variance hi) -
        (conditionalPartialSumCDFCut n j t d hcount lo - gaussianCDFCut mean variance lo)| := by
          congr 1
          ring
    _ ≤ |conditionalPartialSumCDFCut n j t d hcount hi -
          gaussianCDFCut mean variance hi| +
        |conditionalPartialSumCDFCut n j t d hcount lo -
          gaussianCDFCut mean variance lo| := by
            let a : ℝ := conditionalPartialSumCDFCut n j t d hcount hi -
              gaussianCDFCut mean variance hi
            let b : ℝ := conditionalPartialSumCDFCut n j t d hcount lo -
              gaussianCDFCut mean variance lo
            change |a - b| ≤ |a| + |b|
            simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
    _ ≤ 2 * ε := by linarith

/-- If a Gaussian reference band has mass at least `1 - δ`, and the exact
conditional CDF differs by at most `ε` at each endpoint, the discrete band
has mass at least `1 - δ - 2ε`. This is the finite-parameter coverage
statement needed before specializing to a four-standard-deviation band. -/
theorem conditionalPartialSumBand_coverage_of_gaussian_approx (n j t d : ℕ)
    (hcount : 0 < compCount n (j + t) d)
    (mean : ℝ) (variance : NNReal) (lo hi : ℕ) (hlohi : lo ≤ hi)
    (ε δ : ℝ)
    (hlo : |conditionalPartialSumCDFCut n j t d hcount lo -
      gaussianCDFCut mean variance lo| ≤ ε)
    (hhi : |conditionalPartialSumCDFCut n j t d hcount hi -
      gaussianCDFCut mean variance hi| ≤ ε)
    (hgauss : 1 - δ ≤
      gaussianCDFCut mean variance hi - gaussianCDFCut mean variance lo) :
    1 - δ - 2 * ε ≤
      conditionalPartialSumBandMass n j t d hcount lo hi := by
  have h := conditionalPartialSumBand_gaussian_error_le n j t d hcount
    mean variance lo hi hlohi ε hlo hhi
  have hlower := (abs_le.mp h).1
  linarith

/-- Transfer the paper's numerical target using an assumed Gaussian band
mass and two endpoint CDF errors. A total-count coefficient estimate alone
does not supply these hypotheses. -/
theorem conditionalPartialSumBand_99993_of_gaussian_approx (n j t d : ℕ)
    (hcount : 0 < compCount n (j + t) d)
    (mean : ℝ) (variance : NNReal) (lo hi : ℕ) (hlohi : lo ≤ hi)
    (ε : ℝ)
    (hlo : |conditionalPartialSumCDFCut n j t d hcount lo -
      gaussianCDFCut mean variance lo| ≤ ε)
    (hhi : |conditionalPartialSumCDFCut n j t d hcount hi -
      gaussianCDFCut mean variance hi| ≤ ε)
    (hgauss : (99993 : ℝ) / 100000 ≤
      gaussianCDFCut mean variance hi - gaussianCDFCut mean variance lo) :
    (99993 : ℝ) / 100000 - 2 * ε ≤
      conditionalPartialSumBandMass n j t d hcount lo hi := by
  have h := conditionalPartialSumBand_coverage_of_gaussian_approx n j t d
    hcount mean variance lo hi hlohi ε (7 / 100000) hlo hhi
      (by linarith [hgauss])
  convert h using 1
  norm_num
