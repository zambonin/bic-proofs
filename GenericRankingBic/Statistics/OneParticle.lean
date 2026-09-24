import GenericRankingBic.Statistics.Conditional

private theorem binaryComp_zero (k : Nat) : compCount 0 k 1 = 1 := by
  rw [compCount_eq_bicCount]
  have hgf : singlePartGF 1 = (1 + Polynomial.X : Polynomial Nat) := by
    simp [singlePartGF, Finset.sum_range_succ]
  rw [bicCount, hgf, Polynomial.coeff_one_add_X_pow]
  simp

private theorem binaryComp_one (k : Nat) : compCount 1 k 1 = k := by
  rw [compCount_eq_bicCount]
  have hgf : singlePartGF 1 = (1 + Polynomial.X : Polynomial Nat) := by
    simp [singlePartGF, Finset.sum_range_succ]
  rw [bicCount, hgf, Polynomial.coeff_one_add_X_pow]
  simp

private theorem oneParticle_count_pos (j t : Nat) (h : 0 < j + t) :
    0 < compCount 1 (j + t) 1 := by
  simpa only [binaryComp_one] using h

/-- In a binary composition of total one, the first `j` coordinates sum to
zero with mass `t/(j+t)`, where `t` is the remaining number of coordinates. -/
theorem oneParticlePartialSumLaw_zero (j t : Nat) (h : 0 < j + t) :
    conditionalPartialSumLaw 1 j t 1 (oneParticle_count_pos j t h) 0 =
      (t : ENNReal) / (j + t : Nat) := by
  have happly := conditionalPartialSumLaw_apply 1 j t 1 0
    (oneParticle_count_pos j t h) (by omega)
  simpa only [binaryComp_zero, binaryComp_one, Nat.sub_zero, Nat.cast_one,
    one_mul, Nat.cast_add] using happly

/-- At total one, the first partial sum is one with mass `j/(j+t)`. -/
theorem oneParticlePartialSumLaw_one (j t : Nat) (h : 0 < j + t) :
    conditionalPartialSumLaw 1 j t 1 (oneParticle_count_pos j t h) 1 =
      (j : ENNReal) / (j + t : Nat) := by
  have happly := conditionalPartialSumLaw_apply 1 j t 1 1
    (oneParticle_count_pos j t h) (by omega)
  simpa only [binaryComp_zero, binaryComp_one, Nat.sub_self, Nat.cast_one,
    mul_one, Nat.cast_add] using happly

/-- No other partial-sum value occurs in the one-particle law. -/
theorem oneParticlePartialSumLaw_gt_one (j t s : Nat) (h : 0 < j + t)
    (hs : 1 < s) :
    conditionalPartialSumLaw 1 j t 1 (oneParticle_count_pos j t h) s = 0 := by
  exact conditionalPartialSumLaw_apply_gt 1 j t 1 s
    (oneParticle_count_pos j t h) hs

private theorem half_mass (m : Nat) (hm : 0 < m) :
    (m : ENNReal) / (m + m : Nat) = 1 / 2 := by
  have hden : (↑(m + m) : ENNReal) ≠ 0 := by
    norm_cast
    omega
  rw [ENNReal.div_eq_div_iff (by norm_num) (by simp) hden (by simp)]
  norm_cast
  omega

/-- At the middle row of any positive even length, the exact conditional
law assigns one half to each of `0` and `1`, and zero elsewhere. -/
theorem oneParticlePartialSumLaw_halfRow (m : Nat) (hm : 0 < m) :
    conditionalPartialSumLaw 1 m m 1
      (oneParticle_count_pos m m (by omega)) 0 = 1 / 2 ∧
    conditionalPartialSumLaw 1 m m 1
      (oneParticle_count_pos m m (by omega)) 1 = 1 / 2 ∧
    ∀ s, 1 < s →
      conditionalPartialSumLaw 1 m m 1
        (oneParticle_count_pos m m (by omega)) s = 0 := by
  constructor
  · exact (oneParticlePartialSumLaw_zero m m (by omega)).trans (half_mass m hm)
  constructor
  · exact (oneParticlePartialSumLaw_one m m (by omega)).trans (half_mass m hm)
  · intro s hs
    exact oneParticlePartialSumLaw_gt_one m m s (by omega) hs

/-- The middle-row law stays Bernoulli on `{0,1}` as the number of parts
grows. A Gaussian limit needs a regime or normalization that excludes this
fixed-total obstruction. -/
theorem oneParticlePartialSumLaw_halfRow_constant (m r : Nat)
    (hm : 0 < m) (hr : 0 < r) :
    conditionalPartialSumLaw 1 m m 1 (oneParticle_count_pos m m (by omega)) =
      conditionalPartialSumLaw 1 r r 1 (oneParticle_count_pos r r (by omega)) := by
  ext s
  obtain ⟨hm0, hm1, hmgt⟩ := oneParticlePartialSumLaw_halfRow m hm
  obtain ⟨hr0, hr1, hrgt⟩ := oneParticlePartialSumLaw_halfRow r hr
  rcases s with _ | _ | s
  · exact hm0.trans hr0.symm
  · exact hm1.trans hr1.symm
  · exact (hmgt _ (by omega)).trans (hrgt _ (by omega)).symm
