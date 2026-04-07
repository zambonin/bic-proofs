import GenericRankingBic.Ranking.Correctness
import Mathlib.Probability.Distributions.Uniform

variable [C : CountingContract]

/-- Uniform distribution on valid ranks. The positive-count premise rules out
an empty sample space. -/
noncomputable def uniformRank (n k d : ℕ) (hcount : 0 < C.count n k d) :
    PMF (Fin (C.count n k d)) := by
  letI : Nonempty (Fin (C.count n k d)) := ⟨⟨0, hcount⟩⟩
  exact PMF.uniformOfFintype _

/-- Push uniform valid ranks through unranking. The result applies to every
counting implementation and strategy satisfying the generic contracts. -/
noncomputable def uniformUnrank (σ : Strategy) (n k d : ℕ)
    (hcount : 0 < C.count n k d) : PMF (List ℕ) :=
  (uniformRank n k d hcount).map (fun r => unrank σ n k d r.val)

private theorem uniformRank_apply (n k d : ℕ) (hcount : 0 < C.count n k d)
    (r : Fin (C.count n k d)) :
    uniformRank n k d hcount r = (C.count n k d : ENNReal)⁻¹ := by
  unfold uniformRank
  letI : Nonempty (Fin (C.count n k d)) := ⟨⟨0, hcount⟩⟩
  simp

/-- Every valid composition receives probability `1 / C(n,k,d)`. -/
theorem uniformUnrank_apply_of_valid (σ : Strategy) (n k d : ℕ)
    (hcount : 0 < C.count n k d) (z : List ℕ)
    (hsum : z.foldl Nat.add 0 = n) (hlength : z.length = k)
    (hbound : ∀ x ∈ z, x ≤ d) :
    uniformUnrank σ n k d hcount z = (C.count n k d : ENNReal)⁻¹ := by
  let r : Fin (C.count n k d) :=
    ⟨rank σ n k d z, rank_lt_count σ n k d z hsum hlength hbound⟩
  have hpreimage (s : Fin (C.count n k d)) :
      z = unrank σ n k d s.val ↔ s = r := by
    constructor
    · intro hs
      apply Fin.ext
      change s.val = rank σ n k d z
      rw [hs, rank_unrank σ n k d s.val s.isLt]
    · intro hs
      subst s
      exact (unrank_rank σ n k d z hsum hlength hbound).symm
  unfold uniformUnrank
  rw [PMF.map_apply]
  rw [tsum_eq_single r]
  · simp [hpreimage, uniformRank_apply]
  · intro s hs
    simp [hpreimage, hs]

/-- A list outside the bounded-composition sample space has probability zero. -/
theorem uniformUnrank_apply_of_invalid (σ : Strategy) (n k d : ℕ)
    (hcount : 0 < C.count n k d) (z : List ℕ)
    (hbad : z.foldl Nat.add 0 ≠ n ∨ z.length ≠ k ∨ ∃ x ∈ z, d < x) :
    uniformUnrank σ n k d hcount z = 0 := by
  unfold uniformUnrank
  rw [PMF.map_apply]
  have hne (r : Fin (C.count n k d)) : z ≠ unrank σ n k d r.val := by
    have hvalid := unrank_sum_length σ n k d r.val r.isLt
    have hbound := unrank_parts_bounded σ n k d r.val r.isLt
    intro hz
    subst z
    rcases hbad with hsum | hlength | hbound'
    · exact hsum hvalid.1
    · exact hlength hvalid.2
    · rcases hbound' with ⟨x, hx, hdx⟩
      exact Nat.not_le_of_gt hdx (hbound x hx)
  simp [hne]
