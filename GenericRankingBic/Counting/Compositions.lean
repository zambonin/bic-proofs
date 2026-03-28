import Mathlib.Data.Fin.Tuple.NatAntidiagonal

open Finset Nat

/-- The finite set of `k`-tuples with entries in `[0,d]` and sum `n`. -/
def BoundedComp (n k d : ℕ) : Finset (Fin k → ℕ) :=
  (Finset.Nat.antidiagonalTuple k n).filter (fun f => ∀ i, f i ≤ d)

/-- Number of `d`-bounded `k`-compositions of `n`. -/
def compCount (n k d : ℕ) : ℕ :=
  (BoundedComp n k d).card

/-- Last admissible index of the inclusion–exclusion sum. -/
def inclExclBound (n k d : ℕ) : ℕ :=
  min k (n / (d + 1))

theorem mem_BoundedComp {n k d : ℕ} {f : Fin k → ℕ} :
    f ∈ BoundedComp n k d ↔ (∑ i, f i) = n ∧ ∀ i, f i ≤ d := by
  simp only [BoundedComp, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]

theorem BoundedComp_succ (n k d : ℕ) :
    BoundedComp n (k + 1) d =
      (Finset.range (min (n + 1) (d + 1))).biUnion (fun j =>
        (BoundedComp (n - j) k d).image (Fin.cons j)) := by
  ext f
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, mem_BoundedComp]
  constructor
  · rintro ⟨hsum, hbound⟩
    have hhead : f 0 ≤ n := by
      rw [Fin.sum_univ_succ] at hsum
      omega
    refine ⟨f 0, by have := hbound 0; omega, Fin.tail f, ⟨?_, ?_⟩, ?_⟩
    · rw [Fin.sum_univ_succ] at hsum
      change ∑ i : Fin k, f i.succ = n - f 0
      omega
    · exact fun i => hbound i.succ
    · funext i
      exact Fin.cases rfl (fun _ => rfl) i
  · rintro ⟨j, hj, g, ⟨hsum, hbound⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      omega
    · intro i
      exact Fin.cases (by simp only [Fin.cons_zero]; omega)
        (fun j => by simpa only [Fin.cons_succ] using hbound j) i

theorem compCount_succ (n k d : ℕ) :
    compCount n (k + 1) d =
      ∑ j ∈ Finset.range (min (n + 1) (d + 1)), compCount (n - j) k d := by
  rw [compCount, BoundedComp_succ, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.card_image_of_injective _ (fun a b h => by
      funext i
      exact congrFun h i.succ)]
    rfl
  · intro j hj j' hj' hne
    apply Finset.disjoint_left.mpr
    intro f hf hf'
    obtain ⟨g, hg, hfg⟩ := Finset.mem_image.mp hf
    obtain ⟨g', hg', hfg'⟩ := Finset.mem_image.mp hf'
    exact hne (congrFun (hfg.trans hfg'.symm) 0)

theorem BoundedComp_disjoint (n m k d : ℕ) (hnm : n ≠ m) :
    Disjoint (BoundedComp n k d) (BoundedComp m k d) := by
  apply Finset.disjoint_left.mpr
  intro f hf hf'
  exact hnm ((mem_BoundedComp.mp hf).1.symm.trans (mem_BoundedComp.mp hf').1)
