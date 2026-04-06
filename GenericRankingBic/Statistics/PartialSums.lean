import GenericRankingBic.Counting.AccumulatedCount
import GenericRankingBic.Counting.AccumulatedSet
import GenericRankingBic.Counting.RawMoment
import Mathlib.Tactic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas

open Finset Nat

noncomputable section

section Compositions

/-- Coordinate permutations preserve bounded compositions. -/
lemma BoundedComp_perm_invariant (n k d : ℕ) (σ : Equiv.Perm (Fin k))
    (z : Fin k → ℕ) (hz : z ∈ BoundedComp n k d) :
    z ∘ σ ∈ BoundedComp n k d := by
  simp_all +decide [BoundedComp]
  simp [antidiagonalTuple] at *
  rw [Multiset.Nat.mem_antidiagonalTuple] at *
  simpa using Equiv.sum_comp σ z ▸ hz.1

/-- Coordinate permutations preserve accumulated bounded compositions. -/
lemma BoundedCompAcc_perm_invariant (n k d l : ℕ) (σ : Equiv.Perm (Fin k))
    (z : Fin k → ℕ) (hz : z ∈ BoundedCompAcc n k d l) :
    z ∘ σ ∈ BoundedCompAcc n k d l := by
  obtain ⟨j, hj, hz⟩ := Finset.mem_biUnion.mp hz
  exact Finset.mem_biUnion.mpr ⟨j, hj, BoundedComp_perm_invariant (n - j) k d σ z hz⟩

/-- Coordinate sums agree by exchangeability. -/
lemma sum_func_coord_eq_acc_rat (n k d l : ℕ) (f : ℕ → ℚ) (i j : Fin k) :
    ∑ z ∈ BoundedCompAcc n k d l, f (z i) =
    ∑ z ∈ BoundedCompAcc n k d l, f (z j) := by
  refine Finset.sum_bij (fun z _ => z ∘ Equiv.swap i j) ?_ ?_ ?_ ?_ <;> simp_all +decide
  · exact fun z hz => BoundedCompAcc_perm_invariant n k d l _ z hz
  · exact fun a₁ _ a₂ _ h => funext fun x => by simpa using congr_fun h (Equiv.swap i j x)
  · exact fun z hz => ⟨z ∘ Equiv.swap i j, BoundedCompAcc_perm_invariant n k d l _ z hz,
      by ext; simp +decide⟩

/-- Sums over distinct coordinate pairs agree by exchangeability. -/
lemma sum_func_pair_eq_acc_rat (n k d l : ℕ) (f : ℕ → ℕ → ℚ)
    (a b c' d' : Fin k) (hab : a ≠ b) (hcd : c' ≠ d') :
    ∑ z ∈ BoundedCompAcc n k d l, f (z a) (z b) =
    ∑ z ∈ BoundedCompAcc n k d l, f (z c') (z d') := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin k), σ a = c' ∧ σ b = d' := by
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin k), σ a = c' :=
      ⟨Equiv.swap a c', by simp +decide⟩
    use σ * Equiv.swap b (σ⁻¹ d'); aesop
  apply Finset.sum_bij (fun z _ => z ∘ σ.symm)
  · exact fun z hz => BoundedCompAcc_perm_invariant n k d l _ z hz
  · exact fun x _ y _ hxy => funext fun i => by simpa using congr_fun hxy (σ i)
  · exact fun z hz => ⟨z ∘ σ, BoundedCompAcc_perm_invariant n k d l σ z hz, by aesop⟩
  · aesop

/-- Sum of coordinates with index below `j`, as a rational number. -/
def partialSumQ {k : ℕ} (z : Fin k → ℕ) (j : ℕ) : ℚ :=
  ∑ i ∈ Finset.filter (fun i : Fin k => i.val < j) Finset.univ, (z i : ℚ)

/-- Sum of all coordinates, as a rational number. -/
def totalSumQ {k : ℕ} (z : Fin k → ℕ) : ℚ :=
  ∑ i : Fin k, (z i : ℚ)

/-- Sum of the first coordinate over the accumulated class. -/
abbrev coordSum (n k d l : ℕ) (hk : 0 < k) : ℚ :=
  ∑ z ∈ BoundedCompAcc n k d l, (z ⟨0, hk⟩ : ℚ)

/-- Sum of the squared first coordinate over the accumulated class. -/
abbrev coordSqSum (n k d l : ℕ) (hk : 0 < k) : ℚ :=
  ∑ z ∈ BoundedCompAcc n k d l, (z ⟨0, hk⟩ : ℚ) ^ 2

/-- Sum of the product of coordinates zero and one over the accumulated class. -/
abbrev crossSum (n k d l : ℕ) (hk : 1 < k) : ℚ :=
  ∑ z ∈ BoundedCompAcc n k d l, ((z ⟨0, by omega⟩ : ℚ) * (z ⟨1, hk⟩ : ℚ))

/-- The partial-sum total is `j` times the first-coordinate total. -/
lemma sum_partialSumQ (n k d l : ℕ) (hk : 0 < k) (j : ℕ) (hj : j ≤ k) :
    ∑ z ∈ BoundedCompAcc n k d l, partialSumQ z j =
      j * coordSum n k d l hk := by
  have h_sum_partial_sum :
      ∑ z ∈ BoundedCompAcc n k d l,
        ∑ i ∈ Finset.filter (fun i : Fin k => i.val < j) Finset.univ, (z i : ℚ) =
      ∑ i ∈ Finset.filter (fun i : Fin k => i.val < j) Finset.univ,
        ∑ z ∈ BoundedCompAcc n k d l, (z i : ℚ) :=
    Finset.sum_comm
  have h_sum_partial_sum :
      ∑ i ∈ Finset.filter (fun i : Fin k => i.val < j) Finset.univ,
        ∑ z ∈ BoundedCompAcc n k d l, (z i : ℚ) =
      ∑ i ∈ Finset.filter (fun i : Fin k => i.val < j) Finset.univ,
        coordSum n k d l hk :=
    Finset.sum_congr rfl fun i hi =>
      sum_func_coord_eq_acc_rat n k d l (fun x => x) i ⟨0, hk⟩
  simp_all +decide [partialSumQ]
  left
  rw [Finset.card_eq_of_bijective]
  use fun i hi => ⟨i, by linarith⟩
  · grind
  · aesop
  · lia

/-- Summing the total over the class gives `k` times the first-coordinate total. -/
lemma sum_totalSumQ (n k d l : ℕ) (hk : 0 < k) :
    ∑ z ∈ BoundedCompAcc n k d l, totalSumQ z =
      k * coordSum n k d l hk := by
  convert sum_partialSumQ n k d l hk k le_rfl using 1
  unfold partialSumQ totalSumQ
  aesop

/-- Squared partial sums split into diagonal and off-diagonal terms. -/
lemma sum_sq_partialSumQ (n k d l : ℕ) (hk : 1 < k) (j : ℕ) (hj : j ≤ k) :
    ∑ z ∈ BoundedCompAcc n k d l, (partialSumQ z j) ^ 2 =
      j * coordSqSum n k d l (by omega) + j * (j - 1) * crossSum n k d l hk := by
  unfold partialSumQ
  generalize_proofs at *
  -- Split the sum into diagonal and off-diagonal parts.
  have h_split :
      ∑ z ∈ BoundedCompAcc n k d l,
        (∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < j), (z i : ℚ)) ^ 2 =
      ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < j),
        ∑ z ∈ BoundedCompAcc n k d l, (z i : ℚ) ^ 2 +
      ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < j),
        ∑ j_1 ∈ Finset.univ.filter (fun j_1 : Fin k => j_1.val < j),
          if i ≠ j_1 then ∑ z ∈ BoundedCompAcc n k d l, (z i : ℚ) * (z j_1 : ℚ)
          else 0 := by
    simp +decide [sq, Finset.sum_mul _ _ _, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl]
    rw [← Finset.sum_add_distrib]
    intro i hi
    rw [Finset.sum_comm]
    simp +decide [Finset.sum_ite, Finset.filter_ne]
    rw [← Finset.sum_erase_add _ _
      (show i ∈ Finset.filter (fun y : Fin k => (y : ℕ) < j) Finset.univ from by aesop),
      add_comm]
  -- By exchangeability, each inner sum equals coordSqSum.
  have h_diag :
      ∀ i ∈ Finset.univ.filter (fun i : Fin k => i.val < j),
      ∑ z ∈ BoundedCompAcc n k d l, (z i : ℚ) ^ 2 = coordSqSum n k d l ‹_› := by
    intro i hi
    convert sum_func_coord_eq_acc_rat n k d l (fun x => x ^ 2) i ⟨0, by linarith⟩ using 1
  -- By exchangeability, each inner sum equals crossSum.
  have h_off_diag :
      ∀ i ∈ Finset.univ.filter (fun i : Fin k => i.val < j),
      ∀ j_1 ∈ Finset.univ.filter (fun j_1 : Fin k => j_1.val < j),
      i ≠ j_1 →
      ∑ z ∈ BoundedCompAcc n k d l, (z i : ℚ) * (z j_1 : ℚ) = crossSum n k d l hk := by
    intros i hi j_1 hj_1 hij
    convert sum_func_pair_eq_acc_rat n k d l (fun x y => x * y) i j_1
      ⟨0, by linarith⟩ ⟨1, by linarith⟩ hij (by aesop) using 1
  simp_all +decide [Finset.sum_ite, Finset.filter_ne]
  rw [show (Finset.filter (fun i : Fin k => (i : ℕ) < j) Finset.univ).card = j from ?_]
  · ring_nf
    cases j <;> norm_num
    ring
  · rw [Finset.card_eq_of_bijective]
    use fun i hi => ⟨i, by linarith⟩
    · aesop
    · aesop
    · aesop

/-- Squared total sums split into diagonal and off-diagonal terms. -/
lemma sum_sq_totalSumQ (n k d l : ℕ) (hk : 1 < k) :
    ∑ z ∈ BoundedCompAcc n k d l, (totalSumQ z) ^ 2 =
      k * coordSqSum n k d l (by omega) + k * (k - 1) * crossSum n k d l hk := by
  convert sum_sq_partialSumQ n k d l hk k (by linarith) using 1
  unfold totalSumQ partialSumQ
  exact Finset.sum_congr rfl fun _ _ => by
    rw [Finset.sum_filter_of_ne]
    aesop

/-- Partial-sum mean identity before normalization by sample size. -/
theorem expected_partial_sum (n k d l : ℕ) (hk : 0 < k) (j : ℕ) (hj : j ≤ k) :
    (k : ℚ) * ∑ z ∈ BoundedCompAcc n k d l, partialSumQ z j =
    (j : ℚ) * ∑ z ∈ BoundedCompAcc n k d l, totalSumQ z := by
  rw [sum_partialSumQ n k d l hk j hj, sum_totalSumQ n k d l hk]
  ring

/-- Partial-sum variance decomposition before normalization by sample size. -/
theorem variance_partial_sum (n k d l : ℕ) (hk : 1 < k) (j : ℕ) (hj : j ≤ k) :
    let S := BoundedCompAcc n k d l
    let N := (S.card : ℚ)
    let sumR := ∑ z ∈ S, totalSumQ z
    let sumR2 := ∑ z ∈ S, (totalSumQ z) ^ 2
    let sum1 := ∑ z ∈ S, (z ⟨0, by omega⟩ : ℚ)
    let sum1sq := ∑ z ∈ S, (z ⟨0, by omega⟩ : ℚ) ^ 2
    let sumSj := ∑ z ∈ S, partialSumQ z j
    let sumSj2 := ∑ z ∈ S, (partialSumQ z j) ^ 2
    let varX1_num := N * sum1sq - sum1 ^ 2
    let varR_num := N * sumR2 - sumR ^ 2
    let varSj_num := N * sumSj2 - sumSj ^ 2
    varSj_num * (k - 1) * k =
      j * (k - j) * k * varX1_num + j * (j - 1) * varR_num := by
  -- Use the decomposition lemmas to reduce to algebra
  simp only []
  rw [sum_partialSumQ n k d l (by omega) j hj,
      sum_totalSumQ n k d l (by omega),
      sum_sq_partialSumQ n k d l hk j hj,
      sum_sq_totalSumQ n k d l hk]
  ring

/-- The first coordinate is bounded by both the total and the part bound. -/
lemma first_coord_le (n k d : ℕ) (z : Fin (k + 1) → ℕ) (hz : z ∈ BoundedComp n (k + 1) d) :
    z 0 ≤ min n d := by
  refine le_min ?_ ?_
  · -- By definition of antidiagonalTuple, we know that the sum of the elements in z is n.
    have h_sum : ∑ i : Fin (k + 1), z i = n := by
      have h_antidiagonal : z ∈ Finset.Nat.antidiagonalTuple (k + 1) n :=
        Finset.mem_filter.mp hz |>.1
      exact mem_antidiagonalTuple.mp h_antidiagonal
    exact h_sum ▸ Finset.single_le_sum (fun i _ => Nat.zero_le (z i)) (Finset.mem_univ 0)
  · exact Finset.mem_filter.mp hz |>.2 0

/-- Removing a fixed first coordinate preserves the number of compositions. -/
lemma fiber_card_eq (r k d y : ℕ) (hy : y ≤ min r d) :
    (BoundedComp r (k + 1) d |>.filter (fun z => z 0 = y)).card =
    (BoundedComp (r - y) k d).card := by
  refine Finset.card_bij (fun z hz => Fin.tail z) ?_ ?_ ?_
  · simp +contextual [BoundedComp]
    simp +contextual [antidiagonalTuple]
    simp +contextual [Multiset.Nat.antidiagonalTuple, Fin.tail]
    simp +contextual [List.Nat.antidiagonalTuple]
    aesop
  · intro z1 hz1 z2 hz2 heq
    simp only [Finset.mem_filter] at hz1 hz2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hz1.2, hz2.2]
    · exact congr_fun heq j
  · intro b hb
    use Fin.cons y b
    simp_all +decide [BoundedComp]
    simp_all +decide [Fin.forall_fin_succ, antidiagonalTuple]
    simp_all +decide [Multiset.Nat.antidiagonalTuple]
    simp_all +decide [List.Nat.antidiagonalTuple]
    exact ⟨r - y, Nat.add_sub_of_le hy.1, hb.1⟩

set_option maxHeartbeats 800000 in
/-- Removing a fixed first coordinate preserves the accumulated count. -/
lemma fiber_card_acc (n k d l y : ℕ) (hy : y ≤ min n d) :
    (BoundedCompAcc n (k + 1) d l |>.filter (fun z => z 0 = y)).card =
    (BoundedCompAcc (n - y) k d l).card := by
  apply Finset.card_bij (fun z _ => Fin.tail z)
  · intro z hz
    simp only [Finset.mem_filter] at hz
    obtain ⟨hmem, heq⟩ := hz
    simp only [BoundedCompAcc, Finset.mem_biUnion] at hmem ⊢
    obtain ⟨j, hj_range, hj_mem⟩ := hmem
    use j, hj_range
    simp only [BoundedComp, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hj_mem ⊢
    obtain ⟨hsum, hbound⟩ := hj_mem
    refine ⟨?_, fun i => hbound (Fin.succ i)⟩
    rw [Fin.sum_univ_succ] at hsum
    change ∑ i, z (Fin.succ i) = (n - y) - j
    omega
  · intro z1 hz1 z2 hz2 heq
    simp only [Finset.mem_filter] at hz1 hz2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hz1.2, hz2.2]
    · exact congr_fun heq j
  · intro w hw
    simp only [BoundedCompAcc, Finset.mem_biUnion] at hw
    obtain ⟨j, hj_range, hj_mem⟩ := hw
    have hj_le : j ≤ l := by simpa using hj_range
    simp only [BoundedComp, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hj_mem
    obtain ⟨hsum, hbound⟩ := hj_mem
    by_cases hle : j ≤ n - y
    · refine ⟨Fin.cons y w, ?_, ?_⟩
      · simp only [Finset.mem_filter, BoundedCompAcc, Finset.mem_biUnion]
        refine ⟨⟨j, hj_range, ?_⟩, by simp [Fin.cons]⟩
        simp only [BoundedComp, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
        refine ⟨?_, fun i => Fin.cases
          (by simp [Fin.cons]; exact le_trans hy (min_le_right n d))
          (fun j => by simp [Fin.cons_succ]; exact hbound j) i⟩
        rw [Fin.sum_univ_succ, Fin.cons_zero]
        simp only [Fin.cons_succ]
        omega
      · ext; simp [Fin.tail, Fin.cons]
    · push_neg at hle
      have hsum_zero : ∑ i, w i = 0 := by omega
      refine ⟨Fin.cons y w, ?_, ?_⟩
      · simp only [Finset.mem_filter, BoundedCompAcc, Finset.mem_biUnion]
        refine ⟨⟨n - y, ?_, ?_⟩, by simp [Fin.cons]⟩
        · simp only [Finset.mem_range]
          omega
        · simp only [BoundedComp, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
          refine ⟨?_, fun i => Fin.cases
            (by simp [Fin.cons]; exact le_trans hy (min_le_right n d))
            (fun j => by simp [Fin.cons_succ]; exact hbound j) i⟩
          rw [Fin.sum_univ_succ, Fin.cons_zero]
          simp only [Fin.cons_succ]
          omega
      · ext; simp [Fin.tail, Fin.cons]

/-- Sum of squared first coordinates, grouped by the value of that coordinate. -/
theorem var_single_part_decomp (n k d l : ℕ) (hk : 1 < k) :
    ∑ z ∈ BoundedCompAcc n k d l, ((z ⟨0, by omega⟩ : ℤ) ^ 2) =
    ∑ y ∈ Finset.range (min n d + 1),
      (y : ℤ) ^ 2 * (BoundedCompAcc (n - y) (k - 1) d l).card := by
  have := @fiber_card_acc n (k - 1) d l
  rcases k with (_ | _ | k) <;> simp_all +decide [Finset.sum_range_succ']
  · contradiction
  · contradiction
  · rw [← Finset.sum_subset
      (show Finset.filter (fun z => z 0 ≤ min n d) (BoundedCompAcc n (k + 1 + 1) d l) ⊆
        BoundedCompAcc n (k + 1 + 1) d l from Finset.filter_subset _ _)]
    norm_cast
    · have h_split :
          ∑ z ∈ Finset.filter (fun z => z 0 ≤ min n d)
            (BoundedCompAcc n (k + 1 + 1) d l), (z 0 : ℕ) ^ 2 =
          ∑ y ∈ Finset.range (min n d + 1),
            ∑ z ∈ Finset.filter (fun z => z 0 = y)
              (BoundedCompAcc n (k + 1 + 1) d l), (y : ℕ) ^ 2 := by
        simp +decide only [sum_filter]
        rw [Finset.sum_comm, Finset.sum_congr rfl]
        aesop
      simp_all +decide [Finset.sum_range_succ']
      exact Finset.sum_congr rfl fun x hx => by
        rw [this _ (by linarith [Finset.mem_range.mp hx, min_le_left n d])
          (by linarith [Finset.mem_range.mp hx, min_le_right n d])]
        ring
    · intro x hx hx'
      contrapose! hx'
      simp_all +decide [BoundedCompAcc]
      obtain ⟨a, ha, hx⟩ := hx
      have := Finset.mem_filter.mp hx
      simp_all +decide [BoundedComp]
      have := Multiset.Nat.mem_antidiagonalTuple.mp this.1
      simp_all +decide [Fin.sum_univ_succ]
      exact le_trans (Nat.le_add_right _ _) (this.le.trans (Nat.sub_le _ _))

end Compositions
