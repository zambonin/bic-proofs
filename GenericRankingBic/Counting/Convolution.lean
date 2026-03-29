import GenericRankingBic.Counting.GeneratingFunction

open Finset BigOperators Polynomial Nat

/-- Peeling off one part gives Pascal's recurrence, clipped at `min n d`. -/
theorem bicCount_pascal (n k d : Nat) (hk : k > 0) :
    bicCount n k d = ∑ i ∈ Finset.range (Nat.min n d + 1), bicCount (n - i) (k - 1) d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  convert bicCount_conv n 1 k d using 1
  · rw [Nat.add_comm]
  · have h_bic : ∀ i, bicCount i 1 d = if i ≤ d then 1 else 0 := by
      intro i
      split_ifs <;> simp_all +decide [bicCount]
      · unfold singlePartGF
        aesop
      · unfold singlePartGF
        rw [Polynomial.finset_sum_coeff]
        aesop
    simp +decide [Finset.sum_ite, h_bic]
    rcongr x
    aesop

/-- Computable count by convolution over nearly equal part counts. -/
def convCount : ℕ → ℕ → ℕ → ℕ
  | 0, 0, _ => 1
  | _ + 1, 0, _ => 0
  | n, 1, d => if n ≤ d then 1 else 0
  | n, k + 2, d =>
    let kl := (k + 2) / 2
    let kr := k + 2 - kl
    ∑ w ∈ Finset.range (n + 1), convCount w kl d * convCount (n - w) kr d
termination_by _ k _ => k
decreasing_by
  all_goals omega

private lemma convCount_eq_bicCount : ∀ k n d, convCount n k d = bicCount n k d := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro n d
    rcases k with (_ | _ | k)
    · cases n with
      | zero =>
        simp [convCount]
        exact (show bicCount 0 0 d = 1 by unfold bicCount; simp).symm
      | succ n =>
        simp [convCount]
        exact (show bicCount (n + 1) 0 d = 0 by unfold bicCount; simp [Polynomial.coeff_one]).symm
    · cases n with
      | zero => simp [convCount]
      | succ n =>
        simp [convCount]
        split_ifs with h
        · exact (bicCount_one_le h).symm
        · exact (bicCount_one_gt (Nat.lt_of_not_le h)).symm
    · let kl := (k + 2) / 2
      let kr := k + 2 - kl
      have hkl : kl < k + 2 := by omega
      have hkr : kr < k + 2 := by omega
      have hk_eq : k + 2 = kl + kr := by omega

      simp only [convCount]
      have h_ih_l : ∀ w, convCount w kl d = bicCount w kl d := fun w => ih kl hkl w d
      have h_ih_r : ∀ w, convCount w kr d = bicCount w kr d := fun w => ih kr hkr w d

      have heq :
          ∑ w ∈ Finset.range (n + 1), convCount w kl d * convCount (n - w) kr d =
            ∑ w ∈ Finset.range (n + 1), bicCount w kl d * bicCount (n - w) kr d := by
        apply Finset.sum_congr rfl
        intro w _
        rw [h_ih_l, h_ih_r]

      rw [heq]
      have h_conv : bicCount n (k + 2) d =
          ∑ w ∈ Finset.range (n + 1), bicCount w kl d * bicCount (n - w) kr d := by
        have := bicCount_conv n kl kr d
        rw [← hk_eq] at this
        exact this
      exact h_conv.symm

lemma convCount_eq_compCount (n k d : ℕ) : convCount n k d = compCount n k d := by
  rw [compCount_eq_bicCount, convCount_eq_bicCount]
