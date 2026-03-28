import GenericRankingBic.Counting.Compositions
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

open Finset BigOperators Polynomial Nat

/-- Generating polynomial `1 + X + ⋯ + X^d` over `ℤ`. -/
noncomputable def partPoly (d : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range (d + 1), (X : ℤ[X]) ^ j

/-- The coefficient of `X^n` in `(partPoly d)^k` counts bounded compositions. -/
theorem compCount_eq_partPoly_coeff (n k d : ℕ) :
    (compCount n k d : ℤ) = (partPoly d ^ k).coeff n := by
  induction k generalizing n with
  | zero =>
    simp_all +decide
    rcases n with (_ | _ | n) <;> simp_all +decide [Polynomial.coeff_one, compCount]
    unfold BoundedComp
    aesop
  | succ k ih =>
    simp_all +decide [pow_succ, Polynomial.coeff_mul]
    have h_def := compCount_succ n k d
    simp_all +decide [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have h_partPoly_coeff : ∀ x, (partPoly d).coeff x = if x ≤ d then 1 else 0 := by
      unfold partPoly
      aesop
    simp_all +decide [Finset.sum_ite]
    refine Finset.sum_bij (fun x hx => n - x) ?_ ?_ ?_ ?_ <;> simp_all +decide [Finset.mem_range]
    · intros; omega
    · intros; omega
    · exact fun b hb₁ hb₂ => ⟨n - b, ⟨Nat.sub_le _ _,
        Nat.sub_le_of_le_add <| by linarith⟩, Nat.sub_sub_self hb₁⟩

/-- The finite geometric-series identity for `partPoly`. -/
theorem partPoly_geomSeries (d : ℕ) :
    (1 - X : ℤ[X]) * partPoly d = 1 - X ^ (d + 1) := by
  convert geom_sum_mul_neg (X : Polynomial ℤ) d.succ using 1
  unfold partPoly
  ring

/-- The geometric-series identity raised to the `k`th power. -/
theorem partPoly_pow_eq (k d : ℕ) :
    (1 - X : ℤ[X]) ^ k * partPoly d ^ k = (1 - X ^ (d + 1)) ^ k := by
  rw [← mul_pow, partPoly_geomSeries]

/-- Coefficient of `X^n` in `(1 - X)^k`. -/
theorem coeff_one_sub_X_pow (k n : ℕ) :
    ((1 - X : ℤ[X]) ^ k).coeff n = (-1) ^ n * (k.choose n : ℤ) := by
  rw [sub_eq_add_neg, add_comm, add_pow]
  by_cases hn : n ≤ k
  · norm_num [Polynomial.coeff_sum, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single n] <;> norm_num
    · ring_nf
      by_cases h : Even n <;> aesop
    · intro b hb hbn
      ring_nf
      by_cases h : Even b <;> aesop
    · grobner
  · simp +zetaDelta at *
    rw [Finset.sum_eq_zero] <;> norm_num [Nat.choose_eq_zero_of_lt hn]
    exact fun x hx => Or.inl <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by
      erw [Polynomial.natDegree_pow, Polynomial.natDegree_neg, Polynomial.natDegree_X]
      linarith

/-- Coefficient of `X^n` in `(1 - X^(d+1))^k`. -/
theorem coeff_one_sub_X_pow_d (k d n : ℕ) :
    ((1 - X ^ (d + 1) : ℤ[X]) ^ k).coeff n =
      if (d + 1) ∣ n ∧ n / (d + 1) ≤ k
      then (-1) ^ (n / (d + 1)) * (k.choose (n / (d + 1)) : ℤ)
      else 0 := by
  split_ifs with h
  · rw [sub_eq_add_neg, add_comm, add_pow]
    simp_all +decide [mul_comm]
    rw [Finset.sum_eq_single (n / (d + 1))]
    · rw [neg_pow]
      rw [← pow_mul, Nat.mul_div_cancel' h.1]
      ring_nf
      by_cases h : Even (n / (1 + d)) <;> aesop
    · intro b hb hb'
      ring_nf
      by_cases h_even : Even b <;> simp_all +decide [← pow_add]
      · exact fun h => False.elim <| hb' <| by
          nlinarith [Nat.div_mul_cancel (by tauto : d + 1 ∣ n)]
      · exact fun h' => False.elim <| hb' <| by
          nlinarith [Nat.div_mul_cancel (by tauto : d + 1 ∣ n)]
    · exact fun h' => False.elim <| h' <| Finset.mem_range.mpr <| Nat.lt_succ_of_le h.2
  · rw [sub_eq_add_neg, add_comm, add_pow]
    simp +zetaDelta at *
    refine Finset.sum_eq_zero fun i hi => ?_
    ring_nf
    by_cases hi' : Even i <;> simp_all +decide [← pow_add]
    · exact fun hn => absurd (h (hn.symm ▸ ⟨i, by ring⟩)) (by
        nlinarith [Nat.div_mul_cancel (show d + 1 ∣ n from hn.symm ▸ ⟨i, by ring⟩)])
    · exact fun hn => absurd (h (hn.symm ▸ ⟨i, by ring⟩)) (by
        nlinarith [Nat.div_mul_cancel (show d + 1 ∣ n from hn.symm ▸ ⟨i, by ring⟩)])
