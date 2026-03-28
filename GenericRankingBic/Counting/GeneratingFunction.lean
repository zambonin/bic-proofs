import GenericRankingBic.Counting.Compositions
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

open Finset BigOperators Polynomial Nat

/-- Generating polynomial `1 + X + ⋯ + X^d` over `ℕ`. -/
noncomputable def singlePartGF (d : Nat) : Polynomial Nat :=
  ∑ i ∈ Finset.range (d + 1), X ^ i

/-- Coefficient of `X^n` in the `k`th power of `singlePartGF d`. -/
noncomputable def bicCount (n k d : Nat) : Nat :=
  (singlePartGF d ^ k).coeff n

lemma listSumMap_eq_toFinsetSum {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (l : List α) (f : α → β) (h : l.Nodup) :
    (l.map f).sum = l.toFinset.sum f := by
  induction l <;> aesop

/-- A single part exceeding the bound contributes no composition. -/
@[simp]
lemma bicCount_one_gt {i d : Nat} (h : i > d) : bicCount i 1 d = 0 := by
  unfold bicCount singlePartGF
  norm_num [Polynomial.coeff_X_pow]
  linarith

/-- A single part within the bound contributes one composition. -/
@[simp]
lemma bicCount_one_le {i d : Nat} (h : i ≤ d) : bicCount i 1 d = 1 := by
  unfold bicCount singlePartGF
  simp [pow_one]
  assumption

/-- Convolution identity obtained by splitting the parts into two groups. -/
theorem bicCount_conv (n k1 k2 d : Nat) :
    bicCount n (k1 + k2) d =
    ∑ i ∈ Finset.range (n + 1), bicCount i k1 d * bicCount (n - i) k2 d := by
  unfold bicCount
  rw [pow_add, coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (singlePartGF d ^ k1).coeff i * (singlePartGF d ^ k2).coeff j) n

/-- The generating-function coefficient equals the cardinality of `BoundedComp`. -/
@[simp]
theorem compCount_eq_bicCount (n k d : ℕ) :
    compCount n k d = bicCount n k d := by
  induction k generalizing n with
  | zero =>
    unfold bicCount compCount BoundedComp Finset.Nat.antidiagonalTuple
    simp [Polynomial.coeff_one]
    rcases n with (_ | n) <;> simp
  | succ k ih =>
    simp_all +decide [pow_succ, Polynomial.coeff_mul, bicCount]
    have h_def := compCount_succ n k d
    simp_all +decide [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have h_partPoly_coeff : ∀ x, (singlePartGF d).coeff x = if x ≤ d then 1 else 0 := by
      unfold singlePartGF
      aesop
    simp_all +decide [Finset.sum_ite]
    refine Finset.sum_bij (fun x hx => n - x) ?_ ?_ ?_ ?_ <;> simp_all +decide [Finset.mem_range]
    · intros; omega
    · intros; omega
    · exact fun b hb₁ hb₂ => ⟨n - b, ⟨Nat.sub_le _ _,
        Nat.sub_le_of_le_add <| by linarith⟩, Nat.sub_sub_self hb₁⟩
