import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

open Finset Nat

/-- Absorption identity for one binomial coefficient. -/
private lemma choose_mul_sub_eq (m k : ℕ) (hk : k ≤ m) (hm : 1 ≤ m) :
    m.choose k * (m - k) = m * (m - 1).choose k := by
  rw [← Nat.choose_succ_right_eq, mul_comm]
  cases m <;> cases k <;>
    simp_all +decide [Nat.add_one_mul_choose_eq]; linarith!

/-- A binomial-coefficient ratio as a telescoping product.
The bound `p + k ≤ u` keeps the denominator coefficient and all product denominators nonzero. -/
theorem chooseRatio_prod (u p k : ℕ) (hp : p + k ≤ u) :
    (u.choose k : ℚ) / ((u - p).choose k : ℚ) =
    ∏ g ∈ range p, (u - g : ℚ) / (u - g - k : ℚ) := by
  induction' p with p ih generalizing k <;>
    simp_all +decide [Finset.prod_range_succ]
  · exact Nat.ne_of_gt <| Nat.choose_pos hp
  · have h_denom : (Nat.choose (u - p) k : ℚ) * (u - p - k) =
        (u - p) * (Nat.choose (u - p - 1) k : ℚ) := by
      have := choose_mul_sub_eq (u - p) k (by omega) (by omega)
      norm_cast
      rw [Int.subNatNat_of_le (by linarith)]; norm_cast
      rw [Int.subNatNat_of_le (by omega)]; norm_cast
    have := ih k (by linarith)
    simp_all +decide [Nat.sub_sub, add_comm]
    rw [div_eq_div_iff] at *
    · linear_combination'
        this * (u - p - k) +
        h_denom * (∏ x ∈ Finset.range p, (u - x : ℚ))
    · exact ne_of_gt <|
        Nat.cast_pos.mpr <| Nat.choose_pos <| by omega
    · exact Finset.prod_ne_zero_iff.mpr fun x hx =>
        sub_ne_zero_of_ne <| by
          rw [Ne.eq_def, sub_eq_iff_eq_add]; norm_cast
          linarith [Finset.mem_range.mp hx,
            Nat.sub_add_cancel (by linarith : p ≤ u)]
    · exact ne_of_gt <|
        Nat.cast_pos.mpr <| Nat.choose_pos <| by omega
    · exact mul_ne_zero
        (Finset.prod_ne_zero_iff.mpr fun x hx => by
          linarith [show (x : ℚ) < u - k by
            exact lt_tsub_iff_right.mpr
              (by norm_cast; linarith [Finset.mem_range.mp hx])])
        (by linarith [show (p : ℚ) + k < u by norm_cast; linarith])

/-- Single-step case of `chooseRatio_prod`. -/
theorem chooseRatio_step (u k : ℕ) (h : 1 + k ≤ u) :
    (u.choose k : ℚ) / ((u - 1).choose k : ℚ) =
    (u : ℚ) / (u - k : ℚ) := by
  have := chooseRatio_prod u 1 k h
  simp at this; exact this
