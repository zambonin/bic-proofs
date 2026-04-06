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

/-- The binomial factor at an admissible inclusion–exclusion index
`(d + 1) * j ≤ n`. It is not zero-extended outside that range. -/
def inclExclTerm (n i d j : ℕ) : ℕ :=
  (n - (d + 1) * j + (i - 1)).choose (i - 1)

/-- The signed inclusion–exclusion summand at an admissible index. -/
def inclExclSummand (n i d j : ℕ) : ℚ :=
  (-1 : ℚ) ^ j * (i.choose j : ℚ) * inclExclTerm n i d j

/-- At an admissible index, `inclExclTerm` is the binomial factor in `compCount_inclExcl`. -/
theorem inclExclTerm_eq_displayed (n i d j : ℕ)
    (hbound : (d + 1) * j ≤ n) :
    inclExclTerm n i d j =
      (n + i - 1 - (d + 1) * j).choose (i - 1) := by
  cases i with
  | zero => simp [inclExclTerm]
  | succ i =>
    unfold inclExclTerm
    congr 1
    omega

/-- Ratio of binomial factors separated by `p`.
The index bound keeps the denominator coefficient nonzero. -/
theorem inclExclTerm_ratio (n i d j p : ℕ) (hi : 0 < i)
    (hbound : (d + 1) * j + p ≤ n) :
    (inclExclTerm n i d j : ℚ) /
        (inclExclTerm (n - p) i d j : ℚ) =
      ∏ g ∈ range p,
        (((n - (d + 1) * j + (i - 1) : ℕ) : ℚ) - g) /
          (((n - (d + 1) * j + (i - 1) : ℕ) : ℚ) - g - (i - 1 : ℕ)) := by
  have hp : p + (i - 1) ≤ n - (d + 1) * j + (i - 1) := by omega
  have hsub :
      (n - (d + 1) * j + (i - 1)) - p =
        n - p - (d + 1) * j + (i - 1) := by omega
  simpa only [inclExclTerm, hsub] using
    chooseRatio_prod (n - (d + 1) * j + (i - 1)) p (i - 1) hp

/-- Ratio of complete signed summands separated by `p`.
The bound `j ≤ i` makes their common binomial factor nonzero. -/
theorem inclExclSummand_ratio (n i d j p : ℕ) (hi : 0 < i)
    (hj : j ≤ i) (hbound : (d + 1) * j + p ≤ n) :
    inclExclSummand n i d j / inclExclSummand (n - p) i d j =
      ∏ g ∈ range p,
        (((n - (d + 1) * j + (i - 1) : ℕ) : ℚ) - g) /
          (((n - (d + 1) * j + (i - 1) : ℕ) : ℚ) - g - (i - 1 : ℕ)) := by
  have hc : (-1 : ℚ) ^ j * (i.choose j : ℚ) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hj))
  unfold inclExclSummand
  rw [mul_div_mul_left _ _ hc]
  exact inclExclTerm_ratio n i d j p hi hbound

/-- Ratio of consecutive binomial factors. -/
theorem inclExclTerm_ratio_step (n i d j : ℕ) (hi : 0 < i)
    (hbound : (d + 1) * j + 1 ≤ n) :
    (inclExclTerm n i d j : ℚ) /
        (inclExclTerm (n - 1) i d j : ℚ) =
      ((n - (d + 1) * j + (i - 1) : ℕ) : ℚ) /
        ((n - (d + 1) * j : ℕ) : ℚ) := by
  have h := inclExclTerm_ratio n i d j 1 hi hbound
  simp only [prod_range_succ, prod_range_zero, one_mul] at h
  have hden :
      ((n - (d + 1) * j + (i - 1) : ℕ) : ℚ) - (i - 1 : ℕ) =
        ((n - (d + 1) * j : ℕ) : ℚ) := by
    simp only [Nat.cast_add]
    ring
  simpa only [Nat.cast_zero, sub_zero, hden] using h

/-- Ratio of consecutive signed summands. -/
theorem inclExclSummand_ratio_step (n i d j : ℕ) (hi : 0 < i)
    (hj : j ≤ i) (hbound : (d + 1) * j + 1 ≤ n) :
    inclExclSummand n i d j / inclExclSummand (n - 1) i d j =
      ((n - (d + 1) * j + (i - 1) : ℕ) : ℚ) /
        ((n - (d + 1) * j : ℕ) : ℚ) := by
  have hc : (-1 : ℚ) ^ j * (i.choose j : ℚ) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hj))
  unfold inclExclSummand
  rw [mul_div_mul_left _ _ hc]
  exact inclExclTerm_ratio_step n i d j hi hbound
