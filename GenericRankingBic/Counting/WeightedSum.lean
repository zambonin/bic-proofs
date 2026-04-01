import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Finset Nat

/-- Absorption identity: `r * choose r c = c * choose r c + (c + 1) * choose r (c + 1)`. -/
lemma choose_absorption (r c : ℕ) :
    r * r.choose c = c * r.choose c + (c + 1) * r.choose (c + 1) := by
  nlinarith [Nat.add_one_mul_choose_eq r c, Nat.choose_succ_succ r c]

/-- Sum of `r^s * C(r,c)` over `[y-l,y]`, with the lower endpoint clipped at zero. -/
def weightedBinomSum (s c y l : ℕ) : ℕ :=
  ∑ r ∈ Icc (y - l) y, r ^ s * r.choose c

/-- Hockey-stick identity for exponent zero. -/
theorem weightedBinomSum_base (c y l : ℕ) :
    weightedBinomSum 0 c y l = (y + 1).choose (c + 1) - (y - l).choose (c + 1) := by
  induction l generalizing y with
  | zero =>
    simp_all +decide [Nat.choose_succ_succ]
    unfold weightedBinomSum
    aesop
  | succ l ih =>
    rcases y with (_ | y) <;> simp_all +decide [weightedBinomSum]
    · cases c <;> simp +arith +decide [Nat.choose]
    · erw [Finset.sum_Ico_succ_top, ih]
      · rw [tsub_add_eq_add_tsub]
        · simp +arith +decide [Nat.choose_succ_succ, add_comm]
        · exact Nat.choose_le_choose _ (by omega)
      · omega

/-- Recurrence in the weight exponent. -/
theorem weightedBinomSum_succ (s c y l : ℕ) :
    weightedBinomSum (s + 1) c y l =
      c * weightedBinomSum s c y l + (c + 1) * weightedBinomSum s (c + 1) y l := by
  unfold weightedBinomSum
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl; intro r _; rw [pow_succ, mul_assoc, choose_absorption]; ring

/-- Integer-valued weighted sum, equal to zero for a negative upper bound. -/
def weightedBinomSumZ (s c : ℕ) (m : ℤ) (l : ℕ) : ℤ :=
  if m < 0 then 0 else (weightedBinomSum s c m.toNat l : ℤ)

/-- Unweighted integer sum used in accumulated counts. -/
def binomSumZ (c : ℕ) (m : ℤ) (l : ℕ) : ℤ :=
  weightedBinomSumZ 0 c m l

/-- The exponent recurrence for integer upper bounds. -/
theorem weightedBinomSumZ_succ (s c : ℕ) (m : ℤ) (l : ℕ) :
    weightedBinomSumZ (s + 1) c m l =
      c * weightedBinomSumZ s c m l + (c + 1) * weightedBinomSumZ s (c + 1) m l := by
  unfold weightedBinomSumZ
  split_ifs
  · norm_num
  · rw [weightedBinomSum_succ]
    push_cast
    ring
