import GenericRankingBic.Tables.ProbabilisticSize
import GenericRankingBic.Statistics.FourSigma
import Mathlib.Tactic

open Finset

/-- Popoviciu's finite-sample variance bound, including the empty convention. -/
theorem finiteVariance_four_mul_le_width_sq {α : Type*} (S : Finset α)
    (f : α → ℚ) (a b : ℚ) (hf : ∀ z ∈ S, a ≤ f z ∧ f z ≤ b) :
    4 * finiteVariance S f ≤ (b - a) ^ 2 := by
  by_cases hS : S.card = 0
  · simpa [finiteVariance, finiteMean, hS] using sq_nonneg (b - a)
  have hc : (0 : ℚ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hS
  have hsum : (∑ z ∈ S, (f z) ^ 2) ≤
      (a + b) * (∑ z ∈ S, f z) - S.card * (a * b) := by
    calc
      _ ≤ ∑ z ∈ S, ((a + b) * f z - a * b) := by
        apply sum_le_sum
        intro z hz
        have h := mul_nonneg (sub_nonneg.mpr (hf z hz).1)
          (sub_nonneg.mpr (hf z hz).2)
        nlinarith
      _ = _ := by simp [sum_sub_distrib, ← mul_sum]
  have hm : finiteMean S f * S.card = ∑ z ∈ S, f z := by
    simp [finiteMean, ne_of_gt hc]
  have hm2 : finiteMean S (fun z => (f z) ^ 2) * S.card =
      ∑ z ∈ S, (f z) ^ 2 := by simp [finiteMean, ne_of_gt hc]
  have he : finiteMean S (fun z => (f z) ^ 2) ≤
      (a + b) * finiteMean S f - a * b := by
    apply (mul_le_mul_iff_left₀ hc).mp
    rw [← hm, ← hm2] at hsum
    nlinarith [hsum]
  change 4 * (finiteMean S (fun z => (f z)^2) - (finiteMean S f)^2) ≤ _
  nlinarith [sq_nonneg (2 * finiteMean S f - a - b)]

/-- Exact rational partial-sum mean for the inclusive accumulated window. -/
def accPartialMean (n k d l i : ℕ) : ℚ :=
  finiteMean (BoundedCompAcc n k d l) (fun z => partialSumQ z i)

/-- Exact rational partial-sum variance for the inclusive accumulated window. -/
def accPartialVariance (n k d l i : ℕ) : ℚ :=
  finiteVariance (BoundedCompAcc n k d l) (fun z => partialSumQ z i)

private theorem acc_coord_bounded (n k d l : ℕ) (i : Fin k)
    (z : Fin k → ℕ) (hz : z ∈ BoundedCompAcc n k d l) : z i ≤ d := by
  obtain ⟨r, hr, hz⟩ := mem_biUnion.mp hz
  exact (mem_filter.mp hz).2 i

private theorem acc_total_bounded (n k d l : ℕ) (z : Fin k → ℕ)
    (hz : z ∈ BoundedCompAcc n k d l) :
    (n : ℚ) - l ≤ totalSumQ z ∧ totalSumQ z ≤ n := by
  obtain ⟨r, hr, hz⟩ := mem_biUnion.mp hz
  have hr' : r ≤ l := by simpa using hr
  have hs : (∑ i, z i) = n - r :=
    Finset.Nat.mem_antidiagonalTuple.mp (mem_filter.mp hz).1
  have hsq : totalSumQ z = ((n - r : ℕ) : ℚ) := by
    unfold totalSumQ
    exact_mod_cast hs
  rw [hsq]
  constructor
  · have h : n ≤ n - r + l := by omega
    have hq : (n : ℚ) ≤ (n - r : ℕ) + l := by exact_mod_cast h
    linarith
  · exact_mod_cast Nat.sub_le n r

/-- The total varies in an interval of width at most `l`, even when clipped at zero. -/
theorem accTotalVariance_four_mul_le (n k d l : ℕ) :
    4 * finiteVariance (BoundedCompAcc n k d l) totalSumQ ≤ (l : ℚ) ^ 2 := by
  have h := finiteVariance_four_mul_le_width_sq (BoundedCompAcc n k d l)
    totalSumQ ((n : ℚ) - l) n (acc_total_bounded n k d l)
  convert h using 1
  ring

/-- A coordinate remains bounded by `d` in every accumulated window. -/
theorem accFirstVariance_four_mul_le (n k d l : ℕ) (hk : 0 < k) :
    4 * finiteVariance (BoundedCompAcc n k d l)
      (fun z => (z ⟨0, hk⟩ : ℚ)) ≤ (d : ℚ) ^ 2 := by
  have h := finiteVariance_four_mul_le_width_sq (BoundedCompAcc n k d l)
    (fun z => (z ⟨0, hk⟩ : ℚ)) 0 d (by
      intro z hz
      constructor
      · positivity
      · change (z ⟨0, hk⟩ : ℚ) ≤ d
        exact_mod_cast acc_coord_bounded n k d l ⟨0,hk⟩ z hz)
  simpa using h

/-- A uniform accumulated-window variance bound; no Gaussian approximation is used. -/
theorem accPartialVariance_le (n k d l i : ℕ) (hk : 1 < k) (hi : i ≤ k) :
    accPartialVariance n k d l i ≤ (k : ℚ) * (d : ℚ) ^ 2 + (l : ℚ) ^ 2 := by
  by_cases hS : 0 < (BoundedCompAcc n k d l).card
  · let v := finiteVariance (BoundedCompAcc n k d l)
      (fun z => (z ⟨0, by omega⟩ : ℚ))
    let w := finiteVariance (BoundedCompAcc n k d l) totalSumQ
    have hv0 : 0 ≤ v := finiteVariance_nonneg _ _
    have hw0 : 0 ≤ w := finiteVariance_nonneg _ _
    have hv : v ≤ (d : ℚ)^2 := by
      have := accFirstVariance_four_mul_le n k d l (by omega)
      dsimp [v]
      nlinarith [sq_nonneg (d : ℚ)]
    have hw : w ≤ (l : ℚ)^2 := by
      have := accTotalVariance_four_mul_le n k d l
      dsimp [w]
      nlinarith [sq_nonneg (l : ℚ)]
    have hkq : (1 : ℚ) < k := by exact_mod_cast hk
    have hk1 : (0 : ℚ) < (k : ℚ) - 1 := by linarith
    have hk0 : (0 : ℚ) < k := by linarith
    have hiq : (i : ℚ) ≤ k := by exact_mod_cast hi
    have hki : 0 ≤ (k : ℚ) - i := by linarith
    have hA0 : 0 ≤ (i : ℚ) * (k - i) / (k - 1) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg i) hki) (le_of_lt hk1)
    have hA : (i : ℚ) * (k - i) / (k - 1) ≤ k := by
      rw [div_le_iff₀ (by linarith : (0:ℚ) < k - 1)]
      by_cases hi0 : i = 0
      · simp only [hi0, Nat.cast_zero, zero_mul]
        exact le_of_lt (mul_pos hk0 hk1)
      · have hi1 : (1 : ℚ) ≤ i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi0
        nlinarith [mul_nonneg (sub_nonneg.mpr hiq) (sub_nonneg.mpr hi1)]
    have hB0 : 0 ≤ (i : ℚ) * (i - 1) / ((k : ℚ) * (k - 1)) := by
      by_cases hi0 : i = 0
      · simp [hi0]
      · have hi1 : (1 : ℚ) ≤ i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi0
        exact div_nonneg (mul_nonneg (Nat.cast_nonneg i) (by linarith))
          (le_of_lt (mul_pos hk0 hk1))
    have hB : (i : ℚ) * (i - 1) / ((k : ℚ) * (k - 1)) ≤ 1 := by
      rw [div_le_iff₀ (mul_pos hk0 hk1)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hiq) (show (0:ℚ) ≤ k + i - 1 by linarith)]
    unfold accPartialVariance
    rw [variance_partial_sum_normalized n k d l hk i hi hS]
    change _ * v + _ * w ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hv hA0,
      mul_le_mul_of_nonneg_right hA (sq_nonneg (d:ℚ)),
      mul_le_mul_of_nonneg_left hw hB0,
      mul_le_mul_of_nonneg_right hB (sq_nonneg (l:ℚ))]
  · have hempty : BoundedCompAcc n k d l = ∅ :=
      card_eq_zero.mp (Nat.eq_zero_of_not_pos hS)
    simp [accPartialVariance, finiteVariance, finiteMean, hempty]
    positivity

/-- Exact scalar entries retained for one row and inclusive moment window.
The rational band is independent of floating C endpoint computations. -/
def accumulatedBandRow (n k d c l i : ℕ) : Finset ℕ :=
  (range (n + 1)).filter fun j =>
    ((j : ℚ) - accPartialMean n k d l i)^2 ≤
      (c : ℚ)^2 * accPartialVariance n k d l i

private theorem nat_band_card_le (s : Finset ℕ) (μ : ℚ) (R : ℕ)
    (h : ∀ j ∈ s, |(j : ℚ) - μ| ≤ R) : s.card ≤ 2 * R + 1 := by
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    have ha : a ∈ s := min'_mem s hs
    have hsubset : s ⊆ Icc a (a + 2 * R) := by
      intro j hj
      have hmin : a ≤ j := min'_le _ _ hj
      have h₁ := abs_le.mp (h a ha)
      have h₂ := abs_le.mp (h j hj)
      have hupper : j ≤ a + 2 * R := by
        have hq : (j : ℚ) ≤ a + 2 * (R : ℚ) := by linarith
        exact_mod_cast hq
      exact mem_Icc.mpr ⟨hmin,hupper⟩
    have hc := card_le_card hsubset
    simp only [Nat.card_Icc] at hc
    omega
  · have : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    simp [this]

/-- A clipped, rounded integer bound for every scalar band, with all parameters explicit. -/
theorem accumulatedBandRow_card_le (n k d c l i : ℕ) (hk : 1 < k) (hi : i ≤ k) :
    (accumulatedBandRow n k d c l i).card ≤
      2 * c * (d * (Nat.sqrt k + 1) + l) + 1 := by
  let R := c * (d * (Nat.sqrt k + 1) + l)
  have hv := accPartialVariance_le n k d l i hk hi
  have hs : (k : ℚ) ≤ ((Nat.sqrt k + 1 : ℕ) : ℚ)^2 := by
    have := Nat.sqrt_le_add k
    exact_mod_cast (show k ≤ (Nat.sqrt k + 1)^2 by nlinarith)
  have hb : (c : ℚ)^2 * accPartialVariance n k d l i ≤ (R : ℚ)^2 := by
    have hs' : (k : ℚ) ≤ ((Nat.sqrt k : ℚ) + 1)^2 := by simpa using hs
    have hcross : (0 : ℚ) ≤ 2 * (d * ((Nat.sqrt k : ℚ) + 1)) * l := by positivity
    calc
      _ ≤ (c : ℚ)^2 * ((k : ℚ) * (d : ℚ)^2 + (l : ℚ)^2) := by
        exact mul_le_mul_of_nonneg_left hv (sq_nonneg _)
      _ ≤ (c : ℚ)^2 * ((((Nat.sqrt k : ℚ) + 1)^2 * (d : ℚ)^2) + (l : ℚ)^2) := by
        gcongr
      _ ≤ (c : ℚ)^2 * ((d : ℚ) * ((Nat.sqrt k : ℚ) + 1) + l)^2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        nlinarith [hcross]
      _ = _ := by dsimp [R]; push_cast; ring
  have hc := nat_band_card_le (accumulatedBandRow n k d c l i)
    (accPartialMean n k d l i) R (by
      intro j hj
      have hsq := (mem_filter.mp hj).2
      have hsq' := hsq.trans hb
      rw [← sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg R), sq_abs]
      exact hsq')
  simpa [R, Nat.mul_assoc] using hc

/-- Count each scalar separately across the chosen rows and moment windows;
a list-valued accumulated-table cell can contain several such scalars. -/
def accumulatedScalarCells (n k d c : ℕ) (rows windows : Finset ℕ) : ℕ :=
  ∑ i ∈ rows, ∑ l ∈ windows, (accumulatedBandRow n k d c l i).card

/-- Explicit storage bound for arbitrary selected rows/windows, including a sparse row set. -/
theorem accumulatedScalarCells_le (n k d c L : ℕ) (rows windows : Finset ℕ)
    (hk : 1 < k) (hrows : ∀ i ∈ rows, i ≤ k)
    (hwindows : ∀ l ∈ windows, l ≤ L) :
    accumulatedScalarCells n k d c rows windows ≤
      rows.card * windows.card * (2 * c * (d * (Nat.sqrt k + 1) + L) + 1) := by
  unfold accumulatedScalarCells
  calc
    _ ≤ ∑ i ∈ rows, ∑ l ∈ windows,
        (2 * c * (d * (Nat.sqrt k + 1) + L) + 1) := by
      apply sum_le_sum; intro i hi
      apply sum_le_sum; intro l hl
      exact (accumulatedBandRow_card_le n k d c l i hk (hrows i hi)).trans
        (by gcongr; exact hwindows l hl)
    _ = _ := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- The total-range clipping can sharpen the width bound. -/
theorem accumulatedBandRow_card_le_min (n k d c l i : ℕ) (hk : 1 < k) (hi : i ≤ k) :
    (accumulatedBandRow n k d c l i).card ≤
      min (n + 1) (2 * c * (d * (Nat.sqrt k + 1) + l) + 1) := by
  apply le_min
  · simpa using card_le_card (filter_subset
      (fun j : ℕ => ((j : ℚ) - accPartialMean n k d l i)^2 ≤
        (c : ℚ)^2 * accPartialVariance n k d l i) (range (n + 1)))
  · exact accumulatedBandRow_card_le n k d c l i hk hi

/-- A window-sensitive discrete bound, retaining the chosen row set and support clipping. -/
theorem accumulatedScalarCells_le_sum (n k d c : ℕ) (rows windows : Finset ℕ)
    (hk : 1 < k) (hrows : ∀ i ∈ rows, i ≤ k) :
    accumulatedScalarCells n k d c rows windows ≤
      ∑ _i ∈ rows, ∑ l ∈ windows,
        min (n + 1) (2 * c * (d * (Nat.sqrt k + 1) + l) + 1) := by
  apply sum_le_sum; intro i hi
  apply sum_le_sum; intro l _
  exact accumulatedBandRow_card_le_min n k d c l i hk (hrows i hi)

/-- All positive rows and inclusive windows `0,...,L`. -/
theorem accumulatedScalarCells_full_le (n k d c L : ℕ) (hk : 1 < k) :
    accumulatedScalarCells n k d c (Icc 1 k) (range (L + 1)) ≤
      k * (L + 1) * (2 * c * (d * (Nat.sqrt k + 1) + L) + 1) := by
  simpa using accumulatedScalarCells_le n k d c L (Icc 1 k) (range (L + 1)) hk
    (by intro i hi; exact (mem_Icc.mp hi).2)
    (by intro l hl; simpa using hl)

/-- The moment-window indices actually requested by the C sparse-accumulated
constructor are `0,...,d-1`; its rows are `1,...,k`. -/
theorem accumulatedScalarCells_cGrid_le (n k d c : ℕ) (hk : 1 < k) :
    accumulatedScalarCells n k d c (Icc 1 k) (range d) ≤
      k * d * (2 * c * (d * (Nat.sqrt k + 1) + (d - 1)) + 1) := by
  simpa using accumulatedScalarCells_le n k d c (d - 1) (Icc 1 k) (range d) hk
    (by intro i hi; exact (mem_Icc.mp hi).2)
    (by intro l hl; have := mem_range.mp hl; omega)

/-- A finite real bound displaying the fixed-parameter asymptotic constant. -/
theorem accumulatedScalarCells_full_le_real (n k d c L : ℕ) (hk : 1 < k) :
    (accumulatedScalarCells n k d c (Icc 1 k) (range (L + 1)) : ℝ) ≤
      (2 * ((L + 1) * (2 * c * (d + L) + 1) : ℕ) : ℝ) * k * Real.sqrt k := by
  have hrow : 2 * c * (d * (Nat.sqrt k + 1) + L) + 1 ≤
      (2 * c * (d + L) + 1) * (Nat.sqrt k + 1) := by
    have hL : L ≤ L * (Nat.sqrt k + 1) := by nlinarith
    nlinarith [Nat.mul_le_mul_left (2 * c) hL]
  have hnat : accumulatedScalarCells n k d c (Icc 1 k) (range (L + 1)) ≤
      k * ((L + 1) * (2 * c * (d + L) + 1)) * (Nat.sqrt k + 1) := by
    calc
      _ ≤ k * (L + 1) * (2 * c * (d * (Nat.sqrt k + 1) + L) + 1) :=
        accumulatedScalarCells_full_le n k d c L hk
      _ ≤ k * (L + 1) * ((2 * c * (d + L) + 1) * (Nat.sqrt k + 1)) :=
        Nat.mul_le_mul_left _ hrow
      _ = _ := by ring
  have hcast : (accumulatedScalarCells n k d c (Icc 1 k) (range (L + 1)) : ℝ) ≤
      (k : ℝ) * (((L + 1) * (2 * c * (d + L) + 1) : ℕ) : ℝ) *
        ((Nat.sqrt k + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
  have hroot : ((Nat.sqrt k + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt k := by
    have hs := Real.nat_sqrt_le_real_sqrt (a := k)
    have hs1 : (1 : ℝ) ≤ Real.sqrt k := by
      calc
        (1 : ℝ) = Real.sqrt 1 := by simp
        _ ≤ Real.sqrt k := Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ k by omega))
    push_cast
    linarith
  calc
    _ ≤ (k : ℝ) * (((L + 1) * (2 * c * (d + L) + 1) : ℕ) : ℝ) *
        ((Nat.sqrt k + 1 : ℕ) : ℝ) := hcast
    _ ≤ (k : ℝ) * (((L + 1) * (2 * c * (d + L) + 1) : ℕ) : ℝ) *
        (2 * Real.sqrt k) := by gcongr
    _ = _ := by push_cast; ring

open Asymptotics Filter

/-- For fixed `d,c,L`, the scalar count is `O(k sqrt k)`, uniformly in the total.
When `L` grows, use the explicit finite bound instead. -/
theorem accumulatedScalarCells_isBigO (nSeq : ℕ → ℕ) (d c L : ℕ) :
    (fun k : ℕ => (accumulatedScalarCells (nSeq k) k d c (Icc 1 k)
      (range (L + 1)) : ℝ)) =O[atTop] (fun k : ℕ => (k : ℝ) * Real.sqrt k) := by
  apply IsBigO.of_bound (2 * (((L + 1) * (2 * c * (d + L) + 1) : ℕ) : ℝ))
  filter_upwards [eventually_ge_atTop 2] with k hk
  have h := accumulatedScalarCells_full_le_real (nSeq k) k d c L hk
  have hleft : 0 ≤ (accumulatedScalarCells (nSeq k) k d c (Icc 1 k)
      (range (L + 1)) : ℝ) := Nat.cast_nonneg _
  have hright : 0 ≤ (k : ℝ) * Real.sqrt k := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright,
    mul_assoc] using h
