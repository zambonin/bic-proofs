import GenericRankingBic.Tables.Basic
import Mathlib.Analysis.Asymptotics.Defs

/-- Prefix sums paired with the number of additions used to construct them. -/
def prefixScanWithCost (a : Nat) : List Nat → List Nat × Nat
  | [] => ([a], 0)
  | x :: xs =>
    let tail := prefixScanWithCost (a + x) xs
    (a :: tail.1, tail.2 + 1)

theorem prefixScanWithCost_result (a : Nat) (xs : List Nat) :
    (prefixScanWithCost a xs).1 = xs.scanl Nat.add a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [prefixScanWithCost, List.scanl_cons, ih]

theorem prefixScanWithCost_steps (a : Nat) (xs : List Nat) :
    (prefixScanWithCost a xs).2 = xs.length := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [prefixScanWithCost, ih]

/-- Construct `A(n,i,d)` by one running-prefix update per count. The counter
charges one count read and one addition per update, excluding evaluation of
`compCount` and large-integer arithmetic. -/
def accTableEntryIterWithCost (n i d : Nat) : List Nat × Nat :=
  prefixScanWithCost 0
    ((List.range (min n d + 1)).map fun p => compCount (n - p) i d)

theorem accTableEntryIter_steps (n i d : Nat) :
    (accTableEntryIterWithCost n i d).2 = min n d + 1 := by
  simp [accTableEntryIterWithCost, prefixScanWithCost_steps]

theorem accTableEntryIter_steps_le (n i d : Nat) :
    (accTableEntryIterWithCost n i d).2 ≤ d + 1 := by
  rw [accTableEntryIter_steps]
  omega

private theorem sum_map_range (f : Nat → Nat) (t : Nat) :
    ((List.range t).map f).sum = ∑ p ∈ Finset.range t, f p := by
  induction t with
  | zero => simp
  | succ t ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem accTableEntryIter_result (n i d : Nat) :
    (accTableEntryIterWithCost n i d).1 = accTableEntry n i d := by
  apply List.ext_getElem
  · simp [accTableEntryIterWithCost, prefixScanWithCost_result,
      accTableEntry_length]
  · intro t ht1 ht2
    have ht : t ≤ min n d + 1 := by
      simpa [accTableEntryIterWithCost, prefixScanWithCost_result] using ht1
    simp only [accTableEntryIterWithCost, prefixScanWithCost_result]
    rw [List.getElem_scanl]
    simp only [accTableEntry, List.getElem_map, List.getElem_range]
    rw [← List.map_take, List.take_range, min_eq_left ht]
    simpa only [List.sum_eq_foldl] using
      sum_map_range (fun p => compCount (n - p) i d) t

open Asymptotics Filter

/-- A pointwise bound, including the degenerate case `d = 0`. -/
theorem accTableEntryIter_steps_isBigO_add_one (n i : Nat) :
    (fun d : Nat => ((accTableEntryIterWithCost n i d).2 : ℝ))
      =O[atTop] (fun d : Nat => (d + 1 : ℝ)) := by
  apply isBigO_of_le atTop
  intro d
  exact_mod_cast accTableEntryIter_steps_le n i d

/-- The iterative construction uses `O(d)` updates as the bound varies. -/
theorem accTableEntryIter_steps_isBigO (n i : Nat) :
    (fun d : Nat => ((accTableEntryIterWithCost n i d).2 : ℝ))
      =O[atTop] (fun d : Nat => (d : ℝ)) := by
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop 1] with d hd
  have h : (accTableEntryIterWithCost n i d).2 ≤ 2 * d := by
    have hstep := accTableEntryIter_steps_le n i d
    omega
  have hr : ((accTableEntryIterWithCost n i d).2 : ℝ) ≤ 2 * (d : ℝ) := by
    exact_mod_cast h
  have hsteps0 : (0 : ℝ) ≤ ((accTableEntryIterWithCost n i d).2 : ℝ) := by positivity
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hsteps0, abs_of_nonneg hd0] using hr
