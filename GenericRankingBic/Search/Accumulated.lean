import GenericRankingBic.Search.Bisect
import GenericRankingBic.Search.ColexThreshold
import GenericRankingBic.Tables.Basic
import Mathlib.Tactic

/-- Binary search for the last cumulative entry not exceeding `r` in `[lo, hi)`.
Each reduction probes one midpoint of the supplied entry function; `fuel` bounds
these reductions. -/
def accumulatedSearchFuel (entry : Nat → Nat) (r : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then lo
      else
        let mid := (lo + hi) / 2
        if r < entry mid then
          accumulatedSearchFuel entry r fuel lo mid
        else
          accumulatedSearchFuel entry r fuel mid hi

/-- A complete binary search of entries zero through `m`, inclusive. -/
def accumulatedSearch (entry : Nat → Nat) (m r : Nat) : Nat :=
  accumulatedSearchFuel entry r (m + 1) 0 (m + 1)

private theorem midpoint_inside {lo hi : Nat} (h : lo + 1 < hi) :
    lo < (lo + hi) / 2 ∧ (lo + hi) / 2 < hi := by
  omega

/-- The binary search finds the unique threshold even when some adjacent
cumulative entries are equal. -/
theorem accumulatedSearchFuel_eq_threshold (entry : Nat → Nat) (r target fuel lo hi : Nat)
    (hmono : Monotone entry)
    (htarget : entry target ≤ r ∧ r < entry (target + 1))
    (hlo : lo ≤ target) (hhi : target < hi) (hfuel : hi - lo ≤ fuel) :
    accumulatedSearchFuel entry r fuel lo hi = target := by
  induction fuel generalizing lo hi with
  | zero => omega
  | succ fuel ih =>
      unfold accumulatedSearchFuel
      by_cases hsmall : hi ≤ lo + 1
      · simp only [if_pos hsmall]
        omega
      · simp only [if_neg hsmall]
        have hins := midpoint_inside (by omega : lo + 1 < hi)
        by_cases hleft : r < entry ((lo + hi) / 2)
        · simp only [if_pos hleft]
          apply ih lo ((lo + hi) / 2) hlo (by
            by_contra h
            have hm : (lo + hi) / 2 ≤ target := by omega
            exact (not_le_of_gt hleft) (le_trans (hmono hm) htarget.1))
            (by omega)
        · simp only [if_neg hleft]
          apply ih ((lo + hi) / 2) hi (by
            by_contra h
            have hm : target + 1 ≤ (lo + hi) / 2 := by omega
            exact (not_le_of_gt htarget.2) (le_trans (hmono hm) (Nat.le_of_not_gt hleft)))
            hhi (by omega)

theorem accumulatedSearch_eq_threshold (entry : Nat → Nat) (m r target : Nat)
    (hmono : Monotone entry) (htarget : entry target ≤ r ∧ r < entry (target + 1))
    (hbound : target ≤ m) :
    accumulatedSearch entry m r = target := by
  exact accumulatedSearchFuel_eq_threshold entry r target (m + 1) 0 (m + 1)
    hmono htarget (Nat.zero_le _) (by omega) (by omega)

/-- A cumulative entry fetched from the precomputed sequence.  Clipping
extends the last entry beyond the maximum admissible right part. -/
def colexTablePrefix (n i d t : Nat) : Nat :=
  ((accTableEntry n i d).toArray)[min t (min n d + 1)]!

theorem colexTablePrefix_eq_sum (n i d t : Nat) :
    colexTablePrefix n i d t =
      ∑ p ∈ Finset.range (min t (min n d + 1)), compCount (n - p) i d := by
  simp [colexTablePrefix, accTableEntry]

theorem colexTablePrefix_mono (n i d : Nat) : Monotone (colexTablePrefix n i d) := by
  intro a b hab
  rw [colexTablePrefix_eq_sum, colexTablePrefix_eq_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (min_le_min_right _ hab)
  · simp

theorem colexTablePrefix_eq_colexPrefix (n i d p : Nat)
    (hp : p ≤ min n d + 1) :
    colexTablePrefix n i d p =
      colexPrefix (C := finsetInstance) n i d p := by
  rw [colexTablePrefix_eq_sum, min_eq_left hp]
  rfl

theorem colexTablePrefix_final (n i d : Nat) :
    ((accTableEntry n i d).toArray)[min n d + 1]! = compCount n (i + 1) d := by
  have h := colexPrefix_final (C := finsetInstance) n i d
  rw [← colexTablePrefix_eq_colexPrefix n i d (min n d + 1) (le_refl _)] at h
  change colexTablePrefix n i d (min n d + 1) = compCount n (i + 1) d at h
  simpa only [colexTablePrefix, min_self] using h

/-- Search an already constructed accumulated sequence.  Its array is shared
by all midpoint probes. -/
def searchColexWithEntry (entry : Array Nat) (n d r : Nat) : Nat :=
  accumulatedSearch (fun t => entry[min t (min n d + 1)]!) (min n d) r

/-- Search the accumulated table for the colex right-part threshold.  Each
comparison reads one existing entry of `accTableEntry`, rather than summing
the candidate blocks again. -/
def searchColexTable (n i d r : Nat) : Nat :=
  let entry := (accTableEntry n i d).toArray
  searchColexWithEntry entry n d r

theorem searchColexWithEntry_eq_searchColexTable (n i d r : Nat) :
    searchColexWithEntry (accTableEntry n i d).toArray n d r =
      searchColexTable n i d r := rfl

/-- Search a cell of the paper's three-dimensional accumulated table. -/
def searchColexFromMatrix (table : List (List (List Nat)))
    (n i d r : Nat) : Nat :=
  searchColexWithEntry ((table[i]!)[n]!).toArray n d r

theorem searchColexFromMatrix_eq (N K n i d r : Nat)
    (hn : n ≤ N) (hi : i ≤ K) :
    searchColexFromMatrix (accTable N K d) n i d r =
      searchColexTable n i d r := by
  simp [searchColexFromMatrix, searchColexTable, accTable, hi, hn]

theorem searchColexTable_eq_threshold (n i d r target : Nat)
    (hbound : target ≤ min n d)
    (hlo : colexTablePrefix n i d target ≤ r)
    (hhi : r < colexTablePrefix n i d (target + 1)) :
    searchColexTable n i d r = target :=
  accumulatedSearch_eq_threshold (colexTablePrefix n i d) (min n d) r target
    (colexTablePrefix_mono n i d) ⟨hlo, hhi⟩ hbound

/-- Select a colex block from an already constructed accumulated sequence.
Both the threshold and residual rank read the same array. -/
def findBlockColexWithEntry (entry : Array Nat) (n i d r : Nat) : Nat × Nat :=
  if r < entry[min n d + 1]! then
    let p := searchColexWithEntry entry n d r
    (n - p, r - entry[p]!)
  else
    findBlock (C := finsetInstance) n i 1 d (pathDecreasing n) r

/-- The colex block and residual rank, using an accumulated sequence when
the rank is valid.  The fallback preserves the generic scan's behavior for
out-of-range ranks. -/
def findBlockColexTable (n i d r : Nat) : Nat × Nat :=
  let entry := (accTableEntry n i d).toArray
  findBlockColexWithEntry entry n i d r

theorem findBlockColexTable_eq_findBlock (n i d r : Nat) :
    findBlockColexTable n i d r =
      findBlock (C := finsetInstance) n i 1 d (pathDecreasing n) r := by
  by_cases hr : r < compCount n (i + 1) d
  · obtain ⟨p, r', hp, hfind, hlo, hhi, hres⟩ :=
      exists_colex_prefix_threshold (C := finsetInstance) n i d r hr
    have hplo : p ≤ min n d + 1 := by omega
    have hphi : p + 1 ≤ min n d + 1 := by omega
    have hs : searchColexTable n i d r = p :=
      searchColexTable_eq_threshold n i d r p hp
        (by rwa [colexTablePrefix_eq_colexPrefix n i d p hplo])
        (by rwa [colexTablePrefix_eq_colexPrefix n i d (p + 1) hphi])
    have hentry : ((accTableEntry n i d).toArray)[p]! =
        colexTablePrefix n i d p := by
      simp [colexTablePrefix, min_eq_left hplo]
    simp only [findBlockColexTable, findBlockColexWithEntry, colexTablePrefix_final, if_pos hr]
    change (n - searchColexTable n i d r,
      r - ((accTableEntry n i d).toArray)[searchColexTable n i d r]!) = _
    rw [hs, hentry, hfind, hres, colexTablePrefix_eq_colexPrefix n i d p hplo]
  · simp only [findBlockColexTable, findBlockColexWithEntry, colexTablePrefix_final, if_neg hr]

/-- The matrix-backed form uses the existing cell `A(n,i,d)` directly. -/
def findBlockColexFromMatrix (table : List (List (List Nat)))
    (n i d r : Nat) : Nat × Nat :=
  findBlockColexWithEntry ((table[i]!)[n]!).toArray n i d r

theorem findBlockColexFromMatrix_eq_findBlock (N K n i d r : Nat)
    (hn : n ≤ N) (hi : i ≤ K) :
    findBlockColexFromMatrix (accTable N K d) n i d r =
      findBlock (C := finsetInstance) n i 1 d (pathDecreasing n) r := by
  rw [show findBlockColexFromMatrix (accTable N K d) n i d r =
      findBlockColexTable n i d r from by
        simp [findBlockColexFromMatrix, findBlockColexTable, accTable, hi, hn]]
  exact findBlockColexTable_eq_findBlock n i d r

/-- Colex unranking whose block search reads the accumulated sequence. -/
def unrankColexTable (n k d r : Nat) : List Nat :=
  match k with
  | 0 => []
  | 1 => [n]
  | Nat.succ (Nat.succ k') =>
      let i := k' + 1
      let fb := findBlockColexTable n i d r
      let s := splitDivMod (compCount (n - fb.1) 1 d) fb.2
      unrankColexTable fb.1 i d s.1 ++
        unrankColexTable (n - fb.1) 1 d s.2
termination_by k
decreasing_by
  · omega
  · omega

theorem unrankColexTable_eq_unrank :
    ∀ n k d r, unrankColexTable n k d r =
      unrank (C := finsetInstance) (stratColex (C := finsetInstance)) n k d r := by
  intro n k d r
  induction k using Nat.strong_induction_on generalizing n r with
  | h k ih =>
      rcases k with (_ | _ | k)
      · simp [unrankColexTable, unrank]
      · simp [unrankColexTable, unrank]
      · simp only [unrankColexTable, unrank, stratColex, decompRight,
          findBlockColexTable_eq_findBlock]
        rw [ih (k + 1) (by omega)]
        rfl

/-- Convert a previously constructed `accTable` once. All later recursive
lookups use array indexing for the row, column, and cumulative entry. -/
def accTableArrays (table : List (List (List Nat))) :
    Array (Array (Array Nat)) :=
  (table.map fun row => (row.map List.toArray).toArray).toArray

theorem accTableArrays_cell (N K n i d : Nat) (hn : n ≤ N) (hi : i ≤ K) :
    ((accTableArrays (accTable N K d))[i]!)[n]! =
      (accTableEntry n i d).toArray := by
  simp [accTableArrays, accTable, hi, hn]

/-- Select a block using an already converted cell of the global table. -/
def findBlockColexFromArrayMatrix (table : Array (Array (Array Nat)))
    (n i d r : Nat) : Nat × Nat :=
  findBlockColexWithEntry ((table[i]!)[n]!) n i d r

theorem findBlockColexFromArrayMatrix_eq_findBlock
    (N K n i d r : Nat) (hn : n ≤ N) (hi : i ≤ K) :
    findBlockColexFromArrayMatrix (accTableArrays (accTable N K d)) n i d r =
      findBlock (C := finsetInstance) n i 1 d (pathDecreasing n) r := by
  rw [findBlockColexFromArrayMatrix, accTableArrays_cell N K n i d hn hi]
  exact findBlockColexTable_eq_findBlock n i d r

private theorem findBlock_colex_fst_le (n i d r : Nat) :
    (findBlock (C := finsetInstance) n i 1 d (pathDecreasing n) r).1 ≤ n := by
  suffices h : ∀ (p : List Nat) (r : Nat),
      (∀ w ∈ p, w ≤ n) →
      (findBlock (C := finsetInstance) n i 1 d p r).1 ≤ n by
    exact h (pathDecreasing n) r (pathDecreasing_bound n)
  intro p
  induction p with
  | nil =>
      intro r _
      simp [findBlock]
  | cons w ws ih =>
      intro r hp
      have hw : w ≤ n := hp w (by simp)
      have hws : ∀ x ∈ ws, x ≤ n := by
        intro x hx
        exact hp x (by simp [hx])
      by_cases h : r < compCount w i d * compCount (n - w) 1 d
      · change (if r < compCount w i d * compCount (n - w) 1 d then (w, r)
            else findBlock (C := finsetInstance) n i 1 d ws
              (r - compCount w i d * compCount (n - w) 1 d)).1 ≤ n
        simp only [if_pos h]
        exact hw
      · change (if r < compCount w i d * compCount (n - w) 1 d then (w, r)
            else findBlock (C := finsetInstance) n i 1 d ws
              (r - compCount w i d * compCount (n - w) 1 d)).1 ≤ n
        simp only [if_neg h]
        exact ih (r - (compCount w i d * compCount (n - w) 1 d)) hws

private theorem onePartCount_eq_compCount (n d : Nat) :
    (if n ≤ d then 1 else 0) = compCount n 1 d := by
  by_cases h : n ≤ d
  · simpa only [if_pos h] using (finsetInstance.count_one n d h).symm
  · simpa only [if_neg h] using (finsetInstance.count_one_gt n d (by omega)).symm

/-- Recursive colex unranking that reuses one precomputed array matrix at
every level. The matrix is an explicit argument and is never reconstructed by
this function. -/
def unrankColexFromMatrix (table : Array (Array (Array Nat)))
    (n k d r : Nat) : List Nat :=
  match k with
  | 0 => []
  | 1 => [n]
  | Nat.succ (Nat.succ k') =>
      let i := k' + 1
      let fb := findBlockColexFromArrayMatrix table n i d r
      let s := splitDivMod (if n - fb.1 ≤ d then 1 else 0) fb.2
      unrankColexFromMatrix table fb.1 i d s.1 ++
        unrankColexFromMatrix table (n - fb.1) 1 d s.2
termination_by k
decreasing_by
  · omega
  · omega

/-- The matrix-backed recursive algorithm agrees with generic colex
unranking whenever the precomputed table covers the original parameters. -/
theorem unrankColexFromMatrix_eq_unrank (N K n k d r : Nat)
    (hn : n ≤ N) (hk : k ≤ K) :
    unrankColexFromMatrix (accTableArrays (accTable N K d)) n k d r =
      unrank (C := finsetInstance) (stratColex (C := finsetInstance)) n k d r := by
  induction k using Nat.strong_induction_on generalizing n r with
  | h k ih =>
      rcases k with (_ | _ | k)
      · simp [unrankColexFromMatrix, unrank]
      · simp [unrankColexFromMatrix, unrank]
      · have hi : k + 1 ≤ K := by omega
        have hfb := findBlockColexFromArrayMatrix_eq_findBlock N K n (k + 1) d r hn hi
        have hleft :
            (findBlock (C := finsetInstance) n (k + 1) 1 d (pathDecreasing n) r).1 ≤ N :=
          (findBlock_colex_fst_le n (k + 1) d r).trans hn
        simp only [unrankColexFromMatrix, unrank, stratColex, decompRight, hfb,
          onePartCount_eq_compCount]
        rw [ih (k + 1) (by omega) _ _ hleft hi]
        rfl

/-- Convenience entry point: convert a previously built list table once,
then reuse the resulting arrays throughout recursive unranking. -/
def unrankColexFromAccTable (table : List (List (List Nat)))
    (n k d r : Nat) : List Nat :=
  unrankColexFromMatrix (accTableArrays table) n k d r

theorem unrankColexFromAccTable_eq_unrank (N K n k d r : Nat)
    (hn : n ≤ N) (hk : k ≤ K) :
    unrankColexFromAccTable (accTable N K d) n k d r =
      unrank (C := finsetInstance) (stratColex (C := finsetInstance)) n k d r :=
  unrankColexFromMatrix_eq_unrank N K n k d r hn hk
