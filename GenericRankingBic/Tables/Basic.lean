import GenericRankingBic.Counting.AccumulatedCount
import GenericRankingBic.Tables.Size

/-- Dense reference count table of shape `(k+1) × (n+1)`. These lists specify
values and indices, not packed C allocation or efficient lookup. -/
def combTable (n k d : Nat) : List (List Nat) :=
  (List.range (k + 1)).map fun i =>
    (List.range (n + 1)).map fun j => compCount j i d

/-- The cumulative sequence `A(n,i,d)` has entries indexed from zero: its
zeroth entry is zero and entry `t+1` sums the first `t+1` counts. -/
def accTableEntry (n i d : Nat) : List Nat :=
  (List.range (min n d + 2)).map fun t =>
    ∑ p ∈ Finset.range t, compCount (n - p) i d

/-- Dense reference accumulated table, with one complete cumulative list per cell. -/
def accTable (n k d : Nat) : List (List (List Nat)) :=
  (List.range (k + 1)).map fun i =>
    (List.range (n + 1)).map fun j => accTableEntry j i d

theorem combTable_rows (n k d : Nat) : (combTable n k d).length = k + 1 := by
  simp [combTable]

theorem combTable_columns (n k d i : Nat) (hi : i ≤ k) :
    ((combTable n k d)[i]?).map List.length = some (n + 1) := by
  simp [combTable, List.getElem?_range (by omega : i < k + 1)]

theorem accTable_rows (n k d : Nat) : (accTable n k d).length = k + 1 := by
  simp [accTable]

theorem accTable_columns (n k d i : Nat) (hi : i ≤ k) :
    ((accTable n k d)[i]?).map List.length = some (n + 1) := by
  simp [accTable, List.getElem?_range (by omega : i < k + 1)]

theorem combTable_lookup (n k d i j : Nat) (hi : i ≤ k) (hj : j ≤ n) :
    ((combTable n k d)[i]?).bind (fun row => row[j]?) = some (compCount j i d) := by
  simp [combTable, List.getElem?_range (by omega : i < k + 1),
    List.getElem?_range (by omega : j < n + 1)]

theorem accTable_lookup (n k d i j t : Nat)
    (hi : i ≤ k) (hj : j ≤ n) (ht : t ≤ min j d + 1) :
    (((accTable n k d)[i]?).bind (fun row => row[j]?)).bind
      (fun entry => entry[t]?) =
      some (∑ p ∈ Finset.range t, compCount (j - p) i d) := by
  simp [accTable, accTableEntry,
    List.getElem?_range (by omega : i < k + 1),
    List.getElem?_range (by omega : j < n + 1),
    List.getElem?_range (by omega : t < min j d + 2)]

theorem accTableEntry_length (n i d : Nat) :
    (accTableEntry n i d).length = min n d + 2 := by
  simp [accTableEntry]

/-- The final cumulative entry is the paper's closed accumulated count. -/
theorem accTableEntry_last_eq_compCountAcc (n i d : Nat) (hi : 0 < i) :
    ((accTableEntry n i d)[min n d + 1]?).map (fun x => (x : Int)) =
      some (compCountAcc n i d (min n d)) := by
  simp [accTableEntry, compCountAcc_eq_partial_sum_clipped n i d (min n d) hi]

#guard combTable 2 2 2 == [[1, 0, 0], [1, 1, 1], [1, 2, 3]]
#guard accTableEntry 2 1 2 == [0, 1, 2, 3]
