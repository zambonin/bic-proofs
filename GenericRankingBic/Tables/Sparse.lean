import GenericRankingBic.Tables.ProbabilisticSize

/-- Executable columns selected for one sparse row. -/
def sparseBandColumns (n k d c i : ℕ) : List ℕ :=
  (List.range (n + 1)).filter
    (fun j => inStatisticalBand (compPartialMean n k d)
      (compPartialVariance n k d) c i j)

/-- Store only the selected `(column,count)` pairs, with no slots for
columns outside the exact statistical band. -/
def sparseProbCombRow (n k d c i : ℕ) : List (ℕ × ℕ) :=
  (sparseBandColumns n k d c i).map (fun j => (j, compCount j i d))

/-- One sparse row per part count, indexed by `i = 0, …, k`. -/
def sparseProbCombTable (n k d c : ℕ) : List (List (ℕ × ℕ)) :=
  (List.range (k + 1)).map (sparseProbCombRow n k d c)

/-- Count the actual stored `(column,count)` pairs in a sparse table. -/
def sparseProbCombStoredValues (n k d c : ℕ) : ℕ :=
  ((sparseProbCombTable n k d c).map List.length).sum

/-- Look up a sparse row and then its column. -/
def sparseProbCombLookup (table : List (List (ℕ × ℕ))) (i j : ℕ) : Option ℕ :=
  (table[i]?).bind (fun row => row.lookup j)

/-- A total evaluator falls back to the exact count when a value is absent. -/
def sparseProbCombLookupOrCompute (n k d c i j : ℕ) : ℕ :=
  (sparseProbCombLookup (sparseProbCombTable n k d c) i j).getD (compCount j i d)

private theorem list_range_sum_eq_finset_sum (f : ℕ → ℕ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem sparseBandColumns_length (n k d c i : ℕ) :
    (sparseBandColumns n k d c i).length = (retainedBandRow n k d c i).card := by
  have hnodup : (sparseBandColumns n k d c i).Nodup :=
    List.Nodup.filter _ List.nodup_range
  have hcard := List.toFinset_card_of_nodup hnodup
  rw [← hcard]
  simp [sparseBandColumns, retainedBandRow, List.toFinset_filter,
    List.toFinset_range]

private theorem sparseProbCombRow_length (n k d c i : ℕ) :
    (sparseProbCombRow n k d c i).length = (retainedBandRow n k d c i).card := by
  simp [sparseProbCombRow, sparseBandColumns_length]

/-- The number of stored count values is exactly the number of retained
cells in the Boolean band. -/
theorem sparseProbCombStoredValues_eq_retainedBandCells (n k d c : ℕ) :
    sparseProbCombStoredValues n k d c = retainedBandCells n k d c := by
  simp only [sparseProbCombStoredValues, sparseProbCombTable, List.map_map,
    Function.comp_def, sparseProbCombRow_length, retainedBandCells]
  exact list_range_sum_eq_finset_sum _ _

private theorem lookup_graph_if (as : List ℕ) (f : ℕ → ℕ) (j : ℕ) :
    (as.map fun x => (x, f x)).lookup j =
      if j ∈ as then some (f j) else none := by
  by_cases hj : j ∈ as
  · simp [hj, List.lookup_graph f hj]
  · have hnone : (as.map fun x => (x, f x)).lookup j = none := by
      apply List.lookup_eq_none_iff.mpr
      intro p hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      simpa using (show j ≠ x by intro h; apply hj; exact h ▸ hx)
    simp [hj, hnone]

/-- Sparse row lookup reads a stored count exactly on the retained band. -/
theorem sparseProbCombRow_lookup (n k d c i j : ℕ) :
    (sparseProbCombRow n k d c i).lookup j =
      if j ∈ retainedBandRow n k d c i then some (compCount j i d) else none := by
  simpa [sparseProbCombRow, sparseBandColumns, retainedBandRow] using
    lookup_graph_if (sparseBandColumns n k d c i) (fun j => compCount j i d) j

/-- Sparse lookup agrees with the reference table at every valid index. -/
theorem sparseProbCombLookup_eq_dense (n k d c i j : ℕ) (hi : i ≤ k) (hj : j ≤ n) :
    sparseProbCombLookup (sparseProbCombTable n k d c) i j =
      probCombLookup (probCombTableFromCompositions n k d c) i j := by
  rw [probCombTableFromCompositions_lookup n k d c i j hi hj]
  simp [sparseProbCombLookup, sparseProbCombTable,
    List.getElem?_range (by omega : i < k + 1), sparseProbCombRow_lookup,
    retainedBandRow, hj]

/-- A successful sparse lookup returns the exact composition count. -/
theorem sparseProbCombLookup_sound (n k d c i j value : ℕ) (hi : i ≤ k)
    (hj : j ≤ n)
    (h : sparseProbCombLookup (sparseProbCombTable n k d c) i j = some value) :
    value = compCount j i d := by
  rw [sparseProbCombLookup_eq_dense n k d c i j hi hj,
    probCombTableFromCompositions_lookup n k d c i j hi hj] at h
  split at h <;> cases h
  rfl

/-- Fallback evaluation is correct whether or not the cell was retained. -/
theorem sparseProbCombLookupOrCompute_correct (n k d c i j : ℕ)
    (hi : i ≤ k) (hj : j ≤ n) :
    sparseProbCombLookupOrCompute n k d c i j = compCount j i d := by
  rw [sparseProbCombLookupOrCompute,
    sparseProbCombLookup_eq_dense n k d c i j hi hj,
    probCombTableFromCompositions_lookup n k d c i j hi hj]
  split <;> rfl

/-- For fixed `d,c`, stored count values are `O(k sqrt k)`, uniformly in
the total `n(k)`. This counts values, excluding keys, metadata and the bit
width of each natural number. -/
theorem sparseProbCombStoredValues_isBigO (nSeq : ℕ → ℕ) (d c : ℕ) :
    (fun k : ℕ => (sparseProbCombStoredValues (nSeq k) k d c : ℝ))
      =O[Filter.atTop] (fun k : ℕ => (k : ℝ) * Real.sqrt k) := by
  simpa only [sparseProbCombStoredValues_eq_retainedBandCells] using
    retainedBandCells_isBigO nSeq d c
