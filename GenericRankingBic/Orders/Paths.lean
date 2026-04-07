import GenericRankingBic.Orders.RecursiveBlock
import GenericRankingBic.Counting.Instances
import Mathlib.Data.List.Sort

/-- Alternate between the low and high ends of the *full* range:
`0, n, 1, n-1, ...`. This need not induce the paper's alternating order on
valid splits when they form a strict subrange. -/
def pathAlternating (n : Nat) : List Nat :=
  (List.range (n + 1)).mergeSort
    (fun a b => decide (2 * min a (n - a) + (if a ≤ n - a then 0 else 1) ≤
      2 * min b (n - b) + (if b ≤ n - b then 0 else 1)))

/-- Alternating position key on indices `0, ..., m`: index `0` precedes `m`,
then `1` precedes `m-1`, and so forth. -/
def alternatingIndexKey (m i : Nat) : Nat :=
  2 * min i (m - i) + (if i ≤ m - i then 0 else 1)

private theorem mergeSort_pairwise_key (l : List Nat) (key : Nat → Nat) :
    (l.mergeSort (fun a b => decide (key a ≤ key b))).Pairwise
      (fun a b => key a ≤ key b) := by
  have ht : ∀ a b c : Nat,
      decide (key a ≤ key b) = true →
      decide (key b ≤ key c) = true →
      decide (key a ≤ key c) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    exact le_trans hab hbc
  have htotal : ∀ a b : Nat,
      ((decide (key a ≤ key b)) || (decide (key b ≤ key a))) = true := by
    intro a b
    rcases le_total (key a) (key b) with h | h
    · simp [h]
    · simp [h]
  simpa only [decide_eq_true_eq] using List.pairwise_mergeSort ht htotal l

/-- Alternate the ends of a duplicate-free ordered list. -/
def alternateEnds (l : List Nat) : List Nat :=
  l.mergeSort (fun a b => decide
    (alternatingIndexKey (l.length - 1) (l.idxOf a) ≤
      alternatingIndexKey (l.length - 1) (l.idxOf b)))

/-- The exact valid split sequence from the paper, before permutation. -/
def validSplitList [C : CountingContract] (n kl kr d : Nat) : List Nat :=
  (List.range (n + 1)).filter fun w =>
    0 < C.count w kl d * C.count (n - w) kr d

/-- The paper's `P_alt`: alternate the ends of the valid split sequence. -/
def pathAlternatingValid [C : CountingContract] (n kl kr d : Nat) : List Nat :=
  alternateEnds (validSplitList n kl kr d)

theorem alternateEnds_nodup (l : List Nat) (hl : l.Nodup) :
    (alternateEnds l).Nodup := by
  exact List.nodup_mergeSort.mpr hl

theorem alternateEnds_mem (l : List Nat) (w : Nat) :
    w ∈ alternateEnds l ↔ w ∈ l := by
  exact List.mem_mergeSort

/-- Every pair in the output follows the alternating endpoint index order. -/
theorem alternateEnds_order (l : List Nat) :
    (alternateEnds l).Pairwise (fun a b =>
      alternatingIndexKey (l.length - 1) (l.idxOf a) ≤
        alternatingIndexKey (l.length - 1) (l.idxOf b)) := by
  exact mergeSort_pairwise_key l _

theorem pathAlternatingValid_nodup [C : CountingContract] (n kl kr d : Nat) :
    (pathAlternatingValid n kl kr d).Nodup := by
  exact alternateEnds_nodup _ (List.Nodup.filter _ List.nodup_range)

theorem pathAlternatingValid_mem [C : CountingContract] (n kl kr d w : Nat) :
    w ∈ pathAlternatingValid n kl kr d ↔
      w ≤ n ∧ 0 < C.count w kl d * C.count (n - w) kr d := by
  rw [pathAlternatingValid, alternateEnds_mem]
  simp [validSplitList]

theorem pathAlternatingValid_order [C : CountingContract] (n kl kr d : Nat) :
    (pathAlternatingValid n kl kr d).Pairwise (fun a b =>
      alternatingIndexKey ((validSplitList n kl kr d).length - 1)
        ((validSplitList n kl kr d).idxOf a) ≤
      alternatingIndexKey ((validSplitList n kl kr d).length - 1)
        ((validSplitList n kl kr d).idxOf b)) :=
  alternateEnds_order _

/-- A path valid for the generic `Strategy` contract at every bound, whose
positive-size prefix at `d₀` is exactly the paper's alternating path. -/
def pathBousAt [C : CountingContract] (d₀ n kl kr : Nat) : List Nat :=
  let valid := pathAlternatingValid n kl kr d₀
  valid ++ (List.range (n + 1)).filter (fun w => w ∉ valid)

theorem pathBousAt_mem [C : CountingContract] (d₀ n kl kr w : Nat) :
    w ∈ pathBousAt d₀ n kl kr ↔ w ≤ n := by
  constructor
  · intro hw
    rcases List.mem_append.mp hw with hw | hw
    · exact (pathAlternatingValid_mem n kl kr d₀ w).mp hw |>.1
    · exact Nat.le_of_lt_succ (List.mem_range.mp (List.mem_filter.mp hw).1)
  · intro hw
    by_cases hv : w ∈ pathAlternatingValid n kl kr d₀
    · exact List.mem_append.mpr (Or.inl hv)
    · exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr
        ⟨List.mem_range.mpr (Nat.lt_succ_of_le hw), by simpa⟩))

theorem pathBousAt_nodup [C : CountingContract] (d₀ n kl kr : Nat) :
    (pathBousAt d₀ n kl kr).Nodup := by
  apply List.Nodup.append (pathAlternatingValid_nodup n kl kr d₀)
    (List.Nodup.filter _ List.nodup_range)
  intro w hw₁ hw₂
  have hn : w ∉ pathAlternatingValid n kl kr d₀ := by
    simpa using (List.mem_filter.mp hw₂).2
  exact hn hw₁

/-- At its chosen bound, removing zero-size blocks recovers exactly the
paper's `P_alt`, including its endpoint-alternating order. -/
theorem pathBousAt_filter_positive [C : CountingContract] (d₀ n kl kr : Nat) :
    (pathBousAt d₀ n kl kr).filter
      (fun w => 0 < C.count w kl d₀ * C.count (n - w) kr d₀) =
      pathAlternatingValid n kl kr d₀ := by
  let valid := pathAlternatingValid n kl kr d₀
  let rest := (List.range (n + 1)).filter (fun w => w ∉ valid)
  have hvalid : valid.filter
      (fun w => 0 < C.count w kl d₀ * C.count (n - w) kr d₀) = valid := by
    apply List.filter_eq_self.mpr
    intro w hw
    exact decide_eq_true ((pathAlternatingValid_mem n kl kr d₀ w).mp hw |>.2)
  have hrest : rest.filter
      (fun w => 0 < C.count w kl d₀ * C.count (n - w) kr d₀) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro w hw hp
    have hw' := List.mem_filter.mp hw
    have hnot : w ∉ valid := by simpa using hw'.2
    have hpos : 0 < C.count w kl d₀ * C.count (n - w) kr d₀ := by
      simpa using hp
    exact hnot ((pathAlternatingValid_mem n kl kr d₀ w).mpr
      ⟨Nat.le_of_lt_succ (List.mem_range.mp hw'.1), hpos⟩)
  change (valid ++ rest).filter
    (fun w => 0 < C.count w kl d₀ * C.count (n - w) kr d₀) = valid
  rw [List.filter_append, hvalid, hrest, List.append_nil]

/-- The spiral priority key: distance from the integer center, breaking a tie
in favor of the positive side. -/
def spiralIndexKey (center w : Nat) : Nat :=
  2 * (w - center + (center - w)) + (if center ≤ w then 0 else 1)

/-- Visit integer center `⌊n / (kl + kr)⌋`, then values above and below it,
breaking distance ties in favor of the positive side. -/
def pathSpiral (n kl kr : Nat) : List Nat :=
  let center := n / (kl + kr)
  (List.range (n + 1)).mergeSort
    (fun a b => decide (spiralIndexKey center a ≤ spiralIndexKey center b))

/-- The effective spiral path, obtained by retaining precisely the positive-size
blocks. For `kl = 1`, this intersects the spiral with the part bound `d` and
with feasibility of the remaining `kr` parts. -/
def pathSpiralValid [C : CountingContract] (n kl kr d : Nat) : List Nat :=
  (pathSpiral n kl kr).filter fun w =>
    0 < C.count w kl d * C.count (n - w) kr d

theorem pathSpiral_order (n kl kr : Nat) :
    (pathSpiral n kl kr).Pairwise (fun a b =>
      spiralIndexKey (n / (kl + kr)) a ≤ spiralIndexKey (n / (kl + kr)) b) := by
  exact mergeSort_pairwise_key _ _

theorem pathSpiralValid_order [C : CountingContract] (n kl kr d : Nat) :
    (pathSpiralValid n kl kr d).Pairwise (fun a b =>
      spiralIndexKey (n / (kl + kr)) a ≤ spiralIndexKey (n / (kl + kr)) b) := by
  exact (pathSpiral_order n kl kr).filter _

theorem pathAlternating_nodup (n : Nat) : (pathAlternating n).Nodup := by
  exact List.nodup_mergeSort.mpr (List.nodup_range)

theorem pathAlternating_mem (n w : Nat) : w ∈ pathAlternating n ↔ w ≤ n := by
  rw [pathAlternating, List.Perm.mem_iff (List.mergeSort_perm _ _)]
  simp

theorem pathSpiral_nodup (n kl kr : Nat) : (pathSpiral n kl kr).Nodup := by
  exact List.nodup_mergeSort.mpr (List.nodup_range)

theorem pathSpiral_mem (n kl kr w : Nat) : w ∈ pathSpiral n kl kr ↔ w ≤ n := by
  rw [pathSpiral, List.Perm.mem_iff (List.mergeSort_perm _ _)]
  simp

theorem pathSpiralValid_mem [C : CountingContract] (n kl kr d w : Nat) :
    w ∈ pathSpiralValid n kl kr d ↔
      w ≤ n ∧ 0 < C.count w kl d * C.count (n - w) kr d := by
  simp [pathSpiralValid, pathSpiral_mem]

theorem pathSpiralValid_nodup [C : CountingContract] (n kl kr d : Nat) :
    (pathSpiralValid n kl kr d).Nodup := by
  exact (pathSpiral_nodup n kl kr).filter _

/-- An all-range alternating strategy. This is distinct from the paper's
`P_alt` when the valid split interval has different endpoints. -/
def stratAlternatingAll [C : CountingContract] : Strategy where
  decompose := decompBisect
  decompose_sum := stratRecBlock.decompose_sum
  decompose_lt := stratRecBlock.decompose_lt
  path := fun n _ _ => pathAlternating n
  path_nodup := fun n _ _ => pathAlternating_nodup n
  path_bound := fun n _ _ w hw => (pathAlternating_mem n w).mp hw
  path_valid := fun n _ _ _ w hw => (pathAlternating_mem n w).mpr hw.1
  split := fun _ nr _ => splitDivMod nr
  combine := fun _ nr _ => combineMulAdd nr
  split_bound := fun nl nr _ => splitDivMod_bound nl nr
  combine_split := fun _ nr _ => combineMulAdd_splitDivMod nr
  split_combine := fun _ nr _ _ _ _ hrr => splitDivMod_combineMulAdd nr _ _ hrr
  combine_bound := fun nl nr _ => combineMulAdd_bound nl nr

/-- Boustrophedonic strategy at fixed bound `d₀`, since `Strategy.path` has no
bound argument. The valid alternating path comes first; appended blocks have
size zero at `d₀` and complete the path for every bound. -/
def stratBousAt [C : CountingContract] (d₀ : Nat) : Strategy where
  decompose := decompBisect
  decompose_sum := stratRecBlock.decompose_sum
  decompose_lt := stratRecBlock.decompose_lt
  path := fun n kl kr => pathBousAt d₀ n kl kr
  path_nodup := fun n kl kr => pathBousAt_nodup d₀ n kl kr
  path_bound := fun n kl kr w hw => (pathBousAt_mem d₀ n kl kr w).mp hw
  path_valid := fun n kl kr _ w hw => (pathBousAt_mem d₀ n kl kr w).mpr hw.1
  split := fun _ nr _ => splitDivMod nr
  combine := fun _ nr _ => combineMulAdd nr
  split_bound := fun nl nr _ => splitDivMod_bound nl nr
  combine_split := fun _ nr _ => combineMulAdd_splitDivMod nr
  split_combine := fun _ nr _ _ _ _ hrr => splitDivMod_combineMulAdd nr _ _ hrr
  combine_bound := fun nl nr _ => combineMulAdd_bound nl nr

theorem stratBousAt_effective_path [C : CountingContract] (d₀ n kl kr : Nat) :
    ((stratBousAt d₀).path n kl kr).filter
      (fun w => 0 < C.count w kl d₀ * C.count (n - w) kr d₀) =
      pathAlternatingValid n kl kr d₀ :=
  pathBousAt_filter_positive d₀ n kl kr

/-- A spiral search strategy for a left-peeling recursion. -/
def stratSpiral [C : CountingContract] : Strategy where
  decompose := decompLeft
  decompose_sum := decompLeft_sum
  decompose_lt := decompLeft_lt
  path := pathSpiral
  path_nodup := pathSpiral_nodup
  path_bound := fun n kl kr w hw => (pathSpiral_mem n kl kr w).mp hw
  path_valid := fun n kl kr _ w hw => (pathSpiral_mem n kl kr w).mpr hw.1
  split := fun _ nr _ => splitDivMod nr
  combine := fun _ nr _ => combineMulAdd nr
  split_bound := fun nl nr _ => splitDivMod_bound nl nr
  combine_split := fun _ nr _ => combineMulAdd_splitDivMod nr
  split_combine := fun _ nr _ _ _ _ hrr => splitDivMod_combineMulAdd nr _ _ hrr
  combine_bound := fun nl nr _ => combineMulAdd_bound nl nr

theorem rank_unrank_stratAlternatingAll [C : CountingContract] (n k d r : Nat)
    (hr : r < C.count n k d) :
    rank stratAlternatingAll n k d (unrank stratAlternatingAll n k d r) = r :=
  rank_unrank stratAlternatingAll n k d r hr

theorem rank_unrank_stratBousAt [C : CountingContract] (d₀ n k r : Nat)
    (hr : r < C.count n k d₀) :
    rank (stratBousAt d₀) n k d₀ (unrank (stratBousAt d₀) n k d₀ r) = r :=
  rank_unrank (stratBousAt d₀) n k d₀ r hr

theorem rank_unrank_stratSpiral [C : CountingContract] (n k d r : Nat)
    (hr : r < C.count n k d) :
    rank stratSpiral n k d (unrank stratSpiral n k d r) = r :=
  rank_unrank stratSpiral n k d r hr

theorem unrank_rank_stratAlternatingAll [C : CountingContract] (n k d : Nat) (z : List Nat)
    (hn : z.foldl Nat.add 0 = n) (hk : z.length = k) (hb : ∀ x ∈ z, x ≤ d) :
    unrank stratAlternatingAll n k d (rank stratAlternatingAll n k d z) = z :=
  unrank_rank stratAlternatingAll n k d z hn hk hb

theorem unrank_rank_stratBousAt [C : CountingContract] (d₀ n k : Nat) (z : List Nat)
    (hn : z.foldl Nat.add 0 = n) (hk : z.length = k) (hb : ∀ x ∈ z, x ≤ d₀) :
    unrank (stratBousAt d₀) n k d₀ (rank (stratBousAt d₀) n k d₀ z) = z :=
  unrank_rank (stratBousAt d₀) n k d₀ z hn hk hb

theorem unrank_rank_stratSpiral [C : CountingContract] (n k d : Nat) (z : List Nat)
    (hn : z.foldl Nat.add 0 = n) (hk : z.length = k) (hb : ∀ x ∈ z, x ≤ d) :
    unrank stratSpiral n k d (rank stratSpiral n k d z) = z :=
  unrank_rank stratSpiral n k d z hn hk hb

#guard pathAlternating 6 == [0, 6, 1, 5, 2, 4, 3]
#guard alternateEnds [3, 4, 5, 6] == [3, 6, 4, 5]
#guard pathSpiral 8 1 2 == [2, 3, 1, 4, 0, 5, 6, 7, 8]

section
attribute [local instance] finsetInstance
#guard pathAlternatingValid 9 2 2 3 == [3, 6, 4, 5]
#guard pathBousAt 3 9 2 2 == [3, 6, 4, 5, 0, 1, 2, 7, 8, 9]
#guard pathSpiralValid 9 1 3 3 == [2, 3, 1, 0]
#guard rank (stratBousAt 3) 9 4 3 (unrank (stratBousAt 3) 9 4 3 5) == 5
end
