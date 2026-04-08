import GenericRankingBic.Orders.Colex
import GenericRankingBic.Counting.AccumulatedCount
import GenericRankingBic.Counting.Instances
import Mathlib.Tactic

private theorem offset_append_target [C : CountingContract]
    (n kl kr d w : ℕ) : ∀ (pref rest : List ℕ), w ∉ pref →
    offset n kl kr d (pref ++ w :: rest) w =
      (pref.map fun x => C.count x kl d * C.count (n - x) kr d).sum := by
  intro pref
  induction pref with
  | nil => intro rest _; simp [offset]
  | cons x xs ih =>
    intro rest hw
    have hx : x ≠ w := by
      intro h
      exact hw (by simp [h])
    have hxs : w ∉ xs := by
      intro h
      exact hw (List.mem_cons_of_mem _ h)
    simp only [List.cons_append, List.map_cons, List.sum_cons]
    simp [offset, hx, ih rest hxs]

private theorem pathDecreasing_as_last_parts (n : ℕ) :
    pathDecreasing n = (List.range (n + 1)).map (n - ·) := by
  simp only [pathDecreasing, List.range_eq_range', List.reverse_range',
    Nat.zero_add, Nat.add_sub_cancel_right]

private theorem list_sum_range (p : ℕ) (f : ℕ → ℕ) :
    ((List.range p).map f).sum = ∑ j ∈ Finset.range p, f j := by
  induction p with
  | zero => simp
  | succ p ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem colex_offset_eq_prefix [C : CountingContract]
    (n i d p : ℕ) (hp : p ≤ n) :
    offset n i 1 d (pathDecreasing n) (n - p) =
      ∑ j ∈ Finset.range p,
        C.count (n - j) i d * C.count j 1 d := by
  rw [pathDecreasing_as_last_parts]
  have hsplit : n + 1 = p + (n + 1 - p) := by omega
  rw [hsplit, List.range_add, List.map_append]
  have htail :
      (List.map (fun x => n - x) (List.map (fun x => p + x)
        (List.range (n + 1 - p)))) =
        (n - p) :: List.map (fun x => n - x) (List.map (fun x => p + x)
          (List.map Nat.succ (List.range (n - p)))) := by
    have hlen : n + 1 - p = (n - p) + 1 := by omega
    rw [hlen, List.range_succ_eq_map]
    rfl
  rw [htail]
  have hnot : n - p ∉ (List.range p).map (n - ·) := by
    simp only [List.mem_map, List.mem_range]
    rintro ⟨j, hj, heq⟩
    omega
  rw [offset_append_target n i 1 d (n - p) _ _ hnot]
  simp only [List.map_map]
  rw [list_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < p := Finset.mem_range.mp hj
  simp only [Function.comp_apply]
  rw [show n - (n - j) = j by omega]

/-- For `p ≤ min n d + 1`, count compositions with last part below `p`.
Colex visits the candidate left sums `n - p` in decreasing order. -/
def colexPrefix [C : CountingContract] (n i d p : ℕ) : ℕ :=
  ∑ j ∈ Finset.range p, C.count (n - j) i d

/-- The final prefix includes every feasible last-part block. -/
theorem colexPrefix_final [C : CountingContract] (n i d : ℕ) :
    colexPrefix n i d (min n d + 1) = C.count n (i + 1) d := by
  have htotal : C.count n (i + 1) d =
      ∑ p ∈ Finset.range (n + 1), C.count (n - p) i d * C.count p 1 d := by
    rw [C.count_path n (i + 1) i 1 d (pathDecreasing n)
      (by omega) (pathDecreasing_valid n i 1 d)
      (pathDecreasing_bound n) (pathDecreasing_nodup n)]
    rw [pathDecreasing_as_last_parts, List.map_map, list_sum_range]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [Function.comp_apply]
    rw [Nat.sub_sub_self (Nat.le_of_lt_succ (Finset.mem_range.mp hp))]
  rw [htotal]
  symm
  rw [← Finset.sum_subset (Finset.range_mono
    (show min n d + 1 ≤ n + 1 by omega))]
  · unfold colexPrefix
    apply Finset.sum_congr rfl
    intro p hp
    rw [C.count_one p d (by have := Finset.mem_range.mp hp; omega), mul_one]
  · intro p hp hnot
    have hpd : d < p := by
      have := Finset.mem_range.mp hp
      have : ¬p < min n d + 1 := by simpa using hnot
      omega
    rw [C.count_one_gt p d hpd, mul_zero]

private theorem colex_offset_eq_paper_prefix [C : CountingContract]
    (n i d p : ℕ) (hp : p ≤ min n d) :
    offset n i 1 d (pathDecreasing n) (n - p) = colexPrefix n i d p := by
  rw [colex_offset_eq_prefix n i d p (le_trans hp (min_le_left _ _))]
  unfold colexPrefix
  apply Finset.sum_congr rfl
  intro j hj
  rw [C.count_one j d (by have := Finset.mem_range.mp hj; omega), mul_one]

private theorem colex_total_eq_path_sum [C : CountingContract]
    (n i d : ℕ) :
    C.count n (i + 1) d =
      ((pathDecreasing n).map fun w =>
        C.count w i d * C.count (n - w) 1 d).sum := by
  apply C.count_path n (i + 1) i 1 d (pathDecreasing n)
  · omega
  · exact pathDecreasing_valid n i 1 d
  · exact pathDecreasing_bound n
  · exact pathDecreasing_nodup n

/-- For an admissible last part, `findBlock` selects it exactly when the
paper's prefix count first exceeds the rank. The residual is the rank within
the selected block. The statement allows earlier zero-weight blocks. -/
theorem findBlock_colex_iff_prefix_threshold [C : CountingContract]
    (n i d r p r' : ℕ) (hr : r < C.count n (i + 1) d)
    (hp : p ≤ min n d) :
    findBlock n i 1 d (pathDecreasing n) r = (n - p, r') ↔
      colexPrefix n i d p ≤ r ∧
      r < colexPrefix n i d (p + 1) ∧
      r' = r - colexPrefix n i d p := by
  have hsum : r <
      ((pathDecreasing n).map fun w =>
        C.count w i d * C.count (n - w) 1 d).sum := by
    rwa [← colex_total_eq_path_sum]
  have hoff := colex_offset_eq_paper_prefix n i d p hp
  have hone : C.count p 1 d = 1 := C.count_one p d (le_trans hp (min_le_right _ _))
  have hstep : colexPrefix n i d (p + 1) =
      colexPrefix n i d p + C.count (n - p) i d := by
    simp [colexPrefix, Finset.sum_range_succ]
  constructor
  · intro hfind
    have heq := findBlock_correct n i 1 d (pathDecreasing n) r (n - p) r'
      (pathDecreasing_nodup n) hsum hfind
    have hbound := findBlock_bound n i 1 d (pathDecreasing n) r (n - p) r'
      hsum hfind
    rw [hoff] at heq
    rw [show n - (n - p) = p by omega, hone, mul_one] at hbound
    rw [hstep]
    omega
  · rintro ⟨hlo, hhi, hr'⟩
    have hmem : n - p ∈ pathDecreasing n := by
      simp [pathDecreasing]
    have hbound : r - colexPrefix n i d p <
        C.count (n - p) i d * C.count (n - (n - p)) 1 d := by
      rw [show n - (n - p) = p by omega, hone, mul_one]
      omega
    have hfb := findBlock_offset n i 1 d (pathDecreasing n) (n - p)
      (r - colexPrefix n i d p) (pathDecreasing_nodup n) hmem hbound
    rw [hoff, Nat.add_sub_of_le hlo] at hfb
    rwa [hr']

/-- Every valid colex rank has a last-part threshold in the paper's stated
domain. This also proves that the chosen block has positive weight, excluding
zero-count blocks before or after it. -/
theorem exists_colex_prefix_threshold [C : CountingContract]
    (n i d r : ℕ) (hr : r < C.count n (i + 1) d) :
    ∃ p r', p ≤ min n d ∧
      findBlock n i 1 d (pathDecreasing n) r = (n - p, r') ∧
      colexPrefix n i d p ≤ r ∧
      r < colexPrefix n i d (p + 1) ∧
      r' = r - colexPrefix n i d p := by
  let fb := findBlock n i 1 d (pathDecreasing n) r
  have hsum : r <
      ((pathDecreasing n).map fun w =>
        C.count w i d * C.count (n - w) 1 d).sum := by
    rwa [← colex_total_eq_path_sum]
  have hmem : fb.1 ∈ pathDecreasing n :=
    findBlock_mem n i 1 d (pathDecreasing n) r fb.1 fb.2 hsum rfl
  have hle : fb.1 ≤ n := pathDecreasing_bound n fb.1 hmem
  have hbound : fb.2 < C.count fb.1 i d * C.count (n - fb.1) 1 d :=
    findBlock_bound n i 1 d (pathDecreasing n) r fb.1 fb.2 hsum rfl
  have hd : n - fb.1 ≤ d := by
    by_contra h
    have hzero := C.count_one_gt (n - fb.1) d (by omega)
    rw [hzero, mul_zero] at hbound
    omega
  refine ⟨n - fb.1, fb.2, ?_, ?_, ?_⟩
  · exact le_min (Nat.sub_le _ _) hd
  · rw [Nat.sub_sub_self hle]
  · have hiff := (findBlock_colex_iff_prefix_threshold n i d r (n - fb.1) fb.2
      hr (le_min (Nat.sub_le _ _) hd)).mp
    have hfind : findBlock n i 1 d (pathDecreasing n) r =
        (n - (n - fb.1), fb.2) := by
      simp only [Nat.sub_sub_self hle]
      rfl
    exact hiff hfind

/-- The finite set appearing in the paper's minimum expression. -/
def colexThresholdCandidates [C : CountingContract]
    (n i d r : ℕ) : Finset ℕ :=
  (Finset.range (min n d + 1)).filter
    (fun p => r < colexPrefix n i d (p + 1))

private theorem colexPrefix_mono [C : CountingContract]
    (n i d p q : ℕ) (hpq : p ≤ q) :
    colexPrefix n i d p ≤ colexPrefix n i d q := by
  unfold colexPrefix
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono hpq
  · intro j hj hnot
    exact Nat.zero_le _

/-- The selected last part is literally the minimum in the paper's bounded
prefix-threshold set. Repeated prefix values from zero-weight blocks cannot
be selected because the previous prefix is at most the valid rank. -/
theorem findBlock_colex_eq_min_prefix_threshold [C : CountingContract]
    (n i d r p r' : ℕ) (hr : r < C.count n (i + 1) d)
    (hp : p ≤ min n d)
    (hfind : findBlock n i 1 d (pathDecreasing n) r = (n - p, r')) :
    ∃ hnonempty : (colexThresholdCandidates n i d r).Nonempty,
      (colexThresholdCandidates n i d r).min' hnonempty = p := by
  have hthr := (findBlock_colex_iff_prefix_threshold n i d r p r' hr hp).mp hfind
  have hmem : p ∈ colexThresholdCandidates n i d r := by
    simp [colexThresholdCandidates, hp, hthr.2.1]
  refine ⟨⟨p, hmem⟩, ?_⟩
  apply (Finset.min'_eq_iff _ _ _).mpr
  refine ⟨hmem, ?_⟩
  intro q hq
  by_contra hlt
  have hqp : q + 1 ≤ p := by omega
  have hqthr : r < colexPrefix n i d (q + 1) := by
    exact (Finset.mem_filter.mp hq).2
  have hmono := colexPrefix_mono n i d (q + 1) p hqp
  omega

/-- With finite-set counting, the paper's strict prefix threshold is exactly
the closed-form accumulated count already proved in `AccumulatedCount`. -/
theorem colexPrefix_succ_eq_compCountAcc (n i d p : ℕ)
    (hi : 0 < i) (hp : p ≤ n) :
    ((@colexPrefix finsetInstance n i d (p + 1)) : ℤ) =
      compCountAcc n i d p := by
  rw [compCountAcc_eq_partial_sum n i d p hi hp]
  simp [colexPrefix, finsetInstance]
