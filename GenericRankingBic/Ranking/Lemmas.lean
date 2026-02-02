import GenericRankingBic.Counting.Contract
import GenericRankingBic.Ranking.Basic
import GenericRankingBic.Ranking.Strategy
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

lemma foldl_add_base (l : List Nat) (a : Nat) : l.foldl Nat.add a = a + l.foldl Nat.add 0 := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    have h1 : (x :: xs).foldl Nat.add a = xs.foldl Nat.add (a + x) := rfl
    have h2 : (x :: xs).foldl Nat.add 0 = xs.foldl Nat.add (0 + x) := rfl
    rw [h1, h2, Nat.zero_add, ih (a + x), ih x]
    omega

lemma foldl_add_append (l1 l2 : List Nat) :
    (l1 ++ l2).foldl Nat.add 0 = l1.foldl Nat.add 0 + l2.foldl Nat.add 0 := by
  have h : ∀ a, (l1 ++ l2).foldl Nat.add a = l1.foldl Nat.add a + l2.foldl Nat.add 0 := by
    intro a; rw [List.foldl_append, foldl_add_base]
  exact h 0

lemma foldl_take_le (l : List Nat) (n : Nat) :
    (l.take n).foldl Nat.add 0 ≤ l.foldl Nat.add 0 := by
  have := foldl_add_append (l.take n) (l.drop n)
  rw [List.take_append_drop] at this
  omega

variable [C : CountingContract]

/-- The strategy path partitions the count into products of child counts. -/
theorem strategy_count_eq_path_sum (σ : Strategy) (n k d : Nat) (hk : 1 < k) :
    C.count n k d =
      ((σ.path n (σ.decompose k).1 (σ.decompose k).2).map
        (fun w => C.count w (σ.decompose k).1 d *
          C.count (n - w) (σ.decompose k).2 d)).sum := by
  exact C.count_path n k (σ.decompose k).1 (σ.decompose k).2 d _
    (σ.decompose_sum k hk).symm (σ.path_valid n _ _ d)
    (σ.path_bound n _ _) (σ.path_nodup n _ _)

/-- `findBlock` returns an element of the path. -/
theorem findBlock_mem :
    ∀ n kl kr d path r wl r',
    r < (path.map (fun w => C.count w kl d * C.count (n - w) kr d)).sum →
    findBlock n kl kr d path r = (wl, r') → wl ∈ path := by
  intro n kl kr d path r wl r' hr h
  induction path generalizing r wl r' with
  | nil => contradiction
  | cons w ws ih =>
    by_cases hr' : r < C.count w kl d * C.count (n - w) kr d <;> simp_all +decide [findBlock]
    exact Or.inr (ih _ _ _ (by omega) h)

/-- `findBlock` decomposes the rank: r = offset to block wl + residual rank r'. -/
lemma findBlock_correct :
    ∀ n kl kr d path r wl r',
    path.Nodup →
    r < (path.map (fun w => C.count w kl d * C.count (n - w) kr d)).sum →
    findBlock n kl kr d path r = (wl, r') →
    r = offset n kl kr d path wl + r' := by
  intros n kl kr d path r wl r' hpath hr hfindBlock
  induction path generalizing r wl r' with
  | nil => contradiction
  | cons w ws ih =>
    unfold findBlock at hfindBlock
    simp +zetaDelta at *
    split_ifs at hfindBlock
    · -- r falls in the first block, residual is r itself
      cases hfindBlock
      simp +arith +decide [offset]
    · -- r falls in a later block; recurse into the tail
      specialize ih _ _ _ hpath.2 (by omega) hfindBlock
      rw [show offset n kl kr d (w :: ws) wl =
          if w = wl then 0
          else CountingContract.count w kl d * CountingContract.count (n - w) kr d +
            offset n kl kr d ws wl from rfl]
      split_ifs <;> simp_all +decide [Nat.sub_eq_iff_eq_add]
      · exact absurd (findBlock_mem n kl kr d ws (offset n kl kr d ws wl + r') wl r' (by omega)
          hfindBlock) (by aesop)
      · ring

/-- The residual rank returned by `findBlock` is strictly less than the block size. -/
lemma findBlock_bound :
    ∀ n kl kr d path r wl r',
    r < (path.map (fun w => C.count w kl d * C.count (n - w) kr d)).sum →
    findBlock n kl kr d path r = (wl, r') →
    r' < C.count wl kl d * C.count (n - wl) kr d := by
  intros n kl kr d path r wl r' hr hfind
  induction path generalizing r wl r' with
  | nil => contradiction
  | cons w ws hpath =>
    by_cases h : r < C.count w kl d * C.count (n - w) kr d <;> simp_all +decide [findBlock]
    exact hpath _ _ _ (by omega) hfind

/-- Given a block's offset and a residual rank within it, `findBlock` recovers the block. -/
lemma findBlock_offset :
    ∀ n kl kr d path wl r',
    path.Nodup → wl ∈ path →
    r' < C.count wl kl d * C.count (n - wl) kr d →
    findBlock n kl kr d path (offset n kl kr d path wl + r') = (wl, r') := by
  intro n kl kr d path wl r' hpath hwl hr'
  induction path generalizing wl r' with
  | nil => simp +decide [*] at *
  | cons w ws ih =>
    simp +decide [*, findBlock] at *
    cases hwl <;> simp_all +decide [offset]
    grind +ring

/-- The offset to a block plus the block size is at most the total sum. -/
lemma offset_le_sum :
    ∀ n kl kr d path wl,
    path.Nodup → wl ∈ path →
    offset n kl kr d path wl + C.count wl kl d * C.count (n - wl) kr d ≤
      (path.map (fun w => C.count w kl d * C.count (n - w) kr d)).sum := by
  intro n kl kr d path wl hpath hwl
  induction path generalizing wl with
  | nil => contradiction
  | cons w ws ih =>
    by_cases h : w = wl <;> simp_all +decide [offset]
    grind

/-- `rank` decomposes as the offset to the split point plus the combined sub-rank. -/
lemma rank_eq_offset_add_combine :
    ∀ σ n k d L R,
    k > 1 → L.length = (σ.decompose k).1 →
    rank σ n k d (L ++ R) =
      offset n (σ.decompose k).1 (σ.decompose k).2 d
        (σ.path n (σ.decompose k).1 (σ.decompose k).2) (L.foldl Nat.add 0) +
      σ.combine
        (C.count (L.foldl Nat.add 0) (σ.decompose k).1 d)
        (C.count (n - L.foldl Nat.add 0) (σ.decompose k).2 d)
        (L.foldl Nat.add 0)
        (rank σ (L.foldl Nat.add 0) (σ.decompose k).1 d L)
        (rank σ (n - L.foldl Nat.add 0) (σ.decompose k).2 d R) := by
  intro σ n k d L R hk hlen
  match k, hk, hlen with
  | k'' + 2, _, hlen =>
    conv_lhs => unfold rank
    simp only [← hlen, List.take_left, List.drop_left]

/-- Unranking a valid index produces the prescribed total and length. -/
theorem unrank_sum_length :
    ∀ (σ : Strategy) n k d r, r < C.count n k d →
    (unrank σ n k d r).foldl Nat.add 0 = n ∧ (unrank σ n k d r).length = k := by
  intro σ n k d r hr
  induction k using Nat.strong_induction_on generalizing n r with
  | h k ih =>
    rcases k with _ | _ | k
    · have hn : n = 0 := by
        by_contra hn
        rw [C.count_zero n d (Nat.pos_of_ne_zero hn)] at hr
        omega
      subst n
      simp [unrank]
    · simp [unrank]
    · let kl := (σ.decompose (k + 2)).1
      let kr := (σ.decompose (k + 2)).2
      let fb := findBlock n kl kr d (σ.path n kl kr) r
      let s := σ.split (C.count fb.1 kl d) (C.count (n - fb.1) kr d) fb.1 fb.2
      have hsum : r < ((σ.path n kl kr).map
          (fun w => C.count w kl d * C.count (n - w) kr d)).sum := by
        rwa [← strategy_count_eq_path_sum σ n (k + 2) d (by omega)]
      have hmem := findBlock_mem n kl kr d (σ.path n kl kr) r fb.1 fb.2 hsum rfl
      have hfb := findBlock_bound n kl kr d (σ.path n kl kr) r fb.1 fb.2 hsum rfl
      have hs := σ.split_bound _ _ fb.1 fb.2 hfb
      have hleft := ih kl (σ.decompose_lt (k + 2) (by omega)).1 fb.1 s.1 hs.1
      have hright := ih kr (σ.decompose_lt (k + 2) (by omega)).2 (n - fb.1) s.2 hs.2
      rw [unrank]
      change (unrank σ fb.1 kl d s.1 ++ unrank σ (n - fb.1) kr d s.2).foldl Nat.add 0 = n ∧
        (unrank σ fb.1 kl d s.1 ++ unrank σ (n - fb.1) kr d s.2).length = k + 2
      rw [foldl_add_append, List.length_append, hleft.1, hright.1, hleft.2, hright.2]
      exact ⟨Nat.add_sub_of_le (σ.path_bound n kl kr fb.1 hmem),
        σ.decompose_sum (k + 2) (by omega)⟩

lemma unrank_sum (σ : Strategy) n k d r (h : r < C.count n k d) :
    (unrank σ n k d r).foldl Nat.add 0 = n := (unrank_sum_length σ n k d r h).1

lemma unrank_length (σ : Strategy) n k d r (h : r < C.count n k d) :
    (unrank σ n k d r).length = k := (unrank_sum_length σ n k d r h).2

/-- Every part produced by unranking a valid index is at most `d`. -/
theorem unrank_parts_bounded :
    ∀ (σ : Strategy) n k d r, r < C.count n k d →
    ∀ x ∈ unrank σ n k d r, x ≤ d := by
  intro σ n k d r hr
  induction k using Nat.strong_induction_on generalizing n r with
  | h k ih =>
    rcases k with _ | _ | k
    · simp [unrank]
    · have hn : n ≤ d := by
        by_contra hn
        rw [C.count_one_gt n d (by omega)] at hr
        omega
      simpa [unrank] using hn
    · let kl := (σ.decompose (k + 2)).1
      let kr := (σ.decompose (k + 2)).2
      let fb := findBlock n kl kr d (σ.path n kl kr) r
      let s := σ.split (C.count fb.1 kl d) (C.count (n - fb.1) kr d) fb.1 fb.2
      have hsum : r < ((σ.path n kl kr).map
          (fun w => C.count w kl d * C.count (n - w) kr d)).sum := by
        rwa [← strategy_count_eq_path_sum σ n (k + 2) d (by omega)]
      have hfb := findBlock_bound n kl kr d (σ.path n kl kr) r fb.1 fb.2 hsum rfl
      have hs := σ.split_bound _ _ fb.1 fb.2 hfb
      rw [unrank]
      change ∀ x ∈ unrank σ fb.1 kl d s.1 ++ unrank σ (n - fb.1) kr d s.2, x ≤ d
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ih kl (σ.decompose_lt (k + 2) (by omega)).1 fb.1 s.1 hs.1 x hx
      · exact ih kr (σ.decompose_lt (k + 2) (by omega)).2 (n - fb.1) s.2 hs.2 x hx
