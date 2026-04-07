import GenericRankingBic.Ranking.Correctness
import Mathlib.Data.List.GetD

variable [C : CountingContract]

/-- Build the strategy's ordered sequence from its child sequences, without
calling `unrank`. Out-of-range child lookups return the empty list to keep the
definition total; the equality theorem shows valid ranks never use that default. -/
def recursiveSequence (σ : Strategy) (n k d : Nat) : List (List Nat) :=
  match k with
  | 0 => if n = 0 then [[]] else []
  | 1 => if n ≤ d then [[n]] else []
  | Nat.succ (Nat.succ k') =>
    let _h := Nat.succ_lt_succ (Nat.zero_lt_succ k')
    let kl := (σ.decompose (k' + 2)).1
    let kr := (σ.decompose (k' + 2)).2
    (List.range (C.count n (k' + 2) d)).map fun r =>
      let fb := findBlock n kl kr d (σ.path n kl kr) r
      let s := σ.split (C.count fb.1 kl d) (C.count (n - fb.1) kr d) fb.1 fb.2
      (recursiveSequence σ fb.1 kl d).getD s.1 [] ++
        (recursiveSequence σ (n - fb.1) kr d).getD s.2 []
termination_by k
decreasing_by
  · exact (σ.decompose_lt _ _h).1
  · exact (σ.decompose_lt _ _h).2

/-- The list used by the algorithm to enumerate valid ranks. -/
def unrankSequence (σ : Strategy) (n k d : Nat) : List (List Nat) :=
  (List.range (C.count n k d)).map (unrank σ n k d)

@[simp] theorem unrankSequence_length (σ : Strategy) (n k d : Nat) :
    (unrankSequence σ n k d).length = C.count n k d := by
  simp [unrankSequence]

private theorem getD_unrankSequence (σ : Strategy) (n k d r : Nat)
    (hr : r < C.count n k d) :
    (unrankSequence σ n k d).getD r [] = unrank σ n k d r := by
  simp [unrankSequence, List.getD_eq_getElem?_getD, hr]

/-- The independently constructed recursive sequence is exactly the list of
valid unrank outputs in increasing rank order. -/
theorem recursiveSequence_eq_unrankSequence :
    ∀ (σ : Strategy) n k d,
      recursiveSequence σ n k d = unrankSequence σ n k d := by
  intro σ n k d
  induction k using Nat.strong_induction_on generalizing n d with
  | _ k ih =>
    rcases k with (_ | _ | k)
    · by_cases hn : n = 0
      · subst n
        simp [recursiveSequence, unrankSequence, C.count_zero_zero, unrank]
      · have hp : 0 < n := Nat.pos_of_ne_zero hn
        simp [recursiveSequence, unrankSequence, hn, C.count_zero n d hp]
    · by_cases hn : n ≤ d
      · simp [recursiveSequence, unrankSequence, hn, C.count_one n d hn, unrank]
      · have hp : d < n := Nat.lt_of_not_ge hn
        simp [recursiveSequence, unrankSequence, hn, C.count_one_gt n d hp]
    · have hkl : (σ.decompose (k + 2)).1 < k + 2 :=
        (σ.decompose_lt (k + 2) (by omega)).1
      have hkr : (σ.decompose (k + 2)).2 < k + 2 :=
        (σ.decompose_lt (k + 2) (by omega)).2
      simp only [recursiveSequence, unrankSequence]
      apply List.map_congr_left
      intro r hr
      let kl := (σ.decompose (k + 2)).1
      let kr := (σ.decompose (k + 2)).2
      let fb := findBlock n kl kr d (σ.path n kl kr) r
      have hrank : r < C.count n (k + 2) d := List.mem_range.mp hr
      have hblock : fb.2 < C.count fb.1 kl d * C.count (n - fb.1) kr d := by
        apply findBlock_bound n kl kr d (σ.path n kl kr) r fb.1 fb.2
        · rw [← strategy_count_eq_path_sum σ n (k + 2) d (by omega)]
          exact hrank
        · rfl
      have hs := σ.split_bound (C.count fb.1 kl d)
        (C.count (n - fb.1) kr d) fb.1 fb.2 hblock
      rw [ih kl hkl fb.1 d, ih kr hkr (n - fb.1) d]
      rw [getD_unrankSequence σ fb.1 kl d _ hs.1,
        getD_unrankSequence σ (n - fb.1) kr d _ hs.2]
      conv_rhs => rw [unrank]

@[simp] theorem recursiveSequence_length (σ : Strategy) (n k d : Nat) :
    (recursiveSequence σ n k d).length = C.count n k d := by
  rw [recursiveSequence_eq_unrankSequence, unrankSequence_length]

/-- The element at each valid sequence index is the generic unrank output. -/
theorem recursiveSequence_getD (σ : Strategy) (n k d r : Nat)
    (hr : r < C.count n k d) :
    (recursiveSequence σ n k d).getD r [] = unrank σ n k d r := by
  rw [recursiveSequence_eq_unrankSequence]
  exact getD_unrankSequence σ n k d r hr

/-- Ranking recovers the index of every element of the recursive sequence. -/
theorem rank_recursiveSequence_getD (σ : Strategy) (n k d r : Nat)
    (hr : r < C.count n k d) :
    rank σ n k d ((recursiveSequence σ n k d).getD r []) = r := by
  rw [recursiveSequence_getD σ n k d r hr]
  exact rank_unrank σ n k d r hr

/-- The recursive enumeration has no repeated composition. -/
theorem recursiveSequence_nodup (σ : Strategy) (n k d : Nat) :
    (recursiveSequence σ n k d).Nodup := by
  rw [recursiveSequence_eq_unrankSequence]
  unfold unrankSequence
  apply List.Nodup.map_on (l := List.range (C.count n k d))
  · intro r hr s hs heq
    have hr' : r < C.count n k d := List.mem_range.mp hr
    have hs' : s < C.count n k d := List.mem_range.mp hs
    calc
      r = rank σ n k d (unrank σ n k d r) := (rank_unrank σ n k d r hr').symm
      _ = rank σ n k d (unrank σ n k d s) := congrArg _ heq
      _ = s := rank_unrank σ n k d s hs'
  · exact List.nodup_range

/-- The recursive sequence contains precisely the bounded compositions. -/
theorem mem_recursiveSequence_iff (σ : Strategy) (n k d : Nat) (z : List Nat) :
    z ∈ recursiveSequence σ n k d ↔
      z.foldl Nat.add 0 = n ∧ z.length = k ∧ ∀ x ∈ z, x ≤ d := by
  rw [recursiveSequence_eq_unrankSequence]
  unfold unrankSequence
  rw [List.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hr' : r < C.count n k d := List.mem_range.mp hr
    exact ⟨unrank_sum σ n k d r hr', unrank_length σ n k d r hr',
      unrank_parts_bounded σ n k d r hr'⟩
  · rintro ⟨hn, hk, hd⟩
    have hr := rank_lt_count σ n k d z hn hk hd
    exact ⟨rank σ n k d z, List.mem_range.mpr hr,
      unrank_rank σ n k d z hn hk hd⟩
