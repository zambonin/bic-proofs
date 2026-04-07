import GenericRankingBic.Ranking.Correctness
import GenericRankingBic.Ranking.Strategy

/-- At non-base nodes, split into lengths `⌊k/2⌋` and `⌈k/2⌉`. -/
def decompBisect : Nat → Nat × Nat
  | 1 => (1, 0)
  | k => (k / 2, k - k / 2)

private lemma decompBisect_sum : ∀ k, k > 1 → (decompBisect k).1 + (decompBisect k).2 = k := by
  intro k hk
  cases k with
  | zero => omega
  | succ k' =>
    cases k' with
    | zero => omega
    | succ k'' =>
      simp [decompBisect]
      omega

private lemma decompBisect_lt : ∀ k, k > 1 → (decompBisect k).1 < k ∧ (decompBisect k).2 < k := by
  intro k hk
  cases k with
  | zero => omega
  | succ k' =>
    cases k' with
    | zero => omega
    | succ k'' =>
      simp [decompBisect]
      omega

/-- Balanced binary decomposition with increasing left sums and product-rank encoding. -/
def stratRecBlock [C : CountingContract] : Strategy where
  decompose := decompBisect
  decompose_sum := decompBisect_sum
  decompose_lt := decompBisect_lt
  path := fun n _kl _kr => pathIncreasing n
  path_nodup := fun n _kl _kr => pathIncreasing_nodup n
  path_bound := fun n _kl _kr => pathIncreasing_bound n
  path_valid := pathIncreasing_valid
  split := fun _nl nr _wl => splitDivMod nr
  combine := fun _nl nr _wl => combineMulAdd nr
  split_bound := fun nl nr _wl => splitDivMod_bound nl nr
  combine_split := fun _nl nr _wl => combineMulAdd_splitDivMod nr
  split_combine := fun _nl nr _wl _rl _rr _hrl hrr => splitDivMod_combineMulAdd nr _ _ hrr
  combine_bound := fun nl nr _wl => combineMulAdd_bound nl nr

theorem rank_unrank_stratRecBlock [C : CountingContract] :
    ∀ n k d r, r < C.count n k d →
    rank stratRecBlock n k d (unrank stratRecBlock n k d r) = r :=
  fun n k d r hr => rank_unrank stratRecBlock n k d r hr

theorem unrank_rank_stratRecBlock [C : CountingContract] :
    ∀ n k d z, z.foldl Nat.add 0 = n → z.length = k → (∀ x ∈ z, x ≤ d) →
    unrank stratRecBlock n k d (rank stratRecBlock n k d z) = z :=
  fun n k d z hn hk hle =>
    unrank_rank stratRecBlock n k d z hn hk hle

/-- The split used by the recursive block strategy at every non-base node. -/
theorem decompBisect_eq (k : Nat) (hk : 1 < k) :
    decompBisect k = (k / 2, k - k / 2) := by
  match k, hk with
  | k' + 2, _ => rfl

/-- The numeric form of Definition 2's ordered product: first choose the
increasing left sum, then the left composition, then the right composition. -/
theorem rank_stratRecBlock_append [C : CountingContract]
    (n k d : Nat) (L R : List Nat) (hk : 1 < k)
    (hL : L.length = k / 2) :
    rank stratRecBlock n k d (L ++ R) =
      offset n (k / 2) (k - k / 2) d (pathIncreasing n) (L.foldl Nat.add 0) +
        rank stratRecBlock (L.foldl Nat.add 0) (k / 2) d L *
          C.count (n - L.foldl Nat.add 0) (k - k / 2) d +
        rank stratRecBlock (n - L.foldl Nat.add 0) (k - k / 2) d R := by
  have h := rank_eq_offset_add_combine (C := C) stratRecBlock n k d L R hk
    (by simpa only [stratRecBlock, decompBisect_eq k hk] using hL)
  simpa only [stratRecBlock, decompBisect_eq k hk, combineMulAdd, Nat.add_assoc] using h

private theorem offset_append_cons [C : CountingContract]
    (n kl kr d w : Nat) (p s : List Nat) (hw : w ∉ p) :
    offset n kl kr d (p ++ w :: s) w =
      (p.map (fun x => C.count x kl d * C.count (n - x) kr d)).sum := by
  induction p with
  | nil => simp [offset]
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at hw
    simp only [List.cons_append, offset, if_neg (Ne.symm hw.1), List.map_cons, List.sum_cons]
    rw [ih hw.2]

/-- The block offset is the sum of the sizes of all preceding left-sum
blocks in Definition 2. -/
theorem offset_stratRecBlock_eq_sum [C : CountingContract]
    (n kl kr d w : Nat) (hw : w ≤ n) :
    offset n kl kr d (pathIncreasing n) w =
      ((List.range w).map (fun x => C.count x kl d * C.count (n - x) kr d)).sum := by
  have hrange : List.range (n + 1) =
      List.range w ++ w :: ((List.range (n - w)).map (fun x => (w + 1) + x)) := by
    have h : n + 1 = (w + 1) + (n - w) := by omega
    rw [h, List.range_add, List.range_succ]
    simp only [List.append_assoc, List.singleton_append]
  rw [pathIncreasing, hrange]
  exact offset_append_cons n kl kr d w _ _ (by simp)

/-- Each later left-sum block starts after the entire earlier block. -/
theorem offset_stratRecBlock_next_block [C : CountingContract]
    (n kl kr d a b : Nat) (hab : a < b) (hb : b ≤ n) :
    offset n kl kr d (pathIncreasing n) a +
      C.count a kl d * C.count (n - a) kr d ≤
        offset n kl kr d (pathIncreasing n) b := by
  rw [offset_stratRecBlock_eq_sum n kl kr d a (by omega),
    offset_stratRecBlock_eq_sum n kl kr d b hb]
  have h : b = (a + 1) + (b - (a + 1)) := by omega
  conv_rhs => rw [h, List.range_add, List.range_succ]
  simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  omega

/-- A composition in an earlier left-sum block has a smaller recursive-block
rank than every composition in a later left-sum block. -/
theorem rank_stratRecBlock_leftsum_lt [C : CountingContract]
    (n k d : Nat) (L₁ R₁ L₂ R₂ : List Nat)
    (hk : 1 < k)
    (hL₁ : L₁.length = k / 2)
    (hR₁ : R₁.length = k - k / 2)
    (hL₂ : L₂.length = k / 2)
    (hwl : L₁.foldl Nat.add 0 < L₂.foldl Nat.add 0)
    (hwl₂ : L₂.foldl Nat.add 0 ≤ n)
    (hsR₁ : R₁.foldl Nat.add 0 = n - L₁.foldl Nat.add 0)
    (hbL₁ : ∀ x ∈ L₁, x ≤ d)
    (hbR₁ : ∀ x ∈ R₁, x ≤ d) :
    rank stratRecBlock n k d (L₁ ++ R₁) <
      rank stratRecBlock n k d (L₂ ++ R₂) := by
  have hleft := rank_lt_count stratRecBlock (L₁.foldl Nat.add 0) (k / 2) d L₁
    rfl hL₁ hbL₁
  have hright := rank_lt_count stratRecBlock (n - L₁.foldl Nat.add 0)
    (k - k / 2) d R₁ hsR₁ hR₁ hbR₁
  have hwithin :
      rank stratRecBlock (L₁.foldl Nat.add 0) (k / 2) d L₁ *
          C.count (n - L₁.foldl Nat.add 0) (k - k / 2) d +
        rank stratRecBlock (n - L₁.foldl Nat.add 0) (k - k / 2) d R₁ <
      C.count (L₁.foldl Nat.add 0) (k / 2) d *
        C.count (n - L₁.foldl Nat.add 0) (k - k / 2) d := by
    have hm := Nat.mul_le_mul_right
      (C.count (n - L₁.foldl Nat.add 0) (k - k / 2) d)
      (Nat.succ_le_iff.mpr hleft)
    nlinarith
  have hnext := offset_stratRecBlock_next_block n (k / 2) (k - k / 2) d
    (L₁.foldl Nat.add 0) (L₂.foldl Nat.add 0) hwl hwl₂
  rw [rank_stratRecBlock_append n k d L₁ R₁ hk hL₁,
    rank_stratRecBlock_append n k d L₂ R₂ hk hL₂]
  omega

/-- Inside one left-sum block, the recursive-block rank uses the ordered
Cartesian product: left rank is the major key and right rank the minor key. -/
theorem rank_stratRecBlock_product_lex [C : CountingContract]
    (n k d : Nat) (L₁ R₁ L₂ R₂ : List Nat)
    (hk : 1 < k)
    (hL₁ : L₁.length = k / 2)
    (hL₂ : L₂.length = k / 2)
    (hR₁ : R₁.length = k - k / 2)
    (hsame : L₁.foldl Nat.add 0 = L₂.foldl Nat.add 0)
    (hsR₁ : R₁.foldl Nat.add 0 = n - L₁.foldl Nat.add 0)
    (hbR₁ : ∀ x ∈ R₁, x ≤ d)
    (hlex :
      rank stratRecBlock (L₁.foldl Nat.add 0) (k / 2) d L₁ <
        rank stratRecBlock (L₂.foldl Nat.add 0) (k / 2) d L₂ ∨
      (rank stratRecBlock (L₁.foldl Nat.add 0) (k / 2) d L₁ =
          rank stratRecBlock (L₂.foldl Nat.add 0) (k / 2) d L₂ ∧
       rank stratRecBlock (n - L₁.foldl Nat.add 0) (k - k / 2) d R₁ <
          rank stratRecBlock (n - L₂.foldl Nat.add 0) (k - k / 2) d R₂)) :
    rank stratRecBlock n k d (L₁ ++ R₁) <
      rank stratRecBlock n k d (L₂ ++ R₂) := by
  have hright := rank_lt_count stratRecBlock (n - L₁.foldl Nat.add 0)
    (k - k / 2) d R₁ hsR₁ hR₁ hbR₁
  rw [← hsame] at hlex
  rw [rank_stratRecBlock_append n k d L₁ R₁ hk hL₁,
    rank_stratRecBlock_append n k d L₂ R₂ hk hL₂, ← hsame]
  rcases hlex with hleft | ⟨hleft, hright'⟩
  · have hm := Nat.mul_le_mul_right
      (C.count (n - L₁.foldl Nat.add 0) (k - k / 2) d)
      (Nat.succ_le_iff.mpr hleft)
    nlinarith
  · rw [hleft]
    omega

/-- The strict order induced by Definition 2, defined independently of any
ranking algorithm. The right subproblem is compared only after the left
subcompositions agree. -/
def recBlockLT (n k d : Nat) (z₁ z₂ : List Nat) : Prop :=
  match k with
  | 0 => False
  | 1 => False
  | k' + 2 =>
    let kl := (k' + 2) / 2
    let kr := (k' + 2) - kl
    let L₁ := z₁.take kl
    let R₁ := z₁.drop kl
    let L₂ := z₂.take kl
    let R₂ := z₂.drop kl
    let w₁ := L₁.foldl Nat.add 0
    let w₂ := L₂.foldl Nat.add 0
    w₁ < w₂ ∨
      (w₁ = w₂ ∧
        (recBlockLT w₁ kl d L₁ L₂ ∨
          (L₁ = L₂ ∧ recBlockLT (n - w₁) kr d R₁ R₂)))
termination_by k
decreasing_by all_goals omega

theorem recBlockLT_append (n k d : Nat) (L₁ R₁ L₂ R₂ : List Nat)
    (hk : 1 < k) (hL₁ : L₁.length = k / 2) (hL₂ : L₂.length = k / 2) :
    recBlockLT n k d (L₁ ++ R₁) (L₂ ++ R₂) ↔
      L₁.foldl Nat.add 0 < L₂.foldl Nat.add 0 ∨
        (L₁.foldl Nat.add 0 = L₂.foldl Nat.add 0 ∧
          (recBlockLT (L₁.foldl Nat.add 0) (k / 2) d L₁ L₂ ∨
            (L₁ = L₂ ∧
              recBlockLT (n - L₁.foldl Nat.add 0) (k - k / 2) d R₁ R₂))) := by
  match k, hk with
  | k' + 2, _ =>
    conv_lhs => unfold recBlockLT
    have ht : (L₂ ++ R₂).take L₁.length = L₂ := by
      rw [hL₁, ← hL₂, List.take_left]
    have hd : (L₂ ++ R₂).drop L₁.length = R₂ := by
      rw [hL₁, ← hL₂, List.drop_left]
    simp only [← hL₁, List.take_left, List.drop_left, ht, hd]

private theorem recBlock_split_valid (n k d : Nat) (z : List Nat)
    (hsum : z.foldl Nat.add 0 = n)
    (hlen : z.length = k) (hbound : ∀ x ∈ z, x ≤ d) :
    let L := z.take (k / 2)
    let R := z.drop (k / 2)
    L.length = k / 2 ∧ R.length = k - k / 2 ∧
      L.foldl Nat.add 0 ≤ n ∧ R.foldl Nat.add 0 = n - L.foldl Nat.add 0 ∧
      (∀ x ∈ L, x ≤ d) ∧ (∀ x ∈ R, x ≤ d) := by
  dsimp
  have hkl : k / 2 ≤ k := Nat.div_le_self _ _
  have hsum' : (z.take (k / 2)).foldl Nat.add 0 +
      (z.drop (k / 2)).foldl Nat.add 0 = n := by
    rw [← foldl_add_append, List.take_append_drop, hsum]
  refine ⟨by simp [hlen, hkl], by simp [hlen], by omega, by omega, ?_, ?_⟩
  · intro x hx
    exact hbound x (List.mem_of_mem_take hx)
  · intro x hx
    exact hbound x (List.mem_of_mem_drop hx)

/-- For valid bounded compositions, numeric rank compares exactly as the
recursive block order of Definition 2. -/
theorem rank_stratRecBlock_lt_iff_recBlockLT [C : CountingContract]
    (n k d : Nat) (z₁ z₂ : List Nat)
    (hsum₁ : z₁.foldl Nat.add 0 = n) (hlen₁ : z₁.length = k)
    (hbound₁ : ∀ x ∈ z₁, x ≤ d)
    (hsum₂ : z₂.foldl Nat.add 0 = n) (hlen₂ : z₂.length = k)
    (hbound₂ : ∀ x ∈ z₂, x ≤ d) :
    rank stratRecBlock n k d z₁ < rank stratRecBlock n k d z₂ ↔
      recBlockLT n k d z₁ z₂ := by
  induction k using Nat.strong_induction_on generalizing n d z₁ z₂ with
  | _ k ih =>
    rcases k with _ | _ | k'
    · simp [rank, recBlockLT]
    · simp [rank, recBlockLT]
    · let k := k' + 2
      let kl := k / 2
      let kr := k - kl
      let L₁ := z₁.take kl
      let R₁ := z₁.drop kl
      let L₂ := z₂.take kl
      let R₂ := z₂.drop kl
      have hv₁ := recBlock_split_valid n k d z₁ hsum₁ hlen₁ hbound₁
      have hv₂ := recBlock_split_valid n k d z₂ hsum₂ hlen₂ hbound₂
      rcases hv₁ with ⟨hl₁, hr₁, hwl₁, hsr₁, hbl₁, hbr₁⟩
      rcases hv₂ with ⟨hl₂, hr₂, hwl₂, hsr₂, hbl₂, hbr₂⟩
      have hz₁ : z₁ = L₁ ++ R₁ := (List.take_append_drop kl z₁).symm
      have hz₂ : z₂ = L₂ ++ R₂ := (List.take_append_drop kl z₂).symm
      rw [hz₁, hz₂, recBlockLT_append n k d L₁ R₁ L₂ R₂ (by omega) hl₁ hl₂]
      have hkl : kl < k' + 2 := by dsimp [kl, k]; omega
      have hkr : kr < k' + 2 := by dsimp [kr, kl, k]; omega
      have ihL (hw : L₁.foldl Nat.add 0 = L₂.foldl Nat.add 0) :
          rank stratRecBlock (L₁.foldl Nat.add 0) kl d L₁ <
            rank stratRecBlock (L₂.foldl Nat.add 0) kl d L₂ ↔
          recBlockLT (L₁.foldl Nat.add 0) kl d L₁ L₂ := by
        simpa only [← hw] using
          (ih kl hkl (L₁.foldl Nat.add 0) d L₁ L₂ rfl hl₁ hbl₁
            (by rw [hw]) hl₂ hbl₂)
      have ihR (hL : L₁ = L₂) :
          rank stratRecBlock (n - L₁.foldl Nat.add 0) kr d R₁ <
            rank stratRecBlock (n - L₁.foldl Nat.add 0) kr d R₂ ↔
          recBlockLT (n - L₁.foldl Nat.add 0) kr d R₁ R₂ := by
        have hs₂ : R₂.foldl Nat.add 0 = n - L₁.foldl Nat.add 0 := by
          change R₂.foldl Nat.add 0 = n - L₂.foldl Nat.add 0 at hsr₂
          rw [← hL] at hsr₂
          exact hsr₂
        exact ih kr hkr (n - L₁.foldl Nat.add 0) d R₁ R₂ hsr₁ hr₁ hbr₁ hs₂ hr₂ hbr₂
      constructor
      · intro h
        by_cases hw : L₁.foldl Nat.add 0 < L₂.foldl Nat.add 0
        · exact Or.inl hw
        by_cases hw' : L₂.foldl Nat.add 0 < L₁.foldl Nat.add 0
        · have hrev := rank_stratRecBlock_leftsum_lt n k d L₂ R₂ L₁ R₁
            (by omega) hl₂ hr₂ hl₁ hw' hwl₁ hsr₂ hbl₂ hbr₂
          exact False.elim ((not_lt_of_ge (Nat.le_of_lt hrev)) h)
        have heqw : L₁.foldl Nat.add 0 = L₂.foldl Nat.add 0 := by omega
        refine Or.inr ⟨heqw, ?_⟩
        by_cases hleft : rank stratRecBlock (L₁.foldl Nat.add 0) kl d L₁ <
            rank stratRecBlock (L₂.foldl Nat.add 0) kl d L₂
        · exact Or.inl ((ihL heqw).mp hleft)
        by_cases hleft' : rank stratRecBlock (L₂.foldl Nat.add 0) kl d L₂ <
            rank stratRecBlock (L₁.foldl Nat.add 0) kl d L₁
        · have hrev := rank_stratRecBlock_product_lex n k d L₂ R₂ L₁ R₁
            (by omega) hl₂ hl₁ hr₂ heqw.symm hsr₂ hbr₂ (Or.inl hleft')
          exact False.elim ((not_lt_of_ge (Nat.le_of_lt hrev)) h)
        have heql : rank stratRecBlock (L₁.foldl Nat.add 0) kl d L₁ =
            rank stratRecBlock (L₂.foldl Nat.add 0) kl d L₂ := by omega
        have hL : L₁ = L₂ := by
          have h₁ := unrank_rank_stratRecBlock (L₁.foldl Nat.add 0) kl d L₁
            rfl hl₁ hbl₁
          have h₂ := unrank_rank_stratRecBlock (L₁.foldl Nat.add 0) kl d L₂
            (by rw [heqw]) hl₂ hbl₂
          calc
            L₁ = unrank stratRecBlock (L₁.foldl Nat.add 0) kl d
                (rank stratRecBlock (L₁.foldl Nat.add 0) kl d L₁) := h₁.symm
            _ = unrank stratRecBlock (L₁.foldl Nat.add 0) kl d
                (rank stratRecBlock (L₁.foldl Nat.add 0) kl d L₂) := by
                  rw [← heqw] at heql
                  rw [heql]
            _ = L₂ := h₂
        refine Or.inr ⟨hL, (ihR hL).mp ?_⟩
        rw [rank_stratRecBlock_append n k d L₁ R₁ (by omega) hl₁,
          rank_stratRecBlock_append n k d L₂ R₂ (by omega) hl₂] at h
        rw [← heqw] at h heql
        rw [← heql] at h
        dsimp only [kl, kr] at h heql ⊢
        omega
      · intro h
        rcases h with hw | ⟨heqw, hlex⟩
        · exact rank_stratRecBlock_leftsum_lt n k d L₁ R₁ L₂ R₂
            (by omega) hl₁ hr₁ hl₂ hw hwl₂ hsr₁ hbl₁ hbr₁
        rcases hlex with hleft | ⟨hL, hright⟩
        · exact rank_stratRecBlock_product_lex n k d L₁ R₁ L₂ R₂
            (by omega) hl₁ hl₂ hr₁ heqw hsr₁ hbr₁
            (Or.inl ((ihL heqw).mpr hleft))
        · have heql : rank stratRecBlock (L₁.foldl Nat.add 0) kl d L₁ =
              rank stratRecBlock (L₂.foldl Nat.add 0) kl d L₂ := by rw [hL]
          exact rank_stratRecBlock_product_lex n k d L₁ R₁ L₂ R₂
            (by omega) hl₁ hl₂ hr₁ heqw hsr₁ hbr₁
            (Or.inr ⟨heql, by simpa only [hL] using (ihR hL).mpr hright⟩)
