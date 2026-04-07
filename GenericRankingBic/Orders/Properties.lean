import GenericRankingBic.Orders.Colex
import GenericRankingBic.Orders.Gray

variable [C : CountingContract]

private theorem offset_block_le_of_descending (n kl kr d : Nat)
    (p : List Nat) (hp : p.Pairwise (· > ·)) (x y : Nat)
    (hx : x ∈ p) (hy : y ∈ p) (hxy : y < x) :
    offset n kl kr d p x + C.count x kl d * C.count (n - x) kr d ≤
      offset n kl kr d p y := by
  induction p with
  | nil => simp at hx
  | cons w ws ih =>
    have hpair := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hx with rfl | hx'
    · have hne : x ≠ y := by omega
      simp [offset, hne]
    · rcases List.mem_cons.mp hy with rfl | hy'
      · have hgt := hpair.1 x hx'
        omega
      · have hne_x : w ≠ x := by
          have hgt := hpair.1 x hx'
          omega
        have hne_y : w ≠ y := by
          have hgt := hpair.1 y hy'
          omega
        have htail := ih hpair.2 hx' hy'
        simp only [offset, if_neg hne_x, if_neg hne_y]
        omega

private theorem offset_block_le_of_ascending (n kl kr d : Nat)
    (p : List Nat) (hp : p.Pairwise (· < ·)) (x y : Nat)
    (hx : x ∈ p) (hy : y ∈ p) (hxy : x < y) :
    offset n kl kr d p x + C.count x kl d * C.count (n - x) kr d ≤
      offset n kl kr d p y := by
  induction p with
  | nil => simp at hx
  | cons w ws ih =>
    have hpair := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hx with rfl | hx'
    · have hne : x ≠ y := by omega
      simp [offset, hne]
    · rcases List.mem_cons.mp hy with rfl | hy'
      · have hlt := hpair.1 x hx'
        omega
      · have hne_x : w ≠ x := by
          have hlt := hpair.1 x hx'
          omega
        have hne_y : w ≠ y := by
          have hlt := hpair.1 y hy'
          omega
        have htail := ih hpair.2 hx' hy'
        simp only [offset, if_neg hne_x, if_neg hne_y]
        omega

omit C in
private theorem pathDecreasing_pairwise (n : Nat) :
    (pathDecreasing n).Pairwise (· > ·) := by
  have h : (List.range (n + 1)).Pairwise (· < ·) := List.pairwise_lt_range
  simpa only [pathDecreasing, gt_iff_lt] using (List.pairwise_reverse.mpr h)

omit C in
private theorem pathIncreasing_pairwise (n : Nat) :
    (pathIncreasing n).Pairwise (· < ·) := by
  simpa only [pathIncreasing] using (List.pairwise_lt_range :
    (List.range (n + 1)).Pairwise (· < ·))

/-- In the colex strategy, fixing the last part leaves the prefix in its
ordinary colex order. -/
theorem rank_stratColex_append_singleton (n k d a : Nat) (t : List Nat)
    (hk : 0 < k) (ht : t.length = k) (ha : a ≤ d)
    (hs : t.foldl Nat.add 0 + a = n) :
    rank stratColex n (k + 1) d (t ++ [a]) =
      offset n k 1 d (pathDecreasing n) (n - a) +
        rank stratColex (n - a) k d t := by
  have htl : t.foldl Nat.add 0 = n - a := by omega
  have hdec : decompRight (k + 1) = (k, 1) := by
    cases k with
    | zero => omega
    | succ k' => rfl
  have hsplit := rank_eq_offset_add_combine (C := C) stratColex n (k + 1) d t [a]
    (by omega) (by simpa [stratColex, hdec] using ht)
  simp only [stratColex, hdec, combineMulAdd] at hsplit
  have hna : n - t.foldl Nat.add 0 = a := by omega
  have hna2 : n - (n - a) = a := by omega
  rw [htl, hna2, C.count_one a d ha] at hsplit
  simpa only [Nat.mul_one, rank, Nat.add_zero] using hsplit

/-- In each odd first-part block, the Gray strategy reverses the rank of the
remaining suffix. -/
theorem rank_stratGray_cons (n k d a : Nat) (t : List Nat)
    (hk : 0 < k) (ht : t.length = k) (ha : a ≤ d)
    (hs : a + t.foldl Nat.add 0 = n)
    (hb : ∀ x ∈ t, x ≤ d) :
    rank stratGray n (k + 1) d (a :: t) =
      offset n 1 k d (pathIncreasing n) a +
        (if a % 2 = 0 then rank stratGray (n - a) k d t
         else C.count (n - a) k d - 1 - rank stratGray (n - a) k d t) := by
  have htl : t.foldl Nat.add 0 = n - a := by omega
  have hdec : decompLeft (k + 1) = (1, k) := by
    cases k with
    | zero => omega
    | succ k' => rfl
  have hrt : rank stratGray (n - a) k d t < C.count (n - a) k d :=
    rank_lt_count stratGray (n - a) k d t htl ht hb
  have hsplit := rank_eq_offset_add_combine (C := C) stratGray n (k + 1) d [a] t
    (by omega) (by simp [stratGray, hdec])
  have hcpos : C.count (n - a) k d ≠ 0 := by omega
  simp only [stratGray, hdec] at hsplit
  have hfold : List.foldl Nat.add 0 [a] = a := by simp
  rw [hfold] at hsplit
  simp only [List.singleton_append] at hsplit
  change rank stratGray n (k + 1) d (a :: t) =
    offset n 1 k d (pathIncreasing n) a +
      combineGray (C.count a 1 d) (C.count (n - a) k d) a
        (rank stratGray a 1 d [a]) (rank stratGray (n - a) k d t) at hsplit
  have hsingle : rank stratGray a 1 d [a] = 0 := by simp [rank]
  rw [hsingle, C.count_one a d ha] at hsplit
  unfold combineGray at hsplit
  simpa [hcpos] using hsplit

/-- Within a fixed last-part block, colex compares the prefixes in the
same order. -/
theorem rank_stratColex_same_last_iff (n k d a : Nat) (s t : List Nat)
    (hk : 0 < k) (hslen : s.length = k) (htlen : t.length = k)
    (ha : a ≤ d)
    (hssum : s.foldl Nat.add 0 + a = n)
    (htsum : t.foldl Nat.add 0 + a = n) :
    rank stratColex n (k + 1) d (s ++ [a]) <
      rank stratColex n (k + 1) d (t ++ [a]) ↔
    rank stratColex (n - a) k d s < rank stratColex (n - a) k d t := by
  rw [rank_stratColex_append_singleton n k d a s hk hslen ha hssum,
    rank_stratColex_append_singleton n k d a t hk htlen ha htsum]
  omega

/-- Different last parts are ordered increasingly, as in the paper's
colexicographic recursion. -/
theorem rank_stratColex_last_lt (n k d a b : Nat) (s t : List Nat)
    (hk : 0 < k) (hslen : s.length = k) (htlen : t.length = k)
    (ha : a ≤ d) (hb : b ≤ d) (hab : a < b)
    (hssum : s.foldl Nat.add 0 + a = n)
    (htsum : t.foldl Nat.add 0 + b = n)
    (hsbound : ∀ x ∈ s, x ≤ d) :
    rank stratColex n (k + 1) d (s ++ [a]) <
      rank stratColex n (k + 1) d (t ++ [b]) := by
  have hs : s.foldl Nat.add 0 = n - a := by omega
  have hrs := rank_lt_count stratColex (n - a) k d s hs hslen hsbound
  have hmem_a : n - a ∈ pathDecreasing n := by
    simp [pathDecreasing, List.mem_range]
  have hmem_b : n - b ∈ pathDecreasing n := by
    simp [pathDecreasing, List.mem_range]
  have hba : n - b < n - a := by omega
  have hblock := offset_block_le_of_descending n k 1 d (pathDecreasing n)
    (pathDecreasing_pairwise n) (n - a) (n - b) hmem_a hmem_b hba
  have hna : n - (n - a) = a := by omega
  rw [hna, C.count_one a d ha] at hblock
  rw [rank_stratColex_append_singleton n k d a s hk hslen ha hssum,
    rank_stratColex_append_singleton n k d b t hk htlen hb htsum]
  omega

/-- Within a fixed first-part block, the Gray strategy uses forward order
for even first parts and reversed order for odd first parts. -/
theorem rank_stratGray_same_first_iff (n k d a : Nat) (s t : List Nat)
    (hk : 0 < k) (hslen : s.length = k) (htlen : t.length = k)
    (ha : a ≤ d)
    (hssum : a + s.foldl Nat.add 0 = n)
    (htsum : a + t.foldl Nat.add 0 = n)
    (hsbound : ∀ x ∈ s, x ≤ d) (htbound : ∀ x ∈ t, x ≤ d) :
    rank stratGray n (k + 1) d (a :: s) <
      rank stratGray n (k + 1) d (a :: t) ↔
      (if a % 2 = 0 then
        rank stratGray (n - a) k d s < rank stratGray (n - a) k d t
       else rank stratGray (n - a) k d t < rank stratGray (n - a) k d s) := by
  have hs : s.foldl Nat.add 0 = n - a := by omega
  have ht : t.foldl Nat.add 0 = n - a := by omega
  have hrs := rank_lt_count stratGray (n - a) k d s hs hslen hsbound
  have hrt := rank_lt_count stratGray (n - a) k d t ht htlen htbound
  rw [rank_stratGray_cons n k d a s hk hslen ha hssum hsbound,
    rank_stratGray_cons n k d a t hk htlen ha htsum htbound]
  split_ifs <;> omega

/-- Different first parts are ordered increasingly in the reflected Gray
strategy; reflection only changes traversal within a block. -/
theorem rank_stratGray_first_lt (n k d a b : Nat) (s t : List Nat)
    (hk : 0 < k) (hslen : s.length = k) (htlen : t.length = k)
    (ha : a ≤ d) (hb : b ≤ d) (hab : a < b)
    (hssum : a + s.foldl Nat.add 0 = n)
    (htsum : b + t.foldl Nat.add 0 = n)
    (hsbound : ∀ x ∈ s, x ≤ d) (htbound : ∀ x ∈ t, x ≤ d) :
    rank stratGray n (k + 1) d (a :: s) <
      rank stratGray n (k + 1) d (b :: t) := by
  have hss : s.foldl Nat.add 0 = n - a := by omega
  have hrs := rank_lt_count stratGray (n - a) k d s hss hslen hsbound
  have hmem_a : a ∈ pathIncreasing n := by
    simp [pathIncreasing, List.mem_range]
    omega
  have hmem_b : b ∈ pathIncreasing n := by
    simp [pathIncreasing, List.mem_range]
    omega
  have hblock := offset_block_le_of_ascending n 1 k d (pathIncreasing n)
    (pathIncreasing_pairwise n) a b hmem_a hmem_b hab
  rw [C.count_one a d ha] at hblock
  rw [rank_stratGray_cons n k d a s hk hslen ha hssum hsbound,
    rank_stratGray_cons n k d b t hk htlen hb htsum htbound]
  split_ifs <;> omega

/-- Colexicographic comparison reads compositions from right to left. -/
def ColexLt (s t : List Nat) : Prop := List.Lex (· < ·) s.reverse t.reverse

/-- The concrete colex ranking strategy induces exactly the colexicographic
order from Definition 1 on valid bounded compositions. -/
theorem rank_stratColex_lt_iff_colex (n k d : Nat) (s t : List Nat)
    (hslen : s.length = k) (htlen : t.length = k)
    (hssum : s.foldl Nat.add 0 = n) (htsum : t.foldl Nat.add 0 = n)
    (hsbound : ∀ x ∈ s, x ≤ d) (htbound : ∀ x ∈ t, x ≤ d) :
    rank stratColex n k d s < rank stratColex n k d t ↔ ColexLt s t := by
  induction s using List.reverseRecOn generalizing t k n with
  | nil =>
    have hk : k = 0 := by simpa using hslen.symm
    have ht : t = [] := by
      have : t.length = 0 := by omega
      simpa using List.length_eq_zero_iff.mp this
    subst k
    subst t
    simp [ColexLt, rank]
  | append_singleton s a ih =>
    cases t using List.reverseRecOn with
    | nil =>
      simp only [List.length_nil, List.length_append, List.length_singleton] at htlen hslen
      omega
    | append_singleton t b =>
      have hslen' : s.length + 1 = k := by simpa using hslen
      have htlen' : t.length + 1 = k := by simpa using htlen
      have hpre : s.length = t.length := by omega
      have hssum' : s.foldl Nat.add 0 + a = n := by
        simpa [foldl_add_append] using hssum
      have htsum' : t.foldl Nat.add 0 + b = n := by
        simpa [foldl_add_append] using htsum
      have ha : a ≤ d := hsbound a (by simp)
      have hb : b ≤ d := htbound b (by simp)
      have hsbound' : ∀ x ∈ s, x ≤ d := by
        intro x hx
        exact hsbound x (by simp [hx])
      have htbound' : ∀ x ∈ t, x ≤ d := by
        intro x hx
        exact htbound x (by simp [hx])
      by_cases hzero : s.length = 0
      · have hs : s = [] := List.length_eq_zero_iff.mp hzero
        have ht : t = [] := List.length_eq_zero_iff.mp (by omega)
        subst s
        subst t
        have hab : a = b := by omega
        subst b
        simp [ColexLt]
      · have hk : 0 < s.length := by omega
        have hkl : k = s.length + 1 := by omega
        by_cases hab : a < b
        · have hRank := rank_stratColex_last_lt n s.length d a b s t hk rfl hpre.symm
            ha hb hab hssum' htsum' hsbound'
          have hLex : ColexLt (s ++ [a]) (t ++ [b]) := by
            simp only [ColexLt, List.reverse_append, List.reverse_singleton,
              List.singleton_append]
            exact List.Lex.rel hab
          exact iff_of_true (by simpa [hkl] using hRank) hLex
        · by_cases hba : b < a
          · have hRank := rank_stratColex_last_lt n s.length d b a t s hk hpre.symm rfl
              hb ha hba htsum' hssum' htbound'
            have hNotLex : ¬ ColexLt (s ++ [a]) (t ++ [b]) := by
              simp only [ColexLt, List.reverse_append, List.reverse_singleton,
                List.singleton_append]
              intro h
              cases h with
              | rel h => omega
              | cons h => omega
            exact iff_of_false (by
              intro h
              have h' : rank stratColex n (s.length + 1) d (s ++ [a]) <
                  rank stratColex n (s.length + 1) d (t ++ [b]) := by simpa [hkl] using h
              omega) hNotLex
          · have heq : a = b := by omega
            subst b
            rw [hkl, rank_stratColex_same_last_iff n s.length d a s t hk rfl hpre.symm
              ha hssum' htsum']
            have hssum2 : s.foldl Nat.add 0 = n - a := by omega
            have htsum2 : t.foldl Nat.add 0 = n - a := by omega
            have hIH := ih (n - a) s.length t rfl hpre.symm hssum2 htsum2
              hsbound' htbound'
            simpa only [ColexLt, List.reverse_append, List.reverse_singleton,
              List.singleton_append, List.nil_append, List.lex_cons_iff] using hIH
