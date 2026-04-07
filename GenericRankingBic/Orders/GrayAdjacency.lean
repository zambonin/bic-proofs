import GenericRankingBic.Orders.Properties
import GenericRankingBic.Orders.RecursiveBlock

variable [C : CountingContract]

/-- Every counting implementation satisfying the convolution contract has
exactly the feasible support. -/
theorem gray_count_pos_iff (n k d : Nat) :
    0 < C.count n k d ↔ n ≤ k * d := by
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    rcases k with _ | _ | k
    · cases n with
      | zero => simp [C.count_zero_zero]
      | succ n => simp [C.count_zero (n + 1) d (by omega)]
    · by_cases hn : n ≤ d
      · simp [C.count_one n d hn, hn]
      · have hgt : n > d := by omega
        simp [C.count_one_gt n d hgt, hn]
    · have hconv : C.count n (k + 2) d =
          ((List.range (n + 1)).map
            (fun a => C.count a 1 d * C.count (n - a) (k + 1) d)).sum := by
        apply C.count_path n (k + 2) 1 (k + 1) d (List.range (n + 1))
        · omega
        · intro a ha
          exact List.mem_range.mpr (by omega)
        · intro a ha
          exact Nat.le_of_lt_succ (List.mem_range.mp ha)
        · exact List.nodup_range
      change 0 < C.count n (k + 2) d ↔ n ≤ (k + 2) * d
      constructor
      · intro hpos
        by_contra hn
        have hgt : (k + 2) * d < n := by omega
        have hzero : C.count n (k + 2) d = 0 := by
          rw [hconv]
          apply List.sum_eq_zero
          intro x hx
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
          have han : a ≤ n := Nat.le_of_lt_succ (List.mem_range.mp ha)
          by_cases had : a ≤ d
          · have hbad : (k + 1) * d < n - a := by
              have hmul : (k + 2) * d = (k + 1) * d + d := by ring
              omega
            have hzero' : C.count (n - a) (k + 1) d = 0 := by
              have hh := ih (k + 1) (by omega) (n - a)
              omega
            simp [hzero']
          · have hzero' := C.count_one_gt a d (by omega)
            simp [hzero']
        omega
      · intro hn
        let a := n - (k + 1) * d
        have had : a ≤ d := by
          have hmul : (k + 2) * d = (k + 1) * d + d := by ring
          dsimp [a]
          omega
        have han : a ≤ n := Nat.sub_le _ _
        have hrest : n - a ≤ (k + 1) * d := by dsimp [a]; omega
        have hpos1 : 0 < C.count a 1 d := by rw [C.count_one a d had]; omega
        have hpos2 : 0 < C.count (n - a) (k + 1) d :=
          (ih (k + 1) (by omega) (n - a)).2 hrest
        have hle : C.count a 1 d * C.count (n - a) (k + 1) d ≤
            C.count n (k + 2) d := by
          rw [hconv]
          apply List.le_sum_of_mem
          exact List.mem_map.mpr ⟨a, List.mem_range.mpr (by omega), rfl⟩
        have hmulpos := Nat.mul_pos hpos1 hpos2
        omega

private theorem gray_offset_first (n k d : Nat) :
    offset n 1 k d (pathIncreasing n) (n - k * d) = 0 := by
  rw [offset_stratRecBlock_eq_sum n 1 k d (n - k * d) (Nat.sub_le _ _)]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  have hlt : a < n - k * d := List.mem_range.mp ha
  have hbad : k * d < n - a := by omega
  have hzero : C.count (n - a) k d = 0 := by
    have h := gray_count_pos_iff (C := C) (n - a) k d
    omega
  simp [hzero]

private theorem gray_offset_last (n k d : Nat) :
    offset n 1 k d (pathIncreasing n) (min n d) +
      C.count (n - min n d) k d = C.count n (k + 1) d := by
  let b := min n d
  have hbn : b ≤ n := Nat.min_le_left _ _
  have hcount : C.count n (k + 1) d =
      ((List.range (n + 1)).map
        (fun a => C.count a 1 d * C.count (n - a) k d)).sum := by
    apply C.count_path n (k + 1) 1 k d (List.range (n + 1))
    · omega
    · intro a ha
      exact List.mem_range.mpr (by omega)
    · intro a ha
      exact Nat.le_of_lt_succ (List.mem_range.mp ha)
    · exact List.nodup_range
  have hrange : List.range (n + 1) =
      List.range b ++ b :: (List.range (n - b)).map (fun x => b + 1 + x) := by
    have h : n + 1 = (b + 1) + (n - b) := by omega
    rw [h, List.range_add, List.range_succ]
    simp only [List.append_assoc, List.singleton_append]
  have htail :
      (((List.range (n - b)).map (fun x => b + 1 + x)).map
        (fun a => C.count a 1 d * C.count (n - a) k d)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    have hzd : b + 1 + z > d := by
      dsimp [b]
      have hzlt : z < n - min n d := List.mem_range.mp hz
      omega
    simp [C.count_one_gt _ d hzd]
  rw [offset_stratRecBlock_eq_sum n 1 k d b hbn, hcount, hrange]
  simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  rw [htail, C.count_one b d (Nat.min_le_right _ _)]
  simp [b]

/-- Adjacent ranks within the same first-part block are adjacent suffix ranks,
with direction determined by the parity of the first part. -/
theorem stratGray_adjacent_same_first (n k d a : Nat) (s t : List Nat)
    (hk : 0 < k) (hslen : s.length = k) (htlen : t.length = k)
    (ha : a ≤ d) (hssum : a + s.foldl Nat.add 0 = n)
    (htsum : a + t.foldl Nat.add 0 = n)
    (hsbound : ∀ x ∈ s, x ≤ d) (htbound : ∀ x ∈ t, x ≤ d)
    (hadj : rank stratGray n (k + 1) d (a :: s) + 1 =
      rank stratGray n (k + 1) d (a :: t)) :
    if a % 2 = 0 then
      rank stratGray (n - a) k d s + 1 = rank stratGray (n - a) k d t
    else rank stratGray (n - a) k d t + 1 = rank stratGray (n - a) k d s := by
  have hrs := rank_lt_count stratGray (n - a) k d s
    (by omega) hslen hsbound
  have hrt := rank_lt_count stratGray (n - a) k d t
    (by omega) htlen htbound
  rw [rank_stratGray_cons n k d a s hk hslen ha hssum hsbound,
      rank_stratGray_cons n k d a t hk htlen ha htsum htbound] at hadj
  split_ifs at hadj ⊢ <;> omega

/-- The first or last word of the reflected recursive order, specified
without enumerating the intermediate words. `last = false` selects the first
word. -/
def grayEnd (last : Bool) (n k d : Nat) : List Nat :=
  match k with
  | 0 => []
  | 1 => [n]
  | k + 2 =>
      let a := if last then min n d else n - (k + 1) * d
      a :: grayEnd (last != (a % 2 = 1)) (n - a) (k + 1) d

/-- One coordinate increases by one and all others remain fixed. -/
inductive OneIncrease : List Nat → List Nat → Prop
  | head (a : Nat) (s : List Nat) : OneIncrease (a :: s) ((a + 1) :: s)
  | tail (a : Nat) {s t : List Nat} : OneIncrease s t →
      OneIncrease (a :: s) (a :: t)

/-- The number of unequal coordinates, for lists of the same length. -/
def grayHamming (s t : List Nat) : Nat :=
  ((s.zip t).filter (fun p => p.1 != p.2)).length

omit C in
theorem grayHamming_cons (a b : Nat) (s t : List Nat) :
    grayHamming (a :: s) (b :: t) =
      (if a = b then 0 else 1) + grayHamming s t := by
  by_cases h : a = b <;> simp [grayHamming, h]
  omega

omit C in
theorem grayHamming_self (s : List Nat) : grayHamming s s = 0 := by
  induction s with
  | nil => rfl
  | cons a s ih => simpa [grayHamming_cons] using ih

omit C in
theorem grayHamming_symm (s t : List Nat) : grayHamming s t = grayHamming t s := by
  induction s generalizing t with
  | nil => cases t <;> simp [grayHamming]
  | cons a s ih =>
    cases t with
    | nil => simp [grayHamming]
    | cons b t =>
      rw [grayHamming_cons, grayHamming_cons, ih]
      simp only [eq_comm]

omit C in
theorem OneIncrease.grayHamming {s t : List Nat} (h : OneIncrease s t) :
    grayHamming s t = 1 := by
  induction h with
  | head a s => simp [grayHamming_cons, grayHamming_self]
  | tail a h ih => simpa [grayHamming_cons] using ih

omit C in theorem grayEnd_zero (last : Bool) (k d : Nat) :
    grayEnd last 0 k d = List.replicate k 0 := by
  induction k using Nat.strong_induction_on generalizing last with
  | h k ih =>
    rcases k with _ | _ | k
    · rfl
    · rfl
    · simp only [grayEnd, List.replicate_succ]
      simpa using ih (k + 1) (by omega) (last != false)

omit C in theorem grayEnd_max (last : Bool) (k d : Nat) :
    grayEnd last (k * d) k d = List.replicate k d := by
  induction k using Nat.strong_induction_on generalizing last with
  | h k ih =>
    rcases k with _ | _ | k
    · rfl
    · simp [grayEnd]
    · have hmul : (k + 2) * d = (k + 1) * d + d := by ring
      have ha : (if last then min ((k + 2) * d) d
          else (k + 2) * d - (k + 1) * d) = d := by
        cases last <;> simp [hmul]
      have hsub : (k + 2) * d - d = (k + 1) * d := by omega
      simpa only [grayEnd, ha, hsub, List.replicate_succ] using
        congrArg (List.cons d) (ih (k + 1) (by omega) (last != (d % 2 = 1)))

omit C in
/-- Both endpoint sequences move by one coordinate when the total increases
by one. This is the endpoint invariant needed at Gray block boundaries. -/
theorem grayEnd_oneIncrease (last : Bool) (k d n : Nat)
    (hn : n + 1 ≤ k * d) :
    OneIncrease (grayEnd last n k d) (grayEnd last (n + 1) k d) := by
  induction k using Nat.strong_induction_on generalizing last n with
  | h k ih =>
    rcases k with _ | _ | k
    · simp at hn
    · simpa only [grayEnd] using OneIncrease.head n []
    · have hmul : (k + 2) * d = (k + 1) * d + d := by ring
      rw [hmul] at hn
      cases last with
      | false =>
        let a := n - (k + 1) * d
        let b := n + 1 - (k + 1) * d
        change OneIncrease
          (a :: grayEnd (false != (a % 2 = 1)) (n - a) (k + 1) d)
          (b :: grayEnd (false != (b % 2 = 1)) (n + 1 - b) (k + 1) d)
        by_cases hab : a = b
        · rw [← hab]
          have hsub : n + 1 - a = (n - a) + 1 := by omega
          rw [hsub]
          apply OneIncrease.tail
          apply ih (k + 1) (by omega)
          dsimp [a] at *
          omega
        · have hstep : b = a + 1 := by dsimp [a, b] at *; omega
          have hmaxa : n - a = (k + 1) * d := by dsimp [a] at *; omega
          have hmaxb : n + 1 - b = (k + 1) * d := by dsimp [b] at *; omega
          rw [hmaxa, hmaxb, grayEnd_max, grayEnd_max, hstep]
          exact OneIncrease.head a _
      | true =>
        let a := min n d
        let b := min (n + 1) d
        change OneIncrease
          (a :: grayEnd (true != (a % 2 = 1)) (n - a) (k + 1) d)
          (b :: grayEnd (true != (b % 2 = 1)) (n + 1 - b) (k + 1) d)
        by_cases hab : a = b
        · rw [← hab]
          have hsub : n + 1 - a = (n - a) + 1 := by dsimp [a] at *; omega
          rw [hsub]
          apply OneIncrease.tail
          apply ih (k + 1) (by omega)
          dsimp [a] at *
          omega
        · have hstep : b = a + 1 := by dsimp [a, b] at *; omega
          have hzeroa : n - a = 0 := by dsimp [a, b] at *; omega
          have hzerob : n + 1 - b = 0 := by dsimp [a, b] at *; omega
          rw [hzeroa, hzerob, grayEnd_zero, grayEnd_zero, hstep]
          exact OneIncrease.head a _

omit C in
/-- Endpoints are feasible bounded compositions. -/
theorem grayEnd_valid (last : Bool) (n k d : Nat)
    (hn : n ≤ k * d) :
    (grayEnd last n k d).length = k ∧
    (grayEnd last n k d).sum = n ∧
    ∀ x ∈ grayEnd last n k d, x ≤ d := by
  induction k using Nat.strong_induction_on generalizing last n with
  | h k ih =>
    rcases k with _ | _ | k
    · have : n = 0 := by simpa using hn
      subst n
      simp [grayEnd]
    · have hnd : n ≤ d := by simpa using hn
      simp [grayEnd, hnd]
    · have hmul : (k + 2) * d = (k + 1) * d + d := by ring
      rw [hmul] at hn
      let a := if last then min n d else n - (k + 1) * d
      have ha : a ≤ d := by dsimp [a]; split_ifs <;> omega
      have han : a ≤ n := by dsimp [a]; split_ifs <;> omega
      have hrest : n - a ≤ (k + 1) * d := by
        dsimp [a]
        split_ifs <;> omega
      have hrec := ih (k + 1) (by omega) (last != (a % 2 = 1)) (n - a) hrest
      change (a :: grayEnd (last != (a % 2 = 1)) (n - a) (k + 1) d).length = k + 2 ∧
        (a :: grayEnd (last != (a % 2 = 1)) (n - a) (k + 1) d).sum = n ∧
        ∀ x ∈ a :: grayEnd (last != (a % 2 = 1)) (n - a) (k + 1) d, x ≤ d
      simp only [List.length_cons, List.sum_cons, List.mem_cons]
      refine ⟨by omega, by omega, ?_⟩
      intro x hx
      rcases hx with rfl | hx
      · exact ha
      · exact hrec.2.2 x hx

/-- The recursive endpoint words are precisely rank zero and the last rank. -/
theorem grayEnd_rank (last : Bool) (n k d : Nat) (hn : n ≤ k * d) :
    if last then rank stratGray n k d (grayEnd last n k d) + 1 = C.count n k d
    else rank stratGray n k d (grayEnd last n k d) = 0 := by
  induction k using Nat.strong_induction_on generalizing last n with
  | h k ih =>
    rcases k with _ | _ | k
    · have hz : n = 0 := by simpa using hn
      subst n
      cases last <;> simp [grayEnd, rank, C.count_zero_zero]
    · have hnd : n ≤ d := by simpa using hn
      cases last <;> simp [grayEnd, rank, C.count_one n d hnd]
    · have hmul : (k + 2) * d = (k + 1) * d + d := by ring
      rw [hmul] at hn
      let a := if last then min n d else n - (k + 1) * d
      let tail := grayEnd (last != (a % 2 = 1)) (n - a) (k + 1) d
      have ha : a ≤ d := by dsimp [a]; split_ifs <;> omega
      have han : a ≤ n := by dsimp [a]; split_ifs <;> omega
      have hrest : n - a ≤ (k + 1) * d := by
        dsimp [a]
        split_ifs <;> omega
      have hv := grayEnd_valid (last != (a % 2 = 1)) (n - a) (k + 1) d hrest
      have hs : a + tail.foldl Nat.add 0 = n := by
        have hh : tail.foldl Nat.add 0 = n - a := by
          simpa only [List.sum_eq_foldl] using hv.2.1
        omega
      have hrank : rank stratGray n (k + 2) d (a :: tail) =
          offset n 1 (k + 1) d (pathIncreasing n) a +
            (if a % 2 = 0 then rank stratGray (n - a) (k + 1) d tail
             else C.count (n - a) (k + 1) d - 1 -
               rank stratGray (n - a) (k + 1) d tail) := by
        exact rank_stratGray_cons n (k + 1) d a tail (by omega)
          hv.1 ha hs hv.2.2
      have htailpos : 0 < C.count (n - a) (k + 1) d :=
        (gray_count_pos_iff (C := C) (n - a) (k + 1) d).2 hrest
      have htailrank := ih (k + 1) (by omega)
        (last != (a % 2 = 1)) (n - a) hrest
      change (if last != (a % 2 = 1) then
          rank stratGray (n - a) (k + 1) d tail + 1 = C.count (n - a) (k + 1) d
        else rank stratGray (n - a) (k + 1) d tail = 0) at htailrank
      change (if last then rank stratGray n (k + 2) d (a :: tail) + 1 =
        C.count n (k + 2) d else rank stratGray n (k + 2) d (a :: tail) = 0)
      rw [hrank]
      cases last with
      | false =>
        have hoff : offset n 1 (k + 1) d (pathIncreasing n) a = 0 := by
          exact gray_offset_first n (k + 1) d
        rw [hoff]
        by_cases heven : a % 2 = 0
        · simp [heven] at htailrank ⊢
          exact htailrank
        · have hodd : a % 2 = 1 := by omega
          simp [hodd] at htailrank ⊢
          omega
      | true =>
        have hoff : offset n 1 (k + 1) d (pathIncreasing n) a +
            C.count (n - a) (k + 1) d = C.count n (k + 2) d := by
          exact gray_offset_last n (k + 1) d
        by_cases heven : a % 2 = 0
        · simp [heven] at htailrank ⊢
          omega
        · have hodd : a % 2 = 1 := by omega
          simp [hodd] at htailrank ⊢
          omega

private theorem gray_rank_injective (n k d : Nat) (s t : List Nat)
    (hslen : s.length = k) (htlen : t.length = k)
    (hssum : s.sum = n) (htsum : t.sum = n)
    (hsbound : ∀ x ∈ s, x ≤ d) (htbound : ∀ x ∈ t, x ≤ d)
    (hrank : rank stratGray n k d s = rank stratGray n k d t) : s = t := by
  have hsum_s : s.foldl Nat.add 0 = n := by
    simpa only [List.sum_eq_foldl] using hssum
  have hsum_t : t.foldl Nat.add 0 = n := by
    simpa only [List.sum_eq_foldl] using htsum
  calc
    s = unrank stratGray n k d (rank stratGray n k d s) :=
      (unrank_rank stratGray n k d s hsum_s hslen hsbound).symm
    _ = unrank stratGray n k d (rank stratGray n k d t) := by rw [hrank]
    _ = t := unrank_rank stratGray n k d t hsum_t htlen htbound

private theorem gray_eq_first_of_rank_zero (n k d : Nat) (z : List Nat)
    (hn : n ≤ k * d) (hzlen : z.length = k) (hzsum : z.sum = n)
    (hzbound : ∀ x ∈ z, x ≤ d)
    (hrank : rank stratGray n k d z = 0) :
    z = grayEnd false n k d := by
  have he := grayEnd_valid false n k d hn
  apply gray_rank_injective n k d z (grayEnd false n k d)
    hzlen he.1 hzsum he.2.1 hzbound he.2.2
  rw [hrank]
  simpa using (grayEnd_rank (C := C) false n k d hn).symm

private theorem gray_eq_last_of_rank_last (n k d : Nat) (z : List Nat)
    (hn : n ≤ k * d) (hzlen : z.length = k) (hzsum : z.sum = n)
    (hzbound : ∀ x ∈ z, x ≤ d)
    (hrank : rank stratGray n k d z + 1 = C.count n k d) :
    z = grayEnd true n k d := by
  have he := grayEnd_valid true n k d hn
  apply gray_rank_injective n k d z (grayEnd true n k d)
    hzlen he.1 hzsum he.2.1 hzbound he.2.2
  have he_rank := grayEnd_rank (C := C) true n k d hn
  simp at he_rank
  omega

/-- Consecutive ranks cannot skip a feasible first-part block. -/
theorem stratGray_adjacent_first_cases (n k d a b : Nat) (s t : List Nat)
    (hk : 0 < k) (hslen : s.length = k) (htlen : t.length = k)
    (ha : a ≤ d) (hb : b ≤ d)
    (hssum : a + s.foldl Nat.add 0 = n)
    (htsum : b + t.foldl Nat.add 0 = n)
    (hsbound : ∀ x ∈ s, x ≤ d) (htbound : ∀ x ∈ t, x ≤ d)
    (hadj : rank stratGray n (k + 1) d (a :: s) + 1 =
      rank stratGray n (k + 1) d (b :: t)) :
    a = b ∨ b = a + 1 := by
  have hab : a ≤ b := by
    by_contra h
    have hlt := rank_stratGray_first_lt n k d b a t s hk htlen hslen hb ha
      (by omega) htsum hssum htbound hsbound
    omega
  by_cases heq : a = b
  · exact Or.inl heq
  right
  by_contra hgap
  have hgap' : a + 1 < b := by omega
  let c := a + 1
  have hcsum : n - a ≤ k * d := by
    have hrs := rank_lt_count stratGray (n - a) k d s
      (by omega) hslen hsbound
    exact (gray_count_pos_iff (C := C) (n - a) k d).1 (by omega)
  have hcn : c ≤ n := by dsimp [c]; omega
  have hcbound : c ≤ d := by dsimp [c]; omega
  have hcfeas : n - c ≤ k * d := by dsimp [c]; omega
  let u := grayEnd false (n - c) k d
  have hu := grayEnd_valid false (n - c) k d hcfeas
  have husum : c + u.foldl Nat.add 0 = n := by
    have hh : u.foldl Nat.add 0 = n - c := by
      simpa only [List.sum_eq_foldl] using hu.2.1
    omega
  have hleft := rank_stratGray_first_lt n k d a c s u hk hslen hu.1 ha
    hcbound (by dsimp [c]; omega) hssum husum hsbound hu.2.2
  have hright := rank_stratGray_first_lt n k d c b u t hk hu.1 htlen
    hcbound hb (by dsimp [c]; omega) husum htsum hu.2.2 htbound
  omega

/-- In consecutive nonempty first-part blocks, an adjacent pair uses the
corresponding endpoints of the recursive suffix orders. -/
theorem stratGray_adjacent_next_first (n k d a : Nat) (s t : List Nat)
    (hk : 0 < k) (hslen : s.length = k) (htlen : t.length = k)
    (ha : a + 1 ≤ d) (hssum : a + s.foldl Nat.add 0 = n)
    (htsum : a + 1 + t.foldl Nat.add 0 = n)
    (hsbound : ∀ x ∈ s, x ≤ d) (htbound : ∀ x ∈ t, x ≤ d)
    (hadj : rank stratGray n (k + 1) d (a :: s) + 1 =
      rank stratGray n (k + 1) d ((a + 1) :: t)) :
    if a % 2 = 0 then
      rank stratGray (n - a) k d s + 1 = C.count (n - a) k d ∧
      rank stratGray (n - (a + 1)) k d t + 1 = C.count (n - (a + 1)) k d
    else
      rank stratGray (n - a) k d s = 0 ∧
      rank stratGray (n - (a + 1)) k d t = 0 := by
  have han : a + 1 ≤ n := by omega
  have ha0 : a ≤ n := by omega
  have hstep : offset n 1 k d (pathIncreasing n) (a + 1) =
      offset n 1 k d (pathIncreasing n) a + C.count (n - a) k d := by
    rw [offset_stratRecBlock_eq_sum n 1 k d (a + 1) han,
      offset_stratRecBlock_eq_sum n 1 k d a ha0,
      List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    rw [C.count_one a d (by omega)]
    simp
  have hrs := rank_lt_count stratGray (n - a) k d s
    (by omega) hslen hsbound
  have hrt := rank_lt_count stratGray (n - (a + 1)) k d t
    (by omega) htlen htbound
  rw [rank_stratGray_cons n k d a s hk hslen (by omega) hssum hsbound,
      rank_stratGray_cons n k d (a + 1) t hk htlen ha htsum htbound,
      hstep] at hadj
  have hpar : (a + 1) % 2 = 0 ↔ a % 2 ≠ 0 := by omega
  split_ifs at hadj ⊢ <;> omega

/-- Consecutive valid compositions in the reflected Gray order differ in
exactly two coordinates. -/
theorem stratGray_adjacent_hamming_two (n k d : Nat) (z w : List Nat)
    (hzlen : z.length = k) (hwlen : w.length = k)
    (hzsum : z.sum = n) (hwsum : w.sum = n)
    (hzbound : ∀ x ∈ z, x ≤ d) (hwbound : ∀ x ∈ w, x ≤ d)
    (hadj : rank stratGray n k d z + 1 = rank stratGray n k d w) :
    grayHamming z w = 2 := by
  induction k using Nat.strong_induction_on generalizing n z w with
  | h k ih =>
    rcases k with _ | _ | k
    · have hz : z = [] := List.length_eq_zero_iff.mp hzlen
      have hw : w = [] := List.length_eq_zero_iff.mp hwlen
      subst z; subst w
      simp [rank] at hadj
    · have hz : z = [n] := by
        cases z with
        | nil => simp at hzlen
        | cons a s =>
          cases s with
          | nil => simpa using hzsum
          | cons b s => simp at hzlen
      have hw : w = [n] := by
        cases w with
        | nil => simp at hwlen
        | cons a s =>
          cases s with
          | nil => simpa using hwsum
          | cons b s => simp at hwlen
      subst z; subst w
      simp [rank] at hadj
    · rcases z with _ | ⟨a, s⟩
      · simp at hzlen
      rcases w with _ | ⟨b, t⟩
      · simp at hwlen
      have hslen : s.length = k + 1 := by simpa using hzlen
      have htlen : t.length = k + 1 := by simpa using hwlen
      have hssum : a + s.foldl Nat.add 0 = n := by
        have h : a + s.sum = n := by simpa only [List.sum_cons] using hzsum
        simpa only [List.sum_eq_foldl] using h
      have htsum : b + t.foldl Nat.add 0 = n := by
        have h : b + t.sum = n := by simpa only [List.sum_cons] using hwsum
        simpa only [List.sum_eq_foldl] using h
      have ha : a ≤ d := hzbound a (by simp)
      have hb : b ≤ d := hwbound b (by simp)
      have hsbound : ∀ x ∈ s, x ≤ d := by
        intro x hx
        exact hzbound x (by simp [hx])
      have htbound : ∀ x ∈ t, x ≤ d := by
        intro x hx
        exact hwbound x (by simp [hx])
      rcases stratGray_adjacent_first_cases n (k + 1) d a b s t
          (by omega) hslen htlen ha hb hssum htsum hsbound htbound hadj with
        rfl | hnext
      · have hchild := stratGray_adjacent_same_first n (k + 1) d a s t
          (by omega) hslen htlen ha hssum htsum hsbound htbound hadj
        have hsval : s.sum = n - a := by
          rw [List.sum_eq_foldl]
          change s.foldl Nat.add 0 = n - a
          omega
        have htval : t.sum = n - a := by
          rw [List.sum_eq_foldl]
          change t.foldl Nat.add 0 = n - a
          omega
        by_cases heven : a % 2 = 0
        · simp [heven] at hchild
          have hh := ih (k + 1) (by omega) (n - a) s t
            hslen htlen hsval htval hsbound htbound hchild
          simp [grayHamming_cons, hh]
        · simp [heven] at hchild
          have hh := ih (k + 1) (by omega) (n - a) t s
            htlen hslen htval hsval htbound hsbound hchild
          rw [grayHamming_symm] at hh
          simp [grayHamming_cons, hh]
      · subst b
        have hboundary := stratGray_adjacent_next_first n (k + 1) d a s t
          (by omega) hslen htlen hb hssum htsum hsbound htbound hadj
        have hsval : s.sum = n - a := by
          rw [List.sum_eq_foldl]
          change s.foldl Nat.add 0 = n - a
          omega
        have htval : t.sum = n - (a + 1) := by
          rw [List.sum_eq_foldl]
          change t.foldl Nat.add 0 = n - (a + 1)
          omega
        have hsfeas : n - a ≤ (k + 1) * d := by
          have hrs := rank_lt_count stratGray (n - a) (k + 1) d s
            (by omega) hslen hsbound
          exact (gray_count_pos_iff (C := C) (n - a) (k + 1) d).1 (by omega)
        have htfeas : n - (a + 1) ≤ (k + 1) * d := by omega
        have htot : n - (a + 1) + 1 = n - a := by omega
        by_cases heven : a % 2 = 0
        · simp [heven] at hboundary
          have hs_eq := gray_eq_last_of_rank_last (n - a) (k + 1) d s hsfeas
            hslen hsval hsbound hboundary.1
          have ht_eq := gray_eq_last_of_rank_last (n - (a + 1)) (k + 1) d t htfeas
            htlen htval htbound hboundary.2
          have hone := grayEnd_oneIncrease true (k + 1) d (n - (a + 1))
            (by omega)
          rw [htot, ← hs_eq, ← ht_eq] at hone
          have hh := hone.grayHamming
          rw [grayHamming_symm] at hh
          simp [grayHamming_cons, hh]
        · simp [heven] at hboundary
          have hs_eq := gray_eq_first_of_rank_zero (n - a) (k + 1) d s hsfeas
            hslen hsval hsbound hboundary.1
          have ht_eq := gray_eq_first_of_rank_zero (n - (a + 1)) (k + 1) d t htfeas
            htlen htval htbound hboundary.2
          have hone := grayEnd_oneIncrease false (k + 1) d (n - (a + 1))
            (by omega)
          rw [htot, ← hs_eq, ← ht_eq] at hone
          have hh := hone.grayHamming
          rw [grayHamming_symm] at hh
          simp [grayHamming_cons, hh]
