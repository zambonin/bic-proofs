import GenericRankingBic.Orders.RecursiveBlock
import GenericRankingBic.Tables.HalvingSet

/-- Child-row indices in the decomposition tree, including repetitions across
recursive calls. Each pair is recorded once per non-base call; repeated reads
inside a path scan and any initial total-count query are not counted. -/
def lookupRowsTrace [C : CountingContract] (σ : Strategy) (k : Nat) : List Nat :=
  match k with
  | 0 => []
  | 1 => []
  | Nat.succ (Nat.succ k') =>
    let _h := Nat.succ_lt_succ (Nat.zero_lt_succ k')
    let kl := (σ.decompose (k' + 2)).1
    let kr := (σ.decompose (k' + 2)).2
    kl :: kr :: (lookupRowsTrace σ kl ++ lookupRowsTrace σ kr)
termination_by k
decreasing_by
  · exact (σ.decompose_lt _ _h).1
  · exact (σ.decompose_lt _ _h).2

/-- Ranking with a row trace. The numerical result uses the same calls to
`offset`, `C.count`, and `σ.combine` as `rank`; the trace emits each child row
once per recursive call, regardless of repeated accesses inside `offset`. -/
def rankWithRows [C : CountingContract] (σ : Strategy)
    (n k d : Nat) (z : List Nat) : Nat × List Nat :=
  match k with
  | 0 => (0, [])
  | 1 => (0, [])
  | Nat.succ (Nat.succ k') =>
    let _h := Nat.succ_lt_succ (Nat.zero_lt_succ k')
    let kl := (σ.decompose (k' + 2)).1
    let kr := (σ.decompose (k' + 2)).2
    let L := z.take kl
    let R := z.drop kl
    let wl := L.foldl Nat.add 0
    let left := rankWithRows σ wl kl d L
    let right := rankWithRows σ (n - wl) kr d R
    (offset n kl kr d (σ.path n kl kr) wl +
        σ.combine (C.count wl kl d) (C.count (n - wl) kr d) wl
          left.1 right.1,
      kl :: kr :: (left.2 ++ right.2))
termination_by k
decreasing_by
  · exact (σ.decompose_lt _ _h).1
  · exact (σ.decompose_lt _ _h).2

/-- Unranking with a row trace. The composition result uses the same calls to
`findBlock`, `C.count`, and `σ.split` as `unrank`; the trace emits each child
row once per recursive call, regardless of repeated accesses in `findBlock`. -/
def unrankWithRows [C : CountingContract] (σ : Strategy)
    (n k d r : Nat) : List Nat × List Nat :=
  match k with
  | 0 => ([], [])
  | 1 => ([n], [])
  | Nat.succ (Nat.succ k') =>
    let _h := Nat.succ_lt_succ (Nat.zero_lt_succ k')
    let kl := (σ.decompose (k' + 2)).1
    let kr := (σ.decompose (k' + 2)).2
    let fb := findBlock n kl kr d (σ.path n kl kr) r
    let s := σ.split (C.count fb.1 kl d) (C.count (n - fb.1) kr d) fb.1 fb.2
    let left := unrankWithRows σ fb.1 kl d s.1
    let right := unrankWithRows σ (n - fb.1) kr d s.2
    (left.1 ++ right.1, kl :: kr :: (left.2 ++ right.2))
termination_by k
decreasing_by
  · exact (σ.decompose_lt _ _h).1
  · exact (σ.decompose_lt _ _h).2

/-- Row indices queried by `C.count` along the recursive calls of `rank`.
The trace records each pair of row indices once per non-base call; the actual
`offset` traversal may query the same rows more than once. -/
def rankRowsTrace [C : CountingContract] (σ : Strategy)
    (n k d : Nat) (z : List Nat) : List Nat :=
  match k with
  | 0 => []
  | 1 => []
  | Nat.succ (Nat.succ k') =>
    let _h := Nat.succ_lt_succ (Nat.zero_lt_succ k')
    let kl := (σ.decompose (k' + 2)).1
    let kr := (σ.decompose (k' + 2)).2
    let L := z.take kl
    let R := z.drop kl
    let wl := L.foldl Nat.add 0
    kl :: kr ::
      (rankRowsTrace σ wl kl d L ++ rankRowsTrace σ (n - wl) kr d R)
termination_by k
decreasing_by
  · exact (σ.decompose_lt _ _h).1
  · exact (σ.decompose_lt _ _h).2

/-- Row indices queried by `C.count` along the recursive calls of `unrank`.
The trace records each pair of row indices once per non-base call; `findBlock`
may query the same rows more than once while scanning candidate split sums. -/
def unrankRowsTrace [C : CountingContract] (σ : Strategy)
    (n k d r : Nat) : List Nat :=
  match k with
  | 0 => []
  | 1 => []
  | Nat.succ (Nat.succ k') =>
    let _h := Nat.succ_lt_succ (Nat.zero_lt_succ k')
    let kl := (σ.decompose (k' + 2)).1
    let kr := (σ.decompose (k' + 2)).2
    let fb := findBlock n kl kr d (σ.path n kl kr) r
    let s := σ.split (C.count fb.1 kl d) (C.count (n - fb.1) kr d) fb.1 fb.2
    kl :: kr ::
      (unrankRowsTrace σ fb.1 kl d s.1 ++
        unrankRowsTrace σ (n - fb.1) kr d s.2)
termination_by k
decreasing_by
  · exact (σ.decompose_lt _ _h).1
  · exact (σ.decompose_lt _ _h).2

/-- Instrumented ranking projects to the original numerical algorithm and
to the abstract row trace. -/
theorem rankWithRows_spec [C : CountingContract]
    (σ : Strategy) (k n d : Nat) (z : List Nat) :
    (rankWithRows σ n k d z).1 = rank σ n k d z ∧
      (rankWithRows σ n k d z).2 = rankRowsTrace σ n k d z := by
  induction k using Nat.strong_induction_on generalizing n z with
  | h k ih =>
    match k with
    | 0 => simp [rankWithRows, rank, rankRowsTrace]
    | 1 => simp [rankWithRows, rank, rankRowsTrace]
    | k' + 2 =>
      let kl := (σ.decompose (k' + 2)).1
      let kr := (σ.decompose (k' + 2)).2
      let L := z.take kl
      let R := z.drop kl
      let wl := L.foldl Nat.add 0
      have hk : 1 < k' + 2 := by omega
      have hkl : kl < k' + 2 := (σ.decompose_lt (k' + 2) hk).1
      have hkr : kr < k' + 2 := (σ.decompose_lt (k' + 2) hk).2
      have hleft := ih kl hkl wl L
      have hright := ih kr hkr (n - wl) R
      dsimp only [kl, kr, L, R, wl] at hleft hright
      simp only [rankWithRows, rank, rankRowsTrace]
      simp only [hleft.1, hright.1, hleft.2, hright.2, and_self]

/-- Instrumented unranking projects to the original composition algorithm
and to the abstract row trace. -/
theorem unrankWithRows_spec [C : CountingContract]
    (σ : Strategy) (k n d r : Nat) :
    (unrankWithRows σ n k d r).1 = unrank σ n k d r ∧
      (unrankWithRows σ n k d r).2 = unrankRowsTrace σ n k d r := by
  induction k using Nat.strong_induction_on generalizing n r with
  | h k ih =>
    match k with
    | 0 => simp [unrankWithRows, unrank, unrankRowsTrace]
    | 1 => simp [unrankWithRows, unrank, unrankRowsTrace]
    | k' + 2 =>
      let kl := (σ.decompose (k' + 2)).1
      let kr := (σ.decompose (k' + 2)).2
      let fb := findBlock n kl kr d (σ.path n kl kr) r
      let s := σ.split (C.count fb.1 kl d) (C.count (n - fb.1) kr d) fb.1 fb.2
      have hk : 1 < k' + 2 := by omega
      have hkl : kl < k' + 2 := (σ.decompose_lt (k' + 2) hk).1
      have hkr : kr < k' + 2 := (σ.decompose_lt (k' + 2) hk).2
      have hleft := ih kl hkl fb.1 s.1
      have hright := ih kr hkr (n - fb.1) s.2
      dsimp only [kl, kr, fb, s] at hleft hright
      simp only [unrankWithRows, unrank, unrankRowsTrace]
      simp only [hleft.1, hright.1, hleft.2, hright.2, and_self]

theorem rankWithRows_result [C : CountingContract]
    (σ : Strategy) (n k d : Nat) (z : List Nat) :
    (rankWithRows σ n k d z).1 = rank σ n k d z :=
  (rankWithRows_spec σ k n d z).1

theorem rankWithRows_trace [C : CountingContract]
    (σ : Strategy) (n k d : Nat) (z : List Nat) :
    (rankWithRows σ n k d z).2 = rankRowsTrace σ n k d z :=
  (rankWithRows_spec σ k n d z).2

theorem unrankWithRows_result [C : CountingContract]
    (σ : Strategy) (n k d r : Nat) :
    (unrankWithRows σ n k d r).1 = unrank σ n k d r :=
  (unrankWithRows_spec σ k n d r).1

theorem unrankWithRows_trace [C : CountingContract]
    (σ : Strategy) (n k d r : Nat) :
    (unrankWithRows σ n k d r).2 = unrankRowsTrace σ n k d r :=
  (unrankWithRows_spec σ k n d r).2

/-- The rows visited by `rank` depend only on the initial length and the
strategy's decomposition function, even though split sums depend on `z`. -/
theorem rankRowsTrace_eq_lookupRowsTrace [C : CountingContract]
    (σ : Strategy) (k n d : Nat) (z : List Nat) :
    rankRowsTrace σ n k d z = lookupRowsTrace σ k := by
  induction k using Nat.strong_induction_on generalizing n z with
  | h k ih =>
    match k with
    | 0 => simp [rankRowsTrace, lookupRowsTrace]
    | 1 => simp [rankRowsTrace, lookupRowsTrace]
    | k' + 2 =>
      have hk : 1 < k' + 2 := by omega
      have hl := (σ.decompose_lt (k' + 2) hk).1
      have hr := (σ.decompose_lt (k' + 2) hk).2
      simp only [rankRowsTrace, lookupRowsTrace]
      rw [ih _ hl, ih _ hr]

/-- The rows visited by `unrank` depend only on the initial length and the
strategy's decomposition function, even though the chosen blocks depend on
the rank. -/
theorem unrankRowsTrace_eq_lookupRowsTrace [C : CountingContract]
    (σ : Strategy) (k n d r : Nat) :
    unrankRowsTrace σ n k d r = lookupRowsTrace σ k := by
  induction k using Nat.strong_induction_on generalizing n r with
  | h k ih =>
    match k with
    | 0 => simp [unrankRowsTrace, lookupRowsTrace]
    | 1 => simp [unrankRowsTrace, lookupRowsTrace]
    | k' + 2 =>
      have hk : 1 < k' + 2 := by omega
      have hl := (σ.decompose_lt (k' + 2) hk).1
      have hr := (σ.decompose_lt (k' + 2) hk).2
      simp only [unrankRowsTrace, lookupRowsTrace]
      rw [ih _ hl, ih _ hr]

/-- At a non-base recursive-block call, the immediate table lookups use rows
`⌊k/2⌋` and `⌈k/2⌉`, followed by the same trace in both subcalls. -/
theorem lookupRowsTrace_stratRecBlock_step [C : CountingContract]
    (k : Nat) (hk : 1 < k) :
    lookupRowsTrace stratRecBlock k =
      k / 2 :: (k - k / 2) ::
        (lookupRowsTrace stratRecBlock (k / 2) ++
          lookupRowsTrace stratRecBlock (k - k / 2)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [lookupRowsTrace]
  simp only [stratRecBlock, decompBisect_eq (j + 2) (by omega)]

/-- The distinct row indices visited by the recursive-block decomposition
trace are exactly the iterated halving set `H(k)`. -/
theorem lookupRowsTrace_stratRecBlock_toFinset [C : CountingContract]
    (k : Nat) :
    (lookupRowsTrace stratRecBlock k).toFinset = halvingSet k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k ≤ 1
    · interval_cases k <;> simp [lookupRowsTrace, halvingSet]
    · have hkl : k / 2 < k := Nat.div_lt_self (by omega) (by omega)
      have hkr : k - k / 2 < k := by omega
      rw [lookupRowsTrace_stratRecBlock_step k (by omega)]
      simp only [List.toFinset_cons, List.toFinset_append]
      rw [ih (k / 2) hkl, ih (k - k / 2) hkr]
      conv_rhs => rw [halvingSet, if_neg hk]
      ext i
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      tauto

/-- A row appears in the recursive-block count lookup trace exactly when it
belongs to `H(k)`. -/
theorem mem_lookupRowsTrace_stratRecBlock_iff [C : CountingContract]
    (k i : Nat) :
    i ∈ lookupRowsTrace stratRecBlock k ↔ i ∈ halvingSet k := by
  rw [← lookupRowsTrace_stratRecBlock_toFinset k, List.mem_toFinset]

/-- The rank recursion for the recursive-block strategy uses exactly the
table-row indices in `H(k)`, independently of the composition and sum. -/
theorem rankRowsTrace_stratRecBlock_toFinset [C : CountingContract]
    (n k d : Nat) (z : List Nat) :
    (rankRowsTrace stratRecBlock n k d z).toFinset = halvingSet k := by
  rw [rankRowsTrace_eq_lookupRowsTrace, lookupRowsTrace_stratRecBlock_toFinset]

/-- The unrank recursion for the recursive-block strategy uses exactly the
table-row indices in `H(k)`, independently of the rank and sum. -/
theorem unrankRowsTrace_stratRecBlock_toFinset [C : CountingContract]
    (n k d r : Nat) :
    (unrankRowsTrace stratRecBlock n k d r).toFinset = halvingSet k := by
  rw [unrankRowsTrace_eq_lookupRowsTrace, lookupRowsTrace_stratRecBlock_toFinset]

/-- The instrumented ranking algorithm returns the original rank and an
abstract row trace whose support is precisely `H(k)`. -/
theorem rankWithRows_stratRecBlock [C : CountingContract]
    (n k d : Nat) (z : List Nat) :
    (rankWithRows stratRecBlock n k d z).1 = rank stratRecBlock n k d z ∧
      (rankWithRows stratRecBlock n k d z).2.toFinset = halvingSet k := by
  exact ⟨rankWithRows_result stratRecBlock n k d z,
    by rw [rankWithRows_trace, rankRowsTrace_stratRecBlock_toFinset]⟩

/-- The instrumented unranking algorithm returns the original composition
and an abstract row trace whose support is precisely `H(k)`. -/
theorem unrankWithRows_stratRecBlock [C : CountingContract]
    (n k d r : Nat) :
    (unrankWithRows stratRecBlock n k d r).1 = unrank stratRecBlock n k d r ∧
      (unrankWithRows stratRecBlock n k d r).2.toFinset = halvingSet k := by
  exact ⟨unrankWithRows_result stratRecBlock n k d r,
    by rw [unrankWithRows_trace, unrankRowsTrace_stratRecBlock_toFinset]⟩
