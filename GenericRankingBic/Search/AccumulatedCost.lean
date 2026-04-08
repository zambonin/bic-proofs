import GenericRankingBic.Search.Accumulated
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Nat.Log

/-- Search result and number of midpoint probes. For a precomputed array,
each probe is one entry read and one comparison. Array access has unit cost;
table construction, allocation and integer bit operations are excluded. -/
structure AccumulatedSearchRun where
  /-- Selected prefix index. -/
  result : Nat
  /-- Number of midpoint entry reads and comparisons. -/
  probes : Nat

/-- Instrumented counterpart of `accumulatedSearchFuel`. -/
def accumulatedSearchRunFuel (entry : Nat → Nat) (r : Nat) :
    Nat → Nat → Nat → AccumulatedSearchRun
  | 0, lo, _ => ⟨lo, 0⟩
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then ⟨lo, 0⟩
      else
        let mid := (lo + hi) / 2
        if r < entry mid then
          let continuation := accumulatedSearchRunFuel entry r fuel lo mid
          ⟨continuation.result, continuation.probes + 1⟩
        else
          let continuation := accumulatedSearchRunFuel entry r fuel mid hi
          ⟨continuation.result, continuation.probes + 1⟩

/-- Instrumented full search for entries zero through `m`. -/
def accumulatedSearchRun (entry : Nat → Nat) (m r : Nat) :
    AccumulatedSearchRun :=
  accumulatedSearchRunFuel entry r (m + 1) 0 (m + 1)

theorem accumulatedSearchRunFuel_result (entry : Nat → Nat) (r fuel lo hi : Nat) :
    (accumulatedSearchRunFuel entry r fuel lo hi).result =
      accumulatedSearchFuel entry r fuel lo hi := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
      by_cases hsmall : hi ≤ lo + 1
      · simp [accumulatedSearchRunFuel, accumulatedSearchFuel, hsmall]
      · by_cases hleft : r < entry ((lo + hi) / 2)
        · simpa [accumulatedSearchRunFuel, accumulatedSearchFuel, hsmall, hleft]
            using ih lo ((lo + hi) / 2)
        · simpa [accumulatedSearchRunFuel, accumulatedSearchFuel, hsmall, hleft]
            using ih ((lo + hi) / 2) hi

theorem accumulatedSearchRun_result (entry : Nat → Nat) (m r : Nat) :
    (accumulatedSearchRun entry m r).result = accumulatedSearch entry m r :=
  accumulatedSearchRunFuel_result entry r (m + 1) 0 (m + 1)

/-- An interval of width at most one has no midpoint probe. Each larger
interval is split into two intervals of width at most `ceil(width/2)`. -/
theorem accumulatedSearchRunFuel_probes_le_clog (entry : Nat → Nat)
    (r fuel lo hi : Nat) (hlohi : lo ≤ hi) :
    (accumulatedSearchRunFuel entry r fuel lo hi).probes ≤
      Nat.clog 2 (hi - lo) := by
  induction fuel generalizing lo hi with
  | zero => simp [accumulatedSearchRunFuel]
  | succ fuel ih =>
      by_cases hsmall : hi ≤ lo + 1
      · simp [accumulatedSearchRunFuel, hsmall]
      · have hwidth : 1 < hi - lo := by omega
        have hmidlo : lo < (lo + hi) / 2 := by omega
        have hmidhi : (lo + hi) / 2 < hi := by omega
        have hlog := Nat.clog_of_one_lt (b := 2) (n := hi - lo)
          (by omega) hwidth
        by_cases hleft : r < entry ((lo + hi) / 2)
        · have hhalf : (lo + hi) / 2 - lo ≤ (hi - lo + 1) / 2 := by omega
          have hrec := ih lo ((lo + hi) / 2) (by omega)
          have hmono := Nat.clog_monotone 2 hhalf
          simpa [accumulatedSearchRunFuel, hsmall, hleft, hlog] using
            (Nat.add_le_add_right (hrec.trans hmono) 1)
        · have hhalf : hi - (lo + hi) / 2 ≤ (hi - lo + 1) / 2 := by omega
          have hrec := ih ((lo + hi) / 2) hi (by omega)
          have hmono := Nat.clog_monotone 2 hhalf
          simpa [accumulatedSearchRunFuel, hsmall, hleft, hlog] using
            (Nat.add_le_add_right (hrec.trans hmono) 1)

theorem accumulatedSearchRun_probes_le_clog (entry : Nat → Nat) (m r : Nat) :
    (accumulatedSearchRun entry m r).probes ≤ Nat.clog 2 (m + 1) := by
  simpa [accumulatedSearchRun] using
    accumulatedSearchRunFuel_probes_le_clog entry r (m + 1) 0 (m + 1) (by omega)

/-- Instrumented search of one precomputed array. The caller supplies an
array with at least `min n d + 2` entries for every midpoint access to be a
valid read of the accumulated sequence. -/
def searchColexWithEntryRun (entry : Array Nat) (n d r : Nat) :
    AccumulatedSearchRun :=
  accumulatedSearchRun (fun t => entry[min t (min n d + 1)]!) (min n d) r

theorem searchColexWithEntryRun_result (entry : Array Nat) (n d r : Nat) :
    (searchColexWithEntryRun entry n d r).result =
      searchColexWithEntry entry n d r :=
  accumulatedSearchRun_result _ _ _

/-- One read and one comparison are charged for each midpoint, at most the
ceiling binary logarithm of the number of candidate last parts plus one. -/
theorem searchColexWithEntryRun_probes_le_clog (entry : Array Nat)
    (n d r : Nat) :
    (searchColexWithEntryRun entry n d r).probes ≤
      Nat.clog 2 (min n d + 1) := by
  exact accumulatedSearchRun_probes_le_clog _ _ _

theorem searchColexWithEntryRun_probes_le_clog_d (entry : Array Nat)
    (n d r : Nat) :
    (searchColexWithEntryRun entry n d r).probes ≤
      Nat.clog 2 (d + 1) := by
  exact (searchColexWithEntryRun_probes_le_clog entry n d r).trans
    (Nat.clog_monotone 2 (by omega))

/-- A precomputed sequence with `min n d + 2` cells covers every clamped
index that the actual search can request. -/
theorem searchColexWithEntry_read_in_bounds (entry : Array Nat)
    (n d : Nat) (hsize : min n d + 2 ≤ entry.size) (t : Nat) :
    min t (min n d + 1) < entry.size := by
  omega

/-- Result, probe budget, and array bounds for a precomputed entry. -/
theorem searchColexWithEntryRun_precomputed_spec (entry : Array Nat)
    (n d r : Nat) (hsize : min n d + 2 ≤ entry.size) :
    (searchColexWithEntryRun entry n d r).result =
        searchColexWithEntry entry n d r ∧
      (searchColexWithEntryRun entry n d r).probes ≤
        Nat.clog 2 (d + 1) ∧
      ∀ t, min t (min n d + 1) < entry.size := by
  exact ⟨searchColexWithEntryRun_result entry n d r,
    searchColexWithEntryRun_probes_le_clog_d entry n d r,
    searchColexWithEntry_read_in_bounds entry n d hsize⟩

/-- The logical search phase used by `searchColexTable`, instrumented after
the accumulated entry has been constructed. Construction is not charged. -/
def searchColexTableRun (n i d r : Nat) : AccumulatedSearchRun :=
  searchColexWithEntryRun (accTableEntry n i d).toArray n d r

theorem searchColexTableRun_result (n i d r : Nat) :
    (searchColexTableRun n i d r).result = searchColexTable n i d r := by
  exact searchColexWithEntryRun_result _ _ _ _

theorem searchColexTableRun_probes_le_clog_d (n i d r : Nat) :
    (searchColexTableRun n i d r).probes ≤ Nat.clog 2 (d + 1) :=
  searchColexWithEntryRun_probes_le_clog_d _ _ _ _

theorem searchColexTableRun_precomputed_spec (n i d r : Nat) :
    (searchColexTableRun n i d r).result = searchColexTable n i d r ∧
      (searchColexTableRun n i d r).probes ≤ Nat.clog 2 (d + 1) ∧
      ∀ t, min t (min n d + 1) < (accTableEntry n i d).toArray.size := by
  have hsize : min n d + 2 ≤ (accTableEntry n i d).toArray.size := by
    simp [accTableEntry_length]
  exact searchColexWithEntryRun_precomputed_spec _ n d r hsize

open Asymptotics Filter

/-- For any family of precomputed entries whose lengths satisfy the stated
domain contract, midpoint reads and comparisons per part are `O(log d)`.
The logarithm is the discrete ceiling binary logarithm. -/
theorem searchColexWithEntryRun_probes_isBigO_clog
    (entries : Nat → Array Nat) (totals : Nat → Nat) (ranks : Nat → Nat)
    (hsize : ∀ d, min (totals d) d + 2 ≤ (entries d).size) :
    (fun d : Nat =>
      ((searchColexWithEntryRun (entries d) (totals d) d (ranks d)).probes : ℝ))
      =O[atTop] (fun d : Nat => (Nat.clog 2 (d + 1) : ℝ)) := by
  apply isBigO_of_le atTop
  intro d
  have h := (searchColexWithEntryRun_precomputed_spec
    (entries d) (totals d) d (ranks d) (hsize d)).2.1
  simpa using (show
    (↑(searchColexWithEntryRun (entries d) (totals d) d (ranks d)).probes : ℝ) ≤
      (Nat.clog 2 (d + 1) : ℝ) by exact_mod_cast h)
