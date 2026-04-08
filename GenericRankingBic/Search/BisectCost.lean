import GenericRankingBic.Search.Bisect
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Asymptotics.Defs

section BisectCost

variable [C : CountingContract]

/-- A bisection result with split-decision and block-weight counters.
Each weight expression has unit cost; computing a count, list copying and bit
operations are excluded. The leaf charge is its full path length, an upper
bound on the actual linear scan. -/
structure BisectRun where
  /-- Selected block and residual rank. -/
  result : Nat × Nat
  /-- Number of midpoint decisions. -/
  decisions : Nat
  /-- Block-weight calls, charging the full path at a leaf. -/
  weightEvaluations : Nat

/-- The same control flow as `bisectBlockFuel`, with explicit operation counters. -/
def bisectRunFuel (n kl kr d : Nat) : Nat → List Nat → Nat → BisectRun
  | 0, p, r => ⟨findBlock n kl kr d p r, 0, p.length⟩
  | fuel + 1, p, r =>
    if p.length ≤ 1 then ⟨findBlock n kl kr d p r, 0, p.length⟩
    else
      let left := p.take (p.length / 2)
      let right := p.drop (p.length / 2)
      let leftSize := (left.map (blockWeight n kl kr d)).sum
      if r < leftSize then
        let continuation := bisectRunFuel n kl kr d fuel left r
        ⟨continuation.result, continuation.decisions + 1,
          continuation.weightEvaluations + left.length⟩
      else
        let continuation := bisectRunFuel n kl kr d fuel right (r - leftSize)
        ⟨continuation.result, continuation.decisions + 1,
          continuation.weightEvaluations + left.length⟩

/-- Instrumented search with the initial path length as fuel. -/
def bisectRun (n kl kr d : Nat) (p : List Nat) (r : Nat) : BisectRun :=
  bisectRunFuel n kl kr d p.length p r

/-- The instrumented search returns exactly the original search result. -/
theorem bisectRunFuel_result (n kl kr d fuel : Nat) (p : List Nat) (r : Nat) :
    (bisectRunFuel n kl kr d fuel p r).result = bisectBlockFuel n kl kr d fuel p r := by
  induction fuel generalizing p r with
  | zero => rfl
  | succ fuel ih =>
    by_cases hlen : p.length ≤ 1
    · simp [bisectRunFuel, bisectBlockFuel, hlen]
    · by_cases hleft : r < (p.take (p.length / 2) |>.map
          (blockWeight n kl kr d)).sum
      · simp only [List.map_take] at hleft
        simpa [bisectRunFuel, bisectBlockFuel, hlen, hleft] using
          ih (p.take (p.length / 2)) r
      · simp only [List.map_take] at hleft
        simpa [bisectRunFuel, bisectBlockFuel, hlen, hleft] using
          ih (p.drop (p.length / 2)) (r -
            (p.take (p.length / 2) |>.map
              (blockWeight n kl kr d)).sum)

theorem bisectRun_result (n kl kr d : Nat) (p : List Nat) (r : Nat) :
    (bisectRun n kl kr d p r).result = bisectBlock n kl kr d p r :=
  bisectRunFuel_result n kl kr d p.length p r

/-- At most the ceiling binary logarithm of the path length split decisions. -/
theorem bisectRunFuel_decisions_le_clog (n kl kr d fuel : Nat)
    (p : List Nat) (r : Nat) :
    (bisectRunFuel n kl kr d fuel p r).decisions ≤ Nat.clog 2 p.length := by
  induction fuel generalizing p r with
  | zero => simp [bisectRunFuel]
  | succ fuel ih =>
    by_cases hlen : p.length ≤ 1
    · simp [bisectRunFuel, hlen]
    · by_cases hleft : r < (p.take (p.length / 2) |>.map
          (blockWeight n kl kr d)).sum
      · have hhalf : (p.take (p.length / 2)).length ≤ (p.length + 1) / 2 := by
          simp only [List.length_take]
          omega
        simp only [List.map_take] at hleft
        have hrec := ih (p.take (p.length / 2)) r
        have hmono := Nat.clog_monotone 2 hhalf
        have hlog := Nat.clog_of_one_lt (b := 2) (n := p.length) (by omega) (by omega)
        simpa [bisectRunFuel, hlen, hleft, hlog] using
          (Nat.add_le_add_right (hrec.trans hmono) 1)
      · have hhalf : (p.drop (p.length / 2)).length ≤ (p.length + 1) / 2 := by
          simp only [List.length_drop]
          omega
        simp only [List.map_take] at hleft
        have hrec := ih (p.drop (p.length / 2)) (r -
          (p.take (p.length / 2) |>.map
            (blockWeight n kl kr d)).sum)
        have hmono := Nat.clog_monotone 2 hhalf
        have hlog := Nat.clog_of_one_lt (b := 2) (n := p.length) (by omega) (by omega)
        simpa [bisectRunFuel, hlen, hleft, hlog] using
          (Nat.add_le_add_right (hrec.trans hmono) 1)

theorem bisectRun_decisions_le_clog (n kl kr d : Nat) (p : List Nat) (r : Nat) :
    (bisectRun n kl kr d p r).decisions ≤ Nat.clog 2 p.length :=
  bisectRunFuel_decisions_le_clog n kl kr d p.length p r

/-- The current implementation evaluates at most one block weight per path entry.
The result counts all summed half lists and charges a full scan at the leaf. -/
theorem bisectRunFuel_weightEvaluations_le_length (n kl kr d fuel : Nat)
    (p : List Nat) (r : Nat) :
    (bisectRunFuel n kl kr d fuel p r).weightEvaluations ≤ p.length := by
  induction fuel generalizing p r with
  | zero => simp [bisectRunFuel]
  | succ fuel ih =>
    by_cases hlen : p.length ≤ 1
    · simp [bisectRunFuel, hlen]
    · by_cases hleft : r < (p.take (p.length / 2) |>.map
          (blockWeight n kl kr d)).sum
      · have hrec := ih (p.take (p.length / 2)) r
        have hhalf : 2 * (p.take (p.length / 2)).length ≤ p.length := by
          simp only [List.length_take]
          omega
        simp only [List.map_take] at hleft
        simp [bisectRunFuel, hlen, hleft]
        omega
      · have hrec := ih (p.drop (p.length / 2)) (r -
          (p.take (p.length / 2) |>.map (blockWeight n kl kr d)).sum)
        simp only [List.map_take] at hrec
        have hparts : (p.take (p.length / 2)).length +
            (p.drop (p.length / 2)).length = p.length := by
          simp only [List.length_take, List.length_drop]
          omega
        have hleftlen : (p.take (p.length / 2)).length = p.length / 2 := by
          simp only [List.length_take]
          omega
        simp only [List.map_take] at hleft
        simp [bisectRunFuel, hlen, hleft]
        omega

theorem bisectRun_weightEvaluations_le_length (n kl kr d : Nat)
    (p : List Nat) (r : Nat) :
    (bisectRun n kl kr d p r).weightEvaluations ≤ p.length :=
  bisectRunFuel_weightEvaluations_le_length n kl kr d p.length p r

/-- A nontrivial first split already evaluates half the path's block weights.
Thus the current implementation's total weight-evaluation count is not
logarithmic in the path length. -/
theorem bisectRunFuel_firstSplit_evaluations (n kl kr d fuel : Nat)
    (p : List Nat) (r : Nat) (h : 1 < p.length) :
    p.length / 2 ≤
      (bisectRunFuel n kl kr d (fuel + 1) p r).weightEvaluations := by
  have hlen : ¬p.length ≤ 1 := by omega
  unfold bisectRunFuel
  simp only [if_neg hlen]
  split_ifs <;> simp only [List.length_take] <;> omega

theorem bisectRun_firstSplit_evaluations (n kl kr d : Nat)
    (p : List Nat) (r : Nat) (h : 1 < p.length) :
    p.length / 2 ≤ (bisectRun n kl kr d p r).weightEvaluations := by
  obtain ⟨fuel, hfuel⟩ : ∃ fuel, p.length = fuel + 1 := by
    cases hlen : p.length with
    | zero => omega
    | succ fuel => exact ⟨fuel, rfl⟩
  simp only [bisectRun, hfuel]
  simpa [hfuel] using bisectRunFuel_firstSplit_evaluations n kl kr d fuel p r h

open Asymptotics Filter

/-- For a fixed rank and counting problem, the number of split decisions is
`O(log m)` for an `m`-element path. -/
theorem bisectRun_decisions_isBigO_clog (n kl kr d r : Nat) :
    (fun m : Nat => ((bisectRun n kl kr d (List.range m) r).decisions : ℝ))
      =O[atTop] (fun m : Nat => (Nat.clog 2 m : ℝ)) := by
  apply isBigO_of_le atTop
  intro m
  have h := bisectRun_decisions_le_clog n kl kr d (List.range m) r
  simpa using (show (↑(bisectRun n kl kr d (List.range m) r).decisions : ℝ) ≤
      (Nat.clog 2 m : ℝ) by exact_mod_cast (by simpa using h))

/-- The same implementation makes `O(m)` block-weight evaluations, including
an upper charge for its linear leaf scan. -/
theorem bisectRun_weightEvaluations_isBigO_length (n kl kr d r : Nat) :
    (fun m : Nat => ((bisectRun n kl kr d (List.range m) r).weightEvaluations : ℝ))
      =O[atTop] (fun m : Nat => (m : ℝ)) := by
  apply isBigO_of_le atTop
  intro m
  have h := bisectRun_weightEvaluations_le_length n kl kr d (List.range m) r
  simpa using (show (↑(bisectRun n kl kr d (List.range m) r).weightEvaluations : ℝ) ≤
      (m : ℝ) by exact_mod_cast (by simpa using h))

end BisectCost
