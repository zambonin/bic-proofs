import GenericRankingBic.Tables.Basic
import GenericRankingBic.Statistics.PartialSums
import Mathlib.Data.Rat.Defs

/-- Squared rational test for a `c`-standard-deviation band. Its real
absolute-value interpretation requires nonnegative variance; the test alone
gives no coverage probability. -/
def inStatisticalBand (mean variance : Nat → Rat) (c i j : Nat) : Bool :=
  decide (((j : Rat) - mean i) ^ 2 ≤ (c : Rat) ^ 2 * variance i)

/-- Finite mean of a partial sum on `C(n,k,d)`, with value zero for an empty class. -/
def compPartialMean (n k d i : Nat) : Rat :=
  finiteMean (BoundedCompAcc n k d 0) (fun z => partialSumQ z i)

/-- Finite variance of a partial sum on `C(n,k,d)`, with value zero for an empty class. -/
def compPartialVariance (n k d i : Nat) : Rat :=
  finiteVariance (BoundedCompAcc n k d 0) (fun z => partialSumQ z i)

theorem compPartialMean_eq (n k d i : Nat) (hk : 0 < k) (hi : i ≤ k)
    (hS : 0 < (BoundedCompAcc n k d 0).card) :
    compPartialMean n k d i = (i : Rat) * n / k := by
  exact expected_partial_sum_acc_zero n k d hk i hi hS

theorem compPartialVariance_eq (n k d i : Nat) (hk : 1 < k) (hi : i ≤ k)
    (hS : 0 < (BoundedCompAcc n k d 0).card) :
    compPartialVariance n k d i =
      (i : Rat) * (k - i) / (k - 1) *
        finiteVariance (BoundedCompAcc n k d 0)
          (fun z => (z ⟨0, by omega⟩ : Rat)) := by
  rw [compPartialVariance,
    variance_partial_sum_normalized n k d 0 hk i hi hS,
    variance_totalSumQ_acc_zero n k d hS]
  simp

theorem inStatisticalBand_iff (mean variance : Nat → Rat) (c i j : Nat) :
    inStatisticalBand mean variance c i j = true ↔
      ((j : Rat) - mean i) ^ 2 ≤ (c : Rat) ^ 2 * variance i := by
  simp [inStatisticalBand]

/-- Dense reference grid for the truncated `χ_comb`. Cells outside the
chosen band hold `none`; the outer lists still allocate the full grid. -/
def probCombTable (n k d c : Nat) (mean variance : Nat → Rat) :
    List (List (Option Nat)) :=
  (List.range (k + 1)).map fun i =>
    (List.range (n + 1)).map fun j =>
      if inStatisticalBand mean variance c i j then some (compCount j i d) else none

/-- The paper's probabilistic count table using the exact mean and variance
of bounded-composition partial sums. -/
def probCombTableFromCompositions (n k d c : Nat) : List (List (Option Nat)) :=
  probCombTable n k d c (compPartialMean n k d) (compPartialVariance n k d)

/-- Dense reference grid for truncated `χ_acc`. A retained cell contains
the complete cumulative sequence; other cells hold `none`. -/
def probAccTable (n k d c : Nat) (mean variance : Nat → Rat) :
    List (List (Option (List Nat))) :=
  (List.range (k + 1)).map fun i =>
    (List.range (n + 1)).map fun j =>
      if inStatisticalBand mean variance c i j then some (accTableEntry j i d) else none

/-- The analogous accumulated table using the same composition band. -/
def probAccTableFromCompositions (n k d c : Nat) :
    List (List (Option (List Nat))) :=
  probAccTable n k d c (compPartialMean n k d) (compPartialVariance n k d)

/-- The concrete band is precisely the squared form of the paper's
mean-and-variance predicate. -/
theorem compositionBand_iff (n k d c i j : Nat) :
    inStatisticalBand (compPartialMean n k d) (compPartialVariance n k d) c i j = true ↔
      ((j : Rat) - finiteMean (BoundedCompAcc n k d 0)
        (fun z => partialSumQ z i)) ^ 2 ≤
      (c : Rat) ^ 2 * finiteVariance (BoundedCompAcc n k d 0)
        (fun z => partialSumQ z i) := by
  exact inStatisticalBand_iff _ _ _ _ _

/-- For a nonempty class with `k > 1`, the band uses Proposition 5's
specialized mean `i n/k` and variance `i(k-i)/(k-1) Var(X₁)`. -/
theorem compositionBand_eq_prop5 (n k d c i j : Nat) (hk : 1 < k) (hi : i ≤ k)
    (hS : 0 < (BoundedCompAcc n k d 0).card) :
    inStatisticalBand (compPartialMean n k d) (compPartialVariance n k d) c i j = true ↔
      ((j : Rat) - (i : Rat) * n / k) ^ 2 ≤
        (c : Rat) ^ 2 * ((i : Rat) * (k - i) / (k - 1) *
          finiteVariance (BoundedCompAcc n k d 0)
            (fun z => (z ⟨0, by omega⟩ : Rat))) := by
  rw [inStatisticalBand_iff,
    compPartialMean_eq n k d i (by omega) hi hS,
    compPartialVariance_eq n k d i hk hi hS]

/-- Lookup a potentially retained table cell. -/
def probCombLookup (table : List (List (Option Nat))) (i j : Nat) : Option Nat :=
  (((table[i]?).bind fun row => row[j]?)).join

/-- Lookup a potentially retained accumulated sequence. -/
def probAccLookup (table : List (List (Option (List Nat)))) (i j : Nat) : Option (List Nat) :=
  (((table[i]?).bind fun row => row[j]?)).join

/-- A total count evaluator using direct computation when a cell is absent. -/
def probCombLookupOrCompute (n k d c i j : Nat) (mean variance : Nat → Rat) : Nat :=
  (probCombLookup (probCombTable n k d c mean variance) i j).getD (compCount j i d)

/-- Reconstruct an accumulated sequence when it is outside the stored band. -/
def probAccLookupOrCompute (n k d c i j : Nat) (mean variance : Nat → Rat) : List Nat :=
  (probAccLookup (probAccTable n k d c mean variance) i j).getD (accTableEntry j i d)

theorem probCombTable_rows (n k d c : Nat) (mean variance : Nat → Rat) :
    (probCombTable n k d c mean variance).length = k + 1 := by
  simp [probCombTable]

theorem probAccTable_rows (n k d c : Nat) (mean variance : Nat → Rat) :
    (probAccTable n k d c mean variance).length = k + 1 := by
  simp [probAccTable]

theorem probCombTable_lookup (n k d c i j : Nat) (mean variance : Nat → Rat)
    (hi : i ≤ k) (hj : j ≤ n) :
    probCombLookup (probCombTable n k d c mean variance) i j =
      if inStatisticalBand mean variance c i j then some (compCount j i d) else none := by
  simp [probCombLookup, probCombTable,
    List.getElem?_range (by omega : i < k + 1),
    List.getElem?_range (by omega : j < n + 1)]

theorem probAccTable_lookup (n k d c i j : Nat) (mean variance : Nat → Rat)
    (hi : i ≤ k) (hj : j ≤ n) :
    probAccLookup (probAccTable n k d c mean variance) i j =
      if inStatisticalBand mean variance c i j then some (accTableEntry j i d) else none := by
  simp [probAccLookup, probAccTable,
    List.getElem?_range (by omega : i < k + 1),
    List.getElem?_range (by omega : j < n + 1)]

theorem probCombTableFromCompositions_lookup (n k d c i j : Nat)
    (hi : i ≤ k) (hj : j ≤ n) :
    probCombLookup (probCombTableFromCompositions n k d c) i j =
      if inStatisticalBand (compPartialMean n k d) (compPartialVariance n k d) c i j
      then some (compCount j i d) else none :=
  probCombTable_lookup _ _ _ _ _ _ _ _ hi hj

theorem probAccTableFromCompositions_lookup (n k d c i j : Nat)
    (hi : i ≤ k) (hj : j ≤ n) :
    probAccLookup (probAccTableFromCompositions n k d c) i j =
      if inStatisticalBand (compPartialMean n k d) (compPartialVariance n k d) c i j
      then some (accTableEntry j i d) else none :=
  probAccTable_lookup _ _ _ _ _ _ _ _ hi hj

theorem probCombLookupOrCompute_correct (n k d c i j : Nat)
    (mean variance : Nat → Rat) (hi : i ≤ k) (hj : j ≤ n) :
    probCombLookupOrCompute n k d c i j mean variance = compCount j i d := by
  rw [probCombLookupOrCompute, probCombTable_lookup _ _ _ _ _ _ _ _ hi hj]
  split <;> rfl

theorem probAccLookupOrCompute_correct (n k d c i j : Nat)
    (mean variance : Nat → Rat) (hi : i ≤ k) (hj : j ≤ n) :
    probAccLookupOrCompute n k d c i j mean variance = accTableEntry j i d := by
  rw [probAccLookupOrCompute, probAccTable_lookup _ _ _ _ _ _ _ _ hi hj]
  split <;> rfl

/-- A retained lookup is exactly the composition count. -/
theorem probCombLookup_sound (n k d c i j value : Nat)
    (mean variance : Nat → Rat) (hi : i ≤ k) (hj : j ≤ n)
    (h : probCombLookup (probCombTable n k d c mean variance) i j = some value) :
    value = compCount j i d := by
  rw [probCombTable_lookup _ _ _ _ _ _ _ _ hi hj] at h
  split at h <;> cases h
  rfl
