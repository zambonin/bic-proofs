import GenericRankingBic.Orders.Colex
import GenericRankingBic.Counting.BinomialRatio
import GenericRankingBic.Counting.Instances
import GenericRankingBic.Counting.AccumulatedCount
import Mathlib.Tactic

section Bisect

variable [C : CountingContract]

/-- Product of the two child counts at split sum `w`. -/
def blockWeight (n kl kr d w : Nat) : Nat :=
  C.count w kl d * C.count (n - w) kr d

/-- Bisect a path by summing the weights of its left half at each decision.
At zero fuel, the ordinary scan supplies the same result. -/
def bisectBlockFuel (n kl kr d : Nat) : Nat → List Nat → Nat → Nat × Nat
  | 0, p, r => findBlock n kl kr d p r
  | fuel + 1, p, r =>
    if p.length ≤ 1 then findBlock n kl kr d p r
    else
      let left := p.take (p.length / 2)
      let right := p.drop (p.length / 2)
      let leftSize := (left.map (blockWeight n kl kr d)).sum
      if r < leftSize then bisectBlockFuel n kl kr d fuel left r
      else bisectBlockFuel n kl kr d fuel right (r - leftSize)

/-- Bisection with enough fuel for every split. -/
def bisectBlock (n kl kr d : Nat) (p : List Nat) (r : Nat) : Nat × Nat :=
  bisectBlockFuel n kl kr d p.length p r

private theorem findBlock_append_left (n kl kr d : Nat) (xs ys : List Nat) (r : Nat)
    (hr : r < (xs.map (blockWeight n kl kr d)).sum) :
    findBlock n kl kr d (xs ++ ys) r = findBlock n kl kr d xs r := by
  induction xs generalizing r with
  | nil => simp at hr
  | cons x xs ih =>
    simp only [List.cons_append, List.map_cons, List.sum_cons] at *
    change (if r < blockWeight n kl kr d x then (x, r)
      else findBlock n kl kr d (xs ++ ys) (r - blockWeight n kl kr d x)) =
      (if r < blockWeight n kl kr d x then (x, r)
      else findBlock n kl kr d xs (r - blockWeight n kl kr d x))
    split_ifs with h
    · rfl
    · exact ih (r - blockWeight n kl kr d x) (by omega)

private theorem findBlock_append_right (n kl kr d : Nat) (xs ys : List Nat) (r : Nat)
    (hr : (xs.map (blockWeight n kl kr d)).sum ≤ r) :
    findBlock n kl kr d (xs ++ ys) r =
      findBlock n kl kr d ys (r - (xs.map (blockWeight n kl kr d)).sum) := by
  induction xs generalizing r with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.map_cons, List.sum_cons] at *
    change (if r < blockWeight n kl kr d x then (x, r)
      else findBlock n kl kr d (xs ++ ys) (r - blockWeight n kl kr d x)) =
      findBlock n kl kr d ys
        (r - (blockWeight n kl kr d x + (xs.map (blockWeight n kl kr d)).sum))
    split_ifs with h
    · omega
    · rw [ih (r - blockWeight n kl kr d x) (by omega)]
      congr 1
      omega

/-- At every fuel value, the bisection search agrees with the generic linear scan. -/
theorem bisectBlockFuel_eq_findBlock (n kl kr d fuel : Nat) (p : List Nat) (r : Nat) :
    bisectBlockFuel n kl kr d fuel p r = findBlock n kl kr d p r := by
  induction fuel generalizing p r with
  | zero => rfl
  | succ fuel ih =>
    unfold bisectBlockFuel
    split_ifs with hlen
    · rfl
    · dsimp only
      split_ifs with hleft
      · rw [ih]
        calc
          findBlock n kl kr d (p.take (p.length / 2)) r =
              findBlock n kl kr d
                (p.take (p.length / 2) ++ p.drop (p.length / 2)) r :=
            (findBlock_append_left n kl kr d _ _ r hleft).symm
          _ = findBlock n kl kr d p r := by rw [List.take_append_drop]
      · rw [ih]
        calc
          findBlock n kl kr d (p.drop (p.length / 2))
              (r - (p.take (p.length / 2) |>.map (blockWeight n kl kr d)).sum) =
              findBlock n kl kr d
                (p.take (p.length / 2) ++ p.drop (p.length / 2)) r :=
            (findBlock_append_right n kl kr d _ _ r (Nat.le_of_not_gt hleft)).symm
          _ = findBlock n kl kr d p r := by rw [List.take_append_drop]

theorem bisectBlock_eq_findBlock (n kl kr d : Nat) (p : List Nat) (r : Nat) :
    bisectBlock n kl kr d p r = findBlock n kl kr d p r :=
  bisectBlockFuel_eq_findBlock n kl kr d p.length p r

/-- The bisection search is a drop-in replacement for the block choice of colex unranking. -/
theorem bisectColex_eq_findBlock (n k d r : Nat) :
    bisectBlock n (decompRight k).1 (decompRight k).2 d
        (pathDecreasing n) r =
      findBlock n (decompRight k).1 (decompRight k).2 d
        (stratColex.path n (decompRight k).1 (decompRight k).2) r := by
  simpa [stratColex] using
    bisectBlock_eq_findBlock n (decompRight k).1 (decompRight k).2 d (pathDecreasing n) r

/-- Generic unranking with bisection in place of the linear block search. -/
def unrankBisect (σ : Strategy) (n k d r : Nat) : List Nat :=
  match k with
  | 0 => []
  | 1 => [n]
  | Nat.succ (Nat.succ k') =>
    let kl := (σ.decompose (k' + 2)).1
    let kr := (σ.decompose (k' + 2)).2
    let fb := bisectBlock n kl kr d (σ.path n kl kr) r
    let s := σ.split (C.count fb.1 kl d) (C.count (n - fb.1) kr d) fb.1 fb.2
    unrankBisect σ fb.1 kl d s.1 ++ unrankBisect σ (n - fb.1) kr d s.2
termination_by k
decreasing_by
  · exact (σ.decompose_lt _ (by omega)).1
  · exact (σ.decompose_lt _ (by omega)).2

theorem unrankBisect_eq_unrank (σ : Strategy) :
    ∀ n k d r, unrankBisect σ n k d r = unrank σ n k d r := by
  intro n k d r
  induction k using Nat.strong_induction_on generalizing n r with
  | h k ih =>
    rcases k with (_ | _ | k)
    · simp [unrankBisect, unrank]
    · simp [unrankBisect, unrank]
    · rw [unrankBisect, unrank]
      simp only [bisectBlock_eq_findBlock]
      have hlt := σ.decompose_lt (k + 2) (by omega)
      rw [ih _ hlt.1, ih _ hlt.2]

theorem unrankBisect_colex_eq (n k d r : Nat) :
    unrankBisect stratColex n k d r = unrank stratColex n k d r :=
  unrankBisect_eq_unrank stratColex n k d r

end Bisect

/- Cached inclusion–exclusion updates. -/

/-- Reuse the preceding inclusion-exclusion binomial term with one multiplication and
one exact integer division. The formula is valid when the current index is within the
nonzero range; `updatedTerm_eq` records that domain explicitly. -/
def updatedTerm (n i d j previous : Nat) : Nat :=
  previous * (n - (d + 1) * j) / (n - (d + 1) * j + (i - 1))

theorem updatedTerm_eq (n i d j : Nat) (hi : 0 < i)
    (hbound : (d + 1) * j + 1 ≤ n) :
    updatedTerm n i d j (inclExclTerm n i d j) =
      inclExclTerm (n - 1) i d j := by
  let m := n - (d + 1) * j + (i - 1)
  have hm : 0 < m := by dsimp [m]; omega
  have hsub : m - 1 = n - 1 - (d + 1) * j + (i - 1) := by dsimp [m]; omega
  have hdiff : m - (i - 1) = n - (d + 1) * j := by dsimp [m]; omega
  have hchoose := Nat.choose_mul_succ_eq (m - 1) (i - 1)
  have heq : (m - 1).choose (i - 1) * m =
      m.choose (i - 1) * (m - (i - 1)) := by
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))] using hchoose
  unfold updatedTerm inclExclTerm
  rw [← hsub, ← hdiff]
  have hmge : i - 1 ≤ m := by dsimp [m]; omega
  simp only [Nat.sub_add_cancel hmge]
  change m.choose (i - 1) * (m - (i - 1)) / m =
    (m - 1).choose (i - 1)
  have heq' : m * (m - 1).choose (i - 1) =
      m.choose (i - 1) * (m - (i - 1)) := by
    rw [Nat.mul_comm m, heq]
  exact (Nat.eq_div_of_mul_eq_right (Nat.ne_of_gt hm) heq').symm

/-- The binomial term, zeroed outside the active inclusion-exclusion range. -/
def activeTerm (n i d j : Nat) : Nat :=
  if (d + 1) * j ≤ n then inclExclTerm n i d j else 0

/-- Update a cached term as the target sum decreases by one. -/
def updateActiveTerm (n i d j previous : Nat) : Nat :=
  if (d + 1) * j + 1 ≤ n then updatedTerm n i d j previous else 0

theorem updateActiveTerm_eq (n i d j : Nat) (hn : 0 < n) (hi : 0 < i) :
    updateActiveTerm n i d j (activeTerm n i d j) =
      activeTerm (n - 1) i d j := by
  by_cases hnext : (d + 1) * j + 1 ≤ n
  · have hnow : (d + 1) * j ≤ n := by omega
    have htarget : (d + 1) * j ≤ n - 1 := by omega
    simp only [updateActiveTerm, activeTerm, if_pos hnext, if_pos hnow,
      if_pos htarget]
    exact updatedTerm_eq n i d j hi hnext
  · have htarget : ¬(d + 1) * j ≤ n - 1 := by omega
    simp only [updateActiveTerm, activeTerm, if_neg hnext, if_neg htarget]

/-- A cached vector of all signed-sum binomial factors, including zeroes beyond
the active range. The vector length depends only on the number of parts. -/
def termVector (n i d : Nat) : List Nat :=
  (List.range (i + 1)).map (activeTerm n i d)

/-- Update every cached factor once; no binomial coefficient is reevaluated. -/
def updateTermVector (n i d : Nat) (previous : List Nat) : List Nat :=
  let previous := previous.toArray
  (List.range (i + 1)).map
    (fun j => updateActiveTerm n i d j (previous[j]!))

theorem updateTermVector_eq (n i d : Nat) (hn : 0 < n) (hi : 0 < i) :
    updateTermVector n i d (termVector n i d) = termVector (n - 1) i d := by
  unfold updateTermVector termVector
  simp only [List.getElem!_toArray]
  apply List.map_congr_left
  intro j hj
  have hj' : j < i + 1 := List.mem_range.mp hj
  have hget : ((List.range (i + 1)).map (activeTerm n i d))[j]! =
      activeTerm n i d j := by
    simp [hj']
  rw [hget, updateActiveTerm_eq n i d j hn hi]

/-- Evaluate the alternating sum from a cached vector of binomial factors. -/
def countFromTerms (i : Nat) (terms : List Nat) : Nat :=
  let terms := terms.toArray
  (∑ j ∈ Finset.range (i + 1),
    (-1 : ℤ) ^ j * (i.choose j : ℤ) * (terms[j]! : ℤ)).toNat

theorem countFromTerms_eq_inclExclCount (n i d : Nat) (hi : 0 < i) :
    countFromTerms i (termVector n i d) = inclExclCount n i d := by
  rcases i with _ | k
  · omega
  · unfold countFromTerms termVector inclExclCount
    simp only [List.getElem!_toArray]
    congr 1
    let b := min (k + 1) (n / (d + 1))
    have hb : b ≤ k + 1 := min_le_left _ _
    rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hb))]
    · apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ b := Finset.mem_range_succ_iff.mp hj
      have hjbound : (d + 1) * j ≤ n := by
        have hmul := (Nat.le_div_iff_mul_le (by omega : 0 < d + 1)).mp
          (hjle.trans (min_le_right _ _))
        nlinarith
      have hget : ((List.range (k + 2)).map (activeTerm n (k + 1) d))[j]! =
          activeTerm n (k + 1) d j := by simp [show j < k + 2 by omega]
      rw [hget, activeTerm, if_pos hjbound]
      rw [inclExclTerm_eq_displayed n (k + 1) d j hjbound]
      congr 2
    · intro j hj hjnot
      have hjgt : b < j := by
        simp only [Finset.mem_range, not_lt] at hjnot
        omega
      have hjbound : ¬(d + 1) * j ≤ n := by
        intro h
        have hjdiv : j ≤ n / (d + 1) :=
          (Nat.le_div_iff_mul_le (by omega : 0 < d + 1)).2 (by nlinarith)
        have hji : j ≤ k + 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        omega
      have hget : ((List.range (k + 2)).map (activeTerm n (k + 1) d))[j]! =
          activeTerm n (k + 1) d j := by simp [Finset.mem_range.mp hj]
      simp [hget, activeTerm, hjbound]

/-- One complete partial-sum update from cached factors to the next composition count. -/
def updatedCount (n i d : Nat) (previous : List Nat) : Nat :=
  countFromTerms i (updateTermVector n i d previous)

theorem updatedCount_eq_inclExclCount (n i d : Nat) (hn : 0 < n) (hi : 0 < i) :
    updatedCount n i d (termVector n i d) = inclExclCount (n - 1) i d := by
  rw [updatedCount, updateTermVector_eq n i d hn hi]
  exact countFromTerms_eq_inclExclCount (n - 1) i d hi

/-- Build consecutive partial sums while carrying the cached binomial factors.
The first component is the accumulated count and the second is the factor vector
at the final sum. -/
def cachedAccumulated (n i d : Nat) : Nat → Nat × List Nat
  | 0 => (countFromTerms i (termVector n i d), termVector n i d)
  | l + 1 =>
    let previous := cachedAccumulated n i d l
    let nextTerms := updateTermVector (n - l) i d previous.2
    (previous.1 + countFromTerms i nextTerms, nextTerms)

theorem cachedAccumulated_correct (n i d l : Nat) (hi : 0 < i) (hl : l ≤ n) :
    (cachedAccumulated n i d l).1 =
        ∑ j ∈ Finset.range (l + 1), inclExclCount (n - j) i d ∧
      (cachedAccumulated n i d l).2 = termVector (n - l) i d := by
  induction l with
  | zero =>
    simp [cachedAccumulated, countFromTerms_eq_inclExclCount n i d hi]
  | succ l ih =>
    have hle : l ≤ n := by omega
    have hpos : 0 < n - l := by omega
    obtain ⟨hsum, hterms⟩ := ih hle
    have hnext : updateTermVector (n - l) i d (cachedAccumulated n i d l).2 =
        termVector (n - (l + 1)) i d := by
      rw [hterms, updateTermVector_eq _ _ _ hpos hi]
      congr 1
    constructor
    · change (cachedAccumulated n i d l).1 +
          countFromTerms i (updateTermVector (n - l) i d (cachedAccumulated n i d l).2) = _
      rw [hsum, hnext, countFromTerms_eq_inclExclCount _ i d hi]
      conv_rhs => rw [Finset.sum_range_succ]
    · simp only [cachedAccumulated, hnext]

/-- The cached loop computes the analytical accumulated count for every valid window. -/
theorem cachedAccumulated_eq_compCountAcc (n i d l : Nat) (hi : 0 < i)
    (hl : l ≤ n) :
    ((cachedAccumulated n i d l).1 : ℤ) = compCountAcc n i d l := by
  rw [(cachedAccumulated_correct n i d l hi hl).1]
  rw [compCountAcc_eq_partial_sum n i d l hi hl]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  rw [inclExclCount_eq_compCount]
