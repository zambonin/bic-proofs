import GenericRankingBic.Counting.Compositions

/-- Bounded compositions with totals from `n-l` through `n`, clipped at zero.
The set stabilizes once `l ≥ n`. -/
def BoundedCompAcc (n k d l : ℕ) : Finset (Fin k → ℕ) :=
  (Finset.range (l + 1)).biUnion (fun j => BoundedComp (n - j) k d)
