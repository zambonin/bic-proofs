import GenericRankingBic.Counting.Contract
import GenericRankingBic.Ranking.Strategy

variable [C : CountingContract]

/-- Calculates the rank offset for split point `wl`: the sum of block sizes for all split points
appearing before `wl` in the path. -/
def offset (n kl kr d : Nat) (path : List Nat) (wl : Nat) : Nat :=
  match path with
  | [] => 0
  | w :: ws =>
    if w = wl then 0
    else C.count w kl d * C.count (n - w) kr d + offset n kl kr d ws wl

/-- Find the left sum and residual rank of the block containing `r`.
An empty path returns `(0, 0)`; correctness assumes the rank is in range. -/
def findBlock (n kl kr d : Nat) (p : List Nat) (r : Nat) : Nat × Nat :=
  match p with
  | [] => (0, 0)
  | wl :: ws =>
    let v := C.count wl kl d * C.count (n - wl) kr d
    if r < v then (wl, r) else findBlock n kl kr d ws (r - v)

/-- Recursively unrank using the strategy's decomposition, path and rank split.
Validity is proved for `r < C.count n k d`. -/
def unrank (σ : Strategy) (n k d r : Nat) : List Nat :=
  match k with
  | 0 => []
  | 1 => [n]
  | Nat.succ (Nat.succ k') =>
    let _h := Nat.succ_lt_succ (Nat.zero_lt_succ k')
    let kl := (σ.decompose (k' + 2)).1
    let kr := (σ.decompose (k' + 2)).2
    let fb := findBlock n kl kr d (σ.path n kl kr) r
    -- fb.1 is the split point wl, fb.2 is the residual rank within that block
    let s := σ.split (C.count fb.1 kl d) (C.count (n - fb.1) kr d) fb.1 fb.2
    unrank σ fb.1 kl d s.1 ++ unrank σ (n - fb.1) kr d s.2
termination_by k
decreasing_by
  · exact (σ.decompose_lt _ _h).1
  · exact (σ.decompose_lt _ _h).2

/-- Recursively rank the two subcompositions and combine their ranks with the
block offset. Correctness assumes `z` has length `k`, total `n` and parts at most `d`. -/
def rank (σ : Strategy) (n k d : Nat) (z : List Nat) : Nat :=
  match k with
  | 0 => 0
  | 1 => 0
  | Nat.succ (Nat.succ k') =>
    let _h := Nat.succ_lt_succ (Nat.zero_lt_succ k')
    let kl := (σ.decompose (k' + 2)).1
    let kr := (σ.decompose (k' + 2)).2
    let L := z.take kl       -- left sub-composition of length kl
    let R := z.drop kl       -- right sub-composition of length kr
    let wl := L.foldl Nat.add 0   -- sum of left sub-composition = split point
    offset n kl kr d (σ.path n kl kr) wl +
      σ.combine (C.count wl kl d) (C.count (n - wl) kr d) wl
        (rank σ wl kl d L) (rank σ (n - wl) kr d R)
termination_by k
decreasing_by
  · exact (σ.decompose_lt _ _h).1
  · exact (σ.decompose_lt _ _h).2
