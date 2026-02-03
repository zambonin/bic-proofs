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
