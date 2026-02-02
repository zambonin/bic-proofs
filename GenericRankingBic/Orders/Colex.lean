import GenericRankingBic.Ranking.Correctness
import GenericRankingBic.Ranking.Strategy

/-- Right-peeling colex strategy. Left sums decrease, so the last part
increases as in the paper's colex definition. -/
def stratColex [C : CountingContract] : Strategy where
  decompose := decompRight
  decompose_sum := decompRight_sum
  decompose_lt := decompRight_lt
  path := fun n _kl _kr => pathDecreasing n
  path_nodup := fun n _kl _kr => pathDecreasing_nodup n
  path_bound := fun n _kl _kr => pathDecreasing_bound n
  path_valid := pathDecreasing_valid
  split := fun _nl nr _wl => splitDivMod nr
  combine := fun _nl nr _wl => combineMulAdd nr
  split_bound := fun nl nr _wl => splitDivMod_bound nl nr
  combine_split := fun _nl nr _wl => combineMulAdd_splitDivMod nr
  split_combine := fun _nl nr _wl _rl _rr _hrl hrr => splitDivMod_combineMulAdd nr _ _ hrr
  combine_bound := fun nl nr _wl => combineMulAdd_bound nl nr

theorem rank_unrank_stratColex [C : CountingContract] :
    ∀ n k d r, r < C.count n k d →
    rank stratColex n k d (unrank stratColex n k d r) = r :=
  fun n k d r hr => rank_unrank stratColex n k d r hr

theorem unrank_rank_stratColex [C : CountingContract] :
    ∀ n k d z, z.foldl Nat.add 0 = n → z.length = k → (∀ x ∈ z, x ≤ d) →
    unrank stratColex n k d (rank stratColex n k d z) = z :=
  fun n k d z hn hk hle =>
    unrank_rank stratColex n k d z hn hk hle
