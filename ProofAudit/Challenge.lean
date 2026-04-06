import GenericRankingBic

namespace PaperComparator

theorem check_rank_unrank [C : CountingContract] (σ : Strategy) (n k d r : Nat)
    (hr : r < C.count n k d) :
    rank σ n k d (unrank σ n k d r) = r := by
  exact rank_unrank σ n k d r hr

theorem check_unrank_rank [C : CountingContract] (σ : Strategy) (n k d : Nat)
    (z : List Nat) (hn : z.foldl Nat.add 0 = n) (hk : z.length = k)
    (hd : ∀ x ∈ z, x ≤ d) :
    unrank σ n k d (rank σ n k d z) = z := by
  exact unrank_rank σ n k d z hn hk hd

theorem check_rank_bound [C : CountingContract] (σ : Strategy) (n k d : Nat)
    (z : List Nat) (hn : z.foldl Nat.add 0 = n) (hk : z.length = k)
    (hd : ∀ x ∈ z, x ≤ d) : rank σ n k d z < C.count n k d := by
  exact rank_lt_count σ n k d z hn hk hd

theorem check_gf_count (n k d : Nat) : compCount n k d = bicCount n k d := by
  exact compCount_eq_bicCount n k d

theorem check_inclusion_exclusion (n k d : Nat) :
    inclExclCount n k d = compCount n k d := by
  exact inclExclCount_eq_compCount n k d

theorem check_choose_ratio (u p k : Nat) (hp : p + k ≤ u) :
    (u.choose k : Rat) / ((u - p).choose k : Rat) =
      ∏ g ∈ Finset.range p, (u - g : Rat) / (u - g - k : Rat) := by
  exact chooseRatio_prod u p k hp

theorem check_weighted_sum (c y l : Nat) :
    weightedBinomSum 0 c y l =
      (y + 1).choose (c + 1) - (y - l).choose (c + 1) := by
  exact weightedBinomSum_base c y l

theorem check_table_size (n k d : Nat) (hd : d ≤ n) :
    ∑ _i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (n + 1), (min j d + 2) =
      (k + 1) * (d * (d + 1) / 2 + 2 * (d + 1) + (n - d) * (d + 2)) := by
  exact accumulatedTableSize n k d hd

theorem check_halving_set (k : Nat) (hk : 2 ≤ k) :
    (halvingSet k).card = halvingCardFormula k := by
  exact halvingSet_card k hk

theorem check_raw_moment (p n k d l : Nat) (hk : 0 < k) (hl : l ≤ n) :
    rawMoment p n k d l =
      ∑ j ∈ Finset.range (l + 1), (↑(n - j) : Int) ^ p * (compCount (n - j) k d : Int) := by
  exact rawMoment_eq_sum p n k d l hk hl

theorem check_moment_variance (n k d l : Nat) (hk : 0 < k) :
    finiteVariance (BoundedCompAcc n k d l) totalSumQ =
      (rawMoment 2 n k d l : Rat) / (rawMoment 0 n k d l : Rat) -
        ((rawMoment 1 n k d l : Rat) / (rawMoment 0 n k d l : Rat)) ^ 2 := by
  exact finiteVariance_totalSumQ_eq_rawMoments n k d l hk

end PaperComparator
