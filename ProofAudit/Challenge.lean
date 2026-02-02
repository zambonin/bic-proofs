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

end PaperComparator
