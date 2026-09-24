import GenericRankingBic
import Batteries.Tactic.Alias

namespace PaperComparator

alias check_rank_unrank := rank_unrank
alias check_unrank_rank := unrank_rank
alias check_rank_bound := rank_lt_count
alias check_gf_count := compCount_eq_bicCount
alias check_inclusion_exclusion := inclExclCount_eq_compCount
alias check_choose_ratio := chooseRatio_prod
alias check_weighted_sum := weightedBinomSum_base
alias check_table_size := accumulatedTableSize

theorem check_halving_set (k : Nat) (hk : 2 ≤ k) :
    (halvingSet k).card = halvingCardFormula k := by
  exact halvingSet_card k hk

alias check_raw_moment := rawMoment_eq_sum
alias check_recursive_sequence := recursiveSequence_eq_unrankSequence
alias check_bisect := bisectBlock_eq_findBlock
alias check_cached_accumulated := cachedAccumulated_eq_compCountAcc
alias check_bous_path := stratBousAt_effective_path
alias check_moment_variance := finiteVariance_totalSumQ_eq_rawMoments

theorem check_probabilistic_fallback (n k d c i j : Nat)
    (hi : i ≤ k) (hj : j ≤ n) :
    probCombLookupOrCompute n k d c i j
      (compPartialMean n k d) (compPartialVariance n k d) = compCount j i d :=
  probCombLookupOrCompute_correct n k d c i j _ _ hi hj

alias check_variance_nonnegative := compPartialVariance_nonneg
alias check_real_band := compositionBand_iff_abs_le_sqrt
alias check_retained_cell_bound := retainedBandCells_le
alias check_four_sigma_coverage := composition_fourSigma_inside_ge
alias check_conditional_partial_sum_law := conditionalPartialSumLaw_apply
alias check_sparse_count_table_size := sparseProbCombStoredValues_eq_retainedBandCells
alias check_four_sigma_interval := compositionFourSigmaBand_iff_interval

end PaperComparator
