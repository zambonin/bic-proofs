import GenericRankingBic
import Batteries.Tactic.Alias

namespace PaperComparator

alias check_rank_unrank := rank_unrank
alias check_unrank_rank := unrank_rank
alias check_rank_bound := rank_lt_count
alias check_gf_count := compCount_eq_bicCount
alias check_inclusion_exclusion := inclExclCount_eq_compCount

end PaperComparator
