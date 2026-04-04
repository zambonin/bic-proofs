import GenericRankingBic.Counting.AccumulatedCount
import GenericRankingBic.Counting.AccumulatedSet
import GenericRankingBic.Counting.BinomialRatio
import GenericRankingBic.Counting.Compositions
import GenericRankingBic.Counting.Contract
import GenericRankingBic.Counting.Convolution
import GenericRankingBic.Counting.GeneratingFunction
import GenericRankingBic.Counting.InclusionExclusion
import GenericRankingBic.Counting.Instances
import GenericRankingBic.Counting.PolynomialIdentities
import GenericRankingBic.Counting.RawMoment
import GenericRankingBic.Counting.WeightedSum
import GenericRankingBic.Orders.Colex
import GenericRankingBic.Orders.Gray
import GenericRankingBic.Orders.RecursiveBlock
import GenericRankingBic.Ranking.Basic
import GenericRankingBic.Ranking.Correctness
import GenericRankingBic.Ranking.Lemmas
import GenericRankingBic.Ranking.Strategy
import GenericRankingBic.Tables.HalvingSet
import GenericRankingBic.Tables.Size

section

attribute [local instance] inclExclInstance

#eval (List.range (inclExclCount 5 3 2)).map (unrank stratColex 5 3 2)
#eval (List.range (inclExclCount 5 3 2)).map (unrank stratRecBlock 5 3 2)
#eval (List.range (inclExclCount 5 3 2)).map (unrank stratGray 5 3 2)

example : rank stratColex 5 3 2 [2, 1, 2] = 1 := by decide +kernel

end

section

attribute [local instance] finsetInstance

example : rank stratColex 5 3 2 [2, 1, 2] = 1 := by decide +kernel

end

section

attribute [local instance] convInstance

example : rank stratColex 5 3 2 [2, 1, 2] = 1 := by decide +kernel

end
