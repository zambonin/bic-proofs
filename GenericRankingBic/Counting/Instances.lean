import GenericRankingBic.Counting.Contract
import GenericRankingBic.Counting.InclusionExclusion
import GenericRankingBic.Counting.GeneratingFunction
import GenericRankingBic.Counting.Convolution

open Nat Finset

/-- Default noncomputable counting instance, using generating-function coefficients.
The computable alternatives have lower priority; select one explicitly for evaluation. -/
noncomputable instance gfInstance : CountingContract where
  count n k d := bicCount n k d
  count_zero n d hn := by
    unfold bicCount
    simp [Polynomial.coeff_one, Nat.ne_of_gt hn]
  count_zero_zero d := by
    unfold bicCount
    simp
  count_one n d hn := bicCount_one_le hn
  count_one_gt n d hn := bicCount_one_gt hn
  count_path n k kl kr d path h_sum h_valid h_bound h_nodup := by
    rw [h_sum, bicCount_conv, listSumMap_eq_toFinsetSum path _ h_nodup]
    symm
    apply Finset.sum_subset
    · intro w hw
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (h_bound w (List.mem_toFinset.mp hw)))
    · intro w _ hw_not
      by_contra h_ne
      exact hw_not (List.mem_toFinset.mpr (h_valid w ⟨Nat.le_of_lt_succ (Finset.mem_range.mp
        (by assumption)), Nat.pos_of_ne_zero h_ne⟩))

/-- Computable counting instance by enumerating `BoundedComp`. -/
instance (priority := 100) finsetInstance : CountingContract where
  count := compCount
  count_zero n d hn := by
    rw [compCount_eq_bicCount]; exact gfInstance.count_zero n d hn
  count_zero_zero d := by
    rw [compCount_eq_bicCount]; exact gfInstance.count_zero_zero d
  count_one n d hn := by
    rw [compCount_eq_bicCount]; exact gfInstance.count_one n d hn
  count_one_gt n d hn := by
    rw [compCount_eq_bicCount]; exact gfInstance.count_one_gt n d hn
  count_path n k kl kr d path h_sum h_valid h_bound h_nodup := by
    simp only [compCount_eq_bicCount] at h_valid ⊢
    exact gfInstance.count_path n k kl kr d path h_sum h_valid h_bound h_nodup

/-- Computable counting instance using `inclExclCount`. -/
instance (priority := 100) inclExclInstance : CountingContract where
  count := inclExclCount
  count_zero n d hn := by
    rw [inclExclCount_eq_compCount]; exact finsetInstance.count_zero n d hn
  count_zero_zero d := by
    rw [inclExclCount_eq_compCount]; exact finsetInstance.count_zero_zero d
  count_one n d hn := by
    rw [inclExclCount_eq_compCount]; exact finsetInstance.count_one n d hn
  count_one_gt n d hn := by
    rw [inclExclCount_eq_compCount]; exact finsetInstance.count_one_gt n d hn
  count_path n k kl kr d path h_sum h_valid h_bound h_nodup := by
    simp only [inclExclCount_eq_compCount] at h_valid ⊢
    exact finsetInstance.count_path n k kl kr d path h_sum h_valid h_bound h_nodup

/-- Computable counting instance using balanced convolution. -/
instance (priority := 100) convInstance : CountingContract where
  count := convCount
  count_zero n d hn := by
    rw [convCount_eq_compCount]; exact finsetInstance.count_zero n d hn
  count_zero_zero d := by
    rw [convCount_eq_compCount]; exact finsetInstance.count_zero_zero d
  count_one n d hn := by
    rw [convCount_eq_compCount]; exact finsetInstance.count_one n d hn
  count_one_gt n d hn := by
    rw [convCount_eq_compCount]; exact finsetInstance.count_one_gt n d hn
  count_path n k kl kr d path h_sum h_valid h_bound h_nodup := by
    simp only [convCount_eq_compCount] at h_valid ⊢
    exact finsetInstance.count_path n k kl kr d path h_sum h_valid h_bound h_nodup
