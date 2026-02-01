/-- Counts with the base cases and path convolution required by ranking. -/
class CountingContract where
  /-- The counting function C_d(n, k): the number of d-bounded k-compositions of n. -/
  count : Nat → Nat → Nat → Nat
  /-- C_d(n, 0) = 0 for n > 0: an empty composition of a positive integer does not exist. -/
  count_zero : ∀ n d, n > 0 → count n 0 d = 0
  /-- C_d(0, 0) = 1: the empty composition of zero is unique. -/
  count_zero_zero : ∀ d, count 0 0 d = 1
  /-- C_d(n, 1) = 1 for 0 ≤ n ≤ d: a single part within the bound is unique. -/
  count_one : ∀ n d, n ≤ d → count n 1 d = 1
  /-- C_d(n, 1) = 0 for n > d: a single part exceeding the bound is impossible. -/
  count_one_gt : ∀ n d, n > d → count n 1 d = 0
  /-- Convolution over a duplicate-free path in `[0, n]` containing every
  positive block. Zero-size blocks may also occur in the path. -/
  count_path : ∀ n k kl kr d (path : List Nat),
    k = kl + kr →
    (∀ w, w ≤ n ∧ count w kl d * count (n - w) kr d > 0 → w ∈ path) →
    (∀ w ∈ path, w ≤ n) →
    path.Nodup →
    count n k d = (path.map (fun w => count w kl d * count (n - w) kr d)).sum
