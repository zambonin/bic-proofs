import GenericRankingBic.Ranking.Enumeration

variable [C : CountingContract]

/-- The paper's permuted product `L ⊙ₛ R`, with split parameter `w`.
Entry `r` selects child indices using `σ.split`. The product is empty if either
input is empty. -/
def permutedProduct (σ : Strategy) (w : Nat)
    (L R : List (List Nat)) : List (List Nat) :=
  (List.range (L.length * R.length)).map fun r =>
    let s := σ.split L.length R.length w r
    L.getD s.1 [] ++ R.getD s.2 []

@[simp] theorem permutedProduct_length (σ : Strategy) (w : Nat)
    (L R : List (List Nat)) :
    (permutedProduct σ w L R).length = L.length * R.length := by
  simp [permutedProduct]

/-- The path-ordered concatenation of the products of the two child sequences. -/
def concatenatedProducts (σ : Strategy) (n k d : Nat) : List (List Nat) :=
  let kl := (σ.decompose k).1
  let kr := (σ.decompose k).2
  (σ.path n kl kr).flatMap fun w =>
    permutedProduct σ w (recursiveSequence σ w kl d)
      (recursiveSequence σ (n - w) kr d)

private theorem flatMap_ranges_eq_findBlock (n kl kr d : Nat)
    (p : List Nat) (f : Nat → Nat → List Nat) :
    (p.flatMap fun w =>
      (List.range (C.count w kl d * C.count (n - w) kr d)).map (f w)) =
      (List.range ((p.map fun w =>
        C.count w kl d * C.count (n - w) kr d).sum)).map fun r =>
          let fb := findBlock n kl kr d p r
          f fb.1 fb.2 := by
  induction p with
  | nil => simp
  | cons w ws ih =>
    let m := C.count w kl d * C.count (n - w) kr d
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons, List.range_add,
      List.map_append, List.map_map]
    rw [ih]
    congr 1
    · apply List.map_congr_left
      intro r hr
      have h : r < m := List.mem_range.mp hr
      simp [findBlock, m, h]
    · apply List.map_congr_left
      intro r hr
      have h : ¬m + r < m := by omega
      simp [findBlock, m, h]

/-- For every recursive case, the ordered sequence is the paper's path-ordered
concatenation of permuted products of its two child sequences. -/
theorem recursiveSequence_concat (σ : Strategy) (n k d : Nat) (hk : 1 < k) :
    recursiveSequence σ n k d = concatenatedProducts σ n k d := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  let kl := (σ.decompose (k' + 2)).1
  let kr := (σ.decompose (k' + 2)).2
  have hsum : C.count n (k' + 2) d =
      ((σ.path n kl kr).map fun w =>
        C.count w kl d * C.count (n - w) kr d).sum := by
    apply C.count_path n (k' + 2) kl kr d (σ.path n kl kr)
    · exact (σ.decompose_sum (k' + 2) (by omega)).symm
    · intro w hw
      exact σ.path_valid n kl kr d w hw
    · exact σ.path_bound n kl kr
    · exact σ.path_nodup n kl kr
  unfold concatenatedProducts
  simp only [permutedProduct, recursiveSequence_length]
  rw [flatMap_ranges_eq_findBlock n kl kr d
    (σ.path n kl kr) (fun w r =>
      let s := σ.split (C.count w kl d) (C.count (n - w) kr d) w r
      (recursiveSequence σ w kl d).getD s.1 [] ++
        (recursiveSequence σ (n - w) kr d).getD s.2 [])]
  rw [← hsum]
  simp only [recursiveSequence]
  rfl

/-- The displayed concatenation also enumerates unrank outputs in rank order. -/
theorem concatenatedProducts_eq_unrankSequence (σ : Strategy) (n k d : Nat)
    (hk : 1 < k) :
    concatenatedProducts σ n k d = unrankSequence σ n k d := by
  rw [← recursiveSequence_concat σ n k d hk, recursiveSequence_eq_unrankSequence]
