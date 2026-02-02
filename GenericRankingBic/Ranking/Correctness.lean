import GenericRankingBic.Counting.Contract
import GenericRankingBic.Ranking.Lemmas
import GenericRankingBic.Ranking.Strategy
import Mathlib.Data.List.Basic
import Mathlib.Tactic

variable [C : CountingContract]

/-- Ranking an unranked valid index recovers that index. -/
theorem rank_unrank :
    ∀ (σ : Strategy) n k d r, r < C.count n k d →
    rank σ n k d (unrank σ n k d r) = r := by
  intros σ n k d r hr
  induction k using Nat.strong_induction_on generalizing n d r σ with
  | _ k ih =>
    rcases k with (_ | _ | k) <;> simp_all +decide
    · -- k = 0: the composition is empty, rank is 0
      have h_empty : C.count n 0 d = if n = 0 then 1 else 0 := by
        cases n <;> simp +decide [C.count_zero, C.count_zero_zero] at hr ⊢
      generalize_proofs at *
      split_ifs at h_empty <;> simp_all +decide [rank, unrank]
    · -- k = 1: a single-part composition, rank is always 0
      unfold unrank rank
      by_cases h : n ≤ d <;> simp_all +decide [C.count_one, C.count_one_gt]
    · -- k ≥ 2: recursive case — decompose via findBlock
      obtain ⟨wl, r', hr'⟩ : ∃ wl r',
          findBlock n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2 d
            (σ.path n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2) r = (wl, r') ∧
          r = offset n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2 d
            (σ.path n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2) wl + r' := by
        -- findBlock decomposes r = offset + residual
        let fb := findBlock n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2 d
          (σ.path n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2) r
        refine ⟨fb.1, fb.2, rfl, ?_⟩
        apply findBlock_correct n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2 d
          (σ.path n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2) r
          (findBlock n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2 d
            (σ.path n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2) r).1
          (findBlock n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2 d
            (σ.path n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2) r).2
          (σ.path_nodup n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2) (by
            convert hr using 1
            rw [C.count_path] <;> norm_num [σ.decompose_sum]
            · exact fun w hw₁ hw₂ hw₃ =>
                σ.path_valid n (σ.decompose (k + 2) |>.1) (σ.decompose (k + 2) |>.2) d w
                  ⟨hw₁, by positivity⟩ |> fun h => by simpa using h
            · exact σ.path_bound _ _ _
            · exact σ.path_nodup _ _ _) (by rfl)
      -- Split the residual rank into left and right sub-ranks
      obtain ⟨s₁, s₂, hs⟩ : ∃ s₁ s₂,
          σ.split (C.count wl (σ.decompose (k + 2)).1 d)
            (C.count (n - wl) (σ.decompose (k + 2)).2 d) wl r' = (s₁, s₂) ∧
          s₁ < C.count wl (σ.decompose (k + 2)).1 d ∧
          s₂ < C.count (n - wl) (σ.decompose (k + 2)).2 d := by
        have := findBlock_bound n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2 d
          (σ.path n (σ.decompose (k + 2)).1 (σ.decompose (k + 2)).2) r wl r' ?_ hr'.1
        generalize_proofs at *
        · exact ⟨_, _, rfl, σ.split_bound _ _ _ _ this |>.1, σ.split_bound _ _ _ _ this |>.2⟩
        · convert hr using 1
          generalize_proofs at *
          rw [C.count_path] <;> norm_num [σ.decompose_sum]
          · exact fun w hw₁ hw₂ hw₃ =>
              σ.path_valid n (σ.decompose (k + 2) |>.1) (σ.decompose (k + 2) |>.2) d w
                ⟨hw₁, by positivity⟩ |> fun h => by simpa using h
          · exact fun w hw => σ.path_bound n _ _ _ hw
          · exact σ.path_nodup _ _ _
      -- Apply induction hypothesis to both sub-problems
      have h_ind : rank σ wl (σ.decompose (k + 2)).1 d
          (unrank σ wl (σ.decompose (k + 2)).1 d s₁) = s₁ ∧
          rank σ (n - wl) (σ.decompose (k + 2)).2 d
            (unrank σ (n - wl) (σ.decompose (k + 2)).2 d s₂) = s₂ := by
        apply And.intro (ih (σ.decompose (k + 2)).1
          (by linarith [σ.decompose_lt (k + 2) (by linarith)]) σ wl d s₁ hs.right.left)
          (ih (σ.decompose (k + 2)).2 (by linarith [σ.decompose_lt (k + 2) (by linarith)])
            σ (n - wl) d s₂ hs.right.right)
      have h_unrank : unrank σ n (k + 2) d r = unrank σ wl (σ.decompose (k + 2)).1 d s₁ ++
          unrank σ (n - wl) (σ.decompose (k + 2)).2 d s₂ := by
        rw [unrank]
        aesop
      rw [h_unrank, rank_eq_offset_add_combine] <;> simp_all +decide
      · -- The foldl sum of the left unrank equals wl
        rw [show List.foldl Nat.add 0 (unrank σ wl (σ.decompose (k + 2)).1 d s₁) = wl from ?_]
        · have := σ.combine_split (C.count wl (σ.decompose (k + 2)).1 d)
            (C.count (n - wl) (σ.decompose (k + 2)).2 d) wl r'
          aesop
        · exact unrank_sum σ wl (σ.decompose (k + 2) |>.1) d s₁ hs.2.1
      · exact unrank_length σ wl (σ.decompose (k + 2) |>.1) d s₁ hs.2.1 |>
          fun h => h.trans (by simp +decide)

/-- The rank of any valid composition is strictly less than the total count. -/
theorem rank_lt_count :
    ∀ (σ : Strategy) n k d (z : List Nat),
    z.foldl Nat.add 0 = n → z.length = k → (∀ x ∈ z, x ≤ d) →
    rank σ n k d z < C.count n k d := by
  intro σ n k d z hn hk hd
  induction k using Nat.strong_induction_on generalizing n z with
  | _ k ih =>
    rcases k with (_ | _ | k) <;> simp +arith +decide [*] at *
    · cases n <;> simp_all +arith +decide
      rw [C.count_zero_zero]
      unfold rank
      aesop
    · rcases z with (_ | ⟨x, _ | ⟨y, z⟩⟩) <;> simp_all +decide [List.length]
      have h_rank_zero : rank σ n 1 d [n] = 0 := by
        unfold rank
        aesop
      by_cases hn : n > 0 <;> simp_all +decide [CountingContract.count_one]
    · set kl := (σ.decompose (k + 2)).1
      set kr := (σ.decompose (k + 2)).2
      set L := z.take kl
      set R := z.drop kl
      set wl := L.foldl Nat.add 0
      have hL : L.length = kl := by
        exact List.length_take_of_le (by
          linarith [σ.decompose_sum (k + 2) (by linarith),
            σ.decompose_lt (k + 2) (by linarith)]) |> Eq.trans <| by aesop
      have hR : R.length = kr := by
        have hR_length : R.length = z.length - kl := by rw [List.length_drop]
        generalize_proofs at *
        exact hR_length.trans (Nat.sub_eq_of_eq_add <| by
          linarith [σ.decompose_sum (k + 2) (by linarith)])
      have hwl : wl ≤ n := by
        exact hn ▸ foldl_take_le _ _ |> le_trans <| by aesop
      have hL_bound : ∀ x ∈ L, x ≤ d := by
        exact fun x hx => hd x <| List.mem_of_mem_take hx
      have hR_bound : ∀ x ∈ R, x ≤ d := by
        exact fun x hx => hd x <| List.mem_of_mem_drop hx
      have hL_sum : L.foldl Nat.add 0 = wl := rfl
      have hR_sum : R.foldl Nat.add 0 = n - wl := by
        have hsum := foldl_add_append L R
        rw [List.take_append_drop, hn, hL_sum] at hsum
        omega
      generalize_proofs at *
      have h_rank_decomp : rank σ n (k + 2) d z =
          offset n kl kr d (σ.path n kl kr) wl +
          σ.combine (C.count wl kl d) (C.count (n - wl) kr d) wl
            (rank σ wl kl d L) (rank σ (n - wl) kr d R) := by
        rw [show z = L ++ R from by rw [List.take_append_drop]]
        exact rank_eq_offset_add_combine σ n (k + 2) d L R (Nat.le_add_left _ _) hL
      generalize_proofs at *
      -- The combine encoding is bounded by the block size
      have h_offset_combine :
          offset n kl kr d (σ.path n kl kr) wl +
          σ.combine (C.count wl kl d) (C.count (n - wl) kr d) wl
            (rank σ wl kl d L) (rank σ (n - wl) kr d R) <
          C.count wl kl d * C.count (n - wl) kr d + offset n kl kr d (σ.path n kl kr) wl := by
        have h_combine_bound : σ.combine (C.count wl kl d) (C.count (n - wl) kr d) wl
            (rank σ wl kl d L) (rank σ (n - wl) kr d R) <
            C.count wl kl d * C.count (n - wl) kr d := by
          apply σ.combine_bound
          · exact (ih kl (by linarith [σ.decompose_lt (k + 2) (Nat.le_add_left _ _)]) wl L hL_sum hL
              hL_bound)
          · generalize_proofs at *
            exact ih _ (by linarith [(σ.decompose_lt (k + 2) (Nat.le_add_left _ _)).2]) _ _
              hR_sum hR hR_bound |> fun x => x.trans_le (by linarith [(σ.decompose_sum (k + 2)
                (Nat.le_add_left _ _))])
        generalize_proofs at *
        linarith
      generalize_proofs at *
      -- Total count equals the sum over the path by count_path
      have h_count_path : C.count n (k + 2) d = (List.map (fun w =>
          C.count w kl d * C.count (n - w) kr d) (σ.path n kl kr)).sum := by
        apply C.count_path n (k + 2) kl kr d (σ.path n kl kr) (by
          exact Eq.symm (σ.decompose_sum _ (Nat.le_add_left _ _))) (by
          exact fun w hw => σ.path_valid n kl kr d w hw |> fun h => by simpa using h) (by
          exact σ.path_bound n kl kr) (by
          exact σ.path_nodup n kl kr)
      generalize_proofs at *
      -- The offset plus block size is at most the total sum
      have h_offset_block_le_sum : offset n kl kr d (σ.path n kl kr) wl +
          C.count wl kl d * C.count (n - wl) kr d ≤
          (List.map (fun w => C.count w kl d * C.count (n - w) kr d) (σ.path n kl kr)).sum := by
        apply offset_le_sum n kl kr d (σ.path n kl kr) wl (σ.path_nodup n kl kr)
          (σ.path_valid n kl kr d wl ⟨hwl, by exact Nat.pos_of_ne_zero (by omega)⟩)
      generalize_proofs at *
      linarith [h_offset_combine, h_offset_block_le_sum]

/-- Unranking the rank of a valid bounded composition recovers that composition. -/
theorem unrank_rank :
    ∀ (σ : Strategy) n k d (z : List Nat),
    z.foldl Nat.add 0 = n → z.length = k → (∀ x ∈ z, x ≤ d) →
    unrank σ n k d (rank σ n k d z) = z := by
  intro σ n k d z hn hk hle
  induction k using Nat.strong_induction_on generalizing n z d σ with
  | _ k ih =>
    rcases k with (_ | _ | k') <;> simp_all +decide
    · unfold unrank
      aesop
    · rcases z with (_ | ⟨x, _ | ⟨y, z⟩⟩) <;> simp_all +decide [List.foldl]
      unfold unrank
      aesop
    · -- Split z into left (L) and right (R) sub-compositions
      obtain ⟨L, R, hL, hR⟩ : ∃ L R : List ℕ, z = L ++ R ∧ L.length = (σ.decompose (k' + 2)).1 ∧
          R.length = (σ.decompose (k' + 2)).2 := by
        use List.take (k' + 2 - (σ.decompose (k' + 2)).2) z,
          List.drop (k' + 2 - (σ.decompose (k' + 2)).2) z
        generalize_proofs at *
        have := σ.decompose_sum (k' + 2) (by linarith)
        simp_all +decide
        omega
      generalize_proofs at *
      obtain ⟨wl, hwl⟩ : ∃ wl, L.foldl Nat.add 0 = wl ∧ R.foldl Nat.add 0 = n - wl := by
        use L.foldl Nat.add 0
        refine ⟨rfl, ?_⟩
        have h_sum : L.foldl Nat.add 0 + R.foldl Nat.add 0 = n := by
          calc
            L.foldl Nat.add 0 + R.foldl Nat.add 0 = (L ++ R).foldl Nat.add 0 := by
              rw [foldl_add_append]
            _ = z.foldl Nat.add 0 := by rw [← hL]
            _ = n := hn
        omega
      generalize_proofs at *
      obtain ⟨rl, rr, hrl, hrr⟩ : ∃ rl rr,
          rank σ wl (σ.decompose (k' + 2)).1 d L = rl ∧
          rank σ (n - wl) (σ.decompose (k' + 2)).2 d R = rr ∧
          rank σ n (k' + 2) d z = offset n (σ.decompose (k' + 2)).1 (σ.decompose (k' + 2)).2 d
            (σ.path n (σ.decompose (k' + 2)).1 (σ.decompose (k' + 2)).2) wl +
          σ.combine (C.count wl (σ.decompose (k' + 2)).1 d)
            (C.count (n - wl) (σ.decompose (k' + 2)).2 d) wl rl rr := by
        simp +zetaDelta at *
        rw [hL, rank_eq_offset_add_combine] <;> simp +arith +decide [*]
      generalize_proofs at *
      -- findBlock recovers the correct split point from the combined rank
      have h_findBlock : findBlock n (σ.decompose (k' + 2)).1 (σ.decompose (k' + 2)).2 d
          (σ.path n (σ.decompose (k' + 2)).1 (σ.decompose (k' + 2)).2)
          (offset n (σ.decompose (k' + 2)).1 (σ.decompose (k' + 2)).2 d
            (σ.path n (σ.decompose (k' + 2)).1 (σ.decompose (k' + 2)).2) wl +
          σ.combine (C.count wl (σ.decompose (k' + 2)).1 d)
            (C.count (n - wl) (σ.decompose (k' + 2)).2 d) wl rl rr) =
          (wl, σ.combine (C.count wl (σ.decompose (k' + 2)).1 d)
            (C.count (n - wl) (σ.decompose (k' + 2)).2 d) wl rl rr) := by
        have h_findBlock : σ.combine (C.count wl (σ.decompose (k' + 2)).1 d)
            (C.count (n - wl) (σ.decompose (k' + 2)).2 d) wl rl rr <
            C.count wl (σ.decompose (k' + 2)).1 d *
              C.count (n - wl) (σ.decompose (k' + 2)).2 d := by
          apply σ.combine_bound
          · rw [← hrl]
            exact rank_lt_count σ wl (σ.decompose (k' + 2) |>.1) d L
              (by aesop) (by aesop) (by aesop)
          · convert rank_lt_count σ (n - wl) (σ.decompose (k' + 2) |>.2) d R _ _ _ using 1 <;>
              aesop (simp_config := {singlePass := true})
        generalize_proofs at *
        apply findBlock_offset
        · exact σ.path_nodup n (σ.decompose (k' + 2)).1 (σ.decompose (k' + 2)).2
        · -- wl is in the path because it is a valid split point
          apply σ.path_valid n (σ.decompose (k' + 2)).1 (σ.decompose (k' + 2)).2 d wl
          generalize_proofs at *
          exact ⟨hwl.1 ▸ hn ▸ by
            rw [hL, List.foldl_append]
            simp +arith +decide [hwl]
            have h_foldl_ge : ∀ (l : List ℕ) (x : ℕ), x ≤ List.foldl Nat.add x l := by
              intro l x
              induction l using List.reverseRecOn with
              | nil => simp +arith +decide [*]
              | append_singleton l ih => simp +arith +decide [*]; linarith
            generalize_proofs at *
            exact h_foldl_ge _ _ |> le_trans (by simp +decide), pos_of_gt h_findBlock⟩
        · exact h_findBlock
      generalize_proofs at *
      -- split recovers (rl, rr) from the combined rank
      have h_split : σ.split (C.count wl (σ.decompose (k' + 2)).1 d)
          (C.count (n - wl) (σ.decompose (k' + 2)).2 d) wl
          (σ.combine (C.count wl (σ.decompose (k' + 2)).1 d)
            (C.count (n - wl) (σ.decompose (k' + 2)).2 d) wl rl rr) = (rl, rr) := by
        apply σ.split_combine
        · convert rank_lt_count σ wl (σ.decompose (k' + 2) |> Prod.fst) d L _ _ _ using 1 <;>
            aesop (simp_config := {singlePass := true})
        · convert rank_lt_count σ (n - wl) (σ.decompose (k' + 2) |>.2) d R _ _ _ using 1 <;>
            aesop (simp_config := {singlePass := true})
      generalize_proofs at *
      -- Apply induction hypothesis to left sub-composition
      have h_ind_L : unrank σ wl (σ.decompose (k' + 2)).1 d rl = L := by
        have h_ind_L_le : (σ.decompose (k' + 2)).1 ≤ k' + 1 := by
          linarith [σ.decompose_lt (k' + 2) (by linarith)]
        generalize_proofs at *
        rw [← hrl, ih _ h_ind_L_le _ _ _ _ hwl.1 hR.1 (by
          exact fun x hx => hle x <| hL.symm ▸ List.mem_append_left _ hx;)]
      -- Apply induction hypothesis to right sub-composition
      have h_ind_R : unrank σ (n - wl) (σ.decompose (k' + 2)).2 d rr = R := by
        specialize ih (σ.decompose (k' + 2)).2
          (by linarith [σ.decompose_lt (k' + 2) (by linarith)]) σ (n - wl) d R
        generalize_proofs at *
        convert ih hwl.2 hR.2 (fun x hx => hle x <| hL.symm ▸ List.mem_append_right _ hx) using 1
        aesop (simp_config := {singlePass := true})
      generalize_proofs at *
      unfold unrank
      aesop
