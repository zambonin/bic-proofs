import GenericRankingBic.Ranking.Correctness
import GenericRankingBic.Ranking.Strategy
import Mathlib.Tactic

/-- Reflect both sub-ranks in odd blocks; use ordinary divmod in even blocks.
Zero dimensions or an out-of-range quotient also use ordinary divmod. -/
def splitGray (nl nr wl r : Nat) : Nat × Nat :=
  if wl % 2 = 0 ∨ nr = 0 ∨ r / nr ≥ nl then (r / nr, r % nr)
  else (nl - 1 - r / nr, nr - 1 - r % nr)

/-- Combine valid Gray sub-ranks, reflecting both coordinates in odd blocks. -/
def combineGray (nl nr wl rl rr : Nat) : Nat :=
  if wl % 2 = 0 ∨ nr = 0 ∨ rl ≥ nl then rl * nr + rr
  else (nl - 1 - rl) * nr + (nr - 1 - rr)

lemma combineGray_splitGray (nl nr wl : Nat) :
    ∀ r, combineGray nl nr wl (splitGray nl nr wl r).1 (splitGray nl nr wl r).2 = r := by
  intro r
  by_cases h_wl_even : wl % 2 = 0 ∨ nr = 0 ∨ r / nr ≥ nl
  · cases h_wl_even <;> simp +decide [*, splitGray, combineGray]
    · rw [Nat.div_add_mod']
    · rw [Nat.div_add_mod']
  · unfold splitGray combineGray
    simp_all +decide
    split_ifs <;> simp_all +decide [Nat.div_add_mod']
    · grind
    · rw [Nat.sub_sub_self (Nat.le_sub_one_of_lt h_wl_even.2.2),
        Nat.sub_sub_self (Nat.le_sub_one_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero h_wl_even.2.1)))]
      linarith [Nat.mod_add_div r nr]

lemma splitGray_combineGray (nl nr wl : Nat) :
    ∀ rl rr, rl < nl → rr < nr →
    splitGray nl nr wl (combineGray nl nr wl rl rr) = (rl, rr) := by
  intro rl rr hrl hr
  unfold splitGray combineGray
  split_ifs
  · norm_num [Nat.add_div, hr]
    exact ⟨Nat.le_antisymm (Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by nlinarith)
      (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero <| by aesop) |>.2 <| by nlinarith),
      Nat.mod_eq_of_lt hr⟩
  · grind +splitIndPred
  · simp_all +decide [Nat.add_mod]
    exact absurd ‹_› (not_le_of_gt <| Nat.div_lt_of_lt_mul <| by
      nlinarith [Nat.sub_add_cancel (show 1 ≤ nl from by linarith),
        Nat.sub_add_cancel (show rl ≤ nl - 1 from Nat.le_sub_one_of_lt hrl),
        Nat.sub_add_cancel (show 1 ≤ nr from by linarith),
        Nat.sub_add_cancel (show rr ≤ nr - 1 from Nat.le_sub_one_of_lt hr)])
  · rcases nr with (_ | _ | nr) <;> simp_all +decide [Nat.mod_eq_of_lt]
    · omega
    · norm_num [Nat.add_div] at *
      split_ifs <;> simp_all +decide [Nat.div_eq_of_lt, Nat.mod_eq_of_lt]
      · omega
      · omega

lemma splitGray_bound (nl nr wl : Nat) :
    ∀ r, r < nl * nr → (splitGray nl nr wl r).1 < nl ∧ (splitGray nl nr wl r).2 < nr := by
  unfold splitGray
  intro r hr
  split_ifs <;> simp_all +decide
  · exact ⟨Nat.div_lt_of_lt_mul <| by linarith,
      Nat.mod_lt _ <| Nat.pos_of_ne_zero <| by intro h; simp [h] at hr⟩
  · grind +ring

lemma combineGray_bound (nl nr wl : Nat) :
    ∀ rl rr, rl < nl → rr < nr → combineGray nl nr wl rl rr < nl * nr := by
  intro rl rr hrl hr
  unfold combineGray
  split_ifs <;> try nlinarith
  zify
  rw [Nat.sub_sub, Nat.sub_sub, Nat.cast_sub, Nat.cast_sub] <;> push_cast <;> nlinarith

/-- Left-peeling reflected Gray strategy; odd first-part blocks reverse the suffix order. -/
def stratGray [C : CountingContract] : Strategy where
  decompose := decompLeft
  decompose_sum := decompLeft_sum
  decompose_lt := decompLeft_lt
  path := fun n _kl _kr => pathIncreasing n
  path_nodup := fun n _kl _kr => pathIncreasing_nodup n
  path_bound := fun n _kl _kr => pathIncreasing_bound n
  path_valid := pathIncreasing_valid
  split := splitGray
  combine := combineGray
  split_bound := splitGray_bound
  combine_split := combineGray_splitGray
  split_combine := splitGray_combineGray
  combine_bound := combineGray_bound

theorem rank_unrank_stratGray [C : CountingContract] :
    ∀ n k d r, r < C.count n k d →
    rank stratGray n k d (unrank stratGray n k d r) = r :=
  fun n k d r hr => rank_unrank stratGray n k d r hr

theorem unrank_rank_stratGray [C : CountingContract] :
    ∀ n k d z, z.foldl Nat.add 0 = n → z.length = k → (∀ x ∈ z, x ≤ d) →
    unrank stratGray n k d (rank stratGray n k d z) = z :=
  fun n k d z hn hk hle =>
    unrank_rank stratGray n k d z hn hk hle
