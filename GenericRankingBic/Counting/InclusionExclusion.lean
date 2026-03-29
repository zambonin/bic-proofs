import GenericRankingBic.Counting.Compositions
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Tactic

open Finset BigOperators Nat

/-- Stars-and-bars for a positive number of parts. -/
private lemma antidiagonalTuple_card (m k : ℕ) (hk : 0 < k) :
    Finset.card (Finset.Nat.antidiagonalTuple k m) = Nat.choose (m + k - 1) (k - 1) := by
  induction k generalizing m with
  | zero => simp_all +decide
  | succ k ih =>
    simp_all +decide [Finset.Nat.antidiagonalTuple]
    rcases k with (_ | k) <;> simp_all +decide [Multiset.Nat.antidiagonalTuple]
    rw [List.Nat.antidiagonalTuple]
    induction m with
    | zero => simp_all +decide [Nat.choose, add_comm]
    | succ m ih =>
      simp_all +decide [Nat.choose, add_comm, add_assoc]
      rw [show (List.map ((fun a => (k + a.2).choose k) ∘ Prod.map succ id)
                (List.Nat.antidiagonal m)) = List.map (fun a => (k + a.2).choose k)
                (List.Nat.antidiagonal m) from ?_]
      · linarith!
      · exact List.map_congr_left fun x hx => by aesop

/-- Inclusion–exclusion over coordinate violations. -/
private lemma compCount_eq_powerset_sum (n k d : ℕ) (_hk : 0 < k) :
    (compCount n k d : ℤ) =
      ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)),
        (-1 : ℤ) ^ S.card *
          Finset.card (Finset.filter (fun f : Fin k → ℕ => ∀ i ∈ S, f i ≥ d + 1)
            (Finset.Nat.antidiagonalTuple k n)) := by
  have h_incl_excl : ∀ f ∈ Finset.Nat.antidiagonalTuple k n,
      (∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)),
        (-1 : ℤ) ^ S.card * if (∀ i ∈ S, f i ≥ d + 1) then 1 else 0) =
      if (∀ i, f i ≤ d) then 1 else 0 := by
    intro f hf
    have h_filter : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)),
        (-1 : ℤ) ^ S.card * (if ∀ i ∈ S, f i ≥ d + 1 then 1 else 0) =
        ∏ i : Fin k, (if f i ≥ d + 1 then 0 else 1) := by
      have h_filter : ∏ i : Fin k, (1 - if f i ≥ d + 1 then 1 else 0) =
          ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)),
            (-1 : ℤ) ^ S.card * (if ∀ i ∈ S, f i ≥ d + 1 then 1 else 0) := by
        simp +decide [sub_eq_neg_add, Finset.prod_add]
        refine Finset.sum_congr rfl fun x hx => ?_
        split_ifs <;> simp_all +decide
        rw [Finset.prod_eq_zero_iff]
        aesop
      exact h_filter ▸ Finset.prod_congr rfl fun _ _ => by split_ifs <;> ring
    split_ifs <;> simp_all +decide [Finset.prod_ite]
    rw [Finset.card_eq_zero.mpr] <;> aesop
  have h_sum_comm : ∑ f ∈ Finset.Nat.antidiagonalTuple k n,
      (∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)),
        (-1 : ℤ) ^ S.card * if (∀ i ∈ S, f i ≥ d + 1) then 1 else 0) =
      ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)),
        (-1 : ℤ) ^ S.card * ∑ f ∈ Finset.Nat.antidiagonalTuple k n,
          (if ∀ i ∈ S, f i ≥ d + 1 then 1 else 0) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _]
  convert h_sum_comm using 1
  · rw [Finset.sum_congr rfl h_incl_excl]
    unfold compCount BoundedComp
    simp +decide
  · simp +decide

/-- Shifting the violating coordinates reduces each term to stars-and-bars. -/
private lemma inclExcl_subset_card (n k d : ℕ) (hk : 0 < k) (S : Finset (Fin k)) :
    (Finset.card (Finset.filter (fun f : Fin k → ℕ => ∀ i ∈ S, f i ≥ d + 1)
      (Finset.Nat.antidiagonalTuple k n)) : ℤ) =
    if (d + 1) * S.card ≤ n
    then (Nat.choose (n - (d + 1) * S.card + k - 1) (k - 1))
    else 0 := by
  split_ifs
  · rw_mod_cast [← antidiagonalTuple_card]
    · refine Finset.card_bij (fun f hf => fun i => f i - if i ∈ S then d + 1 else 0) ?_ ?_ ?_
      · simp +contextual [antidiagonalTuple]
        intro a ha h; simp_all +decide [Multiset.Nat.mem_antidiagonalTuple, mul_comm]
        rw [← ha, Nat.sub_eq_of_eq_add]
        zify [Finset.sum_add_distrib]
        rw [Finset.sum_congr rfl fun i hi => Nat.cast_sub <|
          show (if i ∈ S then d + 1 else 0) ≤ a i from by aesop]
        norm_num [Finset.sum_ite]
      · simp +contextual [funext_iff]
        grind
      · intro b hb
        refine ⟨fun i => b i + (if i ∈ S then d + 1 else 0), ?_, ?_⟩ <;>
          simp_all +decide [Finset.mem_filter, antidiagonalTuple]
        simp_all +decide [Multiset.Nat.mem_antidiagonalTuple]
        simp_all +decide [Finset.sum_add_distrib]
        grind
    · lia
  · simp +zetaDelta at *
    intro f hf
    by_contra h_contra
    push_neg at h_contra
    have := Multiset.Nat.mem_antidiagonalTuple.mp hf
    exact absurd (this ▸ Finset.sum_le_sum_of_subset (Finset.subset_univ S))
      (by
        simpa [mul_comm] using by
          nlinarith [show ∑ i ∈ S, f i ≥ (d + 1) * S.card from by
            simpa [mul_comm] using Finset.sum_le_sum fun i hi =>
              Nat.succ_le_of_lt <| h_contra i hi])

/-- Group the powerset sum by subset cardinality. -/
private lemma powerset_sum_reindex (n k d : ℕ) :
    ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)),
      (-1 : ℤ) ^ S.card *
        (if (d + 1) * S.card ≤ n
         then (Nat.choose (n - (d + 1) * S.card + k - 1) (k - 1))
         else 0) =
    ∑ i ∈ Finset.range (Nat.floor (n / (d + 1)) + 1),
      (-1 : ℤ) ^ i * Nat.choose k i *
        (Nat.choose (n - (d + 1) * i + k - 1) (k - 1)) := by
  rw [Finset.sum_powerset]
  simp +zetaDelta at *
  rw [← Finset.sum_subset]
  any_goals exact Finset.range (Min.min k (n / (d + 1)) + 1)
  · rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (min_le_right k (n / (d + 1)))))]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.sum_congr rfl fun y hy => if_pos <| ?_]
      · rw [Finset.sum_congr rfl fun y hy => by rw [Finset.mem_powersetCard.mp hy |>.2]]
        norm_num
        ring
      · simp +zetaDelta at *
        nlinarith [Nat.div_mul_le_self n (d + 1)]
    · exact fun x hx₁ hx₂ => by
        rw [Nat.choose_eq_zero_of_lt (by aesop)]
        ring
  · exact Finset.range_mono (Nat.succ_le_succ (min_le_left _ _ ))
  · norm_num +zetaDelta at *
    exact fun x hx₁ hx₂ => Finset.sum_eq_zero fun y hy => if_neg <| by
      have := hx₂ hx₁
      rw [Finset.mem_powersetCard] at hy
      rw [Nat.div_lt_iff_lt_mul <| Nat.succ_pos _] at this
      nlinarith [hy.2]

/-- Inclusion–exclusion count for a positive number of parts.
The finite-set proof groups coordinate-violation subsets by cardinality
and stops the sum at `inclExclBound n k d`. -/
theorem compCount_inclExcl (n k d : ℕ) (hk : 0 < k) :
    (compCount n k d : ℤ) =
      ∑ i ∈ Finset.range (inclExclBound n k d + 1),
        (-1 : ℤ) ^ i * (k.choose i : ℤ) *
          ((n + k - 1 - (d + 1) * i).choose (k - 1) : ℤ) := by
  have h_sum_reindex : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)),
      (-1 : ℤ) ^ S.card * (if (d + 1) * S.card ≤ n then Nat.choose (n - (d + 1) * S.card + k - 1)
        (k - 1) else 0) =
      ∑ i ∈ Finset.range (inclExclBound n k d + 1),
        (-1 : ℤ) ^ i * Nat.choose k i * Nat.choose (n - (d + 1) * i + k - 1) (k - 1) := by
    convert powerset_sum_reindex n k d using 1
    unfold inclExclBound
    cases le_total k (n / (d + 1)) <;> simp_all +decide
    rw [Finset.sum_subset (Finset.range_mono (by linarith : k + 1 ≤ n / (d + 1) + 1))
      fun x hx₁ hx₂ => by rw [Nat.choose_eq_zero_of_lt] <;> aesop]
  convert h_sum_reindex using 1
  · convert compCount_eq_powerset_sum n k d hk using 2
    rw [inclExcl_subset_card n k d hk]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [tsub_right_comm, tsub_add_eq_add_tsub]
    exact le_trans (Nat.mul_le_mul_left _ (Finset.mem_range_succ_iff.mp hi))
      (Nat.mul_le_mul_left _ (min_le_right _ _) |> le_trans <| Nat.mul_div_le _ _)

/-- Computable inclusion–exclusion count, with the empty-composition case handled separately.
For `k > 0`, there are `min k (n / (d + 1)) + 1` signed binomial summands;
this excludes the cost of binomial coefficients and integer arithmetic. -/
def inclExclCount (n k d : ℕ) : ℕ :=
  match k with
  | 0 => if n = 0 then 1 else 0
  | k + 1 =>
    (∑ i ∈ Finset.range (Nat.min (k + 1) (n / (d + 1)) + 1),
      (-1 : ℤ) ^ i * ((k + 1).choose i : ℤ) *
        ((n + k - (d + 1) * i).choose k : ℤ)).toNat

lemma inclExclCount_eq_compCount (n k d : ℕ) : inclExclCount n k d = compCount n k d := by
  rcases k with _ | k
  · simp only [inclExclCount]
    split_ifs with h
    · subst h; unfold compCount BoundedComp; simp
    · unfold compCount BoundedComp Finset.Nat.antidiagonalTuple
      cases n <;> simp_all
  · have hk : 0 < k + 1 := Nat.succ_pos k
    have h := compCount_inclExcl n (k + 1) d hk
    simp only [inclExclCount]
    have heq : ∑ i ∈ Finset.range (Nat.min (k + 1) (n / (d + 1)) + 1),
        (-1 : ℤ) ^ i * ((k + 1).choose i : ℤ) * ((n + k - (d + 1) * i).choose k : ℤ) =
        (compCount n (k + 1) d : ℤ) := by
      unfold inclExclBound at h; exact h.symm
    rw [heq, Int.toNat_natCast]
