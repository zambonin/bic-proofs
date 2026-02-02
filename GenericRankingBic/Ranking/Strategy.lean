import GenericRankingBic.Counting.Contract
import Mathlib.Tactic

/-- Decomposition, traversal and rank arithmetic with the laws used by the inverse proofs. -/
structure Strategy [C : CountingContract] where
  /-- D: decomposition function k → (k_l, k_r). -/
  decompose : Nat → Nat × Nat
  decompose_sum : ∀ k, k > 1 → (decompose k).1 + (decompose k).2 = k
  decompose_lt : ∀ k, k > 1 → (decompose k).1 < k ∧ (decompose k).2 < k
  /-- Candidate left sums in traversal order; zero-size blocks may be included. -/
  path : Nat → Nat → Nat → List Nat
  path_nodup : ∀ n kl kr, (path n kl kr).Nodup
  path_bound : ∀ n kl kr, ∀ w ∈ path n kl kr, w ≤ n
  path_valid : ∀ n kl kr d, ∀ w,
    (w ≤ n ∧ C.count w kl d * C.count (n - w) kr d > 0) → w ∈ path n kl kr
  /-- S: rank split S^{(nl, nr, wl)}(r) → (r_l, r_r). -/
  split : (nl nr wl : Nat) → Nat → Nat × Nat
  /-- S⁻¹: rank combine (r_l, r_r) → r. -/
  combine : (nl nr wl : Nat) → Nat → Nat → Nat
  split_bound : ∀ nl nr wl r, r < nl * nr →
    (split nl nr wl r).1 < nl ∧ (split nl nr wl r).2 < nr
  combine_split : (nl nr wl : Nat) → ∀ r,
    combine nl nr wl (split nl nr wl r).1 (split nl nr wl r).2 = r
  split_combine : (nl nr wl : Nat) → ∀ rl rr, rl < nl → rr < nr →
    split nl nr wl (combine nl nr wl rl rr) = (rl, rr)
  combine_bound : ∀ nl nr wl rl rr, rl < nl → rr < nr →
    combine nl nr wl rl rr < nl * nr

/-- At non-base nodes, peel the last part with split `(k - 1, 1)`. -/
def decompRight : Nat → Nat × Nat
  | 0 => (0, 0)
  | 1 => (1, 0)
  | Nat.succ (Nat.succ k) => (Nat.succ k, 1)

lemma decompRight_sum : ∀ k, k > 1 → (decompRight k).1 + (decompRight k).2 = k := by
  intro k hk
  cases k with
  | zero => omega
  | succ k' =>
    cases k' with
    | zero => omega
    | succ => simp [decompRight]

lemma decompRight_lt : ∀ k, k > 1 → (decompRight k).1 < k ∧ (decompRight k).2 < k := by
  intro k hk
  cases k with
  | zero => omega
  | succ k' =>
    cases k' with
    | zero => omega
    | succ => simp [decompRight]

/-- At non-base nodes, peel the first part with split `(1, k - 1)`. -/
def decompLeft : Nat → Nat × Nat
  | 0 => (0, 0)
  | 1 => (1, 0)
  | Nat.succ (Nat.succ k) => (1, Nat.succ k)

lemma decompLeft_sum : ∀ k, k > 1 → (decompLeft k).1 + (decompLeft k).2 = k := by
  intro k hk
  cases k with
  | zero => omega
  | succ k' =>
    cases k' with
    | zero => omega
    | succ => simp [decompLeft]; omega

lemma decompLeft_lt : ∀ k, k > 1 → (decompLeft k).1 < k ∧ (decompLeft k).2 < k := by
  intro k hk
  cases k with
  | zero => omega
  | succ k' =>
    cases k' with
    | zero => omega
    | succ => simp [decompLeft]

/-- The increasing path P_inc = [0, 1, ..., n]. Only depends on n. -/
def pathIncreasing (n : Nat) : List Nat :=
  List.range (n + 1)

/-- Decreasing left-sum path. With right peeling, this visits the last part from 0 upward. -/
def pathDecreasing (n : Nat) : List Nat :=
  (List.range (n + 1)).reverse

@[simp]
lemma pathDecreasing_nodup : ∀ n, (pathDecreasing n).Nodup := by
  intro n
  simp [pathDecreasing, List.nodup_range]

@[simp]
lemma pathDecreasing_bound : ∀ n, ∀ w ∈ pathDecreasing n, w ≤ n := by
  intro n w hw
  simp only [pathDecreasing, List.mem_reverse, List.mem_range] at hw
  omega

lemma pathDecreasing_valid [C : CountingContract] :
    ∀ n kl kr d w, (w ≤ n ∧ C.count w kl d * C.count (n - w) kr d > 0) →
      w ∈ pathDecreasing n := by
  intro n _ _ _ w h
  simp [pathDecreasing, Nat.lt_succ_of_le h.1]

@[simp]
lemma pathIncreasing_nodup : ∀ n, (pathIncreasing n).Nodup := by
  intros
  exact List.nodup_range

@[simp]
lemma pathIncreasing_bound : ∀ n, ∀ w ∈ pathIncreasing n, w ≤ n := by
  intros n w hw
  exact Nat.le_of_lt_succ (List.mem_range.mp hw)

lemma pathIncreasing_valid [C : CountingContract] :
    ∀ n kl kr d w, (w ≤ n ∧ C.count w kl d * C.count (n - w) kr d > 0) → w ∈ pathIncreasing n := by
  intro n _ _ _ w h
  exact List.mem_range.mpr (Nat.lt_succ_of_le h.1)

/-- Default split: divmod by nr. Encodes a pair (rl, rr) with rr < nr as r = rl * nr + rr. -/
def splitDivMod (nr r : Nat) : Nat × Nat :=
  (r / nr, r % nr)

/-- Encode valid sub-ranks as `rl * nr + rr`. -/
def combineMulAdd (nr rl rr : Nat) : Nat :=
  rl * nr + rr

lemma combineMulAdd_splitDivMod (nr : Nat) :
    ∀ r, combineMulAdd nr (splitDivMod nr r).1 (splitDivMod nr r).2 = r := by
  intro r
  simp [splitDivMod, combineMulAdd, Nat.mul_comm, Nat.div_add_mod]

lemma splitDivMod_combineMulAdd (nr : Nat) :
    ∀ rl rr, rr < nr →
    splitDivMod nr (combineMulAdd nr rl rr) = (rl, rr) := by
  intro rl rr hrr
  simp [splitDivMod, combineMulAdd]
  exact ⟨Nat.le_antisymm (Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by nlinarith)
    (Nat.le_div_iff_mul_le (by linarith) |>.2 <| by nlinarith), Nat.mod_eq_of_lt hrr⟩

lemma splitDivMod_bound (nl nr : Nat) :
    ∀ r, r < nl * nr → (splitDivMod nr r).1 < nl ∧ (splitDivMod nr r).2 < nr := by
  exact fun r hr => ⟨Nat.div_lt_of_lt_mul <| by linarith,
    Nat.mod_lt _ <| Nat.pos_of_ne_zero <| by rintro rfl; linarith⟩

lemma combineMulAdd_bound (nl nr : Nat) :
    ∀ rl rr, rl < nl → rr < nr → combineMulAdd nr rl rr < nl * nr := by
  intro rl rr hrl hrr
  simp [combineMulAdd]
  nlinarith
