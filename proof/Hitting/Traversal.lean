import proof.Hitting.Wasserstein
import proof.Hitting.PiBound

/-!
# The averaged hitting process (`lemma:distribution`, `lemma:step`)

The paper's Algorithm "Wasserstein Walk" is a random process: at step `j` the set `I`
of hit labels is a uniform `j`-subset (`lemma:distribution`), the current vertex has law
`p_I`, and the next step follows an optimal coupling from `p_I` to `q_I`. Instead of
probability, we use the corresponding finite averages:

* `travCost d ν g k B x` is the least cost of `k` further selections from the state
  `(B, x)` (a backward recursion); each selection moves to a point `y` in the support of
  a new label `i` and pays `d x y + g i y`. The extra endpoint cost `g` is zero in the
  paper; the separator uses it for the paths back to the branch sets.
* `travCost_step`: from the state `(B, ·)` averaged against `ν_B`, following a coupling
  `Γ` from `ν_B` to `ν_{Bᶜ}` costs `cost Γ` plus the averaged remaining cost. This is the
  averaged form of the transition probabilities in the proof of `lemma:distribution`.
* `expected_cost_step` averages this over the uniform `j`-subsets, and `expected_step_le` is the
  bound of `lemma:step` on the averaged coupling costs.

`wasserstein_walk` assembles these into a tour whose length is at most the expected
length of the walk of the randomized algorithm. `wasserstein_walk_measures` specializes it to
the uniform weighting, which is the form used by `extended_short_tree`, and
`wasserstein_walk_sets` to uniform measures on sets, which gives `thm:hitting`.

Labels are `Fin q`; the uniform `j`-subsets are `Finset.powersetCard j univ`.
-/

namespace MinorFreeSeparators

open Finset

variable {X : Type*}

/-- Total successive distance along a list of points. -/
def tourLength (d : X → X → ℝ) : List X → ℝ
  | x :: y :: L => d x y + tourLength d (y :: L)
  | _ => 0

/-! ### Combinatorics of label subsets -/

/-- Reindexing pairs `(B, i)` with `|B| = j`, `i ∉ B` by `B' = B ∪ {i}`. -/
lemma sum_powersetCard_compl_insert {q : ℕ} (j : ℕ) (F : Finset (Fin q) → Fin q → ℝ) :
    ∑ B ∈ powersetCard j univ, ∑ i ∈ Bᶜ, F (insert i B) i =
      ∑ B ∈ powersetCard (j + 1) univ, ∑ i ∈ B, F B i := by
  have h1 : ∀ B : Finset (Fin q),
      ∑ i ∈ Bᶜ, F (insert i B) i = ∑ i, if i ∉ B then F (insert i B) i else 0 := by
    intro B; rw [← sum_filter]; congr 1; ext i; simp
  have h2 : ∀ B : Finset (Fin q), ∑ i ∈ B, F B i = ∑ i, if i ∈ B then F B i else 0 := by
    intro B; rw [← sum_filter]; congr 1; ext i; simp
  simp_rw [h1, h2]
  rw [sum_comm, sum_comm (s := powersetCard (j + 1) _)]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_filter, ← sum_filter]
  refine sum_nbij' (insert i) (fun B => B.erase i) ?_ ?_ ?_ ?_ ?_
  · intro B hB
    simp only [mem_filter, mem_powersetCard] at hB ⊢
    exact ⟨⟨subset_univ _, by rw [card_insert_of_notMem hB.2, hB.1.2]⟩,
      mem_insert_self _ _⟩
  · intro B hB
    simp only [mem_filter, mem_powersetCard] at hB ⊢
    refine ⟨⟨subset_univ _, ?_⟩, notMem_erase _ _⟩
    rw [card_erase_of_mem hB.2, hB.1.2]; rfl
  · intro B hB
    simp only [mem_filter] at hB
    exact erase_insert hB.2
  · intro B hB
    simp only [mem_filter] at hB
    exact insert_erase hB.2
  · intro B _; rfl

/-- `∑_{|B| = j} ∑_{i ∉ B} a_i = C(q-1, j) ∑_i a_i`: each label lies outside `C(q-1, j)` of
the `j`-subsets. -/
lemma sum_powersetCard_sum_compl {q : ℕ} (a : Fin q → ℝ) (j : ℕ) :
    ∑ B ∈ powersetCard j univ, ∑ i ∈ Bᶜ, a i = ((q - 1).choose j : ℝ) * ∑ i, a i := by
  set A := ∑ i, a i
  set P : ℕ → ℝ := fun j => ∑ B ∈ powersetCard j univ, ∑ i ∈ B, a i
  have hP : ∀ j, ∑ B ∈ powersetCard j univ, ∑ i ∈ Bᶜ, a i = P (j + 1) := by
    intro j
    simpa using sum_powersetCard_compl_insert j (fun _ i => a i)
  have hrec : ∀ j, P (j + 1) = (q.choose j : ℝ) * A - P j := by
    intro j
    rw [← hP]
    have hA : (q.choose j : ℝ) * A = ∑ _B ∈ powersetCard j (univ : Finset (Fin q)), A := by
      simp [card_powersetCard]
    simp only [P]
    rw [hA, ← sum_sub_distrib]
    refine sum_congr rfl fun B _ => ?_
    have := sum_compl_add_sum B a
    simp only [A]; linarith
  rw [hP]
  rcases q with _ | p
  · simp only [P, A]
    rw [powersetCard_eq_empty.mpr (by simp)]
    simp
  have key : ∀ j, P (j + 1) = (p.choose j : ℝ) * A := by
    intro j
    induction j with
    | zero => rw [hrec]; simp [P]
    | succ j ih =>
      rw [hrec, ih, Nat.choose_succ_succ' p j]
      push_cast; ring
  simpa using key j

/-- The variance identity for subset sums: if `∑_i a_i = 0` and `q = n + 2`, then
`∑_{|B| = j+1} (∑_{i ∈ B} a_i)² = C(n, j) ∑_i a_i²`. -/
lemma sum_powersetCard_sq {q : ℕ} (a : Fin q → ℝ) (ha : ∑ i, a i = 0) (n : ℕ)
    (hq : q = n + 2) (j : ℕ) :
    ∑ B ∈ powersetCard (j + 1) univ, (∑ i ∈ B, a i) ^ 2 = (n.choose j : ℝ) * ∑ i, a i ^ 2 := by
  set N : ℕ → ℝ := fun j => ∑ B ∈ powersetCard j univ, (∑ i ∈ B, a i) ^ 2
  -- `N (j + 1) = ∑_{|B| = j} ∑_{i ∉ B} a_i (a_i + ∑_B a)`, and `∑_{i ∉ B} a_i = -∑_B a`
  have hN : ∀ j, N (j + 1) = ((n + 1).choose j : ℝ) * ∑ i, a i ^ 2 - N j := by
    intro j
    have h := sum_powersetCard_compl_insert j (fun B i => a i * ∑ r ∈ B, a r)
    have hA := sum_powersetCard_sum_compl (fun i => a i ^ 2) j
    beta_reduce at h hA
    rw [show q - 1 = n + 1 by omega] at hA
    have e1 : N (j + 1) = ∑ B ∈ powersetCard (j + 1) univ, ∑ i ∈ B, a i * ∑ r ∈ B, a r := by
      simp only [N, sq, sum_mul]
    rw [e1, ← h, ← hA]
    simp only [N, ← sum_sub_distrib]
    refine sum_congr rfl fun B _ => ?_
    have hs : ∑ i ∈ Bᶜ, a i = -∑ i ∈ B, a i := by
      rw [eq_neg_iff_add_eq_zero, sum_compl_add_sum, ha]
    calc ∑ i ∈ Bᶜ, a i * ∑ r ∈ insert i B, a r
        = ∑ i ∈ Bᶜ, a i ^ 2 + (∑ i ∈ Bᶜ, a i) * ∑ i ∈ B, a i := by
          rw [sum_mul, ← sum_add_distrib]
          refine sum_congr rfl fun i hi => ?_
          rw [sum_insert (mem_compl.1 hi)]; ring
      _ = _ := by rw [hs]; ring
  have key : ∀ j, N (j + 1) = (n.choose j : ℝ) * ∑ i, a i ^ 2 := by
    intro j
    induction j with
    | zero => rw [hN]; simp [N]
    | succ j ih => rw [hN, ih, Nat.choose_succ_succ' n j]; push_cast; ring
  exact key j

/-! ### The backward recursion -/

section Cost

variable [Fintype X] (d : X → X → ℝ) {q : ℕ} (ν : Fin q → X → ℝ) (g : Fin q → X → ℝ)

/-- Valid moves from the selected-label set `B`: a new label and a point of its support. -/
noncomputable def travMoves (B : Finset (Fin q)) : Finset (Fin q × X) :=
  univ.filter fun p => p.1 ∉ B ∧ 0 < ν p.1 p.2

/-- Least cost of `k` further selections from the state `(B, x)`. A selection of label `i`
at a point `y` of its support costs `d x y + g i y`. -/
noncomputable def travCost : ℕ → Finset (Fin q) → X → ℝ
  | 0, _, _ => 0
  | k + 1, B, x =>
    if h : (travMoves ν B).Nonempty then
      (travMoves ν B).inf' h fun p => d x p.2 + g p.1 p.2 + travCost k (insert p.1 B) p.2
    else 0

variable {d ν g}

lemma travCost_le {k : ℕ} {B : Finset (Fin q)} {x : X} {i : Fin q} {y : X} (hi : i ∉ B)
    (hy : 0 < ν i y) :
    travCost d ν g (k + 1) B x ≤ d x y + (g i y + travCost d ν g k (insert i B) y) := by
  have hm : (i, y) ∈ travMoves ν B := by simp [travMoves, hi, hy]
  rw [travCost, dif_pos ⟨_, hm⟩, ← add_assoc]
  exact inf'_le
    (fun p : Fin q × X => d x p.2 + g p.1 p.2 + travCost d ν g k (insert p.1 B) p.2) hm

/-- The recursion is realized by an actual tour, with a selection point for every
remaining label. -/
lemma travCost_realize (hν : ∀ i, ∃ x, 0 < ν i x) :
    ∀ k (B : Finset (Fin q)), B.card + k = q → ∀ x, ∃ L : List X, ∃ z : Fin q → X,
      (∀ i ∉ B, z i ∈ L ∧ 0 < ν i (z i)) ∧
      tourLength d (x :: L) + ∑ i ∈ Bᶜ, g i (z i) ≤ travCost d ν g k B x := by
  intro k
  induction k with
  | zero =>
    intro B hB x
    have hBu : B = univ := eq_univ_of_card B (by simpa using hB)
    refine ⟨[], fun _ => x, fun i hi => absurd (hBu ▸ mem_univ i) hi, ?_⟩
    simp [tourLength, travCost, hBu]
  | succ k ih =>
    intro B hB x
    have hne : (travMoves ν B).Nonempty := by
      obtain ⟨i, hi⟩ : ∃ i, i ∉ B := by
        by_contra h
        push Not at h
        have : B = univ := eq_univ_of_forall h
        rw [this, card_univ, Fintype.card_fin] at hB
        omega
      obtain ⟨y, hy⟩ := hν i
      exact ⟨(i, y), by simp [travMoves, hi, hy]⟩
    obtain ⟨p, hp, hpeq⟩ := exists_mem_eq_inf' hne
      (fun p : Fin q × X => d x p.2 + g p.1 p.2 + travCost d ν g k (insert p.1 B) p.2)
    simp only [travMoves, mem_filter, mem_univ, true_and] at hp
    obtain ⟨L, z, hz, hL⟩ := ih (insert p.1 B)
      (by rw [card_insert_of_notMem hp.1]; omega) p.2
    refine ⟨p.2 :: L, Function.update z p.1 p.2, fun i hi => ?_, ?_⟩
    · by_cases hip : i = p.1
      · subst hip
        simp only [Function.update_self]
        exact ⟨List.mem_cons_self, hp.2⟩
      · rw [Function.update_of_ne hip]
        obtain ⟨h1, h2⟩ := hz i (by simp [hip, hi])
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    · have hmem : p.1 ∈ Bᶜ := mem_compl.mpr hp.1
      rw [← add_sum_erase _ _ hmem, Function.update_self, ← compl_insert]
      have hsum : ∑ i ∈ (insert p.1 B)ᶜ, g i (Function.update z p.1 p.2 i) =
          ∑ i ∈ (insert p.1 B)ᶜ, g i (z i) := by
        refine sum_congr rfl fun i hi => ?_
        rw [Function.update_of_ne]
        rintro rfl
        simp at hi
      rw [hsum, travCost, dif_pos hne, hpeq, tourLength]
      linarith

/-- One step of the averaged process: the cost at `(B, x)`, averaged against the row
marginal `α` of a coupling `Γ` towards the remaining labels, is at most the cost of `Γ`
plus the averaged cost after one more selection. -/
lemma travCost_step (hν0 : ∀ i x, 0 ≤ ν i x) (B : Finset (Fin q)) (k : ℕ)
    (Γ : X → X → ℝ) (α : X → ℝ) (c : ℝ) (hc : 0 < c) (hΓ0 : ∀ x y, 0 ≤ Γ x y)
    (hrow : ∀ x, ∑ y, Γ x y = α x) (hcol : ∀ y, ∑ x, Γ x y = (∑ i ∈ Bᶜ, ν i y) / c) :
    ∑ x, α x * travCost d ν g (k + 1) B x ≤
      ∑ x, ∑ y, d x y * Γ x y +
        (∑ i ∈ Bᶜ, ∑ y, ν i y * (g i y + travCost d ν g k (insert i B) y)) / c := by
  set R : Fin q → X → ℝ := fun i y => g i y + travCost d ν g k (insert i B) y with hR
  set s : X → ℝ := fun y => ∑ i ∈ Bᶜ, ν i y
  have hzero : ∀ x y, s y = 0 → Γ x y = 0 := by
    intro x y hs
    have h1 : ∑ x, Γ x y = 0 := by rw [hcol y]; change s y / c = 0; rw [hs, zero_div]
    exact (sum_eq_zero_iff_of_nonneg (fun x _ => hΓ0 x y)).1 h1 x (mem_univ _)
  have hw : ∀ x y, ∑ i ∈ Bᶜ, Γ x y * ν i y / s y = Γ x y := by
    intro x y
    rw [← sum_div, ← mul_sum]
    by_cases hs : s y = 0
    · simp [hzero x y hs]
    · exact mul_div_cancel_right₀ _ hs
  have hw0 : ∀ x y i, 0 ≤ Γ x y * ν i y / s y := by
    intro x y i
    exact div_nonneg (mul_nonneg (hΓ0 x y) (hν0 i y)) (sum_nonneg fun r _ => hν0 r y)
  have hpt : ∀ x, α x * travCost d ν g (k + 1) B x ≤
      ∑ y, d x y * Γ x y + ∑ y, ∑ i ∈ Bᶜ, Γ x y * ν i y / s y * R i y := by
    intro x
    calc α x * travCost d ν g (k + 1) B x
        = ∑ y, ∑ i ∈ Bᶜ, Γ x y * ν i y / s y * travCost d ν g (k + 1) B x := by
          rw [← hrow x, sum_mul]
          refine sum_congr rfl fun y _ => ?_
          rw [← sum_mul, hw]
      _ ≤ ∑ y, ∑ i ∈ Bᶜ, Γ x y * ν i y / s y * (d x y + R i y) := by
          refine sum_le_sum fun y _ => sum_le_sum fun i hi => ?_
          rcases (hν0 i y).lt_or_eq with hpos | hz
          · exact mul_le_mul_of_nonneg_left (travCost_le (mem_compl.1 hi) hpos) (hw0 x y i)
          · simp [← hz]
      _ = ∑ y, d x y * Γ x y + ∑ y, ∑ i ∈ Bᶜ, Γ x y * ν i y / s y * R i y := by
          rw [← sum_add_distrib]
          refine sum_congr rfl fun y _ => ?_
          have hd : d x y * Γ x y = ∑ i ∈ Bᶜ, Γ x y * ν i y / s y * d x y := by
            rw [← sum_mul, hw]; ring
          rw [hd, ← sum_add_distrib]
          refine sum_congr rfl fun i _ => ?_
          ring
  refine (sum_le_sum fun x _ => hpt x).trans ?_
  rw [sum_add_distrib]
  refine add_le_add le_rfl (le_of_eq ?_)
  have hswap : ∀ F : X → X → Fin q → ℝ,
      ∑ x, ∑ y, ∑ i ∈ Bᶜ, F x y i = ∑ i ∈ Bᶜ, ∑ y, ∑ x, F x y i := by
    intro F
    rw [sum_comm]
    exact (sum_congr rfl fun y _ => sum_comm).trans sum_comm
  rw [hswap, sum_div]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_div]
  refine sum_congr rfl fun y _ => ?_
  have hsum : ∑ x, Γ x y * ν i y / s y * R i y = (∑ x, Γ x y) * ν i y / s y * R i y := by
    rw [sum_mul, sum_div, sum_mul]
  rw [hsum, hcol y]
  by_cases hs : s y = 0
  · have : ν i y = 0 := le_antisymm
      (hs ▸ single_le_sum (fun r _ => hν0 r y) hi) (hν0 i y)
    simp [this]
  · change s y / c * ν i y / s y * _ = _
    simp only [hR]
    field_simp

end Cost

/-! ### Averaging over levels -/

section Level

variable [Fintype X]

/-- `levelSum d ν g k j = ∑_{|B| = j} ∑_x (∑_{i ∈ B} ν_i(x)) travCost_k(B, x)`, which is
`j C(q, j)` times the expected remaining cost at level `j`. -/
noncomputable def levelSum (d : X → X → ℝ) {q : ℕ} (ν g : Fin q → X → ℝ) (k j : ℕ) : ℝ :=
  ∑ B ∈ powersetCard j univ, ∑ x, (∑ i ∈ B, ν i x) * travCost d ν g k B x

variable {d : X → X → ℝ} {q : ℕ} {ν g : Fin q → X → ℝ}

lemma levelSum_zero (j : ℕ) : levelSum d ν g 0 j = 0 := by
  simp [levelSum, travCost]

/-- `travCost_step` summed over the `j`-subsets `B`: the level-`j` sum over `j` is at most the
total coupling cost plus the level-`(j + 1)` sum and the endpoint costs over `q - j`. -/
lemma expected_cost_step (hν0 : ∀ i x, 0 ≤ ν i x) (k j : ℕ) (hjq : j < q)
    (Γ : Finset (Fin q) → X → X → ℝ)
    (hΓ : ∀ B ∈ powersetCard j univ, (∀ x y, 0 ≤ Γ B x y) ∧
      (∀ x, ∑ y, Γ B x y = (∑ i ∈ B, ν i x) / j) ∧
      (∀ y, ∑ x, Γ B x y = (∑ i ∈ Bᶜ, ν i y) / ((q : ℝ) - j))) :
    levelSum d ν g (k + 1) j / j ≤
      ∑ B ∈ powersetCard j univ, ∑ x, ∑ y, d x y * Γ B x y +
        (levelSum d ν g k (j + 1) + ((q - 1).choose j : ℝ) * ∑ i, ∑ y, ν i y * g i y) /
          ((q : ℝ) - j) := by
  have hc : (0 : ℝ) < q - j := by
    have : (j : ℝ) < q := by exact_mod_cast hjq
    linarith
  have hB : ∀ B ∈ powersetCard j univ,
      ∑ x, (∑ i ∈ B, ν i x) * travCost d ν g (k + 1) B x / j ≤
        ∑ x, ∑ y, d x y * Γ B x y +
          (∑ i ∈ Bᶜ, ∑ y, ν i y * (g i y + travCost d ν g k (insert i B) y)) / ((q : ℝ) - j) := by
    intro B hB
    obtain ⟨h0, hr, hcol⟩ := hΓ B hB
    refine le_of_eq_of_le ?_
      (travCost_step hν0 B k (Γ B) (fun x => (∑ i ∈ B, ν i x) / j) _ hc h0 hr hcol)
    refine sum_congr rfl fun x _ => ?_
    ring
  have hre := sum_powersetCard_compl_insert j (fun B' i => ∑ y, ν i y * travCost d ν g k B' y)
  beta_reduce at hre
  have hg := sum_powersetCard_sum_compl (fun i => ∑ y, ν i y * g i y) j
  calc levelSum d ν g (k + 1) j / j
      = ∑ B ∈ powersetCard j univ,
          ∑ x, (∑ i ∈ B, ν i x) * travCost d ν g (k + 1) B x / j := by
        rw [levelSum, sum_div]
        refine sum_congr rfl fun B _ => ?_
        rw [sum_div]
    _ ≤ ∑ B ∈ powersetCard j univ, (∑ x, ∑ y, d x y * Γ B x y +
          (∑ i ∈ Bᶜ, ∑ y, ν i y * (g i y + travCost d ν g k (insert i B) y)) / ((q : ℝ) - j)) :=
        sum_le_sum hB
    _ = _ := by
        rw [sum_add_distrib, ← sum_div]
        congr 2
        simp only [mul_add, sum_add_distrib]
        rw [hg, hre, add_comm]
        congr 1
        rw [levelSum]
        refine sum_congr rfl fun B _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun y _ => ?_
        rw [sum_mul]

end Level

/-! ### Averaged coupling costs -/

/-- Absorption applied twice: `C(q-2, m) q (q-1) = C(q, m+1) (m+1) (q-m-1)`, with
`q = n + 2`. -/
lemma choose_mul_absorb_two {q n m : ℕ} (hq : q = n + 2) (hm : m ≤ n) :
    (n.choose m : ℝ) * q * (q - 1) = (q.choose (m + 1) : ℝ) * (m + 1) * (q - (m + 1)) := by
  subst hq
  have h1 := Nat.add_one_mul_choose_eq n m
  have h2 := Nat.add_one_mul_choose_eq (n + 1) (m + 1)
  have h3 := Nat.choose_succ_right_eq (n + 2) (m + 1)
  rw [show n + 2 - (m + 1) = (n - m) + 1 by omega] at h3
  have key : n.choose m * ((n + 2) * (n + 1)) =
      (n + 2).choose (m + 1) * ((m + 1) * ((n - m) + 1)) := by
    calc n.choose m * ((n + 2) * (n + 1)) = (n + 2) * ((n + 1) * n.choose m) := by ring
      _ = (n + 2) * (n + 1).choose (m + 1) * (m + 1) := by rw [h1]; ring
      _ = (n + 1 + 1).choose (m + 1 + 1) * (m + 1 + 1) * (m + 1) := by rw [← h2]
      _ = _ := by rw [h3]; ring
  have key' : ((n.choose m * ((n + 2) * (n + 1)) : ℕ) : ℝ) =
      (((n + 2).choose (m + 1) * ((m + 1) * ((n - m) + 1)) : ℕ) : ℝ) := by rw [key]
  push_cast [Nat.cast_sub hm] at key' ⊢
  linarith

/-- The expected coupling cost at level `j` (`lemma:step`): averaged over the uniform
`j`-subsets `B`, the bound of `exists_coupling_le` for the coupling from `ν_B` to `ν_{Bᶜ}`
is at most `σ √(qV/(q-1)) / √(j(q-j))`, where `V = ∑_i ‖ν_i/w - mean‖²_{2,w}`. -/
lemma expected_step_le [Fintype X] (w : X → ℝ) (hw : ∀ x, 0 < w x) {q : ℕ} (hq : 2 ≤ q)
    (ν : Fin q → X → ℝ) (j : ℕ) (hj : 0 < j) (hjq : j < q) (σ : ℝ) (hσ : 0 ≤ σ)
    (cost : Finset (Fin q) → ℝ)
    (hcost : ∀ B ∈ powersetCard j univ, cost B ≤ σ *
      √(∑ x, w x * ((∑ i ∈ B, ν i x) / j / w x - (∑ i ∈ Bᶜ, ν i x) / ((q : ℝ) - j) / w x) ^ 2)) :
    ∑ B ∈ powersetCard j univ, cost B ≤ (q.choose j : ℝ) *
      (σ * (√(q * (∑ i, ∑ x, w x * (ν i x / w x - (∑ r, ν r x / w x) / q) ^ 2) /
        (q - 1)) / √(j * ((q : ℝ) - j)))) := by
  obtain ⟨n, hn⟩ : ∃ n, q = n + 2 := ⟨q - 2, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  set g : Fin q → X → ℝ := fun i x => ν i x / w x - (∑ r, ν r x / w x) / q with hg
  set V := ∑ i, ∑ x, w x * g i x ^ 2 with hV
  set jr : ℝ := ((m + 1 : ℕ) : ℝ) with hjr
  have hjr0 : 0 < jr := by positivity
  have hqj : jr < q := by rw [hjr]; exact_mod_cast hjq
  have hq0 : (0 : ℝ) < q := by linarith
  have hqj0 : (0 : ℝ) < q - jr := by linarith
  have hq1 : (1 : ℝ) < q := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  set κ : ℝ := q / (jr * (q - jr)) with hκ
  set Q : Finset (Fin q) → ℝ := fun B =>
    ∑ x, w x * ((∑ i ∈ B, ν i x) / jr / w x - (∑ i ∈ Bᶜ, ν i x) / ((q : ℝ) - jr) / w x) ^ 2
    with hQdef
  set N : ℝ := (q.choose (m + 1) : ℝ) with hN
  have hN0 : 0 < N := by
    simp only [hN]; exact_mod_cast Nat.choose_pos hjq.le
  have hD : ∀ B ∈ powersetCard (m + 1) univ, ∀ x,
      (∑ i ∈ B, ν i x) / jr / w x - (∑ i ∈ Bᶜ, ν i x) / ((q : ℝ) - jr) / w x =
        κ * ∑ i ∈ B, g i x := by
    intro B hB x
    have hcard : (B.card : ℝ) = jr := by
      rw [(mem_powersetCard.1 hB).2]
    have hcomp : ∑ i ∈ Bᶜ, ν i x = ∑ r, ν r x - ∑ i ∈ B, ν i x := by
      rw [← sum_compl_add_sum B]; ring
    have hgs : ∑ i ∈ B, g i x = (∑ i ∈ B, ν i x) / w x - jr * ((∑ r, ν r x) / w x / q) := by
      simp only [hg]
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard, ← sum_div, ← sum_div]
    rw [hcomp, hgs, hκ]
    have := (hw x).ne'
    field_simp
    ring
  have hQ : ∀ B ∈ powersetCard (m + 1) univ,
      Q B = κ ^ 2 * ∑ x, w x * (∑ i ∈ B, g i x) ^ 2 := by
    intro B hB
    simp only [hQdef]
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [hD B hB x]; ring
  have hgsum : ∀ x, ∑ i, g i x = 0 := by
    intro x
    simp only [hg]
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hsumQ : ∑ B ∈ powersetCard (m + 1) univ, Q B =
      κ ^ 2 * (n.choose m : ℝ) * V := by
    rw [sum_congr rfl hQ, ← mul_sum, sum_comm]
    simp_rw [← mul_sum]
    have hvx : ∀ x, ∑ B ∈ powersetCard (m + 1) univ, (∑ i ∈ B, g i x) ^ 2 =
        (n.choose m : ℝ) * ∑ i, g i x ^ 2 :=
      fun x => sum_powersetCard_sq (fun i => g i x) (hgsum x) n hn m
    simp_rw [hvx]
    rw [hV, sum_comm (s := univ (α := Fin q))]
    simp_rw [mul_sum]
    refine sum_congr rfl fun x _ => sum_congr rfl fun i _ => ?_
    ring
  have hQ0 : ∀ B, 0 ≤ Q B := fun B =>
    sum_nonneg fun x _ => mul_nonneg (hw x).le (sq_nonneg _)
  have hV0 : 0 ≤ V := sum_nonneg fun i _ =>
    sum_nonneg fun x _ => mul_nonneg (hw x).le (sq_nonneg _)
  -- Cauchy–Schwarz over the subsets
  have hCS : ∑ B ∈ powersetCard (m + 1) univ, √(Q B) ≤
      √(N * ∑ B ∈ powersetCard (m + 1) univ, Q B) := by
    rw [Real.le_sqrt (sum_nonneg fun B _ => Real.sqrt_nonneg _)
      (mul_nonneg hN0.le (sum_nonneg fun B _ => hQ0 B))]
    refine sq_sum_le_card_mul_sum_sq.trans (le_of_eq ?_)
    rw [card_powersetCard, card_univ, Fintype.card_fin]
    congr 1
    exact sum_congr rfl fun B _ => Real.sq_sqrt (hQ0 B)
  -- evaluate `N ∑ Q`
  have hci := choose_mul_absorb_two hn (show m ≤ n by omega)
  have hW : N * ∑ B ∈ powersetCard (m + 1) univ, Q B =
      N ^ 2 * ((q * V / (q - 1)) / (jr * (q - jr))) := by
    rw [hsumQ, hκ]
    have hc : (n.choose m : ℝ) = N * jr * (q - jr) / (q * (q - 1)) := by
      rw [eq_div_iff (by nlinarith)]
      simpa [hN, hjr, mul_assoc] using hci
    rw [hc]
    field_simp
  have hsq : √(N * ∑ B ∈ powersetCard (m + 1) univ, Q B) =
      N * (√(q * V / (q - 1)) / √(jr * (q - jr))) := by
    rw [hW, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hN0.le,
      Real.sqrt_div' _ (mul_nonneg hjr0.le hqj0.le)]
  calc ∑ B ∈ powersetCard (m + 1) univ, cost B
      ≤ ∑ B ∈ powersetCard (m + 1) univ, σ * √(Q B) :=
        sum_le_sum hcost
    _ = σ * ∑ B ∈ powersetCard (m + 1) univ, √(Q B) := by
        rw [mul_sum]
    _ ≤ σ * √(N * ∑ B ∈ powersetCard (m + 1) univ, Q B) :=
        mul_le_mul_of_nonneg_left hCS hσ
    _ = _ := by rw [hsq]; ring

/-! ### The tour -/

section Tour

variable [Fintype X] {d : X → X → ℝ} {q : ℕ} {ν g : Fin q → X → ℝ} {w : X → ℝ} {σ : ℝ}

/-- `Γ` gives couplings at level `j`: for every `j`-subset `B`, `Γ B` is a transport plan from
`ν_B / j` to `ν_{Bᶜ} / (q - j)` within the cost bound of `exists_coupling_le`. -/
def IsLevelCoupling (d : X → X → ℝ) (w : X → ℝ) (σ : ℝ) (ν : Fin q → X → ℝ)
    (Γ : Finset (Fin q) → X → X → ℝ) (j : ℕ) : Prop :=
  ∀ B ∈ powersetCard j univ, (∀ x y, 0 ≤ Γ B x y) ∧
    (∀ x, ∑ y, Γ B x y = (∑ i ∈ B, ν i x) / j) ∧
    (∀ y, ∑ x, Γ B x y = (∑ i ∈ Bᶜ, ν i y) / ((q : ℝ) - j)) ∧
    ∑ x, ∑ y, d x y * Γ B x y ≤ σ * √(∑ x, w x * ((∑ i ∈ B, ν i x) / j / w x -
      (∑ i ∈ Bᶜ, ν i x) / ((q : ℝ) - j) / w x) ^ 2)

/-- `exists_coupling_le` gives couplings at every level `0 < j < q`. -/
lemma exists_isLevelCoupling (hd0 : ∀ x, d x x = 0) (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (hw : ∀ x, 0 < w x) (hσ : 0 ≤ σ)
    (hvar : ∀ f : X → ℝ, (∀ x y, f x - f y ≤ d x y) →
      ∑ x, w x * (f x - ∑ y, w y * f y) ^ 2 ≤ σ ^ 2)
    (hν0 : ∀ i x, 0 ≤ ν i x) (hν1 : ∀ i, ∑ x, ν i x = 1) :
    ∃ Γ, ∀ j, 0 < j → j < q → IsLevelCoupling d w σ ν Γ j := by
  have hcpl : ∀ B : Finset (Fin q), ∃ Γ : X → X → ℝ, 0 < B.card → B.card < q →
      (∀ x y, 0 ≤ Γ x y) ∧ (∀ x, ∑ y, Γ x y = (∑ i ∈ B, ν i x) / B.card) ∧
      (∀ y, ∑ x, Γ x y = (∑ i ∈ Bᶜ, ν i y) / ((q : ℝ) - B.card)) ∧
      ∑ x, ∑ y, d x y * Γ x y ≤ σ * √(∑ x, w x * ((∑ i ∈ B, ν i x) / B.card / w x -
        (∑ i ∈ Bᶜ, ν i x) / ((q : ℝ) - B.card) / w x) ^ 2) := by
    intro B
    by_cases hB : 0 < B.card ∧ B.card < q
    · have hc : (Bᶜ.card : ℝ) = q - B.card := by
        have h := card_add_card_compl B
        rw [Fintype.card_fin] at h
        have h' : ((B.card + Bᶜ.card : ℕ) : ℝ) = q := by rw [h]
        push_cast at h'
        linarith
      have hpos1 : (0 : ℝ) < B.card := by exact_mod_cast hB.1
      have hpos2 : (0 : ℝ) < q - B.card := by
        have : (B.card : ℝ) < q := by exact_mod_cast hB.2
        linarith
      have hsum : ∀ C : Finset (Fin q), ∑ x, ∑ i ∈ C, ν i x = C.card := by
        intro C
        rw [sum_comm]
        simp [hν1]
      obtain ⟨Γ, h1, h2, h3, h4⟩ := exists_coupling_le d hd0 htri w hw σ hσ hvar
        (fun x => (∑ i ∈ B, ν i x) / B.card) (fun y => (∑ i ∈ Bᶜ, ν i y) / ((q : ℝ) - B.card))
        (fun x => div_nonneg (sum_nonneg fun i _ => hν0 i x) hpos1.le)
        (fun y => div_nonneg (sum_nonneg fun i _ => hν0 i y) hpos2.le)
        (by rw [← sum_div, hsum]; exact div_self hpos1.ne')
        (by rw [← sum_div, hsum, hc]; exact div_self hpos2.ne')
      exact ⟨Γ, fun _ _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hB⟩
  choose Γ hΓ using hcpl
  refine ⟨Γ, fun j hj hjq B hB => ?_⟩
  obtain rfl := (mem_powersetCard.1 hB).2
  exact hΓ B hj hjq

/-- One level of the averaged process (`lemma:step`): the normalized remaining cost at level
`j` exceeds that at level `j + 1` by at most `σ √(qV/(q-1)) / √(j(q-j)) + G/q`, where
`V = ∑_i ‖ν_i/w - mean‖²_{2,w}` and `G = ∑_i E_{ν_i} g_i`. -/
lemma levelSum_div_le (hw : ∀ x, 0 < w x) (hσ : 0 ≤ σ) (hq : 2 ≤ q) (hν0 : ∀ i x, 0 ≤ ν i x)
    {j : ℕ} (hj : 0 < j) (hjq : j < q) {Γ : Finset (Fin q) → X → X → ℝ}
    (hΓ : IsLevelCoupling d w σ ν Γ j) :
    levelSum d ν g (q - j) j / (j * q.choose j) ≤
      σ * (√(q * (∑ i, ∑ x, w x * (ν i x / w x - (∑ r, ν r x / w x) / q) ^ 2) / (q - 1)) /
          √(j * ((q : ℝ) - j))) + (∑ i, ∑ x, ν i x * g i x) / q +
        levelSum d ν g (q - (j + 1)) (j + 1) / (((j + 1 : ℕ) : ℝ) * q.choose (j + 1)) := by
  set K := √(q * (∑ i, ∑ x, w x * (ν i x / w x - (∑ r, ν r x / w x) / q) ^ 2) / (q - 1))
  set G := ∑ i, ∑ x, ν i x * g i x
  have hstep := expected_cost_step (d := d) (g := g) hν0 (q - (j + 1)) j hjq Γ
    fun B hB => ⟨(hΓ B hB).1, (hΓ B hB).2.1, (hΓ B hB).2.2.1⟩
  have hcost := expected_step_le w hw hq ν j hj hjq σ hσ
    (fun B => ∑ x, ∑ y, d x y * Γ B x y) fun B hB => (hΓ B hB).2.2.2
  rw [show q - (j + 1) + 1 = q - j by omega] at hstep
  have hq0 : (0 : ℝ) < q := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hNj : (0 : ℝ) < q.choose j := by exact_mod_cast Nat.choose_pos hjq.le
  have hqj : (0 : ℝ) < q - j := by
    have : (j : ℝ) < q := by exact_mod_cast hjq
    linarith
  have hch : ((q.choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) =
      (q.choose j : ℝ) * ((q : ℝ) - j) := by
    have h := Nat.choose_succ_right_eq q j
    have h' : ((q.choose (j + 1) * (j + 1) : ℕ) : ℝ) = ((q.choose j * (q - j) : ℕ) : ℝ) := by
      rw [h]
    push_cast [Nat.cast_sub hjq.le] at h' ⊢
    exact h'
  have hch' : ((q - 1).choose j : ℝ) * q = (q.choose j : ℝ) * ((q : ℝ) - j) := by
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    have h := Nat.choose_mul_succ_eq p j
    have h' : ((p.choose j * (p + 1) : ℕ) : ℝ) = (((p + 1).choose j * (p + 1 - j) : ℕ) : ℝ) := by
      rw [h]
    push_cast [Nat.cast_sub (show j ≤ p + 1 by omega)] at h' ⊢
    simpa using h'
  set S := ∑ B ∈ powersetCard j univ, ∑ x, ∑ y, d x y * Γ B x y
  set L' := levelSum d ν g (q - (j + 1)) (j + 1)
  have hbS : S / q.choose j ≤ σ * (K / √(j * ((q : ℝ) - j))) := by
    rw [div_le_iff₀ hNj]; linarith
  have hGq : ((q - 1).choose j : ℝ) * G / ((q : ℝ) - j) / q.choose j = G / q := by
    rw [div_div, div_eq_div_iff (by positivity) hq0.ne', mul_comm ((q : ℝ) - j), ← hch']
    ring
  calc levelSum d ν g (q - j) j / (j * q.choose j)
      = levelSum d ν g (q - j) j / j / q.choose j := by rw [div_div]
    _ ≤ (S + (L' + ((q - 1).choose j : ℝ) * G) / ((q : ℝ) - j)) / q.choose j :=
        div_le_div_of_nonneg_right hstep hNj.le
    _ = S / q.choose j + L' / (((j + 1 : ℕ) : ℝ) * q.choose (j + 1)) +
          ((q - 1).choose j : ℝ) * G / ((q : ℝ) - j) / q.choose j := by
        rw [add_div, add_div, add_div, div_div, div_div, mul_comm ((q : ℝ) - j), ← hch]
        ring
    _ ≤ _ := by rw [hGq]; linarith

/-- The expected cost of the averaged process, summed over the `q` first labels: summing
`levelSum_div_le` over the levels, with `∑_j 1/√(j(q-j)) ≤ π`. -/
lemma sum_first_selection_le (hw : ∀ x, 0 < w x) (hσ : 0 ≤ σ) (hq : 2 ≤ q)
    (hν0 : ∀ i x, 0 ≤ ν i x) {Γ : Finset (Fin q) → X → X → ℝ}
    (hΓ : ∀ j, 0 < j → j < q → IsLevelCoupling d w σ ν Γ j) :
    ∑ i, ∑ x, ν i x * (g i x + travCost d ν g (q - 1) {i} x) ≤
      q * (Real.pi * σ * √(q * (∑ i, ∑ x, w x * (ν i x / w x - (∑ r, ν r x / w x) / q) ^ 2) /
        (q - 1)) + ∑ i, ∑ x, ν i x * g i x) := by
  have hlevel := fun j (hj : 0 < j) (hjq : j < q) =>
    levelSum_div_le (g := g) hw hσ hq hν0 hj hjq (hΓ j hj hjq)
  set K := √(q * (∑ i, ∑ x, w x * (ν i x / w x - (∑ r, ν r x / w x) / q) ^ 2) / (q - 1))
  set G := ∑ i, ∑ x, ν i x * g i x with hG
  have hq0 : (0 : ℝ) < q := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  -- the normalized remaining costs `e j` and the per-level bounds `b j`
  set e : ℕ → ℝ := fun j => levelSum d ν g (q - j) j / (j * q.choose j) with he
  set b : ℕ → ℝ := fun t => σ * (K / √(t * ((q : ℝ) - t))) + G / q with hb
  have hrec : ∀ j, 0 < j → j < q → e j ≤ b j + e (j + 1) := by
    intro j hj hjq
    simp only [he, hb]
    linarith [hlevel j hj hjq]
  have htel : ∀ m, m + 1 ≤ q → e (q - m) ≤ ∑ t ∈ Ico (q - m) q, b t := by
    intro m
    induction m with
    | zero => intro _; simp [he, levelSum_zero]
    | succ m ih =>
      intro hm
      have h := hrec (q - (m + 1)) (by omega) (by omega)
      rw [show q - (m + 1) + 1 = q - m by omega] at h
      rw [sum_eq_sum_Ico_succ_bot (by omega), show q - (m + 1) + 1 = q - m by omega]
      linarith [ih (by omega)]
  have he1 : e 1 ≤ Real.pi * σ * K + (q - 1) * G / q := by
    have h := htel (q - 1) (by omega)
    rw [show q - (q - 1) = 1 by omega] at h
    have hK0 : 0 ≤ σ * K := mul_nonneg hσ (Real.sqrt_nonneg _)
    have hpi := sum_inv_sqrt_le_pi q
    calc e 1 ≤ ∑ t ∈ Ico 1 q, b t := h
      _ = σ * K * ∑ t ∈ Ico 1 q, 1 / √((t : ℝ) * ((q : ℝ) - t)) + (q - 1) * (G / q) := by
          simp only [hb, sum_add_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_sum]
          congr 1
          · refine sum_congr rfl fun t _ => ?_; ring
          · rw [Nat.cast_sub (by omega)]; simp
      _ ≤ σ * K * Real.pi + (q - 1) * (G / q) := by gcongr
      _ = Real.pi * σ * K + (q - 1) * G / q := by ring
  -- level `1` is the average over the first selection
  have hlev1 : levelSum d ν g (q - 1) 1 = ∑ i, ∑ x, ν i x * travCost d ν g (q - 1) {i} x := by
    rw [levelSum, powersetCard_one, sum_map]
    simp
  have he1' : levelSum d ν g (q - 1) 1 = q * e 1 := by
    simp only [he, Nat.choose_one_right, Nat.cast_one, one_mul]
    field_simp
  have hsplit : ∑ i, ∑ x, ν i x * (g i x + travCost d ν g (q - 1) {i} x) = G + q * e 1 := by
    rw [← he1', hlev1, hG, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun x _ => by ring
  have e2 : (q : ℝ) * ((q - 1) * G / q) = (q - 1) * G := by field_simp
  rw [hsplit]
  linarith [mul_le_mul_of_nonneg_left he1 hq0.le]

/-- Averaging over the first selection: if the `ν`-weighted total cost is at most `q T`, some
first selection `(i, x)` with `x ∈ supp ν_i` costs at most `T`. -/
lemma exists_first_selection_le (hν0 : ∀ i x, 0 ≤ ν i x) (hν1 : ∀ i, ∑ x, ν i x = 1)
    (hν : ∀ i, ∃ x, 0 < ν i x) (hq : 0 < q) {T : ℝ}
    (h : ∑ i, ∑ x, ν i x * (g i x + travCost d ν g (q - 1) {i} x) ≤ q * T) :
    ∃ i x, 0 < ν i x ∧ g i x + travCost d ν g (q - 1) {i} x ≤ T := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ i x, ν i x * T ≤ ν i x * (g i x + travCost d ν g (q - 1) {i} x) := by
    intro i x
    rcases (hν0 i x).lt_or_eq with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (hcon i x hpos).le hpos.le
    · rw [← hzero]; simp
  obtain ⟨x0, hx0⟩ := hν ⟨0, hq⟩
  have hlt : ∑ i, ∑ x, ν i x * T < ∑ i, ∑ x, ν i x * (g i x + travCost d ν g (q - 1) {i} x) :=
    sum_lt_sum (fun i _ => sum_le_sum fun x _ => hle i x)
      ⟨⟨0, hq⟩, mem_univ _, sum_lt_sum (fun x _ => hle _ x)
        ⟨x0, mem_univ _, mul_lt_mul_of_pos_left (hcon _ _ hx0) hx0⟩⟩
  have htot : ∑ i, ∑ x, ν i x * T = q * T := by
    simp [← sum_mul, hν1]
  linarith

/-- A first selection `(i, x)` followed by the optimal remaining selections gives a tour with
a point of every support, of cost at most `g i x + travCost_{q-1}({i}, x)`. -/
lemma exists_tour_of_first_selection (hν : ∀ i, ∃ x, 0 < ν i x) {i : Fin q} {x : X}
    (hx : 0 < ν i x) :
    ∃ L : List X, ∃ z : Fin q → X, L ≠ [] ∧ (∀ r, z r ∈ L ∧ 0 < ν r (z r)) ∧
      tourLength d L + ∑ r, g r (z r) ≤ g i x + travCost d ν g (q - 1) {i} x := by
  obtain ⟨L, z, hz, hL⟩ := travCost_realize (d := d) (g := g) hν (q - 1) {i}
    (by have := i.pos; simp; omega) x
  refine ⟨x :: L, Function.update z i x, List.cons_ne_nil _ _, fun r => ?_, ?_⟩
  · by_cases hr : r = i
    · subst hr
      simp only [Function.update_self]
      exact ⟨List.mem_cons_self, hx⟩
    · rw [Function.update_of_ne hr]
      obtain ⟨h1, h2⟩ := hz r (by simpa using hr)
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩
  · have hsum : ∑ r, g r (Function.update z i x r) =
        g i x + ∑ r ∈ ({i} : Finset (Fin q))ᶜ, g r (z r) := by
      rw [← add_sum_erase _ _ (mem_univ i), Function.update_self]
      congr 1
      rw [compl_singleton]
      refine sum_congr rfl fun r hr => ?_
      rw [Function.update_of_ne (ne_of_mem_erase hr)]
    rw [hsum]
    linarith

end Tour

/-- **The averaged hitting walk.** For probability vectors `ν_i` (`i : Fin q`) and endpoint
costs `g_i`, there is a tour `L` with a selection point `z_i ∈ supp ν_i` on it for every
label, such that the tour length plus the endpoint costs is at most
`π σ √(qV/(q-1)) + ∑_i E_{ν_i} g_i`, where `V = ∑_i ‖ν_i/w - mean‖²_{2,w}` and `σ²`
bounds the `w`-variance of `d`-Lipschitz functions. This is the expected cost of the
randomized algorithm, summed over its `q - 1` steps (`lemma:step`) using
`∑_j 1/√(j(q-j)) ≤ π`. -/
theorem wasserstein_walk [Fintype X] (d : X → X → ℝ) (hd0 : ∀ x, d x x = 0)
    (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (w : X → ℝ) (hw : ∀ x, 0 < w x) (σ : ℝ) (hσ : 0 ≤ σ)
    (hvar : ∀ f : X → ℝ, (∀ x y, f x - f y ≤ d x y) →
      ∑ x, w x * (f x - ∑ y, w y * f y) ^ 2 ≤ σ ^ 2)
    (q : ℕ) (hq : 2 ≤ q) (ν : Fin q → X → ℝ) (hν0 : ∀ i x, 0 ≤ ν i x)
    (hν1 : ∀ i, ∑ x, ν i x = 1) (g : Fin q → X → ℝ) :
    ∃ L : List X, ∃ z : Fin q → X, L ≠ [] ∧ (∀ i, z i ∈ L ∧ 0 < ν i (z i)) ∧
      tourLength d L + ∑ i, g i (z i) ≤
        Real.pi * σ * √(q *
          (∑ i, ∑ x, w x * (ν i x / w x - (∑ r, ν r x / w x) / q) ^ 2) / (q - 1)) +
        ∑ i, ∑ x, ν i x * g i x := by
  have hν : ∀ i, ∃ x, 0 < ν i x := fun i => by
    obtain ⟨x, -, hx⟩ := exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℝ)) (g := ν i)
      (by simp [hν1 i])
    exact ⟨x, hx⟩
  obtain ⟨Γ, hΓ⟩ := exists_isLevelCoupling hd0 htri hw hσ hvar hν0 hν1
  obtain ⟨i, x, hx, hix⟩ := exists_first_selection_le hν0 hν1 hν (by omega)
    (sum_first_selection_le (g := g) hw hσ hq hν0 hΓ)
  obtain ⟨L, z, hL, hz, hlen⟩ := exists_tour_of_first_selection (d := d) (g := g) hν hx
  exact ⟨L, z, hL, hz, hlen.trans hix⟩

/-! ### Tours through large sets -/

/-- **Tours for spread-out measures.** Let `σ²` bound the average squared deviation of
`d`-Lipschitz functions, and let `ν_1, …, ν_q` (`q ≥ 2`) be probability vectors with
`|X| ∑_x ν_i(x)² ≤ κ` (for the uniform measure on a set, `κ` is `|X|` over its size). Then
some tour has a point `z_i` of the support of each `ν_i`, with
`tourLength + ∑ g_i(z_i) ≤ π σ √(q²(κ-1)/(q-1)) + ∑_i E_{ν_i} g_i`. -/
theorem wasserstein_walk_measures [Fintype X] (d : X → X → ℝ) (hd0 : ∀ x, d x x = 0)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) (σ : ℝ) (hσ : 0 ≤ σ)
    (hvar : ∀ f : X → ℝ, (∀ x y, f x - f y ≤ d x y) →
      ∑ x, (f x - (∑ y, f y) / Fintype.card X) ^ 2 ≤ Fintype.card X * σ ^ 2)
    (q : ℕ) (hq : 2 ≤ q) (ν : Fin q → X → ℝ) (hν0 : ∀ i x, 0 ≤ ν i x)
    (hν1 : ∀ i, ∑ x, ν i x = 1) (κ : ℝ)
    (hκ : ∀ i, (Fintype.card X : ℝ) * ∑ x, ν i x ^ 2 ≤ κ) (g : Fin q → X → ℝ) :
    ∃ L : List X, ∃ z : Fin q → X, L ≠ [] ∧ (∀ i, z i ∈ L ∧ 0 < ν i (z i)) ∧
      tourLength d L + ∑ i, g i (z i) ≤
        Real.pi * σ * √(q ^ 2 * (κ - 1) / (q - 1)) + ∑ i, ∑ x, ν i x * g i x := by
  set N : ℝ := (Fintype.card X : ℝ) with hN
  have hNpos : 0 < N := by
    rcases isEmpty_or_nonempty X with hX | hX
    · have := hν1 ⟨0, by omega⟩
      simp at this
    · simp only [hN]; exact_mod_cast Fintype.card_pos
  have hN0 : N ≠ 0 := hNpos.ne'
  set w : X → ℝ := fun _ => 1 / N
  have hvar' : ∀ f : X → ℝ, (∀ x y, f x - f y ≤ d x y) →
      ∑ x, w x * (f x - ∑ y, w y * f y) ^ 2 ≤ σ ^ 2 := by
    intro f hf
    have h := hvar f hf
    have hmean : ∑ y, w y * f y = (∑ y, f y) / N := by
      simp only [w, ← mul_sum]; ring
    rw [hmean, ← mul_sum, one_div_mul_eq_div, div_le_iff₀ hNpos]
    linarith
  obtain ⟨L, z, hL, hz, hlen⟩ := wasserstein_walk d hd0 htri w (fun _ => by positivity) σ hσ
    hvar' q hq ν hν0 hν1 g
  refine ⟨L, z, hL, hz, hlen.trans ?_⟩
  -- the variance term: `V ≤ ∑_i N ‖ν_i‖² - q ≤ q(κ - 1)`
  set V := ∑ i, ∑ x, w x * (ν i x / w x - (∑ r, ν r x / w x) / q) ^ 2
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  have hnorm : ∀ i, ∑ x, w x * (ν i x / w x) ^ 2 = N * ∑ x, ν i x ^ 2 := by
    intro i
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    simp only [w]
    field_simp
  have hmean : ∀ x, ∑ i, w x * (ν i x / w x - (∑ r, ν r x / w x) / q) ^ 2 =
      ∑ i, w x * (ν i x / w x) ^ 2 - w x * (∑ r, ν r x / w x) ^ 2 / q := by
    intro x
    have e : ∀ i, w x * (ν i x / w x - (∑ r, ν r x / w x) / q) ^ 2 =
        w x * (ν i x / w x) ^ 2 - 2 * w x * (∑ r, ν r x / w x) / q * (ν i x / w x) +
          w x * ((∑ r, ν r x / w x) / q) ^ 2 := fun i => by ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hcs : (q : ℝ) ≤ ∑ x, w x * (∑ r, ν r x / w x) ^ 2 / q := by
    have hsum1 : ∑ x, w x * (∑ r, ν r x / w x) = q := by
      have : ∀ x, w x * (∑ r, ν r x / w x) = ∑ r, ν r x := fun x => by
        rw [mul_sum]
        exact sum_congr rfl fun r _ => by simp only [w]; field_simp
      simp only [this]
      rw [sum_comm]
      simp [hν1]
    have hw1 : ∑ x, w x = 1 := by
      simp only [w, sum_const, card_univ, nsmul_eq_mul, ← hN]
      field_simp
    have hj : (∑ x, w x * (∑ r, ν r x / w x)) ^ 2 ≤
        (∑ x, w x) * ∑ x, w x * (∑ r, ν r x / w x) ^ 2 := by
      have := sum_mul_sq_le_sq_mul_sq univ (fun x => √(w x))
        (fun x => √(w x) * (∑ r, ν r x / w x))
      have hs : ∀ x, √(w x) ^ 2 = w x := fun x =>
        Real.sq_sqrt (by simp only [w]; positivity)
      simp only [mul_pow, hs, ← mul_assoc, ← sq] at this
      convert this using 2
    rw [hsum1, hw1, one_mul] at hj
    rw [← sum_div, le_div_iff₀ hq0]
    nlinarith
  have hVle : V ≤ q * (κ - 1) := by
    have h1 : V = ∑ x, ∑ i, w x * (ν i x / w x - (∑ r, ν r x / w x) / q) ^ 2 := sum_comm
    rw [h1, sum_congr rfl fun x _ => hmean x, sum_sub_distrib, sum_comm,
      sum_congr rfl fun i _ => hnorm i]
    have h2 : ∑ i, N * ∑ x, ν i x ^ 2 ≤ q * κ := by
      calc ∑ i, N * ∑ x, ν i x ^ 2 ≤ ∑ _i : Fin q, κ := sum_le_sum fun i _ => hκ i
        _ = q * κ := by simp
    linarith
  have hV0 : 0 ≤ V := sum_nonneg fun i _ =>
    sum_nonneg fun x _ => mul_nonneg (by simp only [w]; positivity) (sq_nonneg _)
  have hsq : √(q * V / (q - 1)) ≤ √(q ^ 2 * (κ - 1) / (q - 1)) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hq1.le
    nlinarith
  gcongr

/-- **Tours through large sets.** Let `σ²` bound the average squared deviation of
`d`-Lipschitz functions, and let `T_1, …, T_q` (`q ≥ 2`) be sets of size at least `|X|/κ`.
Then some tour meets every `T_i` at a point `z_i`, with
`tourLength + ∑ g_i(z_i) ≤ π σ √(q²(κ-1)/(q-1)) + ∑_i avg_{T_i} g_i`. -/
theorem wasserstein_walk_sets [Fintype X] [DecidableEq X] (d : X → X → ℝ) (hd0 : ∀ x, d x x = 0)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) (σ : ℝ) (hσ : 0 ≤ σ)
    (hvar : ∀ f : X → ℝ, (∀ x y, f x - f y ≤ d x y) →
      ∑ x, (f x - (∑ y, f y) / Fintype.card X) ^ 2 ≤ Fintype.card X * σ ^ 2)
    (q : ℕ) (hq : 2 ≤ q) (T : Fin q → Finset X) (κ : ℝ)
    (hTne : ∀ i, (T i).Nonempty) (hT : ∀ i, (Fintype.card X : ℝ) ≤ κ * (T i).card)
    (g : Fin q → X → ℝ) :
    ∃ L : List X, ∃ z : Fin q → X, L ≠ [] ∧ (∀ i, z i ∈ L ∧ z i ∈ T i) ∧
      tourLength d L + ∑ i, g i (z i) ≤
        Real.pi * σ * √(q ^ 2 * (κ - 1) / (q - 1)) +
          ∑ i, (∑ x ∈ T i, g i x) / (T i).card := by
  have hcard : ∀ i, (0 : ℝ) < (T i).card := fun i => by exact_mod_cast (hTne i).card_pos
  set ν : Fin q → X → ℝ := fun i x => if x ∈ T i then 1 / (T i).card else 0 with hν
  have hν0 : ∀ i x, 0 ≤ ν i x := fun i x => by simp only [hν]; split_ifs <;> positivity
  have hν1 : ∀ i, ∑ x, ν i x = 1 := by
    intro i
    simp only [hν, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
    field_simp [(hcard i).ne']
  have hκ : ∀ i, (Fintype.card X : ℝ) * ∑ x, ν i x ^ 2 ≤ κ := by
    intro i
    have : ∑ x, ν i x ^ 2 = 1 / (T i).card := by
      have e : ∀ x, ν i x ^ 2 = if x ∈ T i then 1 / ((T i).card : ℝ) ^ 2 else 0 := by
        intro x; simp only [hν]; split_ifs <;> simp
      rw [sum_congr rfl fun x _ => e x, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
      field_simp [(hcard i).ne']
    rw [this, mul_one_div, div_le_iff₀ (hcard i)]
    exact hT i
  obtain ⟨L, z, hL, hz, hlen⟩ := wasserstein_walk_measures d hd0 htri σ hσ hvar q hq ν hν0 hν1
    κ hκ g
  refine ⟨L, z, hL, fun i => ⟨(hz i).1, ?_⟩, hlen.trans (le_of_eq ?_)⟩
  · have := (hz i).2
    simp only [hν] at this
    split_ifs at this with h
    · exact h
    · exact absurd this (lt_irrefl 0)
  · congr 1
    refine sum_congr rfl fun i _ => ?_
    simp only [hν, ite_mul, zero_mul, sum_ite_mem, univ_inter, ← mul_sum]
    ring

end MinorFreeSeparators
