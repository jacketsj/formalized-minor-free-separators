import proof.Hitting.Traversal

/-!
# Short hitting walks on expanders (`thm:hitting`, `cor:connector`)

`short_hitting_walk_sharp` is `thm:hitting` with the constant `π √((1 + ψ)(2 + ψ))`, which is less
than `11` (`short_hitting_walk_of_expander`; the paper states `13`). `short_tree_sharp` is
`cor:connector` with the same constant.

`short_hitting_walk` and `short_tree` are the paper's `thm:hitting` and `cor:connector`. The main
theorem does not use them: it uses the variant `extended_short_tree` (in
`proof/Separator/Connector.lean`).
-/

namespace MinorFreeSeparators

open Finset

variable {V : Type*} {G : SimpleGraph V}

/-- The graph distance as a real-valued function. -/
noncomputable abbrev gdist (G : SimpleGraph V) (u v : V) : ℝ := G.dist u v

/-- Concatenating shortest paths along a list gives a walk through the list whose length is
the tour length. -/
lemma exists_walk_of_tour (hG : G.Connected) (x : V) (L : List V) :
    ∃ y, ∃ W : G.Walk x y, (W.length : ℝ) = tourLength (gdist G) (x :: L) ∧
      ∀ z ∈ x :: L, z ∈ W.support := by
  induction L generalizing x with
  | nil => exact ⟨x, .nil, by simp [tourLength], by simp⟩
  | cons z L ih =>
    obtain ⟨y, W, hW, hWL⟩ := ih z
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x z
    refine ⟨y, p.append W, ?_, fun t ht => ?_⟩
    · rw [SimpleGraph.Walk.length_append, tourLength, ← hW]
      push_cast [hp]
      rfl
    · rw [SimpleGraph.Walk.mem_support_append_iff]
      rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inl p.start_mem_support
      · exact Or.inr (hWL t ht)

/-- A `ψ`-vertex expander on at least two vertices has `ψ ≤ 2`. -/
lemma IsVertexExpander.le_two [Fintype V] {ψ : ℝ} (hexp : IsVertexExpander G ψ)
    (hn : 2 ≤ Fintype.card V) : ψ ≤ 2 := by
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset V))
    (n := Fintype.card V / 2) (by simp; omega)
  have h1 := hexp S (by rw [Set.ncard_coe_finset, hS]; omega)
  rw [Set.ncard_coe_finset, hS] at h1
  have h2 : (vertexBoundary G (S : Set V)).ncard ≤ Fintype.card V - Fintype.card V / 2 := by
    have hsub : vertexBoundary G (S : Set V) ⊆ (S : Set V)ᶜ := fun v hv => hv.1
    have := Set.ncard_le_ncard hsub
    rw [Set.ncard_compl, Set.ncard_coe_finset, hS, Nat.card_eq_fintype_card] at this
    exact this
  have hpos : (0 : ℝ) < (Fintype.card V / 2 : ℕ) := by exact_mod_cast Nat.div_pos hn two_pos
  have h3 : ((Fintype.card V - Fintype.card V / 2 : ℕ) : ℝ) ≤ 2 * (Fintype.card V / 2 : ℕ) := by
    exact_mod_cast (show Fintype.card V - Fintype.card V / 2 ≤ 2 * (Fintype.card V / 2) by omega)
  have h4 : ψ * (Fintype.card V / 2 : ℕ) ≤ 2 * (Fintype.card V / 2 : ℕ) :=
    h1.trans ((Nat.cast_le.mpr h2).trans h3)
  exact le_of_mul_le_mul_right h4 hpos

/-- In a nonempty type, a set `X` with `n ≤ h |X|` is nonempty. -/
private lemma nonempty_of_card_le_mul [Fintype V] [Nonempty V] {h : ℕ} {X : Set V}
    (hX : Fintype.card V ≤ h * X.ncard) : X.Nonempty :=
  Set.nonempty_of_ncard_ne_zero fun h0 => by
    rw [h0, mul_zero] at hX
    exact (Fintype.card_pos.trans_le hX).false

/-- The hitting walk for `2 ≤ k ≤ h` sets of size at least `n / h`: `wasserstein_walk_sets`
with `σ = √((1 + ψ)(2 + ψ)) / ψ` from `poincare`. -/
private lemma exists_hitting_walk [Fintype V] (hG : G.Connected) {ψ : ℝ} (hψ : 0 < ψ)
    (hexp : IsVertexExpander G ψ) {h k : ℕ} (hk : 2 ≤ k) (hkh : k ≤ h) (X : Fin k → Set V)
    (hX : ∀ i, Fintype.card V ≤ h * (X i).ncard) :
    ∃ u v, ∃ W : G.Walk u v, (W.length : ℝ) ≤ Real.pi * h * √((1 + ψ) * (2 + ψ)) / ψ ∧
      ∀ i, ∃ x ∈ X i, x ∈ W.support := by
  classical
  have := hG.nonempty
  set σ := √((1 + ψ) * (2 + ψ)) / ψ
  have hσ : 0 ≤ σ := by positivity
  have hσ2 : σ ^ 2 = (1 + ψ) * (2 + ψ) / ψ ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
  obtain ⟨L, z, hL, hz, hlen⟩ := wasserstein_walk_sets (gdist G) (fun x => by simp)
    (fun x y z => dist_triangle_real hG x y z) σ hσ
    (fun f hf => hσ2 ▸ poincare hG hψ hexp f hf) k hk (fun i => (X i).toFinset) h
    (fun i => by simpa using nonempty_of_card_le_mul (hX i))
    (fun i => by have := hX i; rw [Set.ncard_eq_toFinset_card'] at this; exact_mod_cast this)
    (fun _ _ => 0)
  obtain ⟨x, L', rfl⟩ := List.exists_cons_of_ne_nil hL
  obtain ⟨y, W, hW, hWL⟩ := exists_walk_of_tour hG x L'
  refine ⟨x, y, W, ?_, fun i => ⟨z i, by simpa using (hz i).2, hWL _ (hz i).1⟩⟩
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkh' : (k : ℝ) ≤ h := by exact_mod_cast hkh
  have hsq : √((k : ℝ) ^ 2 * (h - 1) / (k - 1)) ≤ h := by
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by linarith)]
    have h1 : (0 : ℝ) ≤ (h - 1) * (k - 1) - 1 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hkh') h1]
  simp only [zero_div, sum_const_zero, add_zero] at hlen
  rw [hW]
  calc tourLength (gdist G) (x :: L') ≤ Real.pi * σ * h :=
        hlen.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
    _ = Real.pi * h * √((1 + ψ) * (2 + ψ)) / ψ := by simp only [σ]; ring

/-- `π √((1 + ψ)(2 + ψ)) < 11` for `0 < ψ ≤ 2`. -/
private lemma pi_mul_sqrt_lt_eleven {ψ : ℝ} (hψ : 0 < ψ) (hψ2 : ψ ≤ 2) :
    Real.pi * √((1 + ψ) * (2 + ψ)) < 11 := by
  have hs : √((1 + ψ) * (2 + ψ)) ≤ √12 := Real.sqrt_le_sqrt (by nlinarith)
  have h12 : √12 < 3.4642 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h0 : 0 ≤ √((1 + ψ) * (2 + ψ)) := Real.sqrt_nonneg _
  nlinarith [Real.pi_pos, Real.pi_lt_d4]

/-- **Short hitting walk** (`thm:hitting`, sharp form, for any `ψ`-vertex expander). Let `G`
be a connected `ψ`-vertex expander on `n` vertices, and `X_1, …, X_k` (`k ≥ 1`) vertex sets
of size at least `n/k`. Then some walk of length at most `π k √((1 + ψ)(2 + ψ)) / ψ` meets
every `X_i`. -/
theorem short_hitting_walk_sharp [Fintype V] (hG : G.Connected) {ψ : ℝ} (hψ : 0 < ψ)
    (hexp : IsVertexExpander G ψ) {k : ℕ} (hk : 1 ≤ k) (X : Fin k → Set V)
    (hX : ∀ i, Fintype.card V ≤ k * (X i).ncard) :
    ∃ u v, ∃ W : G.Walk u v, (W.length : ℝ) ≤ Real.pi * k * √((1 + ψ) * (2 + ψ)) / ψ ∧
      ∀ i, ∃ x ∈ X i, x ∈ W.support := by
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · -- one set: a trivial walk
    have := hG.nonempty
    obtain ⟨x, hx⟩ := nonempty_of_card_le_mul (hX ⟨0, by omega⟩)
    refine ⟨x, x, .nil, ?_, fun i => ⟨x, ?_, by simp⟩⟩
    · rw [SimpleGraph.Walk.length_nil, Nat.cast_zero]
      positivity
    · have : i = ⟨0, by omega⟩ := Fin.ext (by omega)
      exact this ▸ hx
  exact exists_hitting_walk hG hψ hexp hk2 le_rfl X hX

/-- **Short hitting walk** (`thm:hitting` for any `ψ`-vertex expander). Let `G` be a
connected `ψ`-vertex expander on `n` vertices, and `X_1, …, X_k` (`k ≥ 1`) vertex sets of size
at least `n/k`. Then some walk of length less than `11 k / ψ` meets every `X_i`. -/
theorem short_hitting_walk_of_expander [Fintype V] (hG : G.Connected) {ψ : ℝ} (hψ : 0 < ψ)
    (hexp : IsVertexExpander G ψ) {k : ℕ} (hk : 1 ≤ k) (X : Fin k → Set V)
    (hX : ∀ i, Fintype.card V ≤ k * (X i).ncard) :
    ∃ u v, ∃ W : G.Walk u v, (W.length : ℝ) < 11 * k / ψ ∧ ∀ i, ∃ x ∈ X i, x ∈ W.support := by
  obtain ⟨u, v, W, hW, hWX⟩ := short_hitting_walk_sharp hG hψ hexp hk X hX
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rcases Nat.lt_or_ge (Fintype.card V) 2 with hn | hn
  · -- at most one vertex: there are no edges, so `W` has length `0`
    refine ⟨u, v, W, ?_, hWX⟩
    have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have h0 : W.length = 0 := by
      cases W with
      | nil => rfl
      | cons h _ => exact absurd (Subsingleton.elim _ _) (G.ne_of_adj h)
    rw [h0, Nat.cast_zero]
    positivity
  refine ⟨u, v, W, hW.trans_lt ?_, hWX⟩
  have := pi_mul_sqrt_lt_eleven hψ (hexp.le_two hn)
  rw [div_lt_div_iff_of_pos_right hψ]
  nlinarith

/-- **Short Hitting Walk on Expanders** (`thm:hitting`). Let `G` be a connected graph on
`n ≥ 2` vertices and let `X_1, …, X_k` (`k ≥ 1`) be vertex sets, each of size at least
`n/k`. Then `G` has a walk of length less than `11 k / ψ(G)` that meets every `X_i`. -/
theorem short_hitting_walk [Fintype V] (hG : G.Connected) (hn : 2 ≤ Fintype.card V) {k : ℕ}
    (hk : 1 ≤ k) (X : Fin k → Set V) (hX : ∀ i, Fintype.card V ≤ k * (X i).ncard) :
    ∃ u v, ∃ W : G.Walk u v, (W.length : ℝ) < 11 * k / vertexExpansion G ∧
      ∀ i, ∃ x ∈ X i, x ∈ W.support :=
  short_hitting_walk_of_expander hG (vertexExpansion_pos hG hn) isVertexExpander_vertexExpansion
    hk X hX

/-- The vertex set of a walk has at most `length + 1` vertices. -/
lemma walk_support_ncard_le {u v : V} (W : G.Walk u v) :
    {x | x ∈ W.support}.ncard ≤ W.length + 1 := by
  classical
  rw [show {x | x ∈ W.support} = (W.support.toFinset : Set V) by ext; simp,
    Set.ncard_coe_finset, ← SimpleGraph.Walk.length_support]
  exact List.toFinset_card_le _

/-- A vertex expander with `ψ > 0` is connected. -/
lemma IsVertexExpander.connected [Fintype V] [Nonempty V] {ψ : ℝ} (hψ : 0 < ψ)
    (hexp : IsVertexExpander G ψ) : G.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  obtain ⟨v⟩ := ‹Nonempty V›
  refine ⟨v, fun w => ?_⟩
  by_contra hvw
  set C : Set V := {x | G.Reachable v x}
  have hbdry : ∀ S : Set V, (S = C ∨ S = Cᶜ) → vertexBoundary G S = ∅ := by
    rintro S hS
    ext x
    simp only [vertexBoundary, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
      not_exists]
    intro hx y hy hyx
    rcases hS with rfl | rfl
    · exact hx (show G.Reachable v x from hy.trans hyx.reachable)
    · exact hy (show G.Reachable v y from (show G.Reachable v x from by
        by_contra h; exact hx h).trans hyx.symm.reachable)
  have hsum : C.ncard + Cᶜ.ncard = Fintype.card V := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  have hCne : C.Nonempty := ⟨v, SimpleGraph.Reachable.refl v⟩
  have hCcne : Cᶜ.Nonempty := ⟨w, hvw⟩
  rcases le_total (2 * C.ncard) (Fintype.card V) with h | h
  · have := hexp C h
    rw [hbdry C (Or.inl rfl), Set.ncard_empty, Nat.cast_zero] at this
    have hpos : (0 : ℝ) < C.ncard := by exact_mod_cast hCne.ncard_pos
    nlinarith
  · have := hexp Cᶜ (by omega)
    rw [hbdry Cᶜ (Or.inr rfl), Set.ncard_empty, Nat.cast_zero] at this
    have hpos : (0 : ℝ) < Cᶜ.ncard := by exact_mod_cast hCcne.ncard_pos
    nlinarith

/-- **ShortTree** (`cor:connector`, sharp form). If `G` is a `ψ`-vertex expander
(`ψ > 0`) and `X_1, …, X_k` with `k ≤ h` are vertex sets of size at least `|V(G)|/h`, then
some connected vertex set `T` (the vertices of a tree in `G`) meets every `X_i` and has at
most `π h √((1 + ψ)(2 + ψ)) / ψ + 1` vertices. -/
theorem short_tree_sharp [Fintype V] [Nonempty V] {ψ : ℝ} (hψ : 0 < ψ)
    (hexp : IsVertexExpander G ψ) {h k : ℕ} (hkh : k ≤ h) (X : Fin k → Set V)
    (hX : ∀ i, Fintype.card V ≤ h * (X i).ncard) :
    ∃ T : Set V, (G.induce T).Connected ∧ (∀ i, (T ∩ X i).Nonempty) ∧
      (T.ncard : ℝ) ≤ Real.pi * h * √((1 + ψ) * (2 + ψ)) / ψ + 1 := by
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · -- at most one set: a single vertex
    obtain ⟨x, hx⟩ : ∃ x : V, ∀ i, x ∈ X i := by
      rcases Nat.lt_succ_iff.mp hk1 |>.lt_or_eq with hk0 | rfl
      · obtain ⟨x⟩ := ‹Nonempty V›
        exact ⟨x, fun i => absurd i.isLt (by omega)⟩
      · obtain ⟨x, hx⟩ := nonempty_of_card_le_mul (hX 0)
        exact ⟨x, fun i => by rwa [Fin.fin_one_eq_zero i]⟩
    refine ⟨{x}, by simp, fun i => ⟨x, rfl, hx i⟩, ?_⟩
    rw [Set.ncard_singleton, Nat.cast_one, le_add_iff_nonneg_left]
    positivity
  obtain ⟨u, v, W, hW, hWX⟩ := exists_hitting_walk (hexp.connected hψ) hψ hexp hk2 hkh X hX
  refine ⟨{x | x ∈ W.support}, W.connected_induce_support, fun i => ?_, ?_⟩
  · obtain ⟨x, hxX, hxW⟩ := hWX i
    exact ⟨x, hxW, hxX⟩
  · have := walk_support_ncard_le W
    calc ({x | x ∈ W.support}.ncard : ℝ) ≤ W.length + 1 := by exact_mod_cast this
      _ ≤ _ := by linarith

/-- **ShortTree** (`cor:connector`). If `G` is a `ψ`-vertex expander on at least two vertices
and `X_1, …, X_k` with `k ≤ h` are vertex sets of size at least `|V(G)|/h`, then some connected
vertex set (the vertices of a tree in `G`) meets every `X_i` and has fewer than `13 h / ψ`
vertices. -/
theorem short_tree [Fintype V] {ψ : ℝ} (hψ : 0 < ψ) (hexp : IsVertexExpander G ψ)
    (hn : 2 ≤ Fintype.card V) {h k : ℕ} (hh : 1 ≤ h) (hkh : k ≤ h) (X : Fin k → Set V)
    (hX : ∀ i, Fintype.card V ≤ h * (X i).ncard) :
    ∃ T : Set V, (G.induce T).Connected ∧ (∀ i, (T ∩ X i).Nonempty) ∧
      (T.ncard : ℝ) < 13 * h / ψ := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨T, hT, hTX, hcard⟩ := short_tree_sharp hψ hexp hkh X hX
  refine ⟨T, hT, hTX, hcard.trans_lt ?_⟩
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hψ2 := hexp.le_two hn
  have := pi_mul_sqrt_lt_eleven hψ hψ2
  -- `π h √((1 + ψ)(2 + ψ)) < 11 h` and `ψ ≤ 2 h`
  rw [div_add_one hψ.ne', div_lt_div_iff_of_pos_right hψ]
  nlinarith

end MinorFreeSeparators
