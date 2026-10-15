import proof.Separator.Config

/-!
# The minimal configuration

Assume `G` is `K_h`-minor-free and has no balanced separator with at most `K` vertices.
A configuration whose region is smallest admits none of the three moves. Hence its region
is a truncated expander at scale `ℓ` with slack `L` (Case 1 fails), the balls around each
attachment set grow by at least `β` per layer (Case 2 fails, cf. `clm:n/h-size`), and no
connector with at most `a` vertices exists (Case 3 fails). But the hitting walk produces
such a connector, so no configuration exists. Since the trivial configuration exists, `G`
has a balanced separator with at most `K` vertices (`separator_of_params`).

The cost of the cuts is controlled by `heavy_margin`: deleting `X`, the cuts `F_C`, and
any `|H| - ⌊n/2⌋` vertices of the region would already be a balanced separator, so the
region stays heavy by a margin, which bounds `X` (`discarded_lt`).

The parameters and the inequalities they must satisfy are collected in `SepParams`.
-/

namespace MinorFreeSeparators

open Finset

/-- Parameters of the separator argument for a graph with `n` vertices and no `K_h` minor:
the expansion scale `ℓ` with slack `L`, the tent size `S`, the ball growth `β` (so the
attachment bound is `b = β - 1`), the mean path cost `E` of a tent measure, the connector
size `a`, and the separator size `K`. `path` bounds `E` from the growth alone or from the
growth and the expansion. `budget_expand` covers Case 1 and `budget_branch` Cases 2 and 3. -/
structure SepParams (n h : ℕ) where
  ℓ : ℝ
  L : ℝ
  S : ℕ
  β : ℕ
  a : ℝ
  E : ℝ
  K : ℝ
  ℓ_pos : 0 < ℓ
  L_nonneg : 0 ≤ L
  one_le_S : 1 ≤ S
  one_le_β : 1 ≤ β
  one_le_a : 1 ≤ a
  two_S_le : 2 * S ≤ n
  path : ((S - 1) * (2 * S - 1) / 6 + β * (S - 1) / 2 + β ^ 2 / 4) / (β * (S + 1)) ≤ E ∨
    (4 * S ≤ n + 1 ∧ 1 ≤ β * ℓ ∧ β * (ℓ + 1) ≤ S ∧
      β * (ℓ + 1) ≤ (ℓ + 1 / 2) * ((n + 1) / (4 * (L + ℓ + 1))) ∧
      expPath S β ℓ ((n + 1) / (4 * (L + ℓ + 1))) ≤ E)
  connector : 4 ≤ h → 1 + Real.pi * Real.sqrt (truncVar ℓ L) *
    Real.sqrt (h * (n * (2 * (2 * S + 1) / (3 * S * (S + 1))) - 1)) + (h - 2) * E ≤ a
  budget_expand : (h - 2) * max a (β - 1) +
    ((2 * L + 3 * ℓ + 1) * n + 2 * L + ℓ + 1) / (2 * (ℓ + 1) * (2 * L + 2 * ℓ + 1)) ≤ K
  budget_branch : (h - 2) * max a (β - 1) + (n + 1 + 2 * ℓ * max a (β - 1)) / (2 * (ℓ + 1)) ≤ K

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {h : ℕ} (P : SepParams (Fintype.card V) h)

namespace SepParams

lemma max_pos : 0 < max P.a (P.β - 1) := lt_of_lt_of_le (by linarith [P.one_le_a]) (le_max_left _ _)

end SepParams

section Minimal

variable (hG : ¬HasCliqueMinor G h)
  (hsep : ∀ Z : Set V, (Z.ncard : ℝ) ≤ P.K → ∃ Q, IsPiece G Zᶜ Q ∧ Fintype.card V < 2 * Q.ncard)
  (D : Config G P.ℓ P.a (P.β - 1))
  (hmin : ∀ E : Config G P.ℓ P.a (P.β - 1), D.region.ncard ≤ E.region.ncard)
  (htouch : ∀ C ∈ D.branches, (relBoundary G D.region C).Nonempty)

include hmin in
/-- A move to a configuration on a proper subset of the region is impossible. -/
lemma region_not_shrink {H : Set V} (hH : H ⊆ D.region) {x : V} (hx : x ∈ D.region)
    (hxH : x ∉ H) (E : Config G P.ℓ P.a (P.β - 1)) (hE : E.region = H) : False := by
  have h1 := hmin E
  rw [hE] at h1
  have h2 := Set.ncard_lt_ncard (Set.ssubset_iff_of_subset hH |>.mpr ⟨x, hx, hxH⟩)
  omega

include hsep in
/-- The region stays heavy by a margin: deleting `X`, the cuts `F_C`, and any
`|H| - ⌊n/2⌋` vertices of the region would give a balanced separator. -/
lemma heavy_margin : P.K < D.discarded.ncard + D.branches.card * max P.a (P.β - 1) +
    (D.region.ncard - ((Fintype.card V : ℝ) - 1) / 2) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨Y, hYR, hYcard⟩ := Set.exists_subset_card_eq (s := D.region)
    (show D.region.ncard - Fintype.card V / 2 ≤ D.region.ncard by omega)
  obtain ⟨H', hH', -, hhH', -⟩ := D.robust hsep Y (by
    have h1 : ((D.region.ncard - Fintype.card V / 2 : ℕ) : ℝ) ≤
        D.region.ncard - ((Fintype.card V : ℝ) - 1) / 2 := by
      have hle : Fintype.card V / 2 ≤ D.region.ncard := by have := D.heavy; omega
      rw [Nat.cast_sub hle]
      have : ((Fintype.card V : ℝ) - 1) / 2 ≤ ((Fintype.card V / 2 : ℕ) : ℝ) := by
        have := Nat.div_add_mod (Fintype.card V) 2
        have hm := Nat.mod_lt (Fintype.card V) two_pos
        have : ((Fintype.card V : ℕ) : ℝ) ≤ 2 * ((Fintype.card V / 2 : ℕ) : ℝ) + 1 := by
          exact_mod_cast (show Fintype.card V ≤ 2 * (Fintype.card V / 2) + 1 by omega)
        linarith
      linarith
    rw [hYcard]
    linarith)
  have hsub : H' ⊆ D.region \ Y := hH'
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_diff hYR (Set.toFinite _), hYcard] at h1
  omega

include hsep in
/-- `X` is small: `ℓ |X| < (n + 1)/2 - K + |𝒦| max(a, b)`. -/
lemma discarded_lt : P.ℓ * D.discarded.ncard <
    ((Fintype.card V : ℝ) + 1) / 2 - P.K + D.branches.card * max P.a (P.β - 1) := by
  have h1 := heavy_margin P hsep D
  have h2 := D.discarded_le (by linarith [P.ℓ_pos])
  have hℓ := P.ℓ_pos
  rw [le_div_iff₀ (by linarith)] at h2
  linarith

lemma card_mul_le (hG : ¬HasCliqueMinor G h)
    (htouch : ∀ C ∈ D.branches, (relBoundary G D.region C).Nonempty) :
    (D.branches.card : ℝ) * max P.a (P.β - 1) ≤ (h - 2) * max P.a (P.β - 1) := by
  have h2 : (D.branches.card : ℝ) ≤ h - 2 := by
    have := D.card_le hG htouch
    have : ((D.branches.card + 2 : ℕ) : ℝ) ≤ h := by exact_mod_cast this
    push_cast at this
    linarith
  exact mul_le_mul_of_nonneg_right h2 P.max_pos.le

include hG hsep htouch in
/-- Robustness in the minimal configuration, for a set `Y` with `|Y| ≤ max(a, b)`. -/
lemma robust_small (Y : Set V) (hY : (Y.ncard : ℝ) ≤ max P.a (P.β - 1)) :
    ∃ H', H' ⊆ D.region \ Y ∧ (G.induce H').Connected ∧ Fintype.card V < 2 * H'.ncard ∧
      ∀ u ∈ H', ∀ v ∈ D.region, G.Adj u v → v ∉ H' → v ∈ Y := by
  refine D.robust hsep Y ?_
  have hP := discarded_lt P hsep D
  have hQ := card_mul_le P D hG htouch
  have hB := P.budget_branch
  have hℓ := P.ℓ_pos
  set M := max P.a (P.β - 1)
  set Q := (D.branches.card : ℝ) * M
  set X := (D.discarded.ncard : ℝ)
  -- `ℓ (X + Q + M) < (n + 1)/2 - K + (ℓ + 1) Q + ℓ M ≤ ℓ K`
  have hB' : (Fintype.card V + 1 + 2 * P.ℓ * M : ℝ) ≤ 2 * (P.ℓ + 1) * (P.K - Q) := by
    have := (div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (P.ℓ + 1))).mp
      (by linarith : (Fintype.card V + 1 + 2 * P.ℓ * M : ℝ) / (2 * (P.ℓ + 1)) ≤ P.K - Q)
    linarith
  have hlt : P.ℓ * (X + Q + M) < P.ℓ * P.K := by nlinarith
  have := lt_of_mul_lt_mul_left hlt (by linarith)
  linarith

include hG hsep htouch in
/-- The cost of a Case 1 cut `Y` with `2(ℓ + 1 + L)|Y| < |H|` fits in the budget. -/
lemma cut_budget (Y : Set V) (hY : 2 * (P.ℓ + 1 + P.L) * Y.ncard < D.region.ncard) :
    (D.discarded.ncard : ℝ) + D.branches.card * max P.a (P.β - 1) + Y.ncard ≤ P.K := by
  have hℓ := P.ℓ_pos
  have hL := P.L_nonneg
  have hP := discarded_lt P hsep D
  have hQ := card_mul_le P D hG htouch
  have hBe := P.budget_expand
  have h2 := D.discarded_le (by linarith : (0 : ℝ) ≤ P.ℓ)
  rw [le_div_iff₀ (by linarith)] at h2
  set M := max P.a (P.β - 1)
  set Q := (D.branches.card : ℝ) * M
  set X := (D.discarded.ncard : ℝ)
  set n : ℝ := (Fintype.card V : ℝ)
  set Λ := P.L + P.ℓ + 1
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  -- `2Λ(X + Y) ≤ n + (2L + ℓ + 1) X`, using `(ℓ + 1) X + |H| ≤ n`
  have hXY : 2 * Λ * (X + Y.ncard) ≤ n + (2 * P.L + P.ℓ + 1) * X := by
    have : (P.ℓ + 1) * (2 * Λ * (X + Y.ncard)) ≤ (P.ℓ + 1) * (n + (2 * P.L + P.ℓ + 1) * X) := by
      nlinarith
    exact le_of_mul_le_mul_left this (by linarith)
  -- with `ℓ X < (n + 1)/2 - K + Q` and `budget_expand`
  have hXY' : P.ℓ * (2 * Λ * (X + Y.ncard)) ≤ P.ℓ * n + (2 * P.L + P.ℓ + 1) * (P.ℓ * X) := by
    nlinarith
  have hXY'' : (2 * P.L + P.ℓ + 1) * (P.ℓ * X) ≤
      (2 * P.L + P.ℓ + 1) * ((n + 1) / 2 - P.K + Q) :=
    mul_le_mul_of_nonneg_left hP.le (by linarith)
  have hD : 0 < 2 * (P.ℓ + 1) * (2 * P.L + 2 * P.ℓ + 1) := by positivity
  have hBe' : (2 * P.L + 3 * P.ℓ + 1) * n + 2 * P.L + P.ℓ + 1 ≤
      2 * (P.ℓ + 1) * (2 * P.L + 2 * P.ℓ + 1) * (P.K - Q) := by
    have := (div_le_iff₀ hD).mp
      (by linarith : ((2 * P.L + 3 * P.ℓ + 1) * n + 2 * P.L + P.ℓ + 1) /
        (2 * (P.ℓ + 1) * (2 * P.L + 2 * P.ℓ + 1)) ≤ P.K - Q)
    linarith
  have hfin : 2 * Λ * P.ℓ * (X + Y.ncard) ≤ 2 * Λ * P.ℓ * (P.K - Q) := by nlinarith
  have := le_of_mul_le_mul_left hfin (by positivity)
  linarith

include hG hsep hmin htouch in
/-- Case 1 fails: the region is a truncated expander, in ambient form. Every `A` with
`|A| ≤ |H|/2` has `|∂_H A| ≥ |A|/ℓ` or `|∂_H A| ≥ |H|/(2(ℓ + 1 + L))`. -/
lemma expansion_ambient (A : Set V) (hAR : A ⊆ D.region) (hsize : 2 * A.ncard ≤ D.region.ncard) :
    (A.ncard : ℝ) ≤ P.ℓ * (relBoundary G D.region A).ncard ∨
      (D.region.ncard : ℝ) ≤ 2 * (P.ℓ + 1 + P.L) * (relBoundary G D.region A).ncard := by
  have hℓ := P.ℓ_pos
  by_contra hcon
  push Not at hcon
  obtain ⟨hlt, hlt2⟩ := hcon
  set Y := relBoundary G D.region A
  have hYR : Y ⊆ D.region := fun _ hy => hy.1
  obtain ⟨H', hH', hcH', hhH', hbH'⟩ := D.robust hsep Y (cut_budget P hG hsep D htouch Y hlt2)
  have hHR : H' ⊆ D.region := fun _ hx => (hH' hx).1
  -- `H'` avoids `A`
  have hHA : Disjoint H' A := by
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hne
    obtain ⟨v, hvH, hvY⟩ := connected_meets_vertexBoundary hcH' hne (by
      have := (Set.ncard_le_card D.region).trans_eq Nat.card_eq_fintype_card; omega)
    exact (hH' hvH).2 ⟨hHR hvH, hvY⟩
  obtain ⟨x, hxA⟩ : A.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.ncard_empty, Nat.cast_zero] at hlt
    exact absurd hlt (not_lt.mpr (by positivity))
  refine region_not_shrink P D hmin hHR (hAR hxA) (Set.disjoint_right.mp hHA hxA)
    (D.shrink H' Y hHR hcH' hhH' hbH' ?_) rfl
  -- the budget: `ℓ |Y| < |A|` pays for discarding `Y`
  have hdisj1 : Disjoint H' Y := Set.disjoint_left.mpr fun _ hx hy => (hH' hx).2 hy
  have hdisj2 : Disjoint A Y := Set.disjoint_left.mpr fun _ hx hy => hy.2.1 hx
  have hsum : H'.ncard + A.ncard + Y.ncard ≤ D.region.ncard := by
    rw [← Set.ncard_union_eq hHA, ← Set.ncard_union_eq (Set.disjoint_union_left.mpr
      ⟨hdisj1, hdisj2⟩)]
    exact Set.ncard_le_ncard (Set.union_subset (Set.union_subset hHR hAR) hYR)
  have hsum' : (H'.ncard : ℝ) + A.ncard + Y.ncard ≤ D.region.ncard := by exact_mod_cast hsum
  have hu : ((D.discarded ∪ Y).ncard : ℝ) ≤ D.discarded.ncard + Y.ncard := by
    exact_mod_cast Set.ncard_union_le _ _
  nlinarith [D.budget]

include hG hsep hmin htouch in
/-- Case 2 fails: a light ball around an attachment set cannot be absorbed. -/
lemma absorb_impossible (C : Set V) (hC : C ∈ D.branches) (A : Set V) (hAR : A ⊆ D.region)
    (hNA : relBoundary G D.region C ⊆ A) (hcA : (G.induce (C ∪ A)).Connected)
    (hA : 2 * A.ncard ≤ Fintype.card V)
    (hY : ((relBoundary G D.region A).ncard : ℝ) ≤ P.β - 1) : False := by
  set Y := relBoundary G D.region A
  obtain ⟨K', hK', hcK', hhK', -⟩ := robust_small P hG hsep D htouch Y
    (hY.trans (le_max_right _ _))
  have hKA : Disjoint K' A := by
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hne
    obtain ⟨v, hvK, hvY⟩ := connected_meets_vertexBoundary hcK' hne (by omega)
    exact (hK' hvK).2 ⟨(hK' hvK).1, hvY⟩
  obtain ⟨H', hH', hKH'⟩ := exists_piece_superset (R := D.region \ A) hcK'
    (fun x hx => ⟨(hK' hx).1, Set.disjoint_left.mp hKA hx⟩)
  have hhH' : Fintype.card V < 2 * H'.ncard := lt_of_lt_of_le hhK' (by
    have := Set.ncard_le_ncard hKH' (Set.toFinite _); omega)
  have hHR : H' ⊆ D.region := fun _ hx => (hH'.1 hx).1
  have hbound : ((relBoundary G H' (C ∪ A)).ncard : ℝ) ≤ P.β - 1 := by
    refine le_trans (Nat.cast_le.mpr (Set.ncard_le_ncard ?_ (Set.toFinite _))) hY
    rintro v ⟨hv, hvCA, u, hu | hu, huv⟩
    · exact absurd (hNA ⟨hHR hv, fun h => hvCA (Or.inl h), u, hu, huv⟩) (hH'.1 hv).2
    · exact ⟨hHR hv, fun h => hvCA (Or.inr h), u, hu, huv⟩
  obtain ⟨x, hx⟩ := htouch C hC
  refine region_not_shrink P D hmin hHR hx.1 (fun hxH => (hH'.1 hxH).2 (hNA hx))
    (D.absorb C hC H' A hH'.1 hAR hH'.2.1 hhH' hcA ?_ hbound) rfl
  intro u hu v hv huv hvH
  by_contra hvA
  exact hvH (hH'.2.2 u hu v ⟨hv, hvA⟩ huv)

include hG hsep hmin htouch in
/-- Case 3 fails: there is no small connector meeting every branch set. -/
lemma connector_impossible (T : Set V) (hT : T ⊆ D.region) (hcT : (G.induce T).Connected)
    (hsize : (T.ncard : ℝ) ≤ P.a) (hadj : ∀ C ∈ D.branches, ∃ u ∈ T, ∃ v ∈ C, G.Adj u v) :
    False := by
  obtain ⟨H', hH', hcH', hhH', hbH'⟩ := robust_small P hG hsep D htouch T
    (hsize.trans (le_max_left _ _))
  have hHR : H' ⊆ D.region := fun _ hx => (hH' hx).1
  obtain ⟨x, hx⟩ := connected_nonempty hcT
  exact region_not_shrink P D hmin hHR (hT hx) (fun hxH => (hH' hxH).2 hx)
    (D.addBranch H' T hH' hT hcH' hhH' hcT hsize hbH' hadj) rfl

open scoped Classical

/-- The vertices of the region adjacent to `C`, as a subset of the region. -/
def Config.attach {ℓ a b : ℝ} (D : Config G ℓ a b) (C : Set V) : Set D.region :=
  {x | x.val ∈ relBoundary G D.region C}

include hG hsep hmin htouch in
/-- Case 1 fails: the region is a truncated expander at scale `ℓ` with slack `L`. -/
lemma region_truncExpander : IsTruncExpander (G.induce D.region) P.ℓ P.L := by
  intro S hS
  have h1 := expansion_ambient P hG hsep D hmin htouch (Subtype.val '' S)
    (by rintro _ ⟨x, -, rfl⟩; exact x.property)
    (by rw [ncard_image_val]; simpa [Set.ncard_univ, Nat.card_eq_fintype_card,
      Set.ncard_eq_toFinset_card'] using hS)
  rw [ncard_image_val, relBoundary, ← image_vertexBoundary_induce, ncard_image_val] at h1
  rwa [Set.fintypeCard_eq_ncard]

include hG hsep hmin htouch in
/-- Case 2 fails: around the attachment set of a branch set, the balls grow by at least `β`
per layer while they have fewer than `S` vertices. -/
lemma ball_growth {C : Set V} (hC : C ∈ D.branches) (r : ℕ)
    (hlt : (ball (G.induce D.region) (D.attach C) r).ncard < P.S) :
    P.β ≤ (vertexBoundary (G.induce D.region) (ball (G.induce D.region) (D.attach C) r)).ncard := by
  by_contra hcon
  push Not at hcon
  set R := D.region
  set B := ball (G.induce R) (D.attach C) r
  refine absorb_impossible P hG hsep D hmin htouch C hC (Subtype.val '' B)
    (by rintro _ ⟨x, -, rfl⟩; exact x.property) ?_ ?_ ?_ ?_
  · intro v hv
    exact ⟨⟨v, hv.1⟩, subset_ball _ r (show (⟨v, hv.1⟩ : R) ∈ D.attach C from hv), rfl⟩
  · apply connected_union_of_attached (D.branch_connected C hC)
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨u, hu, p, hp⟩ := exists_walk_in_ball D.connected hy
    obtain ⟨-, -, w, hwC, hwu⟩ := hu
    refine ⟨C ∪ Subtype.val '' {z | z ∈ p.support}, ?_, ?_, ?_, ?_⟩
    · exact Set.union_subset_union_right _ (Set.image_mono fun z hz => hp z hz)
    · exact Or.inr ⟨y, p.end_mem_support, rfl⟩
    · exact SimpleGraph.connected_induce_union (D.branch_connected C hC).preconnected
        (induce_connected_lift p.connected_induce_support).preconnected hwC
        ⟨u, p.start_mem_support, rfl⟩ hwu
    · exact ⟨w, Or.inl hwC, hwC⟩
  · rw [ncard_image_val]
    have := P.two_S_le
    omega
  · rw [relBoundary, ← image_vertexBoundary_induce, ncard_image_val]
    have : ((vertexBoundary (G.induce R) B).ncard : ℝ) + 1 ≤ P.β := by exact_mod_cast hcon
    linarith

include hG hsep hmin htouch in
/-- The tent measure near the attachment set of a branch set: `∑ ν² ≤ 2(2S+1)/(3S(S+1))`
and mean distance at most `E`. -/
lemma exists_tent {C : Set V} (hC : C ∈ D.branches) :
    ∃ ν : D.region → ℝ, (∀ x, 0 ≤ ν x) ∧ ∑ x, ν x = 1 ∧
      3 * P.S * (P.S + 1) * ∑ x, ν x ^ 2 ≤ 2 * (2 * P.S + 1) ∧
      ∑ x, ν x * setDist (G.induce D.region) (D.attach C) x ≤ P.E := by
  classical
  have hU : (D.attach C).Nonempty := by
    obtain ⟨v, hv⟩ := htouch C hC
    exact ⟨⟨v, hv.1⟩, hv⟩
  have hgrow := ball_growth P hG hsep D hmin htouch hC
  rcases P.path with hE | ⟨h4S, hu, hβS, hβτ, hE⟩
  · obtain ⟨ν, h0, h1, h2, h3⟩ :=
      exists_tent_measure D.connected hU P.one_le_S P.one_le_β hgrow
    exact ⟨ν, h0, h1, h2, h3.trans hE⟩
  · have hℓ := P.ℓ_pos
    have hL := P.L_nonneg
    have hn : (Fintype.card V : ℝ) + 1 ≤ 2 * Fintype.card D.region := by
      have := D.heavy
      rw [Set.fintypeCard_eq_ncard]
      exact_mod_cast (show Fintype.card V + 1 ≤ 2 * D.region.ncard by omega)
    obtain ⟨ν, h0, h1, h2, h3⟩ := exists_tent_measure_exp D.connected hU P.one_le_S P.one_le_β
      hgrow hℓ (region_truncExpander P hG hsep D hmin htouch) (by
        have : (4 * P.S : ℝ) ≤ Fintype.card V + 1 := by exact_mod_cast h4S
        have : (2 * P.S : ℝ) ≤ Fintype.card D.region := by linarith
        exact_mod_cast this) (by positivity) (by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith) hu hβS hβτ
    exact ⟨ν, h0, h1, h2, h3.trans hE⟩

/-- The square root in the connector bound: `q²(Nc - 1)/(q - 1) ≤ h(nc - 1)` when
`2 ≤ q ≤ h - 2`, `N ≤ n` and `1 ≤ nc`. -/
lemma connector_arg_le {q h N n c : ℝ} (hq : 2 ≤ q) (hqh : q + 2 ≤ h) (hN : N ≤ n)
    (hc : 0 ≤ c) (hnc : 1 ≤ n * c) : q ^ 2 * (N * c - 1) / (q - 1) ≤ h * (n * c - 1) := by
  rw [div_le_iff₀ (by linarith)]
  have hxy : N * c - 1 ≤ n * c - 1 := by nlinarith
  have hq1 : (0 : ℝ) ≤ q - 1 := by linarith
  rcases le_total 0 (N * c - 1) with hx | hx
  · have h2 : q ^ 2 ≤ (q + 2) * (q - 1) := by nlinarith
    have e1 := mul_le_mul_of_nonneg_right h2 hx
    have e2 := mul_le_mul_of_nonneg_right hqh (mul_nonneg hq1 hx)
    have e3 := mul_le_mul_of_nonneg_left hxy (mul_nonneg (by linarith : (0 : ℝ) ≤ h) hq1)
    nlinarith
  · have e1 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg q) hx
    have e2 : 0 ≤ h * (n * c - 1) * (q - 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hq1
    nlinarith

include hG hsep hmin htouch in
/-- The minimal configuration cannot exist: the hitting walk gives a connector of size at most
`a` (Case 3). -/
lemma minimal_false : False := by
  classical
  set q := D.branches.card
  have hqh := D.card_le hG htouch
  rcases Nat.lt_or_ge q 2 with hq | hq
  · -- at most one branch set: a single vertex is a connector
    obtain ⟨v, hvR, hv⟩ : ∃ v ∈ D.region, ∀ C ∈ D.branches, ∃ w ∈ C, G.Adj v w := by
      rcases Nat.lt_succ_iff.mp hq |>.lt_or_eq with hq0 | hq1
      · obtain ⟨v, hv⟩ := connected_nonempty D.connected
        exact ⟨v, hv, fun C hC => absurd (Finset.card_pos.mpr ⟨C, hC⟩) (by omega)⟩
      · obtain ⟨C, hC⟩ := Finset.card_eq_one.mp hq1
        obtain ⟨v, hvR, -, w, hw, hwv⟩ := htouch C (by simp [hC])
        refine ⟨v, hvR, fun C' hC' => ?_⟩
        rw [hC, Finset.mem_singleton] at hC'
        exact ⟨w, hC' ▸ hw, hwv.symm⟩
    refine connector_impossible P hG hsep D hmin htouch {v} (by simpa using hvR) (by simp)
      (by rw [Set.ncard_singleton, Nat.cast_one]; exact P.one_le_a) fun C hC => ?_
    obtain ⟨w, hw, hvw⟩ := hv C hC
    exact ⟨v, rfl, w, hw, hvw⟩
  -- at least two branch sets: the hitting walk for the tent measures
  let e := D.branches.equivFin.symm
  let U : Fin q → Set D.region := fun i => D.attach (e i).val
  have hU : ∀ i, (U i).Nonempty := fun i => by
    obtain ⟨v, hv⟩ := htouch _ (e i).property
    exact ⟨⟨v, hv.1⟩, hv⟩
  have hmeas := fun i => exists_tent P hG hsep D hmin htouch (e i).property
  have hE0 : 0 ≤ P.E := by
    obtain ⟨ν, h0, -, -, h3⟩ := hmeas ⟨0, by omega⟩
    exact le_trans (Finset.sum_nonneg fun x _ => mul_nonneg (h0 x) (Nat.cast_nonneg _)) h3
  obtain ⟨T, hTc, hTU, hTcard⟩ := extended_short_tree D.connected P.ℓ_pos P.L_nonneg
    (region_truncExpander P hG hsep D hmin htouch) hq U P.one_le_S hU hmeas
  refine connector_impossible P hG hsep D hmin htouch (Subtype.val '' T)
    (by rintro _ ⟨x, -, rfl⟩; exact x.property) (induce_connected_lift hTc) ?_ ?_
  · -- the size bound
    rw [ncard_image_val]
    refine hTcard.trans (le_trans ?_ (P.connector (by omega)))
    have hS : (1 : ℝ) ≤ P.S := by exact_mod_cast P.one_le_S
    have h2S : (2 * P.S : ℝ) ≤ Fintype.card V := by exact_mod_cast P.two_S_le
    have hsq := Real.sqrt_le_sqrt (connector_arg_le (q := q) (h := h)
      (N := Fintype.card D.region) (n := Fintype.card V)
      (c := 2 * (2 * P.S + 1) / (3 * P.S * (P.S + 1))) (by exact_mod_cast hq)
      (by exact_mod_cast hqh) (by exact_mod_cast Fintype.card_subtype_le _) (by positivity)
      (by rw [mul_div_assoc', le_div_iff₀ (by positivity)]; nlinarith))
    have hσ : 0 ≤ Real.pi * Real.sqrt (truncVar P.ℓ P.L) := by positivity
    have hqh' : (q + 2 : ℝ) ≤ h := by exact_mod_cast hqh
    have hqt := mul_le_mul_of_nonneg_right (show (q : ℝ) ≤ h - 2 by linarith) hE0
    nlinarith [mul_le_mul_of_nonneg_left hsq hσ]
  · intro C hC
    obtain ⟨x, hxT, hxU⟩ := hTU (e.symm ⟨C, hC⟩)
    have hxU' : x.val ∈ relBoundary G D.region C := by
      simpa [U, Config.attach, Equiv.apply_symm_apply] using hxU
    obtain ⟨-, -, w, hwC, hwx⟩ := hxU'
    exact ⟨x.val, ⟨x, hxT, rfl⟩, w, hwC, hwx.symm⟩

end Minimal

/-- **The separator theorem, parametric form.** A `K_h`-minor-free graph has a balanced
separator with at most `K` vertices, for any parameters satisfying `SepParams`. -/
theorem separator_of_params (G : SimpleGraph V) (hh : 2 ≤ h) (hG : ¬HasCliqueMinor G h)
    (P : SepParams (Fintype.card V) h) :
    ∃ S : Finset V, IsBalancedSeparator G S ∧ (S.card : ℝ) ≤ P.K := by
  classical
  by_contra hcon
  have hsep : ∀ Z : Set V, (Z.ncard : ℝ) ≤ P.K →
      ∃ Q, IsPiece G Zᶜ Q ∧ Fintype.card V < 2 * Q.ncard := by
    intro Z hZ
    have hbal : ¬IsBalancedSeparator G Z.toFinset := fun hb =>
      hcon ⟨Z.toFinset, hb, by rwa [← Set.ncard_eq_toFinset_card']⟩
    unfold IsBalancedSeparator at hbal
    push Not at hbal
    obtain ⟨C, hC⟩ := hbal
    have hp := isPiece_deletedComponent (G := G) (Z.toFinset : Set V) C
    refine ⟨deletedComponent G _ C, ⟨fun x hx => by simpa using hp.1 hx, hp.2.1,
      fun u hu v hv huv => hp.2.2 u hu v (by simpa using hv) huv⟩, ?_⟩
    rw [deletedComponent_ncard]
    exact hC
  have hK0 : 0 ≤ P.K := by
    have := P.budget_branch
    have hh' : (2 : ℝ) ≤ h := by exact_mod_cast hh
    have h1 : 0 ≤ (h - 2 : ℝ) * max P.a (P.β - 1) := mul_nonneg (by linarith) P.max_pos.le
    have h2 : 0 ≤ (Fintype.card V + 1 + 2 * P.ℓ * max P.a (P.β - 1) : ℝ) / (2 * (P.ℓ + 1)) := by
      have := P.ℓ_pos; have := P.max_pos; positivity
    linarith
  obtain ⟨Q, hQ, hQh⟩ := hsep ∅ (by simpa using hK0)
  have hinit : Nonempty (Config G P.ℓ P.a (P.β - 1)) := ⟨{
    region := Q
    discarded := ∅
    branches := ∅
    connected := hQ.2.1
    heavy := hQh
    branch_connected := by simp
    region_branch := by simp
    branch_disjoint := by simp
    branch_adjacent := by simp
    boundary := fun u hu v huv hv => absurd (hQ.2.2 u hu v (by simp) huv) hv
    budget := by
      simp only [Set.ncard_empty, Nat.cast_zero, mul_zero, add_zero]
      exact_mod_cast (Set.ncard_le_card Q).trans_eq Nat.card_eq_fintype_card
    branch_bound := by simp }⟩
  obtain ⟨D, hmin, htouch⟩ := Config.exists_minimal hinit
  exact minimal_false P hG hsep D hmin htouch

end MinorFreeSeparators
