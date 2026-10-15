import definitions
import Mathlib

/-!
# Graph preliminaries

Connected vertex sets, components of induced subgraphs, the vertex boundary,
and vertex expansion (`def:expansion` of the paper).

Vertex sets are `Set V`, measured with `Set.ncard`.
-/

namespace MinorFreeSeparators

variable {V W : Type*}

section Connected

variable {G : SimpleGraph V} {H : SimpleGraph W}

lemma connected_nonempty {A : Set V} (hc : (G.induce A).Connected) : A.Nonempty := by
  obtain ⟨u⟩ := hc.nonempty
  exact ⟨u, u.property⟩

/-- The image of a connected set under a graph homomorphism is connected. -/
lemma induce_connected_image (f : G →g H) {A : Set V}
    (hc : (G.induce A).Connected) : (H.induce (f '' A)).Connected := by
  let g : G.induce A →g H.induce (f '' A) :=
    { toFun := fun x => ⟨f x, ⟨x, x.property, rfl⟩⟩
      map_rel' := fun h => f.map_adj h }
  apply hc.map g
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- A connected set of an induced subgraph is connected in the ambient graph. -/
lemma induce_connected_lift {A : Set V} {B : Set A}
    (hc : ((G.induce A).induce B).Connected) :
    (G.induce (Subtype.val '' B)).Connected :=
  induce_connected_image (SimpleGraph.Embedding.induce A).toHom hc

/-- A connected set cannot cross a cut with no crossing edges. -/
lemma connected_closed_subset {K A : Set V} (hc : (G.induce K).Connected)
    (hne : (K ∩ A).Nonempty)
    (hclosed : ∀ u ∈ K ∩ A, ∀ v ∈ K, G.Adj u v → v ∈ A) : K ⊆ A := by
  obtain ⟨u, huK, huA⟩ := hne
  intro v hv
  obtain ⟨p⟩ := hc ⟨u, huK⟩ ⟨v, hv⟩
  suffices ∀ (x y : K) (p : (G.induce K).Walk x y), x.val ∈ A → y.val ∈ A from this _ _ p huA
  intro x y p
  induction p with
  | nil => exact id
  | cons hadj _ ih =>
    exact fun hx => ih (hclosed _ ⟨Subtype.property _, hx⟩ _ (Subtype.property _) hadj)

/-- The union of a connected set with connected sets attached to it is connected. -/
lemma connected_union_of_attached {C A : Set V} (hC : (G.induce C).Connected)
    (hA : ∀ x ∈ A, ∃ S ⊆ C ∪ A, x ∈ S ∧ (G.induce S).Connected ∧ (S ∩ C).Nonempty) :
    (G.induce (C ∪ A)).Connected := by
  have hlift : ∀ S (hS : S ⊆ C ∪ A), (G.induce S).Connected → ∀ x (hx : x ∈ S) y (hy : y ∈ S),
      (G.induce (C ∪ A)).Reachable ⟨x, hS hx⟩ ⟨y, hS hy⟩ := by
    intro S hS hc x hx y hy
    exact (hc ⟨x, hx⟩ ⟨y, hy⟩).map (G.induceHomOfLE hS).toHom
  obtain ⟨c0⟩ := hC.nonempty
  have hC' : C ⊆ C ∪ A := Set.subset_union_left
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨c0.val, hC' c0.property⟩, ?_⟩
  rintro ⟨x, hx | hx⟩
  · exact hlift C hC' hC _ c0.property x hx
  · obtain ⟨S, hS, hxS, hcS, y, hyS, hyC⟩ := hA x hx
    exact (hlift C hC' hC _ c0.property y hyC).trans (hlift S hS hcS y hyS x hxS)

end Connected

section Pieces

variable {G : SimpleGraph V}

/-- `P` is the vertex set of a connected component of the subgraph induced by `R`. -/
def IsPiece (G : SimpleGraph V) (R P : Set V) : Prop :=
  P ⊆ R ∧ (G.induce P).Connected ∧ ∀ u ∈ P, ∀ v ∈ R, G.Adj u v → v ∈ P

lemma ncard_image_val {H : Set V} (A : Set H) : (Subtype.val '' A).ncard = A.ncard :=
  Set.ncard_image_of_injective _ Subtype.val_injective

/-- The vertices of a component of `G - Z`, in the original vertex type. -/
def deletedComponent (G : SimpleGraph V) (Z : Set V)
    (C : (G.induce Zᶜ).ConnectedComponent) : Set V := Subtype.val '' C.supp

lemma deletedComponent_ncard (Z : Set V) (C : (G.induce Zᶜ).ConnectedComponent) :
    (deletedComponent G Z C).ncard = C.supp.ncard :=
  ncard_image_val C.supp

lemma isPiece_deletedComponent (Z : Set V) (C : (G.induce Zᶜ).ConnectedComponent) :
    IsPiece G Zᶜ (deletedComponent G Z C) := by
  refine ⟨?_, induce_connected_lift C.connected_toSimpleGraph, ?_⟩
  · rintro x ⟨v, _, rfl⟩
    exact v.property
  · rintro u ⟨u', hu', rfl⟩ v hv huv
    exact ⟨⟨v, hv⟩, C.mem_supp_of_adj_mem_supp hu' huv, rfl⟩

/-- Every connected subset of `R` lies in a piece of `R`. -/
lemma exists_piece_superset {R K : Set V} (hK : (G.induce K).Connected) (hKR : K ⊆ R) :
    ∃ P, IsPiece G R P ∧ K ⊆ P := by
  obtain ⟨u⟩ := hK.nonempty
  have hR : K ⊆ Rᶜᶜ := by simpa using hKR
  let C := (G.induce Rᶜᶜ).connectedComponentMk ⟨u.val, hR u.property⟩
  refine ⟨deletedComponent G Rᶜ C, by simpa using isPiece_deletedComponent Rᶜ C, ?_⟩
  intro v hv
  refine ⟨⟨v, hR hv⟩, ?_, rfl⟩
  apply SimpleGraph.ConnectedComponent.sound
  exact (hK ⟨v, hv⟩ u).map (G.induceHomOfLE hR).toHom

end Pieces

section Boundary

variable {G : SimpleGraph V}

/-- The vertex boundary `∂S`: vertices outside `S` with a neighbour in `S`. -/
def vertexBoundary (G : SimpleGraph V) (S : Set V) : Set V :=
  {v | v ∉ S ∧ ∃ u ∈ S, G.Adj u v}

lemma disjoint_vertexBoundary (S : Set V) : Disjoint S (vertexBoundary G S) :=
  Set.disjoint_left.mpr fun _ hv h => h.1 hv

/-- The boundary in an induced subgraph is the boundary relative to its vertex set. -/
lemma image_vertexBoundary_induce {H : Set V} (A : Set H) :
    Subtype.val '' vertexBoundary (G.induce H) A = H ∩ vertexBoundary G (Subtype.val '' A) := by
  ext v
  constructor
  · rintro ⟨v, ⟨hv, u, hu, huv⟩, rfl⟩
    refine ⟨v.property, ?_, u.val, ⟨u, hu, rfl⟩, huv⟩
    rintro ⟨w, hw, he⟩
    exact hv (Subtype.ext he ▸ hw)
  · rintro ⟨hvH, hv, u, ⟨u', hu', rfl⟩, huv⟩
    exact ⟨⟨v, hvH⟩, ⟨fun hx => hv ⟨⟨v, hvH⟩, hx, rfl⟩, u', hu', huv⟩, rfl⟩

/-- A connected set that meets `A` and is heavier than `A` meets the boundary of `A`. -/
lemma connected_meets_vertexBoundary [Finite V] {K A : Set V} (hK : (G.induce K).Connected)
    (hKA : (K ∩ A).Nonempty) (hcard : A.ncard < K.ncard) :
    (K ∩ vertexBoundary G A).Nonempty := by
  by_contra hne
  have hsub : K ⊆ A := connected_closed_subset hK hKA fun u hu v hv huv => by
    by_contra hvA
    exact hne ⟨v, hv, hvA, u, hu.2, huv⟩
  exact absurd (Set.ncard_le_ncard hsub) (not_le.mpr hcard)

end Boundary

section Expansion

/-- `G` is a `ψ`-vertex expander: `|∂S| ≥ ψ |S|` for every `S` with `|S| ≤ |V|/2`. -/
def IsVertexExpander [Fintype V] (G : SimpleGraph V) (ψ : ℝ) : Prop :=
  ∀ S : Set V, 2 * S.ncard ≤ Fintype.card V → ψ * S.ncard ≤ (vertexBoundary G S).ncard

/-- `G` is a truncated expander at scale `ℓ` with slack `L ≥ 0`: every `S` with
`|S| ≤ |V|/2` has `|S| ≤ ℓ |∂S|` or `|V| ≤ 2(ℓ + 1 + L) |∂S|`. So expansion is only required
while `|∂S| < |V|/(2(ℓ + 1 + L))`; this is all the Poincaré inequality uses. -/
def IsTruncExpander [Fintype V] (G : SimpleGraph V) (ℓ L : ℝ) : Prop :=
  ∀ S : Set V, 2 * S.ncard ≤ Fintype.card V → (S.ncard : ℝ) ≤ ℓ * (vertexBoundary G S).ncard ∨
    (Fintype.card V : ℝ) ≤ 2 * (ℓ + 1 + L) * (vertexBoundary G S).ncard

lemma IsVertexExpander.isTruncExpander [Fintype V] {G : SimpleGraph V} {ψ : ℝ}
    (h : IsVertexExpander G ψ) (hψ : 0 < ψ) : IsTruncExpander G (1 / ψ) 0 := fun S hS => by
  left
  have := h S hS
  rw [one_div_mul_eq_div, le_div_iff₀ hψ]
  linarith

/-- The vertex expansion `ψ(G) = min {|∂S| / |S| : 0 < |S| ≤ n/2}` (`def:expansion`).
The family is empty when `n ≤ 1`, and then the value is `0`. -/
noncomputable def vertexExpansion [Fintype V] (G : SimpleGraph V) : ℝ :=
  sInf {ψ | ∃ S : Set V, 0 < S.ncard ∧ 2 * S.ncard ≤ Fintype.card V ∧
    ψ = (vertexBoundary G S).ncard / S.ncard}

variable [Fintype V] {G : SimpleGraph V}

lemma isVertexExpander_vertexExpansion : IsVertexExpander G (vertexExpansion G) := by
  intro S hS
  rcases Nat.eq_zero_or_pos S.ncard with h0 | hpos
  · simp [h0]
  have hle : vertexExpansion G ≤ (vertexBoundary G S).ncard / S.ncard :=
    csInf_le ⟨0, by rintro _ ⟨T, -, -, rfl⟩; positivity⟩ ⟨S, hpos, hS, rfl⟩
  have : (0 : ℝ) < S.ncard := by exact_mod_cast hpos
  rwa [le_div_iff₀ this] at hle

/-- A connected graph with at least two vertices has positive vertex expansion. -/
lemma vertexExpansion_pos (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    0 < vertexExpansion G := by
  -- the infimum of the finitely many ratios is attained at some `S`
  obtain ⟨v⟩ := hG.nonempty
  obtain ⟨S, hpos, hS, heq⟩ : vertexExpansion G ∈ (_ : Set ℝ) :=
    Set.Nonempty.csInf_mem ⟨_, {v}, by simp, by simpa using hn, rfl⟩
      ((Set.finite_range fun S : Set V => ((vertexBoundary G S).ncard : ℝ) / S.ncard).subset
        (by rintro _ ⟨S, -, -, rfl⟩; exact ⟨S, rfl⟩))
  rw [heq]
  refine div_pos ?_ (by exact_mod_cast hpos)
  -- `S` is a proper nonempty subset, so a walk out of it crosses its boundary
  obtain ⟨u, hu⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
  obtain ⟨w, hw⟩ : ∃ w, w ∉ S := by
    by_contra! h
    rw [Set.eq_univ_of_forall h, Set.ncard_univ, Nat.card_eq_fintype_card] at hS
    omega
  obtain ⟨d, -, hd1, hd2⟩ := (hG.preconnected u w).some.exists_boundary_dart S hu hw
  have hne : (vertexBoundary G S).Nonempty := ⟨d.snd, hd2, d.fst, hd1, d.adj⟩
  exact_mod_cast (Set.ncard_pos (Set.toFinite _)).mpr hne

end Expansion

end MinorFreeSeparators
