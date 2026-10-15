import proof.Separator.Connector

/-!
# Configurations

The separator argument is an extremal version of the paper's Algorithm
`BalancedSeparator`. A configuration consists of
* a connected region `H` with more than half of the vertices,
* a discarded set `X`, paid for by the shrinkage of `H`,
* branch sets `𝒦` forming a clique model, all disjoint from `H`,

such that every vertex outside `H` with a neighbour in `H` is discarded or lies in a
branch set, and every branch set `C` is small (`|C| ≤ a`) or has few attachments
(`|∂_H C| ≤ b`). The three moves are the three cases of the algorithm: removing a sparse
cut (`shrink`, Case 1), growing a branch set by a ball (`absorb`, Case 2), and adding a
new branch set (`addBranch`, Case 3). Each move replaces the region by a subset;
`Minimal.lean` applies them with a proper subset to contradict minimality.

The fields are the invariants of the algorithm's analysis:
* `branch_connected`, `branch_disjoint`, `branch_adjacent`, `region_branch`:
  `lem:invariants` (`𝒦` is a clique minor model disjoint from `H`);
* `boundary`: `lem:size` (1), `∂_G H ⊆ X ∪ V(𝒦)`;
* `budget`: replaces `lem:size` (2); `X` is paid for at rate `ℓ + 1` by the vertices
  removed from `H`;
* `branch_bound`: replaces `lem:size` (3);
* `heavy`: the region has more than `n/2` vertices; once no heavy region remains, the
  current cut is a separator (`lem:balance`, with `1/2` in place of `3/4`).
-/

namespace MinorFreeSeparators

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- `∂_H A`: the vertices of `H` outside `A` with a neighbour in `A`. -/
def relBoundary (H A : Set V) : Set V := H ∩ vertexBoundary G A

/-- A configuration `(H, X, 𝒦)`. -/
structure Config (ℓ a b : ℝ) where
  region : Set V
  discarded : Set V
  branches : Finset (Set V)
  connected : (G.induce region).Connected
  heavy : Fintype.card V < 2 * region.ncard
  branch_connected : ∀ C ∈ branches, (G.induce C).Connected
  region_branch : ∀ C ∈ branches, Disjoint region C
  branch_disjoint : (↑branches : Set (Set V)).Pairwise Disjoint
  branch_adjacent : ∀ C ∈ branches, ∀ D ∈ branches, C ≠ D → ∃ u ∈ C, ∃ v ∈ D, G.Adj u v
  boundary : ∀ u ∈ region, ∀ v, G.Adj u v → v ∉ region →
    v ∈ discarded ∨ ∃ C ∈ branches, v ∈ C
  budget : (region.ncard : ℝ) + (ℓ + 1) * discarded.ncard ≤ Fintype.card V
  branch_bound : ∀ C ∈ branches, (C.ncard : ℝ) ≤ a ∨ ((relBoundary G region C).ncard : ℝ) ≤ b

variable {G} {ℓ a b : ℝ}

omit [Fintype V] in
lemma relBoundary_mono {H H' A : Set V} (hH : H' ⊆ H) :
    relBoundary G H' A ⊆ relBoundary G H A := fun _ hx => ⟨hH hx.1, hx.2⟩

omit [Fintype V] in
/-- Adding a set adjacent to every member keeps a family of sets pairwise adjacent. -/
lemma adjacent_insert [DecidableEq (Set V)] {B : Finset (Set V)} {N : Set V}
    (hB : ∀ C ∈ B, ∀ E ∈ B, C ≠ E → ∃ u ∈ C, ∃ v ∈ E, G.Adj u v)
    (hN : ∀ C ∈ B, ∃ u ∈ N, ∃ v ∈ C, G.Adj u v) :
    ∀ C ∈ insert N B, ∀ E ∈ insert N B, C ≠ E → ∃ u ∈ C, ∃ v ∈ E, G.Adj u v := by
  intro C hC E hE hne
  rw [Finset.mem_insert] at hC hE
  rcases hC with rfl | hC <;> rcases hE with rfl | hE
  · exact absurd rfl hne
  · exact hN E hE
  · obtain ⟨u, hu, v, hv, huv⟩ := hN C hC
    exact ⟨v, hv, u, hu, huv.symm⟩
  · exact hB C hC E hE hne

namespace Config

/-- The branch sets form a `K_|𝒦|` model, so there are fewer than `h` of them. -/
lemma card_lt (D : Config G ℓ a b) {h : ℕ} (hm : ¬HasCliqueMinor G h) : D.branches.card < h := by
  classical
  by_contra! hh
  let e := (Fintype.equivFin ↥D.branches).symm
  let f : Fin h → ↥D.branches := fun i => e (Fin.castLE (by simpa using hh) i)
  have hf : Function.Injective f := e.injective.comp (Fin.castLE_injective _)
  apply hm
  refine ⟨fun i => (f i).val, fun i => connected_nonempty (D.branch_connected _ (f i).property),
    fun i => D.branch_connected _ (f i).property, fun i j hij => ?_, fun i j hij => ?_⟩
  · exact D.branch_disjoint (f i).property (f j).property (fun he => hij (hf (Subtype.ext he)))
  · exact D.branch_adjacent _ (f i).property _ (f j).property
      (fun he => hij (hf (Subtype.ext he)))

/-- If every branch set touches the region, the region is a further branch set, so there
are at most `h - 2` branch sets. -/
lemma card_le (D : Config G ℓ a b) {h : ℕ} (hm : ¬HasCliqueMinor G h)
    (htouch : ∀ C ∈ D.branches, (relBoundary G D.region C).Nonempty) :
    D.branches.card + 2 ≤ h := by
  classical
  have hlt := D.card_lt hm
  by_contra hcon
  have heq : D.branches.card + 1 = h := by omega
  let e := D.branches.equivFin.symm
  let bag : Fin h → Set V := fun i =>
    if hi : (i : ℕ) < D.branches.card then (e ⟨i, hi⟩).val else D.region
  have hbag : ∀ i : Fin h, (hi : (i : ℕ) < D.branches.card) → bag i = (e ⟨i, hi⟩).val :=
    fun i hi => dif_pos hi
  have hlast : ∀ i : Fin h, ¬(i : ℕ) < D.branches.card → bag i = D.region :=
    fun i hi => dif_neg hi
  apply hm
  refine ⟨bag, fun i => ?_, fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · by_cases hi : (i : ℕ) < D.branches.card
    · rw [hbag i hi]; exact connected_nonempty (D.branch_connected _ (e _).property)
    · rw [hlast i hi]; exact connected_nonempty D.connected
  · by_cases hi : (i : ℕ) < D.branches.card
    · rw [hbag i hi]; exact D.branch_connected _ (e _).property
    · rw [hlast i hi]; exact D.connected
  · by_cases hi : (i : ℕ) < D.branches.card <;> by_cases hj : (j : ℕ) < D.branches.card
    · rw [hbag i hi, hbag j hj]
      refine D.branch_disjoint (e _).property (e _).property fun he => hij ?_
      have := e.injective (Subtype.ext he)
      exact Fin.ext (by simpa using congrArg Fin.val this)
    · rw [hbag i hi, hlast j hj]; exact (D.region_branch _ (e _).property).symm
    · rw [hlast i hi, hbag j hj]; exact D.region_branch _ (e _).property
    · exact absurd (Fin.ext (by omega)) hij
  · by_cases hi : (i : ℕ) < D.branches.card <;> by_cases hj : (j : ℕ) < D.branches.card
    · rw [hbag i hi, hbag j hj]
      refine D.branch_adjacent _ (e _).property _ (e _).property fun he => hij ?_
      have := e.injective (Subtype.ext he)
      exact Fin.ext (by simpa using congrArg Fin.val this)
    · rw [hbag i hi, hlast j hj]
      obtain ⟨v, hvR, -, u, hu, huv⟩ := htouch _ (e ⟨i, hi⟩).property
      exact ⟨u, hu, v, hvR, huv⟩
    · rw [hlast i hi, hbag j hj]
      obtain ⟨v, hvR, -, u, hu, huv⟩ := htouch _ (e ⟨j, hj⟩).property
      exact ⟨v, hvR, u, hu, huv.symm⟩
    · exact absurd (Fin.ext (by omega)) hij

/-- `F_C`: the branch set itself if it is small, and its attachment set otherwise. -/
noncomputable def cut (D : Config G ℓ a b) (C : Set V) : Set V :=
  if (C.ncard : ℝ) ≤ a then C else relBoundary G D.region C

lemma cut_ncard_le (D : Config G ℓ a b) {C : Set V} (hC : C ∈ D.branches) :
    ((D.cut C).ncard : ℝ) ≤ max a b := by
  unfold cut
  split_ifs with hs
  · exact hs.trans (le_max_left _ _)
  · exact ((D.branch_bound C hC).resolve_left hs).trans (le_max_right _ _)

/-- The discarded set is paid for by the shrinkage of the region. -/
lemma discarded_le (D : Config G ℓ a b) (hℓ : 0 ≤ ℓ) :
    (D.discarded.ncard : ℝ) ≤ (Fintype.card V - D.region.ncard) / (ℓ + 1) := by
  rw [le_div_iff₀ (by linarith)]
  linarith [D.budget]

/-- **Robustness.** If deleting `X`, the cuts `F_C` and `Y` costs at most `K`, and there is no
balanced separator of size `K`, then `H - Y` has a heavy component, whose boundary inside `H`
lies in `Y`. -/
lemma robust (D : Config G ℓ a b) {K : ℝ}
    (hsep : ∀ Z : Set V, (Z.ncard : ℝ) ≤ K → ∃ P, IsPiece G Zᶜ P ∧ Fintype.card V < 2 * P.ncard)
    (Y : Set V) (hY : (D.discarded.ncard : ℝ) + D.branches.card * max a b + Y.ncard ≤ K) :
    ∃ H', H' ⊆ D.region \ Y ∧ (G.induce H').Connected ∧ Fintype.card V < 2 * H'.ncard ∧
      ∀ u ∈ H', ∀ v ∈ D.region, G.Adj u v → v ∉ H' → v ∈ Y := by
  classical
  let F := ⋃ C ∈ D.branches, D.cut C
  have hF : (F.ncard : ℝ) ≤ D.branches.card * max a b := by
    calc (F.ncard : ℝ) ≤ ∑ C ∈ D.branches, ((D.cut C).ncard : ℝ) :=
          mod_cast Finset.set_ncard_biUnion_le _ _
      _ ≤ ∑ _C ∈ D.branches, max a b := Finset.sum_le_sum fun C hC => D.cut_ncard_le hC
      _ = _ := by simp
  let Z := D.discarded ∪ F ∪ Y
  have hZ : (Z.ncard : ℝ) ≤ K := by
    have h1 := Set.ncard_union_le (D.discarded ∪ F) Y
    have h2 := Set.ncard_union_le D.discarded F
    have : (Z.ncard : ℝ) ≤ D.discarded.ncard + F.ncard + Y.ncard := by
      exact_mod_cast h1.trans (Nat.add_le_add_right h2 _)
    linarith
  obtain ⟨P, hP, hPh⟩ := hsep Z hZ
  -- the heavy piece meets the heavy region, and cannot leave it
  have hmeet : (P ∩ D.region).Nonempty := by
    by_contra hn
    have hd : Disjoint P D.region := Set.disjoint_iff_inter_eq_empty.mpr
      (Set.not_nonempty_iff_eq_empty.mp hn)
    have := Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)
    have h2 := Set.ncard_le_card (P ∪ D.region)
    rw [Nat.card_eq_fintype_card, this] at h2
    have := D.heavy
    omega
  have hPR : P ⊆ D.region := by
    apply connected_closed_subset hP.2.1 hmeet
    intro u hu v hv huv
    by_contra hvR
    have hvZ : v ∉ Z := hP.1 hv
    have huZ : u ∉ Z := hP.1 hu.1
    rcases D.boundary u hu.2 v huv hvR with hvX | ⟨B, hB, hvB⟩
    · exact hvZ (Or.inl (Or.inl hvX))
    · by_cases hs : (B.ncard : ℝ) ≤ a
      · exact hvZ (Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨B, hB, by simpa [cut, hs] using hvB⟩)))
      · refine huZ (Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨B, hB, ?_⟩)))
        simp only [cut, if_neg hs]
        exact ⟨hu.2, fun huB => Set.disjoint_left.mp (D.region_branch B hB) hu.2 huB,
          v, hvB, huv.symm⟩
  obtain ⟨H', hH', hPH'⟩ := exists_piece_superset (R := D.region \ Y) hP.2.1
    (fun x hx => ⟨hPR hx, fun hy => hP.1 hx (Or.inr hy)⟩)
  refine ⟨H', hH'.1, hH'.2.1, lt_of_lt_of_le hPh (by
    have := Set.ncard_le_ncard hPH' (Set.toFinite _); omega), fun u hu v hv huv hvH => ?_⟩
  by_contra hvY
  exact hvH (hH'.2.2 u hu v ⟨hv, hvY⟩ huv)

/-- Discard branch sets with no neighbour in the region. -/
noncomputable def trim (D : Config G ℓ a b) : Config G ℓ a b := by
  classical
  exact { D with
    branches := D.branches.filter (fun C => (relBoundary G D.region C).Nonempty)
    branch_connected := fun C hC => D.branch_connected C (Finset.mem_filter.mp hC).1
    region_branch := fun C hC => D.region_branch C (Finset.mem_filter.mp hC).1
    branch_disjoint := fun C hC B hB hne => D.branch_disjoint
      (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hB).1 hne
    branch_adjacent := fun C hC B hB hne => D.branch_adjacent C
      (Finset.mem_filter.mp hC).1 B (Finset.mem_filter.mp hB).1 hne
    boundary := by
      intro u hu v huv hv
      rcases D.boundary u hu v huv hv with hx | ⟨C, hC, hvC⟩
      · exact Or.inl hx
      · refine Or.inr ⟨C, Finset.mem_filter.mpr ⟨hC, u, hu, ?_, v, hvC, huv.symm⟩, hvC⟩
        exact fun huC => Set.disjoint_left.mp (D.region_branch C hC) hu huC
    branch_bound := fun C hC => D.branch_bound C (Finset.mem_filter.mp hC).1 }

/-- A configuration whose region is smallest, with every branch set touching the region. -/
lemma exists_minimal (hex : Nonempty (Config G ℓ a b)) :
    ∃ D : Config G ℓ a b, (∀ E : Config G ℓ a b, D.region.ncard ≤ E.region.ncard) ∧
      ∀ C ∈ D.branches, (relBoundary G D.region C).Nonempty := by
  classical
  have hn : ∃ n : ℕ, ∃ D : Config G ℓ a b, D.region.ncard = n := by
    obtain ⟨D⟩ := hex
    exact ⟨_, D, rfl⟩
  obtain ⟨D, hD⟩ := Nat.find_spec hn
  refine ⟨D.trim, fun E => ?_, fun C hC => (Finset.mem_filter.mp hC).2⟩
  change D.region.ncard ≤ E.region.ncard
  rw [hD]
  exact Nat.find_min' hn ⟨E, rfl⟩

lemma branch_bound_mono (D : Config G ℓ a b) {H : Set V} (hH : H ⊆ D.region) :
    ∀ C ∈ D.branches, (C.ncard : ℝ) ≤ a ∨ ((relBoundary G H C).ncard : ℝ) ≤ b := by
  intro C hC
  rcases D.branch_bound C hC with hs | hs
  · exact Or.inl hs
  · exact Or.inr ((Nat.cast_le.mpr (Set.ncard_le_ncard (relBoundary_mono hH))).trans hs)

lemma budget_mono (D : Config G ℓ a b) {H : Set V} (hH : H ⊆ D.region) :
    (H.ncard : ℝ) + (ℓ + 1) * D.discarded.ncard ≤ Fintype.card V := by
  have : (H.ncard : ℝ) ≤ D.region.ncard := mod_cast Set.ncard_le_ncard hH
  linarith [D.budget]

/-- Case 1 (sparse cut): shrink the region to `H`, discarding the cut `Y`. -/
def shrink (D : Config G ℓ a b) (H Y : Set V) (hH : H ⊆ D.region)
    (hc : (G.induce H).Connected) (hh : Fintype.card V < 2 * H.ncard)
    (hb : ∀ u ∈ H, ∀ v ∈ D.region, G.Adj u v → v ∉ H → v ∈ Y)
    (hbudget : (H.ncard : ℝ) + (ℓ + 1) * (D.discarded ∪ Y).ncard ≤ Fintype.card V) :
    Config G ℓ a b where
  region := H
  discarded := D.discarded ∪ Y
  branches := D.branches
  connected := hc
  heavy := hh
  branch_connected := D.branch_connected
  region_branch := fun C hC => (D.region_branch C hC).mono_left hH
  branch_disjoint := D.branch_disjoint
  branch_adjacent := D.branch_adjacent
  boundary := by
    intro u hu v huv hv
    by_cases hvR : v ∈ D.region
    · exact Or.inl (Or.inr (hb u hu v hvR huv hv))
    · rcases D.boundary u (hH hu) v huv hvR with hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inr hx
  budget := hbudget
  branch_bound := D.branch_bound_mono hH

/-- Case 2 (growing a branch set): enlarge the branch set `C` by `A`. -/
noncomputable def absorb (D : Config G ℓ a b) (C : Set V) (hC : C ∈ D.branches) (H A : Set V)
    (hH : H ⊆ D.region \ A) (hA : A ⊆ D.region)
    (hcH : (G.induce H).Connected) (hh : Fintype.card V < 2 * H.ncard)
    (hcA : (G.induce (C ∪ A)).Connected)
    (hb : ∀ u ∈ H, ∀ v ∈ D.region, G.Adj u v → v ∉ H → v ∈ A)
    (hbound : ((relBoundary G H (C ∪ A)).ncard : ℝ) ≤ b) :
    Config G ℓ a b := by
  classical
  have hHR : H ⊆ D.region := fun _ hx => (hH hx).1
  have hsub : D.branches.erase C ⊆ D.branches := Finset.erase_subset C D.branches
  exact {
    region := H
    discarded := D.discarded
    branches := insert (C ∪ A) (D.branches.erase C)
    connected := hcH
    heavy := hh
    branch_connected := (Finset.forall_mem_insert _ _ _).mpr
      ⟨hcA, fun B hB => D.branch_connected B (hsub hB)⟩
    region_branch := (Finset.forall_mem_insert _ _ _).mpr
      ⟨Set.disjoint_union_right.mpr ⟨(D.region_branch C hC).mono_left hHR,
          Set.disjoint_left.mpr fun _ hx => (hH hx).2⟩,
        fun B hB => (D.region_branch B (hsub hB)).mono_left hHR⟩
    branch_disjoint := by
      rw [Finset.coe_insert]
      refine (D.branch_disjoint.mono (Finset.coe_subset.mpr hsub)).insert_of_symmetric
        symmetric_disjoint fun B hB _ => ?_
      obtain ⟨hne, hB⟩ := Finset.mem_erase.mp hB
      exact Set.disjoint_union_left.mpr
        ⟨D.branch_disjoint hC hB hne.symm, (D.region_branch B hB).mono_left hA⟩
    branch_adjacent := adjacent_insert
      (fun B hB E hE => D.branch_adjacent B (hsub hB) E (hsub hE)) fun B hB => by
        obtain ⟨hne, hB⟩ := Finset.mem_erase.mp hB
        obtain ⟨u, hu, v, hv, huv⟩ := D.branch_adjacent C hC B hB hne.symm
        exact ⟨u, Or.inl hu, v, hv, huv⟩
    boundary := by
      intro u hu v huv hv
      by_cases hvR : v ∈ D.region
      · exact Or.inr ⟨C ∪ A, Finset.mem_insert_self _ _, Or.inr (hb u hu v hvR huv hv)⟩
      · rcases D.boundary u (hHR hu) v huv hvR with hx | ⟨B, hB, hvB⟩
        · exact Or.inl hx
        · by_cases he : B = C
          · subst B; exact Or.inr ⟨C ∪ A, Finset.mem_insert_self _ _, Or.inl hvB⟩
          · exact Or.inr ⟨B, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he, hB⟩), hvB⟩
    budget := D.budget_mono hHR
    branch_bound := (Finset.forall_mem_insert _ _ _).mpr
      ⟨Or.inr hbound, fun B hB => D.branch_bound_mono hHR B (hsub hB)⟩ }

/-- Case 3 (new branch set): add the connector `T` as a branch set. -/
noncomputable def addBranch (D : Config G ℓ a b) (H T : Set V) (hH : H ⊆ D.region \ T)
    (hT : T ⊆ D.region) (hcH : (G.induce H).Connected) (hh : Fintype.card V < 2 * H.ncard)
    (hcT : (G.induce T).Connected) (hsize : (T.ncard : ℝ) ≤ a)
    (hb : ∀ u ∈ H, ∀ v ∈ D.region, G.Adj u v → v ∉ H → v ∈ T)
    (hadj : ∀ C ∈ D.branches, ∃ u ∈ T, ∃ v ∈ C, G.Adj u v) :
    Config G ℓ a b := by
  classical
  have hHR : H ⊆ D.region := fun _ hx => (hH hx).1
  exact {
    region := H
    discarded := D.discarded
    branches := insert T D.branches
    connected := hcH
    heavy := hh
    branch_connected := (Finset.forall_mem_insert _ _ _).mpr ⟨hcT, D.branch_connected⟩
    region_branch := (Finset.forall_mem_insert _ _ _).mpr
      ⟨Set.disjoint_left.mpr fun _ hx => (hH hx).2,
        fun C hC => (D.region_branch C hC).mono_left hHR⟩
    branch_disjoint := by
      rw [Finset.coe_insert]
      exact D.branch_disjoint.insert_of_symmetric symmetric_disjoint
        fun C hC _ => (D.region_branch C hC).mono_left hT
    branch_adjacent := adjacent_insert D.branch_adjacent hadj
    boundary := by
      intro u hu v huv hv
      by_cases hvR : v ∈ D.region
      · exact Or.inr ⟨T, Finset.mem_insert_self _ _, hb u hu v hvR huv hv⟩
      · rcases D.boundary u (hHR hu) v huv hvR with hx | ⟨C, hC, hvC⟩
        · exact Or.inl hx
        · exact Or.inr ⟨C, Finset.mem_insert_of_mem hC, hvC⟩
    budget := D.budget_mono hHR
    branch_bound := (Finset.forall_mem_insert _ _ _).mpr ⟨Or.inl hsize, D.branch_bound_mono hHR⟩ }

end Config

end MinorFreeSeparators
