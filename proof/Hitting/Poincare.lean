import proof.Graph.Basic

/-!
# A Poincaré inequality for vertex expanders (`thm:poincare`)

The paper cites [BHT00, Theorem 1]: a `d_G`-Lipschitz function `f` on a connected
graph satisfies `∑ (f v - f̄)² ≤ 2n / (√(1 + ψ) - 1)²`. We prove
`∑ (f v - f̄)² ≤ n (1 + ψ)(2 + ψ) / ψ²` for any `ψ`-vertex expander, which is stronger when
`ψ ≤ 2` (always the case with at least two vertices) and about four times smaller for
small `ψ`.

Proof. Let `m` be a median of `f` and `U = {f ≤ m}`. The set `T r` (`farSet`) of vertices
at distance more than `r` from `U` contains `{f > m + r}`, and its boundary lies in
`T (r - 1) \ T r`, so expansion gives `|T r| ≤ (1 + ψ)^{-r} |T 0|`. Summing
`(f - m)₊² ≤ ∑_{r < f - m} (2r + 1)` over vertices gives
`∑ (f - m)₊² ≤ |T 0| ∑ (2r + 1)(1 + ψ)^{-r} = |T 0| (1 + ψ)(2 + ψ)/ψ²`.
The lower tail is symmetric, and the variance is at most the second moment about `m`.

The separator argument only has a truncated expander (`IsTruncExpander G ℓ L`): sets need
`|∂S| ≥ |S|/ℓ` only while `|∂S| < τ`, where `τ = n/(2Λ)` and `Λ = L + ℓ + 1` (the
`ℓ + 1 + L` of `IsTruncExpander`). The far sets then lose `τ` vertices per step for `⌈L⌉`
steps before shrinking by the factor `ℓ/(ℓ + 1)` (`envelope`), and `poincare_of_trunc` gives
`∑ (f v - f̄)² ≤ n · truncVar ℓ L`. The bound above is its case `ℓ = 1/ψ`, `L = 0`.
-/

namespace MinorFreeSeparators

open Finset

section Sums

/-- `y² ≤ ∑_{r < N, r < y} (2r + 1)` for `0 ≤ y ≤ N`. -/
lemma sq_le_sum_odd {y : ℝ} (hy : 0 ≤ y) (N : ℕ) (hN : y ≤ N) :
    y ^ 2 ≤ ∑ r ∈ range N, (2 * (r : ℝ) + 1) * if (r : ℝ) < y then 1 else 0 := by
  induction N with
  | zero => simp [le_antisymm (by simpa using hN) hy]
  | succ N ih =>
    rcases le_or_gt y N with h | h
    · rw [sum_range_succ]
      have := ih h
      have : 0 ≤ (2 * (N : ℝ) + 1) * if (N : ℝ) < y then 1 else 0 := by positivity
      linarith
    · have hall : ∀ r ∈ range (N + 1), ((2 * (r : ℝ) + 1) * if (r : ℝ) < y then 1 else 0) =
          2 * (r : ℝ) + 1 := by
        intro r hr
        have : (r : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hr)
        rw [if_pos (by linarith), mul_one]
      rw [sum_congr rfl hall]
      have hodd : ∀ M : ℕ, ∑ r ∈ range M, (2 * (r : ℝ) + 1) = (M : ℝ) ^ 2 := by
        intro M
        induction M with
        | zero => simp
        | succ M ihM => rw [sum_range_succ, ihM]; push_cast; ring
      rw [hodd]
      push_cast at hN ⊢
      nlinarith

/-- Partial sums of `∑ (2r + 1) ρ^r = (1 + ρ)/(1 - ρ)²`. -/
lemma sum_odd_mul_pow_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (N : ℕ) :
    ∑ r ∈ range N, (2 * (r : ℝ) + 1) * ρ ^ r ≤ (1 + ρ) / (1 - ρ) ^ 2 := by
  have hd : 0 < (1 - ρ) ^ 2 := by nlinarith
  have key : ∀ N : ℕ, (∑ r ∈ range N, (2 * (r : ℝ) + 1) * ρ ^ r) * (1 - ρ) ^ 2 =
      (1 + ρ) - ρ ^ N * ((2 * N + 1) - (2 * N - 1) * ρ) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, add_mul, ih, pow_succ]
      push_cast
      ring
  rw [le_div_iff₀ hd, key]
  have : 0 ≤ ρ ^ N * ((2 * N + 1) - (2 * N - 1) * ρ) := by
    apply mul_nonneg (pow_nonneg hρ0 N)
    nlinarith
  linarith

/-- The variance is at most the second moment about any point. -/
lemma sum_sq_sub_mean_le {X : Type*} [Fintype X] (f : X → ℝ) (m : ℝ) :
    ∑ x, (f x - (∑ y, f y) / Fintype.card X) ^ 2 ≤ ∑ x, (f x - m) ^ 2 := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simp
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  set μ := (∑ y, f y) / Fintype.card X
  have hμ : ∑ y, f y = Fintype.card X * μ := by simp only [μ]; field_simp
  have h : ∑ x, (f x - m) ^ 2 = ∑ x, (f x - μ) ^ 2 + Fintype.card X * (μ - m) ^ 2 := by
    have e : ∀ x, (f x - m) ^ 2 = (f x - μ) ^ 2 + 2 * (μ - m) * f x - (μ ^ 2 - m ^ 2) := by
      intro x; ring
    simp only [e, sum_sub_distrib, sum_add_distrib, ← mul_sum, hμ, sum_const, card_univ,
      nsmul_eq_mul]
    ring
  rw [h]
  have : 0 ≤ (Fintype.card X : ℝ) * (μ - m) ^ 2 := by positivity
  linarith

end Sums

variable {V : Type*} {G : SimpleGraph V}

/-- A median of `f`: at most half of the vertices lie strictly above it, and at most
half strictly below it. -/
lemma exists_median [Fintype V] [Nonempty V] (f : V → ℝ) :
    ∃ m, 2 * {v | m < f v}.ncard ≤ Fintype.card V ∧ 2 * {v | f v < m}.ncard ≤ Fintype.card V := by
  classical
  have hcompl : ∀ m, {v | m < f v}.ncard + {v | f v ≤ m}.ncard = Fintype.card V := by
    intro m
    rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ, ← Set.ncard_union_eq]
    · congr 1; ext v; simp [lt_or_ge]
    · exact Set.disjoint_left.mpr fun v h1 h2 =>
        (not_le.mpr (show m < f v from h1)) (show f v ≤ m from h2)
  set S := univ.filter fun x => Fintype.card V ≤ 2 * {y | f y ≤ f x}.ncard
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := Finite.exists_max f
    refine ⟨x, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    have : {y | f y ≤ f x} = Set.univ := Set.eq_univ_of_forall hx
    rw [this, Set.ncard_univ, Nat.card_eq_fintype_card]
    omega
  obtain ⟨x0, hx0S, hx0⟩ := S.exists_min_image f hS
  refine ⟨f x0, ?_, ?_⟩
  · have := (mem_filter.mp hx0S).2
    have := hcompl (f x0)
    omega
  by_contra hlt
  push Not at hlt
  have hne : {v | f v < f x0}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hlt
    simp at hlt
  obtain ⟨y, hyF, hy⟩ := Set.exists_max_image _ f (Set.toFinite _) hne
  have hset : {x | f x ≤ f y} = {x | f x < f x0} := by
    ext x
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => h.trans_lt hyF, fun h => hy x h⟩
  have hyS : y ∈ S := mem_filter.mpr ⟨mem_univ _, by rw [hset]; exact hlt.le⟩
  exact absurd (hx0 y hyS) (not_le.mpr hyF)

/-- Vertices at distance more than `r` from every vertex of `U`. -/
def farSet (G : SimpleGraph V) (U : Set V) (r : ℕ) : Set V := {v | ∀ u ∈ U, r < G.dist u v}

lemma farSet_anti (U : Set V) {r s : ℕ} (hrs : r ≤ s) : farSet G U s ⊆ farSet G U r :=
  fun _ hv u hu => lt_of_le_of_lt hrs (hv u hu)

lemma farSet_zero (hG : G.Connected) (U : Set V) : farSet G U 0 = Uᶜ := by
  ext v
  simp only [farSet, Set.mem_setOf_eq, Set.mem_compl_iff, Nat.pos_iff_ne_zero, ne_eq,
    hG.dist_eq_zero_iff]
  exact ⟨fun h hv => h v hv rfl, fun h u hu huv => h (huv ▸ hu)⟩

lemma vertexBoundary_farSet_subset (hG : G.Connected) (U : Set V) (r : ℕ) :
    vertexBoundary G (farSet G U (r + 1)) ⊆ farSet G U r \ farSet G U (r + 1) := by
  rintro v ⟨hv, w, hw, hwv⟩
  refine ⟨fun u hu => ?_, hv⟩
  have h1 := hG.dist_triangle (u := u) (v := v) (w := w)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hwv.symm] at h1
  have := hw u hu
  omega

/-- The bound on `∑_r (2r + 1) |T_r|` for one tail, in units of `τ = |V|/(2Λ)` with
`Λ = L + ℓ + 1` and `R = ⌈L⌉`: the far sets lose `τ` vertices per step for `R` steps, and
shrink by the factor `ℓ/(ℓ + 1)` afterwards. -/
noncomputable def tailBound (ℓ L : ℝ) : ℝ :=
  (L + ℓ + 1) * (⌈L⌉₊ : ℝ) ^ 2 - (⌈L⌉₊ : ℝ) * (⌈L⌉₊ - 1) * (4 * ⌈L⌉₊ + 1) / 6 +
    (L + ℓ + 1 - ⌈L⌉₊) * (ℓ + 1) * (2 * ⌈L⌉₊ + 2 * ℓ + 1)

/-- The variance constant of truncated expanders, `tailBound ℓ L / Λ`. For `L = 0` it is
`(ℓ + 1)(2ℓ + 1)`. -/
noncomputable def truncVar (ℓ L : ℝ) : ℝ := tailBound ℓ L / (L + ℓ + 1)

lemma truncVar_zero (ℓ : ℝ) (hℓ : 0 < ℓ) : truncVar ℓ 0 = (ℓ + 1) * (2 * ℓ + 1) := by
  rw [truncVar, tailBound, Nat.ceil_zero, Nat.cast_zero]
  field_simp
  ring

/-- Rounding `L` up to `⌈L⌉` costs at most `(L + ℓ + 2)/4` in `tailBound`. -/
lemma tailBound_le (ℓ : ℝ) {L : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L) :
    tailBound ℓ L ≤ (L + ℓ + 1) * L ^ 2 - L * (L - 1) * (4 * L + 1) / 6 +
      (ℓ + 1) * (ℓ + 1) * (2 * L + 2 * ℓ + 1) + (L + ℓ + 2) / 4 := by
  have h1 : L ≤ ⌈L⌉₊ := Nat.le_ceil L
  have h2 : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one hL
  obtain ⟨s, hs0, hs1, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ (⌈L⌉₊ : ℝ) = L + s :=
    ⟨⌈L⌉₊ - L, by linarith, by linarith, by ring⟩
  unfold tailBound
  rw [hs]
  have hA : 0 ≤ L + ℓ := by linarith
  nlinarith [mul_nonneg hA (sq_nonneg (s - 1 / 2)), mul_nonneg hs0 (sq_nonneg (s - 1 / 2)),
    mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 1 - s), mul_nonneg (mul_nonneg hs0 hs0)
      (by linarith : (0 : ℝ) ≤ 1 - s), sq_nonneg (s - 3 / 5)]

lemma truncVar_le (ℓ : ℝ) {L : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L) :
    truncVar ℓ L ≤ ((L + ℓ + 1) * L ^ 2 - L * (L - 1) * (4 * L + 1) / 6 +
      (ℓ + 1) * (ℓ + 1) * (2 * L + 2 * ℓ + 1) + (L + ℓ + 2) / 4) / (L + ℓ + 1) :=
  div_le_div_of_nonneg_right (tailBound_le ℓ hℓ hL) (by linarith)

/-- The envelope of the far sets, starting at `Λτ`: linear for `⌈L⌉` steps, geometric
afterwards. -/
noncomputable def envelope (ℓ L τ : ℝ) (r : ℕ) : ℝ :=
  if r ≤ ⌈L⌉₊ then (L + ℓ + 1 - r) * τ
  else (L + ℓ + 1 - ⌈L⌉₊) * τ * (ℓ / (ℓ + 1)) ^ (r - ⌈L⌉₊)

lemma envelope_ceil_add (ℓ L τ : ℝ) (j : ℕ) :
    envelope ℓ L τ (⌈L⌉₊ + j) = (L + ℓ + 1 - ⌈L⌉₊) * τ * (ℓ / (ℓ + 1)) ^ j := by
  unfold envelope
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [if_neg (by omega), Nat.add_sub_cancel_left]

lemma envelope_nonneg {ℓ L τ : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L) (hτ : 0 ≤ τ) (r : ℕ) :
    0 ≤ envelope ℓ L τ r := by
  have hRL : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one hL
  unfold envelope
  split_ifs with h
  · have : (r : ℝ) ≤ ⌈L⌉₊ := by exact_mod_cast h
    exact mul_nonneg (by linarith) hτ
  · exact mul_nonneg (mul_nonneg (by linarith) hτ) (by positivity)

/-- The envelope absorbs both kinds of steps: a loss of the fraction `1/(ℓ + 1)` and a loss
of `τ`. -/
lemma envelope_step {ℓ L τ : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L) (hτ : 0 ≤ τ) (r : ℕ) :
    ℓ * envelope ℓ L τ r ≤ (ℓ + 1) * envelope ℓ L τ (r + 1) ∧
      envelope ℓ L τ r ≤ envelope ℓ L τ (r + 1) + τ := by
  have hLR : L ≤ ⌈L⌉₊ := Nat.le_ceil L
  have hℓ1 : 0 < ℓ + 1 := by linarith
  rcases lt_or_ge r ⌈L⌉₊ with hr | hr
  · have hrL : (r : ℝ) < L := Nat.lt_ceil.mp hr
    unfold envelope
    rw [if_pos hr.le, if_pos (by omega)]
    push_cast
    constructor <;> nlinarith
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
    rw [add_assoc, envelope_ceil_add, envelope_ceil_add, pow_succ,
      ← mul_assoc ((L + ℓ + 1 - ⌈L⌉₊) * τ)]
    -- after `⌈L⌉` steps the envelope is at most `(ℓ + 1)τ`
    have hc : 0 ≤ (L + ℓ + 1 - ⌈L⌉₊) * τ :=
      mul_nonneg (by linarith [Nat.ceil_lt_add_one hL]) hτ
    have hpow : (ℓ / (ℓ + 1)) ^ j ≤ 1 :=
      pow_le_one₀ (by positivity) ((div_le_one hℓ1).mpr (by linarith))
    have hle : (L + ℓ + 1 - ⌈L⌉₊) * τ * (ℓ / (ℓ + 1)) ^ j ≤ (ℓ + 1) * τ :=
      (mul_le_of_le_one_right hc hpow).trans (mul_le_mul_of_nonneg_right (by linarith) hτ)
    generalize (L + ℓ + 1 - ⌈L⌉₊) * τ * (ℓ / (ℓ + 1)) ^ j = y at hle ⊢
    constructor
    · exact le_of_eq (by field_simp)
    · rw [mul_div_assoc', div_add' _ _ _ hℓ1.ne', le_div_iff₀ hℓ1]
      linarith

/-- A sequence starting below `Λτ` that loses `τ` or the fraction `1/(ℓ + 1)` at each step
stays below the envelope. -/
lemma le_envelope {T : ℕ → ℝ} {ℓ L τ : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L) (hτ : 0 ≤ τ)
    (h0 : T 0 ≤ (L + ℓ + 1) * τ)
    (hstep : ∀ r, (ℓ + 1) * T (r + 1) ≤ ℓ * T r ∨ T (r + 1) + τ ≤ T r) (r : ℕ) :
    T r ≤ envelope ℓ L τ r := by
  induction r with
  | zero => simpa [envelope] using h0
  | succ r ih =>
    obtain ⟨h1, h2⟩ := envelope_step hℓ hL hτ r
    rcases hstep r with h | h
    · refine le_of_mul_le_mul_left (h.trans ?_) (by linarith : (0 : ℝ) < ℓ + 1)
      exact (mul_le_mul_of_nonneg_left ih hℓ.le).trans h1
    · linarith

/-- `∑_{r < R} (2r + 1)(Λ - r) = Λ R² - R(R - 1)(4R + 1)/6`. -/
lemma sum_odd_mul_sub (Λ : ℝ) (R : ℕ) :
    ∑ r ∈ range R, (2 * (r : ℝ) + 1) * (Λ - r) =
      Λ * (R : ℝ) ^ 2 - (R : ℝ) * (R - 1) * (4 * R + 1) / 6 := by
  induction R with
  | zero => simp
  | succ R ih => rw [sum_range_succ, ih]; push_cast; ring

/-- The weighted sum of the envelope: `∑_{r < M} (2r + 1) envelope r ≤ τ tailBound ℓ L`. -/
lemma sum_envelope_le {ℓ L τ : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L) (hτ : 0 ≤ τ) (M : ℕ) :
    ∑ r ∈ range M, (2 * (r : ℝ) + 1) * envelope ℓ L τ r ≤ τ * tailBound ℓ L := by
  set R := ⌈L⌉₊
  have hRL : (R : ℝ) < L + 1 := Nat.ceil_lt_add_one hL
  have hℓ1 : 0 < ℓ + 1 := by linarith
  set ρ := ℓ / (ℓ + 1)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by rw [div_lt_one hℓ1]; linarith
  -- extend the sum to `R + M` terms: `R` linear ones and `M` geometric ones
  have h1 : ∑ r ∈ range M, (2 * (r : ℝ) + 1) * envelope ℓ L τ r ≤
      ∑ r ∈ range (R + M), (2 * (r : ℝ) + 1) * envelope ℓ L τ r :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun r _ _ =>
      mul_nonneg (by positivity) (envelope_nonneg hℓ hL hτ r)
  rw [sum_range_add] at h1
  have h2 : ∑ r ∈ range R, (2 * (r : ℝ) + 1) * envelope ℓ L τ r =
      τ * (∑ r ∈ range R, (2 * (r : ℝ) + 1) * (L + ℓ + 1 - r)) := by
    rw [mul_sum]
    refine sum_congr rfl fun r hr => ?_
    unfold envelope
    rw [if_pos (by have := mem_range.mp hr; omega)]
    ring
  have h3 : ∑ j ∈ range M, (2 * ((R + j : ℕ) : ℝ) + 1) * envelope ℓ L τ (R + j) =
      (L + ℓ + 1 - R) * τ * (2 * R * ∑ j ∈ range M, ρ ^ j +
        ∑ j ∈ range M, (2 * (j : ℝ) + 1) * ρ ^ j) := by
    rw [mul_sum, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [envelope_ceil_add]
    push_cast
    ring
  have hgeom : ∑ j ∈ range M, ρ ^ j ≤ ℓ + 1 := by
    rw [range_eq_Ico]
    refine (geom_sum_Ico_le_of_lt_one hρ0 hρ1).trans_eq ?_
    simp only [ρ]
    field_simp
    ring
  have hodd : ∑ j ∈ range M, (2 * (j : ℝ) + 1) * ρ ^ j ≤ (ℓ + 1) * (2 * ℓ + 1) := by
    refine (sum_odd_mul_pow_le hρ0 hρ1 M).trans_eq ?_
    simp only [ρ]
    field_simp
    ring
  have h4 : (L + ℓ + 1 - R) * τ * (2 * R * ∑ j ∈ range M, ρ ^ j +
      ∑ j ∈ range M, (2 * (j : ℝ) + 1) * ρ ^ j) ≤
      (L + ℓ + 1 - R) * τ * (2 * R * (ℓ + 1) + (ℓ + 1) * (2 * ℓ + 1)) := by
    have : 0 ≤ L + ℓ + 1 - R := by linarith
    gcongr
  rw [h2, h3, sum_odd_mul_sub] at h1
  refine h1.trans ?_
  rw [tailBound]
  linarith

/-- One step of the far sets: either they shrink by the factor `ℓ/(ℓ + 1)` or they lose
`τ = |V|/(2Λ)` vertices. -/
lemma farSet_step [Fintype V] (hG : G.Connected) {ℓ L : ℝ} (hℓ : 0 ≤ ℓ) (hL : 0 ≤ L)
    (hexp : IsTruncExpander G ℓ L)
    (U : Set V) (hU : 2 * Uᶜ.ncard ≤ Fintype.card V) (r : ℕ) :
    (ℓ + 1) * ((farSet G U (r + 1)).ncard : ℝ) ≤ ℓ * (farSet G U r).ncard ∨
      ((farSet G U (r + 1)).ncard : ℝ) + Fintype.card V / (2 * (L + ℓ + 1)) ≤
        (farSet G U r).ncard := by
  set T := farSet G U (r + 1)
  have hT0 : T ⊆ Uᶜ := farSet_zero hG U ▸ farSet_anti U (Nat.zero_le _)
  have hexpT := hexp T (le_trans (by have := Set.ncard_le_ncard hT0; omega) hU)
  have hdisj : Disjoint T (vertexBoundary G T) := disjoint_vertexBoundary T
  have hunion : T ∪ vertexBoundary G T ⊆ farSet G U r :=
    Set.union_subset (farSet_anti U (Nat.le_succ r))
      (fun v hv => (vertexBoundary_farSet_subset hG U r hv).1)
  have hcard : (T.ncard : ℝ) + (vertexBoundary G T).ncard ≤ (farSet G U r).ncard := by
    have := Set.ncard_le_ncard hunion
    rw [Set.ncard_union_eq hdisj] at this
    exact_mod_cast this
  rcases hexpT with h | h
  · left
    have : 0 ≤ ℓ * ((vertexBoundary G T).ncard : ℝ) := le_trans (Nat.cast_nonneg _) h
    nlinarith
  · right
    have : (Fintype.card V : ℝ) / (2 * (L + ℓ + 1)) ≤ (vertexBoundary G T).ncard := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith

/-- The upper tail: `∑ (f - m)₊² ≤ τ tailBound ℓ L` with `τ = |V|/(2Λ)`. -/
lemma sum_sq_pos_part_le [Fintype V] (hG : G.Connected) {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L)
    (hexp : IsTruncExpander G ℓ L) (f : V → ℝ) (hf : ∀ u v, f u - f v ≤ G.dist u v) (m : ℝ)
    (hm : 2 * {v | m < f v}.ncard ≤ Fintype.card V) :
    ∑ v, max (f v - m) 0 ^ 2 ≤ Fintype.card V / (2 * (L + ℓ + 1)) * tailBound ℓ L := by
  classical
  set U : Set V := {v | f v ≤ m}
  have hUc : Uᶜ = {v | m < f v} := by ext v; simp [U]
  set τ : ℝ := Fintype.card V / (2 * (L + ℓ + 1))
  have hτ : 0 ≤ τ := by positivity
  -- far sets contain the level sets above `m`
  have hlevel : ∀ r : ℕ, {v | m + r < f v} ⊆ farSet G U r := by
    intro r v (hv : m + r < f v) u (hu : f u ≤ m)
    have := hf v u
    rw [SimpleGraph.dist_comm] at this
    exact_mod_cast (by linarith : (r : ℝ) < G.dist u v)
  have hfar : ∀ r : ℕ, (({v | m + r < f v} : Set V).ncard : ℝ) ≤ envelope ℓ L τ r := by
    intro r
    have h1 : (({v | m + r < f v} : Set V).ncard : ℝ) ≤ (farSet G U r).ncard := by
      exact_mod_cast Set.ncard_le_ncard (hlevel r)
    refine h1.trans (le_envelope (T := fun r => ((farSet G U r).ncard : ℝ)) hℓ hL hτ ?_
      (farSet_step hG hℓ.le hL hexp U (hUc ▸ hm)) r)
    show ((farSet G U 0).ncard : ℝ) ≤ _
    rw [farSet_zero hG, hUc]
    have : (2 * ({v | m < f v} : Set V).ncard : ℝ) ≤ Fintype.card V := by exact_mod_cast hm
    simp only [τ]
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith
  -- truncate the layer-cake sum
  set N : ℕ := ⌈∑ v, max (f v - m) 0⌉₊
  have hN : ∀ v, max (f v - m) 0 ≤ N := fun v =>
    (single_le_sum (fun w _ => le_max_right (f w - m) 0) (mem_univ v)).trans (Nat.le_ceil _)
  have hpt : ∀ v, max (f v - m) 0 ^ 2 ≤
      ∑ r ∈ range N, (2 * (r : ℝ) + 1) * if m + r < f v then 1 else 0 := by
    intro v
    refine (sq_le_sum_odd (le_max_right _ _) N (hN v)).trans (le_of_eq ?_)
    refine sum_congr rfl fun r _ => ?_
    have : (r : ℝ) < max (f v - m) 0 ↔ m + r < f v := by
      rw [lt_max_iff, lt_sub_iff_add_lt', or_iff_left (Nat.cast_nonneg r).not_gt]
    simp only [this]
  have hcount : ∀ r : ℕ, ∑ v, (if m + r < f v then (1 : ℝ) else 0) =
      ({v | m + r < f v} : Set V).ncard := by
    intro r
    rw [sum_boole, Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
  calc ∑ v, max (f v - m) 0 ^ 2
      ≤ ∑ v, ∑ r ∈ range N, (2 * (r : ℝ) + 1) * if m + r < f v then 1 else 0 :=
        sum_le_sum fun v _ => hpt v
    _ = ∑ r ∈ range N, (2 * (r : ℝ) + 1) * ({v | m + r < f v} : Set V).ncard := by
        rw [sum_comm]
        refine sum_congr rfl fun r _ => ?_
        rw [← mul_sum, hcount]
    _ ≤ ∑ r ∈ range N, (2 * (r : ℝ) + 1) * envelope ℓ L τ r :=
        sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hfar r) (by positivity)
    _ ≤ τ * tailBound ℓ L := sum_envelope_le hℓ hL hτ N

/-- **Poincaré inequality** for truncated expanders: if `G` is a connected truncated expander
at scale `ℓ` with slack `L` and `f` is `1`-Lipschitz for the graph distance, then
`∑_v (f v - f̄)² ≤ n · truncVar ℓ L`. -/
theorem poincare_of_trunc [Fintype V] (hG : G.Connected) {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L)
    (hexp : IsTruncExpander G ℓ L) (f : V → ℝ) (hf : ∀ u v, f u - f v ≤ G.dist u v) :
    ∑ v, (f v - (∑ u, f u) / Fintype.card V) ^ 2 ≤ Fintype.card V * truncVar ℓ L := by
  have := hG.nonempty
  obtain ⟨m, hm1, hm2⟩ := exists_median f
  have hup := sum_sq_pos_part_le hG hℓ hL hexp f hf m hm1
  have hlow := sum_sq_pos_part_le hG hℓ hL hexp (fun v => -f v)
    (fun u v => by have := hf v u; rw [SimpleGraph.dist_comm] at this; linarith) (-m)
    (by simpa [neg_lt_neg_iff] using hm2)
  have hsplit : ∀ v, (f v - m) ^ 2 = max (f v - m) 0 ^ 2 + max (-f v - -m) 0 ^ 2 := by
    intro v
    rcases le_total (f v) m with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have he : Fintype.card V * truncVar ℓ L =
      2 * (Fintype.card V / (2 * (L + ℓ + 1)) * tailBound ℓ L) := by
    rw [truncVar]; field_simp
  calc ∑ v, (f v - (∑ u, f u) / Fintype.card V) ^ 2 ≤ ∑ v, (f v - m) ^ 2 :=
        sum_sq_sub_mean_le f m
    _ = ∑ v, max (f v - m) 0 ^ 2 + ∑ v, max (-f v - -m) 0 ^ 2 := by
        rw [← sum_add_distrib]; exact sum_congr rfl fun v _ => hsplit v
    _ ≤ _ := by rw [he]; linarith

/-- **Poincaré inequality** (`thm:poincare`). If `G` is a connected `ψ`-vertex expander and
`f` is `1`-Lipschitz for the graph distance, then `∑_v (f v - f̄)² ≤ n (1 + ψ)(2 + ψ) / ψ²`. -/
theorem poincare [Fintype V] (hG : G.Connected) {ψ : ℝ} (hψ : 0 < ψ)
    (hexp : IsVertexExpander G ψ) (f : V → ℝ) (hf : ∀ u v, f u - f v ≤ G.dist u v) :
    ∑ v, (f v - (∑ u, f u) / Fintype.card V) ^ 2 ≤
      Fintype.card V * ((1 + ψ) * (2 + ψ) / ψ ^ 2) := by
  have h := poincare_of_trunc hG (by positivity) le_rfl (hexp.isTruncExpander hψ) f hf
  rw [truncVar_zero _ (by positivity)] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  field_simp

end MinorFreeSeparators
