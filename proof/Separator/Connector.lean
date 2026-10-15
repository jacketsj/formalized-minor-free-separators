import proof.Hitting.HittingWalk
import proof.Separator.Growth

/-!
# The connector of the separator argument

This is Case 3 of the algorithm: `ShortTree` followed by the extension by shortest paths
(`cor:connector` and `clm:n/h-size` of the paper, in the form used here).

In the separator argument the region `H` is a truncated expander at scale `ℓ`, and around
each attachment set `U_i` the balls `B(U_i, r)` grow by at least `β` vertices per layer while
they have fewer than `S` vertices. Ranking the vertices by distance from `U_i`, the tent
measure `ν_i` gives the vertex of rank `j < S` weight proportional to `S - j`
(`exists_tent_measure`). We run the hitting walk for `ν_1, …, ν_q` and attach a shortest
path from the visited point of each `ν_i` back to `U_i`. The visited point has law `ν_i` on
average, so the paths cost on average about `S/(3β) + 1/2` vertices each. Among measures
with the same `∑ ν²` (which controls the walk), the tent measure has the least mean
distance; the uniform measure on the same number of closest vertices costs `9/8` as much,
and the paper attaches paths of the full radius.

The expansion of `H` also makes the balls grow by the fraction `1/ℓ` per layer once they
have about `βℓ` vertices, so the mean distance is then only logarithmic in `S/(βℓ)`
(`exists_tent_measure_exp`, using the potential of `proof/Separator/Growth.lean`).
-/

namespace MinorFreeSeparators

open Finset

variable {W : Type*} {H : SimpleGraph W}

/-- The ball `B(U, r)`: vertices at distance at most `r` from `U`. (`H.dist` is `0` between
vertices in different components; `H` is connected wherever balls are used.) -/
def ball (H : SimpleGraph W) (U : Set W) (r : ℕ) : Set W := {v | ∃ u ∈ U, H.dist u v ≤ r}

/-- The distance from `U` (zero when `U` is empty). -/
noncomputable def setDist (H : SimpleGraph W) (U : Set W) (v : W) : ℕ :=
  sInf ((fun u => H.dist u v) '' U)

lemma exists_setDist {U : Set W} (hU : U.Nonempty) (v : W) :
    ∃ u ∈ U, H.dist u v = setDist H U v :=
  Nat.sInf_mem (hU.image _)

lemma setDist_le {U : Set W} {u v : W} (hu : u ∈ U) : setDist H U v ≤ H.dist u v :=
  Nat.sInf_le ⟨u, hu, rfl⟩

lemma mem_ball_iff {U : Set W} (hU : U.Nonempty) {v : W} {r : ℕ} :
    v ∈ ball H U r ↔ setDist H U v ≤ r := by
  constructor
  · rintro ⟨u, hu, h⟩; exact (setDist_le hu).trans h
  · intro h
    obtain ⟨u, hu, he⟩ := exists_setDist (H := H) hU v
    exact ⟨u, hu, he ▸ h⟩

lemma ball_mono (U : Set W) {r r' : ℕ} (h : r ≤ r') : ball H U r ⊆ ball H U r' :=
  fun _ ⟨u, hu, hd⟩ => ⟨u, hu, hd.trans h⟩

lemma subset_ball (U : Set W) (r : ℕ) : U ⊆ ball H U r :=
  fun u hu => ⟨u, hu, by simp⟩

lemma vertexBoundary_ball_subset (hH : H.Connected) (U : Set W) (r : ℕ) :
    vertexBoundary H (ball H U r) ⊆ ball H U (r + 1) := by
  rintro v ⟨-, w, ⟨u, hu, hw⟩, hwv⟩
  refine ⟨u, hu, ?_⟩
  have h1 := hH.dist_triangle (u := u) (v := w) (w := v)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hwv] at h1
  omega

/-- Every vertex of a ball is reached from `U` by a walk inside the ball. -/
lemma exists_walk_in_ball (hH : H.Connected) {U : Set W} {r : ℕ} {y : W}
    (hy : y ∈ ball H U r) : ∃ u ∈ U, ∃ p : H.Walk u y, ∀ w ∈ p.support, w ∈ ball H U r := by
  classical
  obtain ⟨u, hu, hd⟩ := hy
  obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist u y
  refine ⟨u, hu, p, fun w hw => ⟨u, hu, ?_⟩⟩
  calc H.dist u w ≤ (p.takeUntil w hw).length := SimpleGraph.dist_le _
    _ ≤ p.length := p.length_takeUntil_le hw
    _ = H.dist u y := hp
    _ ≤ r := hd

variable [Fintype W]

/-- Balls that grow by `β` per layer while smaller than `s` reach size `min s (1 + rβ)`. -/
lemma min_le_ncard_ball (hH : H.Connected) {U : Set W} (hU : U.Nonempty) {s β : ℕ}
    (hgrow : ∀ r, (ball H U r).ncard < s → β ≤ (vertexBoundary H (ball H U r)).ncard) (r : ℕ) :
    min s (1 + r * β) ≤ (ball H U r).ncard := by
  induction r with
  | zero =>
    have := Set.ncard_le_ncard (subset_ball (H := H) U 0) (Set.toFinite _)
    have := hU.ncard_pos (Set.toFinite _)
    simp only [zero_mul, add_zero]
    omega
  | succ r ih =>
    have hsub := ball_mono (H := H) U (show r ≤ r + 1 by omega)
    rcases Nat.lt_or_ge (ball H U r).ncard s with hlt | hge
    · have hb := hgrow r hlt
      have hdisj := disjoint_vertexBoundary (G := H) (ball H U r)
      have hunion : ball H U r ∪ vertexBoundary H (ball H U r) ⊆ ball H U (r + 1) :=
        Set.union_subset hsub (vertexBoundary_ball_subset hH U r)
      have hc := Set.ncard_le_ncard hunion (Set.toFinite _)
      rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)] at hc
      have ih' : 1 + r * β ≤ (ball H U r).ncard := by
        rcases le_total s (1 + r * β) with h | h
        · rw [min_eq_left h] at ih; omega
        · rwa [min_eq_right h] at ih
      have : (r + 1) * β = r * β + β := by ring
      rw [this]
      omega
    · have := Set.ncard_le_ncard hsub (Set.toFinite _)
      omega

/-- `2β (t c - β t (t - 1)/2) ≤ c (c + β) + β²/4` for all `t`. With `c = s - 1` this bounds
the total distance of the `s` closest vertices when the first `t` layers have at least `β`
vertices each. -/
lemma layer_sum_le (c β t : ℝ) :
    2 * β * (t * c - β * t * (t - 1) / 2) ≤ c * (c + β) + β ^ 2 / 4 := by
  nlinarith [sq_nonneg (c - β * t + β / 2)]

/-- The `s` vertices closest to `U`, by layers: if `r₀` is the first radius with
`|B(U, r₀)| ≥ s`, some set of `s` vertices has total distance `∑_{r < r₀} (s - |B(U, r)|)`
from `U`. -/
lemma exists_close_set_layers [DecidableEq W] {U : Set W} (hU : U.Nonempty) {s : ℕ}
    (hex : ∃ r, s ≤ (ball H U r).ncard) :
    ∃ X : Finset W, ∃ r₀, X.card = s ∧ (∀ r, s ≤ (ball H U r).ncard → r₀ ≤ r) ∧
      (∀ r < r₀, (ball H U r).ncard < s) ∧
      ∑ v ∈ X, (setDist H U v : ℝ) = ∑ r ∈ range r₀, ((s : ℝ) - (ball H U r).ncard) := by
  classical
  have hc : ∀ S : Set W, S.toFinset.card = S.ncard := fun S => by
    rw [Set.ncard_eq_toFinset_card']
  set r₀ := Nat.find hex
  have hr₀ : s ≤ (ball H U r₀).ncard := Nat.find_spec hex
  have hsmall : ∀ r < r₀, (ball H U r).ncard < s := fun r hr => not_le.mp (Nat.find_min hex hr)
  -- `X` lies between the inner ball `I` (all of it is taken) and the outer ball `O`
  set I : Finset W := if r₀ = 0 then ∅ else (ball H U (r₀ - 1)).toFinset
  set O : Finset W := (ball H U r₀).toFinset
  have hIO : I ⊆ O := by
    simp only [I, O]
    split_ifs
    · exact Finset.empty_subset _
    · exact Set.toFinset_subset_toFinset.mpr (ball_mono U (Nat.sub_le r₀ 1))
  have hIs : I.card ≤ s := by
    simp only [I]
    split_ifs with h
    · simp
    · rw [hc]; exact (hsmall (r₀ - 1) (by omega)).le
  have hsO : s ≤ O.card := by simp only [O]; rw [hc]; exact hr₀
  obtain ⟨X, hIX, hXO, hXcard⟩ := Finset.exists_subsuperset_card_eq hIO hIs hsO
  refine ⟨X, r₀, hXcard, fun r hr => Nat.find_min' hex hr, hsmall, ?_⟩
  have hXball : ∀ v ∈ X, setDist H U v ≤ r₀ := fun v hv =>
    (mem_ball_iff hU).mp (Set.mem_toFinset.mp (hXO hv))
  -- layer cake: `d(v) = #{r < r₀ : r < d(v)}`
  have hcake : ∀ v ∈ X, (setDist H U v : ℝ) =
      ∑ r ∈ range r₀, if r < setDist H U v then (1 : ℝ) else 0 := by
    intro v hv
    have hd := hXball v hv
    rw [sum_boole]
    have : (range r₀).filter (fun r => r < setDist H U v) = range (setDist H U v) := by
      ext r; simp only [mem_filter, mem_range]; omega
    rw [this, card_range]
  have hlayer : ∀ r ∈ range r₀, ((X.filter fun v => r < setDist H U v).card : ℝ) =
      (s : ℝ) - (ball H U r).ncard := by
    intro r hr
    have hr₀' := mem_range.mp hr
    set B := (ball H U r).toFinset
    have hBX : B ⊆ X := by
      intro v hv
      apply hIX
      simp only [I, if_neg (show r₀ ≠ 0 by omega)]
      exact Set.toFinset_subset_toFinset.mpr (ball_mono U (by omega)) hv
    have hfilt : X.filter (fun v => r < setDist H U v) = X \ B := by
      ext v
      simp only [mem_filter, mem_sdiff, B, Set.mem_toFinset, mem_ball_iff hU, not_le]
    have hBs : B.card ≤ s := hXcard ▸ card_le_card hBX
    rw [hfilt, card_sdiff_of_subset hBX, hXcard, Nat.cast_sub hBs]
    simp only [B, hc]
  calc ∑ v ∈ X, (setDist H U v : ℝ)
      = ∑ v ∈ X, ∑ r ∈ range r₀, if r < setDist H U v then (1 : ℝ) else 0 := by
        rw [sum_congr rfl hcake]
    _ = ∑ r ∈ range r₀, ((X.filter fun v => r < setDist H U v).card : ℝ) := by
        rw [sum_comm]
        exact sum_congr rfl fun r _ => by rw [sum_boole]
    _ = _ := sum_congr rfl hlayer

/-- The `s` vertices closest to `U` have total distance at most
`((s - 1)(s - 1 + β) + β²/4) / (2β)` when the balls grow by at least `β ≥ 1` per layer while
they have fewer than `s` vertices. -/
lemma exists_close_set [DecidableEq W] (hH : H.Connected) {U : Set W} (hU : U.Nonempty)
    {s β : ℕ} (hβ : 1 ≤ β) (hgrow : ∀ r, (ball H U r).ncard < s →
      β ≤ (vertexBoundary H (ball H U r)).ncard) :
    ∃ X : Finset W, X.card = s ∧
      2 * β * ∑ v ∈ X, (setDist H U v : ℝ) ≤ (s - 1) * (s - 1 + β) + β ^ 2 / 4 := by
  have hbig : s ≤ (ball H U s).ncard := by
    have := min_le_ncard_ball hH hU hgrow s
    have : s ≤ 1 + s * β := by nlinarith
    omega
  obtain ⟨X, r₀, hXcard, -, hsmall, hsum⟩ := exists_close_set_layers hU ⟨s, hbig⟩
  refine ⟨X, hXcard, ?_⟩
  -- each layer `r < r₀` misses at most `s - 1 - rβ` of the `s` vertices
  have hlayer : ∀ r ∈ range r₀, (s : ℝ) - (ball H U r).ncard ≤ (s - 1 : ℝ) - r * β := by
    intro r hr
    have hb := min_le_ncard_ball hH hU hgrow r
    have hlt := hsmall r (mem_range.mp hr)
    have : 1 + r * β ≤ (ball H U r).ncard := by
      rcases le_total s (1 + r * β) with h | h
      · rw [min_eq_left h] at hb; omega
      · rwa [min_eq_right h] at hb
    have : (1 : ℝ) + r * β ≤ (ball H U r).ncard := by exact_mod_cast this
    linarith
  have htot : ∑ r ∈ range r₀, ((s - 1 : ℝ) - r * β) =
      r₀ * (s - 1) - β * r₀ * (r₀ - 1) / 2 := by
    have h := Finset.sum_range_id_mul_two r₀
    have h' : (∑ r ∈ range r₀, (r : ℝ)) * 2 = r₀ * ((r₀ - 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, ← Nat.cast_ofNat, ← Nat.cast_mul, h, Nat.cast_mul]
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_mul]
    rcases Nat.eq_zero_or_pos r₀ with h0 | hpos
    · rw [h0]; simp
    · rw [Nat.cast_sub hpos] at h'
      push_cast at h'
      linear_combination (-(β : ℝ) / 2) * h'
  calc 2 * β * ∑ v ∈ X, (setDist H U v : ℝ)
      ≤ 2 * β * ∑ r ∈ range r₀, ((s - 1 : ℝ) - r * β) := by
        rw [hsum]
        exact mul_le_mul_of_nonneg_left (sum_le_sum hlayer) (by positivity)
    _ = 2 * β * (r₀ * (s - 1) - β * r₀ * (r₀ - 1) / 2) := by rw [htot]
    _ ≤ (s - 1) * (s - 1 + β) + β ^ 2 / 4 := layer_sum_le _ _ _

/-- The `s` vertices closest to `U` have total distance at most
`∑_{r < M} (s - min(s, |B(U, r)|))` for any `M` with `|B(U, M)| ≥ s`. -/
lemma exists_close_layers [DecidableEq W] {U : Set W} (hU : U.Nonempty) {s M : ℕ}
    (hM : s ≤ (ball H U M).ncard) :
    ∃ X : Finset W, X.card = s ∧ ∑ v ∈ X, (setDist H U v : ℝ) ≤
      ∑ r ∈ range M, ((s : ℝ) - (min s (ball H U r).ncard : ℕ)) := by
  obtain ⟨X, r₀, hXcard, hmin, hsmall, hsum⟩ := exists_close_set_layers hU ⟨M, hM⟩
  refine ⟨X, hXcard, ?_⟩
  rw [hsum]
  calc ∑ r ∈ range r₀, ((s : ℝ) - (ball H U r).ncard)
      = ∑ r ∈ range r₀, ((s : ℝ) - (min s (ball H U r).ncard : ℕ)) :=
        sum_congr rfl fun r hr => by rw [min_eq_right (hsmall r (mem_range.mp hr)).le]
    _ ≤ _ := by
        refine sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (hmin M hM))
          fun r _ _ => ?_
        have : ((min s (ball H U r).ncard : ℕ) : ℝ) ≤ s := by exact_mod_cast min_le_left _ _
        linarith

/-- `∑_{t < S} (t + 1 - min(t + 1, g)) = (S - min(S, g))(S - min(S, g) + 1)/2`. -/
lemma sum_range_sub_min (S g : ℕ) :
    ∑ t ∈ range S, (((t : ℝ) + 1) - (min (t + 1) g : ℕ)) =
      ((S : ℝ) - (min S g : ℕ)) * ((S : ℝ) - (min S g : ℕ) + 1) / 2 := by
  induction S with
  | zero => simp
  | succ S ih =>
    rw [sum_range_succ, ih]
    rcases le_total (S + 1) g with h | h
    · rw [min_eq_left h, min_eq_left (by omega : S ≤ g)]; push_cast; ring
    · rw [min_eq_right h]
      rcases le_total S g with h' | h'
      · have hg : g = S + 1 ∨ g = S := by omega
        rcases hg with rfl | rfl
        · rw [min_eq_left h']; push_cast; ring
        · rw [min_self]; push_cast; ring
      · rw [min_eq_right h']; push_cast; ring

/-- `∑_{t < S} (t + 1) = S(S+1)/2`. -/
lemma sum_range_add_one (S : ℕ) : ∑ t ∈ range S, ((t : ℝ) + 1) = S * (S + 1) / 2 := by
  induction S with
  | zero => simp
  | succ S ih => rw [sum_range_succ, ih]; push_cast; ring

/-- `∑_{t < S} (t(t + β) + β²/4)`, the total distance of the tent measure (up to a factor). -/
lemma sum_range_tent (S : ℕ) (β : ℝ) : ∑ t ∈ range S, ((t : ℝ) * (t + β) + β ^ 2 / 4) =
    ((S : ℝ) - 1) * S * (2 * S - 1) / 6 + β * S * (S - 1) / 2 + S * β ^ 2 / 4 := by
  induction S with
  | zero => simp
  | succ S ih => rw [sum_range_succ, ih]; push_cast; ring

/-- `∑_{a, b < S} min(a + 1, b + 1) = S(S+1)(2S+1)/6`. -/
lemma sum_range_min (S : ℕ) : ∑ a ∈ range S, ∑ b ∈ range S, min ((a : ℝ) + 1) ((b : ℝ) + 1) =
    S * (S + 1) * (2 * S + 1) / 6 := by
  induction S with
  | zero => simp
  | succ S ih =>
    have hrow : ∀ b ∈ range S, min ((S : ℝ) + 1) ((b : ℝ) + 1) = b + 1 := fun b hb =>
      min_eq_right (by have : (b : ℝ) < S := (by exact_mod_cast mem_range.mp hb); linarith)
    have hcol : ∀ a ∈ range S, min ((a : ℝ) + 1) ((S : ℝ) + 1) = a + 1 := fun a ha =>
      min_eq_left (by have : (a : ℝ) < S := (by exact_mod_cast mem_range.mp ha); linarith)
    simp only [sum_range_succ, sum_add_distrib, min_self]
    rw [ih, sum_congr rfl hcol, sum_congr rfl hrow, sum_range_add_one]
    push_cast; ring

/-- The average of the uniform measures on sets `X_t` of sizes `t + 1` (`t < S`), weighted by
`t + 1`: total mass `1`, `∑ ν² ≤ 2(2S+1)/(3S(S+1))`, and averages
`∑ ν f = (∑_t ∑_{v ∈ X_t} f v) / (S(S+1)/2)`. -/
lemma tent_measure_of_sets [DecidableEq W] {S : ℕ} (hS : 1 ≤ S) (X : ℕ → Finset W)
    (hXcard : ∀ t ∈ range S, (X t).card = t + 1) :
    ∃ ν : W → ℝ, (∀ x, 0 ≤ ν x) ∧ ∑ x, ν x = 1 ∧
      3 * S * (S + 1) * ∑ x, ν x ^ 2 ≤ 2 * (2 * S + 1) ∧
      ∀ f : W → ℝ, ∑ x, ν x * f x = (∑ t ∈ range S, ∑ v ∈ X t, f v) / (S * (S + 1) / 2) := by
  classical
  have hS0 : (0 : ℝ) < S := by exact_mod_cast hS
  set Z : ℝ := S * (S + 1) / 2 with hZ
  have hZ0 : 0 < Z := by positivity
  set ind : ℕ → W → ℝ := fun t x => if x ∈ X t then 1 else 0 with hind_def
  set ν : W → ℝ := fun x => (∑ t ∈ range S, ind t x) / Z with hν_def
  have hind : ∀ t x, 0 ≤ ind t x := fun t x => by simp only [ind]; split_ifs <;> norm_num
  have hcount : ∀ t, ∑ x, ind t x = (X t).card := by
    intro t; simp [ind]
  have hpair : ∀ t t', ∑ x, ind t x * ind t' x = (X t ∩ X t').card := by
    intro t t'
    have e : ∀ x, ind t x * ind t' x = if x ∈ X t ∩ X t' then 1 else 0 := by
      intro x; simp only [ind, mem_inter]; split_ifs <;> simp_all
    rw [sum_congr rfl fun x _ => e x, sum_boole]
    congr 2
    ext x; simp
  refine ⟨ν, fun x => div_nonneg (sum_nonneg fun t _ => hind t x) hZ0.le, ?_, ?_, ?_⟩
  · -- total mass
    simp only [ν, ← sum_div]
    rw [sum_comm, sum_congr rfl fun t _ => hcount t, div_eq_one_iff_eq hZ0.ne',
      sum_congr rfl fun t ht => by rw [hXcard t ht], hZ, ← sum_range_add_one]
    push_cast; rfl
  · -- the sum of squares
    have hsq : ∑ x, ν x ^ 2 =
        (∑ t ∈ range S, ∑ t' ∈ range S, ((X t ∩ X t').card : ℝ)) / Z ^ 2 := by
      have e1 : ∀ x, ν x ^ 2 = (∑ t ∈ range S, ∑ t' ∈ range S, ind t x * ind t' x) / Z ^ 2 := by
        intro x; simp only [ν]; rw [div_pow, sq, sum_mul_sum]
      rw [sum_congr rfl fun x _ => e1 x, ← sum_div]
      congr 1
      rw [sum_comm]
      refine sum_congr rfl fun t _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun t' _ => hpair t t'
    have hle : ∑ t ∈ range S, ∑ t' ∈ range S, ((X t ∩ X t').card : ℝ) ≤
        S * (S + 1) * (2 * S + 1) / 6 := by
      rw [← sum_range_min]
      refine sum_le_sum fun t ht => sum_le_sum fun t' ht' => ?_
      have h1 := card_le_card (inter_subset_left (s₁ := X t) (s₂ := X t'))
      have h2 := card_le_card (inter_subset_right (s₁ := X t) (s₂ := X t'))
      rw [hXcard t ht] at h1
      rw [hXcard t' ht'] at h2
      refine le_min ?_ ?_ <;> [exact_mod_cast h1; exact_mod_cast h2]
    rw [hsq, mul_div_assoc', div_le_iff₀ (by positivity), hZ]
    nlinarith
  · -- averages
    intro f
    simp only [ν, div_mul_eq_mul_div, ← sum_div, sum_mul]
    rw [sum_comm]
    congr 1
    refine sum_congr rfl fun t _ => ?_
    simp [ind]

/-- **The tent measure.** Averaging the uniform measures on the `t` closest vertices to `U`,
weighted by `t = 1, …, S`, gives a measure with `∑ ν² ≤ 2(2S+1)/(3S(S+1)) ≈ 4/(3S)` and
mean distance from `U` about `S/(3β) + 1/2`: about `8/9` of the uniform measure with the
same `∑ ν²`. Its weight decreases linearly in the rank of a vertex by distance. -/
lemma exists_tent_measure [DecidableEq W] (hH : H.Connected) {U : Set W} (hU : U.Nonempty)
    {S β : ℕ} (hS : 1 ≤ S) (hβ : 1 ≤ β) (hgrow : ∀ r, (ball H U r).ncard < S →
      β ≤ (vertexBoundary H (ball H U r)).ncard) :
    ∃ ν : W → ℝ, (∀ x, 0 ≤ ν x) ∧ ∑ x, ν x = 1 ∧
      3 * S * (S + 1) * ∑ x, ν x ^ 2 ≤ 2 * (2 * S + 1) ∧
      ∑ x, ν x * setDist H U x ≤
        ((S - 1) * (2 * S - 1) / 6 + β * (S - 1) / 2 + β ^ 2 / 4) / (β * (S + 1)) := by
  classical
  have hclose : ∀ t ∈ range S, ∃ X : Finset W, X.card = t + 1 ∧
      2 * β * ∑ v ∈ X, (setDist H U v : ℝ) ≤ (t : ℝ) * (t + β) + β ^ 2 / 4 := by
    intro t ht
    obtain ⟨X, hX, hXs⟩ := exists_close_set (s := t + 1) hH hU hβ fun r hr =>
      hgrow r (lt_of_lt_of_le hr (by have := mem_range.mp ht; omega))
    refine ⟨X, hX, hXs.trans (le_of_eq ?_)⟩
    push_cast; ring
  choose! X hXcard hXsum using hclose
  obtain ⟨ν, hν0, hν1, hνsq, hνf⟩ := tent_measure_of_sets hS X hXcard
  refine ⟨ν, hν0, hν1, hνsq, ?_⟩
  have hS0 : (0 : ℝ) < S := by exact_mod_cast hS
  have hβ0 : (0 : ℝ) < β := by exact_mod_cast hβ
  have htot : 2 * β * ∑ t ∈ range S, ∑ v ∈ X t, (setDist H U v : ℝ) ≤
      ((S : ℝ) - 1) * S * (2 * S - 1) / 6 + β * S * (S - 1) / 2 + S * β ^ 2 / 4 := by
    rw [← sum_range_tent, mul_sum]
    exact sum_le_sum hXsum
  rw [hνf, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **The tent measure in an expander.** If moreover `H` is a truncated expander at scale `ℓ`
with slack `L`, `2S ≤ |V(H)|` and `2(L + ℓ + 1)τ ≤ |V(H)|`, the balls also grow by the
fraction `1/ℓ` or by `τ`, and the mean distance is at most `expPath S β ℓ τ`. -/
lemma exists_tent_measure_exp [DecidableEq W] (hH : H.Connected) {U : Set W} (hU : U.Nonempty)
    {S β : ℕ} (hS : 1 ≤ S) (hβ : 1 ≤ β) (hgrow : ∀ r, (ball H U r).ncard < S →
      β ≤ (vertexBoundary H (ball H U r)).ncard)
    {ℓ L τ : ℝ} (hℓ : 0 < ℓ) (hexp : IsTruncExpander H ℓ L) (h2S : 2 * S ≤ Fintype.card W)
    (hτ : 0 < τ) (hτW : 2 * (L + ℓ + 1) * τ ≤ Fintype.card W) (hu : 1 ≤ β * ℓ)
    (hβS : β * (ℓ + 1) ≤ S) (hβτ : β * (ℓ + 1) ≤ (ℓ + 1 / 2) * τ) :
    ∃ ν : W → ℝ, (∀ x, 0 ≤ ν x) ∧ ∑ x, ν x = 1 ∧
      3 * S * (S + 1) * ∑ x, ν x ^ 2 ≤ 2 * (2 * S + 1) ∧
      ∑ x, ν x * setDist H U x ≤ expPath S β ℓ τ := by
  classical
  have hbig : S ≤ (ball H U S).ncard := by
    have := min_le_ncard_ball hH hU hgrow S
    have : S ≤ 1 + S * β := by nlinarith
    omega
  have hclose : ∀ t ∈ range S, ∃ X : Finset W, X.card = t + 1 ∧
      ∑ v ∈ X, (setDist H U v : ℝ) ≤
        ∑ r ∈ range S, (((t + 1 : ℕ) : ℝ) - (min (t + 1) (ball H U r).ncard : ℕ)) := by
    intro t ht
    exact exists_close_layers hU (le_trans (by have := mem_range.mp ht; omega) hbig)
  choose! X hXcard hXsum using hclose
  obtain ⟨ν, hν0, hν1, hνsq, hνf⟩ := tent_measure_of_sets hS X hXcard
  refine ⟨ν, hν0, hν1, hνsq, ?_⟩
  have hS0 : (0 : ℝ) < S := by exact_mod_cast hS
  -- the capped ball sizes
  set x : ℕ → ℝ := fun r => ((min S (ball H U r).ncard : ℕ) : ℝ) with hx
  have htot : ∑ t ∈ range S, ∑ v ∈ X t, (setDist H U v : ℝ) ≤
      ∑ r ∈ range S, ((S : ℝ) - x r) * ((S : ℝ) - x r + 1) / 2 := by
    calc ∑ t ∈ range S, ∑ v ∈ X t, (setDist H U v : ℝ)
        ≤ ∑ t ∈ range S, ∑ r ∈ range S,
            (((t + 1 : ℕ) : ℝ) - (min (t + 1) (ball H U r).ncard : ℕ)) := sum_le_sum hXsum
      _ = ∑ r ∈ range S, ∑ t ∈ range S,
            (((t : ℝ) + 1) - (min (t + 1) (ball H U r).ncard : ℕ)) := by
          rw [sum_comm]; push_cast; rfl
      _ = _ := sum_congr rfl fun r _ => sum_range_sub_min S _
  have hmean : ∑ x', ν x' * setDist H U x' ≤ ∑ r ∈ range S, tentTail S (x r) := by
    rw [hνf, div_le_iff₀ (by positivity), sum_mul]
    refine htot.trans (le_of_eq (sum_congr rfl fun r _ => ?_))
    unfold tentTail
    field_simp
  refine hmean.trans (tent_sum_le_expPath (by exact_mod_cast hS) (by exact_mod_cast hβ) hℓ hτ hu
    hβS hβτ x ?_ ?_ ?_ ?_ S)
  · -- `x 0 ≥ 1`
    simp only [x]
    have h1 := Set.ncard_le_ncard (subset_ball (H := H) U 0) (Set.toFinite _)
    have h2 := hU.ncard_pos (Set.toFinite _)
    have : 1 ≤ min S (ball H U 0).ncard := le_min hS (by omega)
    exact_mod_cast this
  · intro r; simp only [x]; exact_mod_cast min_le_left _ _
  · intro r; simp only [x]
    exact_mod_cast min_le_min_left S (Set.ncard_le_ncard (ball_mono U (Nat.le_succ r))
      (Set.toFinite _))
  · -- growth
    intro r hr
    simp only [x] at hr ⊢
    have hlt : (ball H U r).ncard < S := by
      by_contra hc; push Not at hc
      rw [min_eq_left hc] at hr; exact lt_irrefl _ hr
    rw [min_eq_right hlt.le]
    set B := ball H U r
    set D := vertexBoundary H B
    have hdisj := disjoint_vertexBoundary (G := H) B
    have hunion : B ∪ D ⊆ ball H U (r + 1) :=
      Set.union_subset (ball_mono U (Nat.le_succ r)) (vertexBoundary_ball_subset hH U r)
    have hc := Set.ncard_le_ncard hunion (Set.toFinite _)
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)] at hc
    have hβD := hgrow r hlt
    rcases le_total S (ball H U (r + 1)).ncard with h | h
    · left; rw [min_eq_left h]
    right
    rw [min_eq_right h]
    have hc' : (B.ncard : ℝ) + D.ncard ≤ (ball H U (r + 1)).ncard := by exact_mod_cast hc
    have hβD' : (β : ℝ) ≤ D.ncard := by exact_mod_cast hβD
    refine ⟨by linarith, ?_⟩
    have h2B : 2 * B.ncard ≤ Fintype.card W := by omega
    rcases hexp B h2B with he | he
    · left
      have : 0 ≤ (B.ncard : ℝ) := Nat.cast_nonneg _
      nlinarith
    · right
      have : τ ≤ D.ncard := by
        have hΛ : 0 < 2 * (L + ℓ + 1) := by
          by_contra hc; push Not at hc
          have : (Fintype.card W : ℝ) ≤ 0 := by nlinarith [Nat.cast_nonneg (α := ℝ) D.ncard]
          have : (0 : ℝ) < Fintype.card W := by
            have := hU.ncard_pos (Set.toFinite _)
            have := Set.ncard_le_card U
            rw [Nat.card_eq_fintype_card] at this
            exact_mod_cast (show 0 < Fintype.card W by omega)
          linarith
        have := le_trans hτW he
        nlinarith
      linarith

omit [Fintype W] in
/-- A walk with paths attached at its vertices spans a connected set. -/
lemma connected_walk_union_paths [DecidableEq W] {x y : W} (Wk : H.Walk x y) {q : ℕ}
    {u z : Fin q → W} (P : ∀ i, H.Walk (u i) (z i)) (hz : ∀ i, z i ∈ Wk.support) :
    (H.induce ((Wk.support.toFinset ∪ univ.biUnion fun i => (P i).support.toFinset :
      Finset W) : Set W)).Connected := by
  have hC : (H.induce ({v | v ∈ Wk.support} : Set W)).Connected := Wk.connected_induce_support
  have e : ((Wk.support.toFinset ∪ univ.biUnion fun i => (P i).support.toFinset : Finset W) :
      Set W) = {v | v ∈ Wk.support} ∪ ⋃ i, {v | v ∈ (P i).support} := by
    ext v; simp
  rw [e]
  refine connected_union_of_attached hC fun v hv => ?_
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
  exact ⟨{v | v ∈ (P i).support}, fun w hw => Or.inr (Set.mem_iUnion.mpr ⟨i, hw⟩), hi,
    (P i).connected_induce_support, ⟨z i, (P i).end_mem_support, hz i⟩⟩

omit [Fintype W] in
/-- A walk with paths attached at its vertices spans at most `|W| + 1 + ∑ |P i|` vertices. -/
lemma card_walk_union_paths_le [DecidableEq W] {x y : W} (Wk : H.Walk x y) {q : ℕ}
    {u z : Fin q → W} (P : ∀ i, H.Walk (u i) (z i)) (hz : ∀ i, z i ∈ Wk.support) :
    (Wk.support.toFinset ∪ univ.biUnion fun i => (P i).support.toFinset).card ≤
      Wk.length + 1 + ∑ i, (P i).length := by
  set Wf := Wk.support.toFinset
  -- each path adds at most its length: its endpoint `z i` is already on the walk
  have hP : ∀ i, ((P i).support.toFinset \ Wf).card ≤ (P i).length := by
    intro i
    have h1 : (P i).support.toFinset \ Wf ⊆ ((P i).support.toFinset).erase (z i) := by
      intro v hv
      rw [mem_sdiff] at hv
      exact mem_erase.mpr ⟨fun h => hv.2 (h ▸ List.mem_toFinset.mpr (hz i)), hv.1⟩
    have h2 := card_le_card h1
    rw [card_erase_of_mem (List.mem_toFinset.mpr (P i).end_mem_support)] at h2
    have h3 := List.toFinset_card_le (P i).support
    rw [SimpleGraph.Walk.length_support] at h3
    omega
  have hsub : Wf ∪ univ.biUnion (fun i => (P i).support.toFinset) ⊆
      Wf ∪ univ.biUnion fun i => (P i).support.toFinset \ Wf := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · exact mem_union_left _ h
    · by_cases hvW : v ∈ Wf
      · exact mem_union_left _ hvW
      · obtain ⟨i, -, hi⟩ := mem_biUnion.mp h
        exact mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _, mem_sdiff.mpr ⟨hi, hvW⟩⟩)
  have hW : Wf.card ≤ Wk.length + 1 := by
    have := List.toFinset_card_le Wk.support
    rwa [SimpleGraph.Walk.length_support] at this
  calc _ ≤ (Wf ∪ univ.biUnion fun i => (P i).support.toFinset \ Wf).card := card_le_card hsub
    _ ≤ Wf.card + (univ.biUnion fun i => (P i).support.toFinset \ Wf).card := card_union_le _ _
    _ ≤ Wf.card + ∑ i, ((P i).support.toFinset \ Wf).card := by gcongr; exact card_biUnion_le
    _ ≤ Wk.length + 1 + ∑ i, (P i).length := add_le_add hW (sum_le_sum fun i _ => hP i)

/-- **ShortTree, extended** (Case 3 of the algorithm). Let `H` be a connected truncated
expander at scale `ℓ` with slack `L` and `U_1, …, U_q` (`q ≥ 2`) nonempty vertex sets, each
with a measure `ν_i` with `∑ ν_i² ≤ κ'` and mean distance at most `E` from `U_i`, where
`κ' = 2(2S+1)/(3S(S+1))` (the tent measures `exists_tent_measure`,
`exists_tent_measure_exp`). Then some connected vertex set meets every `U_i` and has at most
`1 + π √(truncVar ℓ L) √(q²(|V(H)| κ' - 1)/(q - 1)) + q E` vertices: a hitting walk for the
measures `ν_i`, extended by shortest paths back to the sets `U_i`. -/
theorem extended_short_tree [DecidableEq W] (hH : H.Connected) {ℓ L : ℝ} (hℓ : 0 < ℓ)
    (hL : 0 ≤ L) (hexp : IsTruncExpander H ℓ L) {q : ℕ} (hq : 2 ≤ q) (U : Fin q → Set W)
    {S : ℕ} (hS : 1 ≤ S) {E : ℝ} (hU : ∀ i, (U i).Nonempty)
    (hmeas : ∀ i, ∃ ν : W → ℝ, (∀ x, 0 ≤ ν x) ∧ ∑ x, ν x = 1 ∧
      3 * S * (S + 1) * ∑ x, ν x ^ 2 ≤ 2 * (2 * S + 1) ∧ ∑ x, ν x * setDist H (U i) x ≤ E) :
    ∃ T : Set W, (H.induce T).Connected ∧ (∀ i, (T ∩ U i).Nonempty) ∧
      (T.ncard : ℝ) ≤ 1 + Real.pi * Real.sqrt (truncVar ℓ L) *
        Real.sqrt (q ^ 2 * (Fintype.card W * (2 * (2 * S + 1) / (3 * S * (S + 1))) - 1) /
          (q - 1)) + q * E := by
  classical
  have hS0 : (0 : ℝ) < S := by exact_mod_cast hS
  choose ν hν0 hν1 hνsq hνd using hmeas
  set σ := Real.sqrt (truncVar ℓ L)
  have hσ2 : truncVar ℓ L ≤ σ ^ 2 := by
    rcases le_total 0 (truncVar ℓ L) with h | h
    · rw [Real.sq_sqrt h]
    · have : σ = 0 := Real.sqrt_eq_zero'.mpr h
      rw [this]; linarith
  set N : ℝ := ((Fintype.card W : ℕ) : ℝ) with hN
  set g : Fin q → W → ℝ := fun i v => setDist H (U i) v
  obtain ⟨tour, z, htour, hz, hlen⟩ := wasserstein_walk_measures (gdist H) (fun x => by simp)
    (fun x y z => dist_triangle_real hH x y z) σ (Real.sqrt_nonneg _)
    (fun f hf => (poincare_of_trunc hH hℓ hL hexp f hf).trans
      (mul_le_mul_of_nonneg_left hσ2 (Nat.cast_nonneg _))) q hq ν hν0 hν1
    (N * (2 * (2 * S + 1) / (3 * S * (S + 1)))) (fun i => by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      have := hνsq i
      have hN0 : 0 ≤ N := Nat.cast_nonneg _
      nlinarith) g
  -- the walk through the tour, and shortest paths from the visited points back to `U i`
  obtain ⟨x, tour', rfl⟩ := List.exists_cons_of_ne_nil htour
  obtain ⟨y, Wk, hWk, hWL⟩ := exists_walk_of_tour hH x tour'
  have hpath : ∀ i, ∃ u ∈ U i, ∃ P : H.Walk u (z i), P.length = setDist H (U i) (z i) := by
    intro i
    obtain ⟨u, hu, hd⟩ := exists_setDist (H := H) (hU i) (z i)
    obtain ⟨P, hP⟩ := hH.exists_walk_length_eq_dist u (z i)
    exact ⟨u, hu, P, hP.trans hd⟩
  choose u hu P hP using hpath
  have hzW : ∀ i, z i ∈ Wk.support := fun i => hWL _ (hz i).1
  refine ⟨(Wk.support.toFinset ∪ univ.biUnion fun i => (P i).support.toFinset : Finset W),
    connected_walk_union_paths Wk P hzW, fun i => ⟨u i, ?_, hu i⟩, ?_⟩
  · exact mem_coe.mpr (mem_union_right _ (mem_biUnion.mpr
      ⟨i, mem_univ _, List.mem_toFinset.mpr (P i).start_mem_support⟩))
  · have hg : ∑ i, g i (z i) = ∑ i, ((P i).length : ℝ) := by
      refine sum_congr rfl fun i _ => ?_
      simp only [g, hP i]
    have hsumavg : ∑ i, ∑ x, ν i x * g i x ≤ q * E := by
      calc ∑ i, ∑ x, ν i x * g i x ≤ ∑ _i : Fin q, E := sum_le_sum fun i _ => hνd i
        _ = _ := by simp [sum_const, card_univ]
    have hT : (((Wk.support.toFinset ∪ univ.biUnion fun i => (P i).support.toFinset).card :
        ℕ) : ℝ) ≤ Wk.length + 1 + ∑ i, ((P i).length : ℝ) := by
      exact_mod_cast card_walk_union_paths_le Wk P hzW
    rw [hg] at hlen
    rw [Set.ncard_coe_finset]
    rw [hWk] at hT
    simp only [N] at hlen
    linarith

end MinorFreeSeparators
