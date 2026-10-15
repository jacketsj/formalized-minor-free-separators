import proof.Parameters.Common

/-!
# Parameters for `4 ≤ h ≤ 40`

With `y = √n > 3.2 h` we take `ℓ = 0.62 y/h - 1`, `L = (ℓ + 1)/2`, `β = ⌈2.15 y⌉` and
`S = ⌈4n/(3κ)⌉` with `κ = 0.15 h + 4`, and bound the path cost using the growth `β` only.
The budget inequalities become polynomial inequalities in `z = y - 3.2 h ≥ 0` and
`w = h - 4 ∈ [0, 36]`, checked by `bernstein_linarith`.
-/

namespace MinorFreeSeparators.SmallH

open Real

/-- `√(truncVar ℓ ((ℓ + 1)/2)) ≤ 1.4814 (ℓ + 0.92)` for `ℓ ≥ 0.984`. -/
lemma sqrt_truncVar_le {ℓ : ℝ} (hℓ : 123 / 125 ≤ ℓ) :
    √(truncVar ℓ ((ℓ + 1) / 2)) ≤ 7407 / 5000 * (ℓ + 23 / 25) := by
  have hℓ0 : 0 < ℓ := by linarith
  refine sqrt_le_of_sq_le (by positivity) ((truncVar_le ℓ hℓ0 (by linarith)).trans ?_)
  rw [div_le_iff₀ (by linarith)]
  have h1 := sub_nonneg.mpr hℓ
  nlinarith [mul_nonneg h1 h1, mul_nonneg (mul_nonneg h1 h1) h1]

/-- `√(h (n κ' - 1)) ≤ 0.42 h + 2.58` when `S ≥ 4n/(3κ)`, `κ = 0.15 h + 4`. -/
lemma sqrt_tour_le {h n S : ℝ} (hh : 4 ≤ h) (hS : 1 ≤ S) (hn : 0 ≤ n)
    (hS1 : 4 * n ≤ 3 * (3 * h / 20 + 4) * S) :
    √(h * (n * (2 * (2 * S + 1) / (3 * S * (S + 1))) - 1)) ≤ 21 * h / 50 + 129 / 50 := by
  refine sqrt_le_of_sq_le (by positivity) ?_
  have h1 := nkappa_le hS hn
  have h2 : 4 * n / (3 * S) ≤ 3 * h / 20 + 4 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (by linarith : (0 : ℝ) ≤ h)
  nlinarith [sq_nonneg (h - 1577 / 100)]

/-- The mean path cost for `4 ≤ h`:
`(h - 2) E ≤ 80(h-2)y/(387κ) + 25/516 + (h-2)/2 + 129κ/1024 + 75κ/16384`, where
`E = ((S-1)(2S-1)/6 + β(S-1)/2 + β²/4)/(β(S+1))`, for `S ≈ 4y²/(3κ)`, `β ≈ 2.15 y`. -/
lemma path_le {y h S β : ℝ} (hh : 4 ≤ h) (hy : 16 / 5 * h ≤ y)
    (hS1 : 4 * y ^ 2 ≤ 3 * (3 * h / 20 + 4) * S)
    (hS2 : 3 * (3 * h / 20 + 4) * S ≤ 4 * y ^ 2 + 3 * (3 * h / 20 + 4))
    (hβ1 : 43 * y / 20 ≤ β) (hβ2 : β ≤ 43 * y / 20 + 1) :
    (h - 2) * (((S - 1) * (2 * S - 1) / 6 + β * (S - 1) / 2 + β ^ 2 / 4) / (β * (S + 1))) ≤
      80 * (h - 2) * y / (387 * (3 * h / 20 + 4)) + 25 / 516 + (h - 2) / 2 +
        129 * (3 * h / 20 + 4) / 1024 + 75 * (3 * h / 20 + 4) / 16384 := by
  set κ := 3 * h / 20 + 4 with hκ
  have hy0 : 0 < y := by linarith
  have hβ0 : 0 < β := by linarith
  have hκ0 : 0 < κ := by linarith
  have hS1' : 1 ≤ S := by
    by_contra h1; push Not at h1
    have : 3 * κ * S < 3 * κ := by nlinarith
    nlinarith
  have hS0 : 0 < S := by linarith
  have hh2 : 0 ≤ h - 2 := by linarith
  -- `E ≤ S/(3β) + 1/2 + β/(4S)`
  have h1 : ((S - 1) * (2 * S - 1) / 6 + β * (S - 1) / 2 + β ^ 2 / 4) / (β * (S + 1)) ≤
      S / (3 * β) + 1 / 2 + β / (4 * S) := by
    have e : S / (3 * β) + 1 / 2 + β / (4 * S) =
        (S ^ 2 / 3 + β * S / 2 + β ^ 2 / 4) / (β * S) := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ S ^ 2 / 3 + β * S / 2 + β ^ 2 / 4 := by positivity
    nlinarith
  -- `(h - 2) S/(3β) ≤ 80(h-2)y/(387κ) + 25/516`
  have h2 : (h - 2) * (S / (3 * β)) ≤ 80 * (h - 2) * y / (387 * κ) + 25 / 516 := by
    have e1 : S / (3 * β) ≤ (4 * y ^ 2 / (3 * κ) + 1) / (129 * y / 20) := by
      apply div_le_div₀ (by positivity) _ (by positivity) (by linarith)
      rw [div_add_one (by positivity), le_div_iff₀ (by positivity)]; linarith
    have e2 : (4 * y ^ 2 / (3 * κ) + 1) / (129 * y / 20) =
        80 * y / (387 * κ) + 20 / (129 * y) := by
      field_simp; ring
    have e3 : (h - 2) * (20 / (129 * y)) ≤ 25 / 516 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc (h - 2) * (S / (3 * β)) ≤ (h - 2) * (80 * y / (387 * κ) + 20 / (129 * y)) := by
          rw [← e2]; exact mul_le_mul_of_nonneg_left e1 hh2
      _ = 80 * (h - 2) * y / (387 * κ) + (h - 2) * (20 / (129 * y)) := by ring
      _ ≤ _ := by linarith
  -- `(h - 2) β/(4S) ≤ 129κ/1024 + 75κ/16384`
  have h3 : (h - 2) * (β / (4 * S)) ≤ 129 * κ / 1024 + 75 * κ / 16384 := by
    have e1 : β / (4 * S) ≤ (43 * y / 20 + 1) * (3 * κ) / (16 * y ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have e2 : (h - 2) * ((43 * y / 20 + 1) * (3 * κ) / (16 * y ^ 2)) ≤
        129 * κ / 1024 + 75 * κ / 16384 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have hκy : 0 ≤ κ * y := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hy hκy, mul_le_mul_of_nonneg_left hy hκ0.le]
    exact (mul_le_mul_of_nonneg_left e1 hh2).trans e2
  calc (h - 2) * (((S - 1) * (2 * S - 1) / 6 + β * (S - 1) / 2 + β ^ 2 / 4) / (β * (S + 1)))
      ≤ (h - 2) * (S / (3 * β) + 1 / 2 + β / (4 * S)) := mul_le_mul_of_nonneg_left h1 hh2
    _ = (h - 2) * (S / (3 * β)) + (h - 2) / 2 + (h - 2) * (β / (4 * S)) := by ring
    _ ≤ _ := by linarith

/-- The bound `â` on the connector size for `4 ≤ h ≤ 40`. -/
noncomputable def connBound (y h : ℝ) : ℝ :=
  1 + 25 / 516 + 129 * (3 * h / 20 + 4) / 1024 + 75 * (3 * h / 20 + 4) / 16384 +
    3927 / 1250 * (7407 / 5000 * (31 * y / (50 * h) - 1 + 23 / 25)) * (21 * h / 50 + 129 / 50) +
    (h - 2) / 2 + 80 * (h - 2) * y / (387 * (3 * h / 20 + 4))

lemma mul_connBound {y h : ℝ} (hh : 0 < h) : h * (3 * h / 20 + 4) * connBound y h =
    h * (3 * h / 20 + 4) * (1 + 25 / 516 + 129 * (3 * h / 20 + 4) / 1024 +
      75 * (3 * h / 20 + 4) / 16384) +
    3927 / 1250 * (7407 / 5000 * (31 * y / 50 - 2 * h / 25)) * (21 * h / 50 + 129 / 50) *
      (3 * h / 20 + 4) + h * (3 * h / 20 + 4) * (h - 2) / 2 + 80 * (h - 2) * y * h / 387 := by
  unfold connBound
  have : (0 : ℝ) < 3 * h / 20 + 4 := by linarith
  field_simp
  ring

/-- Case 1 budget for `4 ≤ h ≤ 40`. -/
lemma budget_expand_le {y h ℓ L M : ℝ} (hh : 4 ≤ h) (hh40 : h ≤ 40) (hy : 16 / 5 * h ≤ y)
    (hℓ : ℓ = 31 * y / (50 * h) - 1) (hL : L = (ℓ + 1) / 2)
    (hM : M ≤ 43 * y / 20 ∨ M ≤ connBound y h) :
    (h - 2) * M + ((2 * L + 3 * ℓ + 1) * y ^ 2 + 2 * L + ℓ + 1) /
        (2 * (ℓ + 1) * (2 * L + 2 * ℓ + 1)) ≤ 16 / 5 * h * y := by
  have hh0 : 0 < h := by linarith
  refine budget_expand_of (p := 31 * y / 50 - h) (u := 1 / 2) (by linarith) (by linarith)
    (by norm_num) (by rw [hℓ]; field_simp) (by rw [hL]; ring) (by positivity)
    (mul_connBound hh0) hM ?_ ?_ <;>
  · obtain ⟨z, hz, rfl⟩ : ∃ z, 0 ≤ z ∧ y = 16 / 5 * h + z :=
      ⟨y - 16 / 5 * h, by linarith, by ring⟩
    obtain ⟨w, hw, rfl⟩ : ∃ w, 0 ≤ w ∧ h = 4 + w := ⟨h - 4, by linarith, by ring⟩
    have hv : 0 ≤ 36 - w := by linarith
    bernstein_linarith hz hw hv 3 6

/-- Cases 2 and 3 budget for `4 ≤ h ≤ 40`. -/
lemma budget_branch_le {y h ℓ M : ℝ} (hh : 4 ≤ h) (hh40 : h ≤ 40) (hy : 16 / 5 * h ≤ y)
    (hℓ : ℓ = 31 * y / (50 * h) - 1) (hM : M ≤ 43 * y / 20 ∨ M ≤ connBound y h) :
    (h - 2) * M + (y ^ 2 + 1 + 2 * ℓ * M) / (2 * (ℓ + 1)) ≤ 16 / 5 * h * y := by
  have hh0 : 0 < h := by linarith
  refine budget_branch_of (p := 31 * y / 50 - h) (by linarith) (by linarith)
    (by rw [hℓ]; field_simp) (by positivity) (mul_connBound hh0) hM ?_ ?_ <;>
  · obtain ⟨z, hz, rfl⟩ : ∃ z, 0 ≤ z ∧ y = 16 / 5 * h + z :=
      ⟨y - 16 / 5 * h, by linarith, by ring⟩
    obtain ⟨w, hw, rfl⟩ : ∃ w, 0 ≤ w ∧ h = 4 + w := ⟨h - 4, by linarith, by ring⟩
    have hv : 0 ≤ 36 - w := by linarith
    bernstein_linarith hz hw hv 2 5

/-- The parameters for `4 ≤ h ≤ 40` and `√n > 3.2 h`. -/
lemma exists_params (n h : ℕ) (hh : 4 ≤ h) (hh40 : h ≤ 40) (hn : 16 / 5 * (h : ℝ) < √n) :
    ∃ P : SepParams n h, P.K ≤ 16 / 5 * h * √n := by
  obtain ⟨y, hy_def⟩ : ∃ y, y = √(n : ℝ) := ⟨_, rfl⟩
  rw [← hy_def] at hn ⊢
  have hy : y ^ 2 = n := by rw [hy_def]; exact sq_sqrt (Nat.cast_nonneg n)
  have hh4 : (4 : ℝ) ≤ h := by exact_mod_cast hh
  have hh40' : (h : ℝ) ≤ 40 := by exact_mod_cast hh40
  have hh0 : (0 : ℝ) < h := by linarith
  have hy0 : 0 < y := by linarith
  obtain ⟨ℓ, hℓ_def⟩ : ∃ ℓ : ℝ, ℓ = 31 * y / (50 * h) - 1 := ⟨_, rfl⟩
  have hℓ1 : 123 / 125 ≤ ℓ := by
    rw [hℓ_def, le_sub_iff_add_le, le_div_iff₀ (by positivity)]; nlinarith
  obtain ⟨β, hβ_def⟩ : ∃ β : ℕ, β = ⌈43 * y / 20⌉₊ := ⟨_, rfl⟩
  obtain ⟨hβ1, hβ2⟩ : 43 * y / 20 ≤ β ∧ (β : ℝ) ≤ 43 * y / 20 + 1 :=
    hβ_def ▸ ceil_bounds (by positivity)
  have hβpos : 1 ≤ β := by exact_mod_cast (show (1 : ℝ) ≤ β by linarith)
  obtain ⟨S, hS_def⟩ : ∃ S : ℕ, S = ⌈4 * y ^ 2 / (3 * (3 * h / 20 + 4))⌉₊ := ⟨_, rfl⟩
  obtain ⟨hS1', hS2'⟩ : 4 * y ^ 2 / (3 * (3 * h / 20 + 4)) ≤ S ∧
      (S : ℝ) ≤ 4 * y ^ 2 / (3 * (3 * h / 20 + 4)) + 1 :=
    hS_def ▸ ceil_bounds (by positivity)
  have hκ0 : (0 : ℝ) < 3 * (3 * h / 20 + 4) := by positivity
  have hS1 : 4 * y ^ 2 ≤ 3 * (3 * h / 20 + 4) * S := by
    rw [div_le_iff₀ hκ0] at hS1'; linarith
  have hS2 : 3 * (3 * h / 20 + 4) * S ≤ 4 * y ^ 2 + 3 * (3 * h / 20 + 4) := by
    rw [div_add_one hκ0.ne', le_div_iff₀ hκ0] at hS2'; linarith
  have hy2 : (16 / 5 * h) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by positivity) hn.le 2
  have hSR : (1 : ℝ) ≤ S := by
    have : 3 * (3 * h / 20 + 4) ≤ 4 * y ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left (by linarith) hκ0
  have h2S : 2 * S ≤ n := by
    have : 3 * (3 * h / 20 + 4) * (2 * S) ≤ 3 * (3 * h / 20 + 4) * y ^ 2 := by nlinarith
    exact_mod_cast hy ▸ le_of_mul_le_mul_left this hκ0
  -- the connector size `a`
  obtain ⟨E, hE_def⟩ : ∃ E : ℝ,
      E = ((S - 1) * (2 * S - 1) / 6 + β * (S - 1) / 2 + β ^ 2 / 4) / (β * (S + 1)) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by
    rw [hE_def]
    apply div_nonneg _ (by positivity)
    have : (0 : ℝ) ≤ (S - 1) * (2 * S - 1) := by nlinarith
    nlinarith
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 1 + π * √(truncVar ℓ ((ℓ + 1) / 2)) *
      √(h * (n * (2 * (2 * S + 1) / (3 * S * (S + 1))) - 1)) + (h - 2) * E := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by
    have : 0 ≤ ((h : ℝ) - 2) * E := mul_nonneg (by linarith) hE0
    have : 0 ≤ π * √(truncVar ℓ ((ℓ + 1) / 2)) *
      √(h * (n * (2 * (2 * S + 1) / (3 * S * (S + 1))) - 1)) := by positivity
    linarith
  have ha : a ≤ connBound y h := by
    have h1 : π * √(truncVar ℓ ((ℓ + 1) / 2)) *
        √(h * (n * (2 * (2 * S + 1) / (3 * S * (S + 1))) - 1)) ≤
        3927 / 1250 * (7407 / 5000 * (ℓ + 23 / 25)) * (21 * h / 50 + 129 / 50) :=
      mul_le_mul (mul_le_mul pi_le_d4 (sqrt_truncVar_le hℓ1) (sqrt_nonneg _) (by norm_num))
        (sqrt_tour_le hh4 hSR (Nat.cast_nonneg n) (by rw [← hy]; linarith)) (sqrt_nonneg _)
        (by positivity)
    have h2 := path_le hh4 hn.le hS1 hS2 hβ1 hβ2
    rw [← hE_def] at h2
    rw [ha_def]
    unfold connBound
    rw [← hℓ_def]
    linarith
  have hM := max_le_or ha (show (β : ℝ) - 1 ≤ 43 * y / 20 by linarith)
  refine ⟨{ ℓ := ℓ, L := (ℓ + 1) / 2, S := S, β := β, a := a, E := E, K := 16 / 5 * h * y
            ℓ_pos := by linarith
            L_nonneg := by linarith
            one_le_S := by exact_mod_cast hSR
            one_le_β := hβpos
            one_le_a := ha1
            two_S_le := h2S
            path := Or.inl hE_def.ge
            connector := fun _ => ha_def.ge
            budget_expand := by rw [← hy]; exact budget_expand_le hh4 hh40' hn.le hℓ_def rfl hM
            budget_branch := by rw [← hy]; exact budget_branch_le hh4 hh40' hn.le hℓ_def hM },
    le_rfl⟩

end MinorFreeSeparators.SmallH
