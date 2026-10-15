import proof.Parameters.Common

/-!
# Parameters for `h ≥ 41`

With `y = √n > 3.2 h` we take `ℓ = 0.56 y/h - 1.17`, `L = 0.65 (ℓ + 1)`, `β = ⌈1.98 y⌉` and
`S = ⌈8 β (ℓ + 1.17)⌉`, so that `S/(βℓ) ≈ 8 (1 + 1.17/ℓ)`. The path cost uses the expansion
(`expPath`) and is at most `1.7019 ℓ + 2.56` plus small terms. The budget inequalities become
polynomial inequalities in `z = y - 3.2 h ≥ 0` and `w = h - 41 ≥ 0` with nonnegative
coefficients, checked by `monomial_linarith`.
-/

namespace MinorFreeSeparators.LargeH

open Real

/-- `√(truncVar ℓ (0.65 (ℓ + 1))) ≤ 1.5205 (ℓ + 0.97)` for `ℓ ≥ 0.622`. -/
lemma sqrt_truncVar_le {ℓ : ℝ} (hℓ : 311 / 500 ≤ ℓ) :
    √(truncVar ℓ (13 * (ℓ + 1) / 20)) ≤ 3041 / 2000 * (ℓ + 97 / 100) := by
  have hℓ0 : 0 < ℓ := by linarith
  refine sqrt_le_of_sq_le (by positivity) ((truncVar_le ℓ hℓ0 (by positivity)).trans ?_)
  rw [div_le_iff₀ (by positivity)]
  have h1 := sub_nonneg.mpr hℓ
  nlinarith [mul_nonneg h1 h1, mul_nonneg (mul_nonneg h1 h1) h1]

/-- `√(h (n κ' - 1)) ≤ h/2.579` when `S ≥ 8β · 0.56 y/h` and `β ≥ 1.98 y`. -/
lemma sqrt_tour_le {y h S β : ℝ} (hh : 0 < h) (hy : 0 < y) (hS : 1 ≤ S)
    (hβ : 99 * y / 50 ≤ β) (hS1 : 8 * β * (14 * y / (25 * h)) ≤ S) :
    √(h * (y ^ 2 * (2 * (2 * S + 1) / (3 * S * (S + 1))) - 1)) ≤ 1000 * h / 2579 := by
  refine sqrt_le_of_sq_le (by positivity) ?_
  have h1 := nkappa_le hS (sq_nonneg y)
  have hβ0 : 0 < β := by linarith
  have h2 : 4 * y ^ 2 / (3 * S) ≤ 625 * h / 4158 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have e : 8 * β * (14 * y / (25 * h)) * h = 112 * β * y / 25 := by field_simp; ring
    have := mul_le_mul_of_nonneg_right hS1 hh.le
    rw [e] at this
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hh.le
  nlinarith

/-- The main part of the path cost is at most `1.7019 ℓ + 2.56`. -/
lemma path_main_le {ℓ : ℝ} (hℓ : 311 / 500 ≤ ℓ) :
    1 + 117 / 100 + ℓ + (ℓ + 1 / 2) * (1299651 / 625000 - 3 / 2) +
      (117 / 100) ^ 2 / (12 * ℓ * (ℓ + 117 / 100)) +
      (ℓ / (8 * (ℓ + 117 / 100)) * (ℓ + 1) - (ℓ / (8 * (ℓ + 117 / 100))) ^ 2 * (ℓ / 6 + 1 / 4)) ≤
      17019 / 10000 * ℓ + 64 / 25 := by
  have hℓ0 : 0 < ℓ := by linarith
  rw [← sub_nonneg]
  have e : 17019 / 10000 * ℓ + 64 / 25 - (1 + 117 / 100 + ℓ + (ℓ + 1 / 2) *
      (1299651 / 625000 - 3 / 2) + (117 / 100) ^ 2 / (12 * ℓ * (ℓ + 117 / 100)) +
      (ℓ / (8 * (ℓ + 117 / 100)) * (ℓ + 1) - (ℓ / (8 * (ℓ + 117 / 100))) ^ 2 *
        (ℓ / 6 + 1 / 4))) =
      (1877 / 156250 * ℓ ^ 4 + 179232159 / 7812500 * ℓ ^ 3 + 9601373691 / 195312500 * ℓ ^ 2 +
        869894883 / 195312500 * ℓ - 1601613 / 62500) / (192 * ℓ * (ℓ + 117 / 100) ^ 2) := by
    field_simp
    ring
  rw [e]
  apply div_nonneg _ (by positivity)
  have h1 := sub_nonneg.mpr hℓ
  nlinarith [mul_nonneg h1 h1, mul_nonneg (mul_nonneg h1 h1) h1,
    mul_nonneg (mul_nonneg h1 h1) (mul_nonneg h1 h1)]

/-- `log(S/(βℓ)) ≤ log 8 + log(1 + 1.17/ℓ) + 1/(8β(ℓ + 1.17))`, with the series bound for the
middle term. -/
lemma log_ratio_le {S β ℓ : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ) (hS1 : 8 * β * (ℓ + 117 / 100) ≤ S)
    (hS2 : S ≤ 8 * β * (ℓ + 117 / 100) + 1) :
    Real.log (S / (β * ℓ)) ≤ 1299651 / 625000 +
      (4 * (117 / 100 / ℓ) / (3 * (117 / 100 / ℓ + 2)) +
        117 / 100 / ℓ * (117 / 100 / ℓ + 2) / (6 * (117 / 100 / ℓ + 1))) +
      1 / (8 * β * (ℓ + 117 / 100)) := by
  have hc : 0 < 8 * β * (ℓ + 117 / 100) := by positivity
  have hS0 : 0 < S := by linarith
  have e : S / (β * ℓ) = 2 ^ 3 * (1 + 117 / 100 / ℓ) * (S / (8 * β * (ℓ + 117 / 100))) := by
    field_simp; ring
  rw [e, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_pow]
  have h2 := Real.log_two_lt_d9
  have h3 := log_one_add_le (by positivity : (0 : ℝ) ≤ 117 / 100 / ℓ)
  have h4 := Real.log_le_sub_one_of_pos (div_pos hS0 hc)
  have h5 : S / (8 * β * (ℓ + 117 / 100)) - 1 ≤ 1 / (8 * β * (ℓ + 117 / 100)) := by
    rw [div_sub_one hc.ne', div_le_div_iff_of_pos_right hc]; linarith
  norm_num at h2
  linarith

/-- `(ℓ + 1/2) · (the series bound for log(1 + 1.17/ℓ)) ≤ 1.17 + 1.17²/(12ℓ(ℓ + 1.17))`. -/
lemma mul_log_series_le {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (ℓ + 1 / 2) * (4 * (117 / 100 / ℓ) / (3 * (117 / 100 / ℓ + 2)) +
        117 / 100 / ℓ * (117 / 100 / ℓ + 2) / (6 * (117 / 100 / ℓ + 1))) ≤
      117 / 100 + (117 / 100) ^ 2 / (12 * ℓ * (ℓ + 117 / 100)) := by
  have e1 : 4 * (117 / 100 / ℓ) / (3 * (117 / 100 / ℓ + 2)) =
      468 / (300 * (117 / 100 + 2 * ℓ)) := by
    field_simp; norm_num
  have e2 : 117 / 100 / ℓ * (117 / 100 / ℓ + 2) / (6 * (117 / 100 / ℓ + 1)) =
      117 / 100 * (117 / 100 + 2 * ℓ) / (6 * ℓ * (117 / 100 + ℓ)) := by
    field_simp
  rw [e1, e2]
  have h1 : (ℓ + 1 / 2) * (468 / (300 * (117 / 100 + 2 * ℓ))) ≤ 78 / 100 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have h2 : (ℓ + 1 / 2) * (117 / 100 * (117 / 100 + 2 * ℓ) / (6 * ℓ * (117 / 100 + ℓ))) ≤
      39 / 100 + (117 / 100) ^ 2 / (12 * ℓ * (ℓ + 117 / 100)) := by
    rw [mul_div_assoc', div_add_div _ _ (by norm_num) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hℓ hℓ, mul_pos (mul_pos hℓ hℓ) hℓ, pow_pos hℓ 4]
  linarith

/-- Bounds on `ℓ = 0.56 y/h - 1.17` for `h ≥ 41` and `y ≥ 3.2 h`. -/
lemma ell_bounds {y h ℓ : ℝ} (hh : 41 ≤ h) (hy : 16 / 5 * h ≤ y)
    (hℓ : ℓ = 14 * y / (25 * h) - 117 / 100) :
    311 / 500 ≤ ℓ ∧ (ℓ + 117 / 100) * h = 14 * y / 25 ∧ ℓ + 117 / 100 ≤ 14 * y / 1025 := by
  have hh0 : 0 < h := by linarith
  have hℓh : (ℓ + 117 / 100) * h = 14 * y / 25 := by rw [hℓ]; field_simp; ring
  refine ⟨?_, hℓh, le_of_mul_le_mul_right (by rw [hℓh]; nlinarith) hh0⟩
  rw [hℓ, le_sub_iff_add_le, le_div_iff₀ (by positivity)]; nlinarith

/-- `t = S/((ℓ + 1/2)τ) ≤ 85.1/h` for `h ≥ 41`. -/
lemma ratio_le {y h S β ℓ : ℝ} (hh : 41 ≤ h) (hy : 16 / 5 * h ≤ y) (hℓ1 : 311 / 500 ≤ ℓ)
    (hℓh : (ℓ + 117 / 100) * h = 14 * y / 25) (hβ2 : β ≤ 99 * y / 50 + 1)
    (hS2 : S ≤ 8 * β * (ℓ + 117 / 100) + 1) (hS0 : 0 < S) :
    S / ((ℓ + 1 / 2) * ((y ^ 2 + 1) / (4 * (13 * (ℓ + 1) / 20 + ℓ + 1)))) ≤ 851 / 10 / h := by
  have hh0 : 0 < h := by linarith
  have hy0 : 0 < y := by linarith
  have hℓ' : 0 < ℓ + 1 / 2 := by linarith
  rw [div_le_div_iff₀ (by positivity) hh0]
  rw [show (ℓ + 1 / 2) * ((y ^ 2 + 1) / (4 * (13 * (ℓ + 1) / 20 + ℓ + 1))) =
    (ℓ + 1 / 2) * (y ^ 2 + 1) / (33 * (ℓ + 1) / 5) by field_simp; ring]
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  have hSh : S * h ≤ 8 * (99 * y / 50 + 1) * (14 * y / 25) + h := by
    have h1 := mul_le_mul_of_nonneg_right hS2 hh0.le
    have e : (8 * β * (ℓ + 117 / 100) + 1) * h = 8 * β * (14 * y / 25) + h := by
      rw [← hℓh]; ring
    rw [e] at h1
    have h2 := mul_le_mul_of_nonneg_right hβ2 (by positivity : (0 : ℝ) ≤ 8 * (14 * y / 25))
    linarith
  have hl : ℓ + 1 ≤ 1446 / 1000 * (ℓ + 1 / 2) := by linarith
  have h1 := mul_le_mul hl hSh (by positivity) (by positivity)
  have k1 := mul_nonneg hℓ'.le (show 0 ≤ 4444 / 10000 * y ^ 2 - 46 * y by nlinarith)
  have k2 := mul_le_mul_of_nonneg_left (show h ≤ 5 * y / 16 by linarith) hℓ'.le
  have k3 := mul_nonneg hℓ'.le hy0.le
  linarith

/-- The growth of `g(w) = w(ℓ + 1) - w²(ℓ/6 + 1/4)` for `0 ≤ w ≤ ℓ/(8(ℓ + 1.17))`. -/
lemma growth_term_le {ℓ w : ℝ} (hℓ : 0 < ℓ) (hwm : w ≤ ℓ / (8 * (ℓ + 117 / 100))) :
    ℓ * (-w + w ^ 2 / 3) + (ℓ + 1 / 2) * (2 * w - w ^ 2 / 2) ≤
      ℓ / (8 * (ℓ + 117 / 100)) * (ℓ + 1) - (ℓ / (8 * (ℓ + 117 / 100))) ^ 2 * (ℓ / 6 + 1 / 4) := by
  set wm := ℓ / (8 * (ℓ + 117 / 100))
  have hwm1 : wm ≤ 1 / 8 := by
    simp only [wm]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have e : ℓ * (-w + w ^ 2 / 3) + (ℓ + 1 / 2) * (2 * w - w ^ 2 / 2) =
      w * (ℓ + 1) - w ^ 2 * (ℓ / 6 + 1 / 4) := by ring
  rw [e]
  have h1 : 0 ≤ (wm - w) * ((ℓ + 1) - (w + wm) * (ℓ / 6 + 1 / 4)) :=
    mul_nonneg (by linarith) (by nlinarith)
  nlinarith

/-- The small terms of the path cost: `ℓ/S + (ℓ + 1/2)/(S + 1) + (ℓ + 1/2)/(8β(ℓ + 1.17))
≤ 3/(8β)`. -/
lemma small_terms_le {S β ℓ : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ) (hS1 : 8 * β * (ℓ + 117 / 100) ≤ S) :
    ℓ / S + (ℓ + 1 / 2) * (1 / (S + 1)) + (ℓ + 1 / 2) * (1 / (8 * β * (ℓ + 117 / 100))) ≤
      3 / (8 * β) := by
  have hc : 0 < 8 * β * (ℓ + 117 / 100) := by positivity
  have hS0 : 0 < S := by linarith
  have h1 : ℓ / S ≤ 1 / (8 * β) := by
    rw [div_le_div_iff₀ hS0 (by positivity)]; nlinarith
  have h2 : (ℓ + 1 / 2) * (1 / (S + 1)) ≤ 1 / (8 * β) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h3 : (ℓ + 1 / 2) * (1 / (8 * β * (ℓ + 117 / 100))) ≤ 1 / (8 * β) := by
    rw [mul_one_div, div_le_div_iff₀ hc (by positivity)]; nlinarith
  have : 3 / (8 * β) = 1 / (8 * β) + 1 / (8 * β) + 1 / (8 * β) := by ring
  linarith

/-- `expPath ≤ 1.7019 ℓ + 2.56 + 3/(8β) + (the correction for the last phase)`. -/
lemma expPath_le {S β ℓ τ t : ℝ} (hS : 1 ≤ S) (hβ : 0 < β) (hℓ1 : 311 / 500 ≤ ℓ)
    (hu : β * ℓ ≤ S) (hS1 : 8 * β * (ℓ + 117 / 100) ≤ S)
    (hS2 : S ≤ 8 * β * (ℓ + 117 / 100) + 1) (hτ : 0 < τ) (ht : S / ((ℓ + 1 / 2) * τ) ≤ t) :
    expPath S β ℓ τ ≤ 17019 / 10000 * ℓ + 64 / 25 + 3 / (8 * β) +
      ((ℓ + 1 / 2) * t ^ 4 / 192 + t ^ 2 / (32 * τ)) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ' : 0 < ℓ + 1 / 2 := by linarith
  have hS0 : 0 < S := by linarith
  have hu0 : 0 < β * ℓ := by positivity
  have hA : tentTail S 1 ≤ 1 := by
    unfold tentTail; rw [div_le_one (by positivity)]; nlinarith
  have hB := expPath_lin_le hS hβ hℓ0 hu
  have hC := mul_le_mul_of_nonneg_left (tentLog_le hS hu0 hu) hℓ'.le
  have hD := mul_le_mul_of_nonneg_left (log_ratio_le hβ hℓ0 hS1 hS2) hℓ'.le
  have hE := mul_log_series_le hℓ0
  have hF := expPath_last_le hS hℓ0 hτ ht
  have hwm : β * ℓ / S ≤ ℓ / (8 * (ℓ + 117 / 100)) := by
    rw [div_le_div_iff₀ hS0 (by positivity)]
    have := mul_le_mul_of_nonneg_left hS1 hℓ0.le
    linarith
  have hG := growth_term_le hℓ0 hwm
  have hH := path_main_le hℓ1
  have hsmall := small_terms_le hβ hℓ0 hS1
  unfold expPath
  linarith

/-- The correction for the last phase in `expPath_le`, for `h ≥ 41`, `t = 85.1/h`. -/
lemma last_phase_le {y h ℓ : ℝ} (hh : 41 ≤ h) (hy : 16 / 5 * h ≤ y) (hℓ1 : 311 / 500 ≤ ℓ)
    (hℓh : (ℓ + 117 / 100) * h = 14 * y / 25) (hℓy : ℓ + 117 / 100 ≤ 14 * y / 1025) :
    (h - 2) * ((ℓ + 1 / 2) * (851 / 10 / h) ^ 4 / 192 +
      (851 / 10 / h) ^ 2 / (32 * ((y ^ 2 + 1) / (4 * (13 * (ℓ + 1) / 20 + ℓ + 1))))) ≤
      1 / 20 + 163 * (14 * y / 1025 - 117 / 100 + 1 / 2) / h := by
  have hh0 : 0 < h := by linarith
  have hy0 : 0 < y := by linarith
  have hh2 : 0 ≤ h - 2 := by linarith
  have k2 : (h - 2) * ((ℓ + 1 / 2) * (851 / 10 / h) ^ 4 / 192) ≤
      163 * (14 * y / 1025 - 117 / 100 + 1 / 2) / h := by
    rw [div_pow, le_div_iff₀ hh0]
    have e : (h - 2) * ((ℓ + 1 / 2) * ((851 / 10) ^ 4 / h ^ 4) / 192) * h =
        (ℓ + 1 / 2) * ((851 / 10) ^ 4 / 192) * ((h - 2) / h ^ 3) := by
      field_simp
    rw [e]
    have h1 : (h - 2) / h ^ 3 ≤ 1 / 1681 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h41 : (41 : ℝ) * 41 ≤ h * h := mul_le_mul hh hh (by norm_num) (by linarith)
      have := mul_le_mul_of_nonneg_right h41 hh0.le
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (ℓ + 1 / 2) *
      ((851 / 10) ^ 4 / 192))
    have h3 := mul_le_mul_of_nonneg_right (show ℓ + 1 / 2 ≤ 14 * y / 1025 - 117 / 100 + 1 / 2
      by linarith) (by norm_num : (0 : ℝ) ≤ (851 / 10) ^ 4 / 192 / 1681)
    nlinarith
  have k3 : (h - 2) * ((851 / 10 / h) ^ 2 /
      (32 * ((y ^ 2 + 1) / (4 * (13 * (ℓ + 1) / 20 + ℓ + 1))))) ≤ 1 / 20 := by
    rw [div_pow, show (h - 2) * ((851 / 10) ^ 2 / h ^ 2 / (32 * ((y ^ 2 + 1) /
      (4 * (13 * (ℓ + 1) / 20 + ℓ + 1))))) = (851 / 10) ^ 2 * (33 * (ℓ + 1) / 20) * (h - 2) /
        (8 * h ^ 2 * (y ^ 2 + 1)) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have a1 : (ℓ + 1) * (h - 2) ≤ 14 * y / 25 := by nlinarith
    have a2 : (1681 : ℝ) ≤ h ^ 2 := by nlinarith
    have a3 : 656 / 5 * y ≤ y ^ 2 := by nlinarith
    have a4 : 1681 * (656 / 5 * y) ≤ h ^ 2 * y ^ 2 :=
      mul_le_mul a2 a3 (by positivity) (by positivity)
    nlinarith
  linarith [mul_add (h - 2) ((ℓ + 1 / 2) * (851 / 10 / h) ^ 4 / 192)
    ((851 / 10 / h) ^ 2 / (32 * ((y ^ 2 + 1) / (4 * (13 * (ℓ + 1) / 20 + ℓ + 1)))))]

/-- The mean path cost under expansion, for `h ≥ 41`: `(h - 2) expPath` is at most
`(h - 2)(1.7019 ℓ + 2.56)` plus small terms. -/
lemma path_le {y h S β ℓ : ℝ} (hh : 41 ≤ h) (hy : 16 / 5 * h ≤ y)
    (hℓ : ℓ = 14 * y / (25 * h) - 117 / 100) (hβ1 : 99 * y / 50 ≤ β) (hβ2 : β ≤ 99 * y / 50 + 1)
    (hS1 : 8 * β * (ℓ + 117 / 100) ≤ S) (hS2 : S ≤ 8 * β * (ℓ + 117 / 100) + 1) :
    (h - 2) * expPath S β ℓ ((y ^ 2 + 1) / (4 * (13 * (ℓ + 1) / 20 + ℓ + 1))) ≤
      (h - 2) * (17019 / 10000 * ℓ + 64 / 25) + 125 / 2112 + 1 / 20 +
        163 * (14 * y / 1025 - 117 / 100 + 1 / 2) / h := by
  have hh0 : 0 < h := by linarith
  have hy0 : 0 < y := by linarith
  obtain ⟨hℓ1, hℓh, hℓy⟩ := ell_bounds hh hy hℓ
  have hβ0 : 0 < β := by linarith
  have hS : 1 ≤ S := by
    have := mul_le_mul (show (1 : ℝ) ≤ 8 * β by linarith) (show 1 ≤ ℓ + 117 / 100 by linarith)
      (by norm_num) (by linarith)
    linarith
  have hu : β * ℓ ≤ S := by
    have := mul_le_mul_of_nonneg_left (show ℓ ≤ 8 * (ℓ + 117 / 100) by linarith) hβ0.le
    linarith
  have ht := ratio_le hh hy hℓ1 hℓh hβ2 hS2 (by linarith)
  have hexp := expPath_le hS hβ0 hℓ1 hu hS1 hS2 (by positivity) ht
  have hh2 : 0 ≤ h - 2 := by linarith
  have k1 : (h - 2) * (3 / (8 * β)) ≤ 125 / 2112 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have k2 := last_phase_le hh hy hℓ1 hℓh hℓy
  have := mul_le_mul_of_nonneg_left hexp hh2
  nlinarith

/-- The bound `â` on the connector size for `h ≥ 41`. -/
noncomputable def connBound (y h : ℝ) : ℝ :=
  1 + 125 / 2112 + 1 / 20 +
    3927 / 1250 * (3041 / 2000 * (14 * y / (25 * h) - 117 / 100 + 97 / 100)) * (1000 * h / 2579) +
    (h - 2) * (17019 / 10000 * (14 * y / (25 * h) - 117 / 100) + 64 / 25) +
    163 * (14 * y / 1025 - 117 / 100 + 1 / 2) / h

lemma mul_connBound {y h : ℝ} (hh : 0 < h) : h * connBound y h =
    h * (1 + 125 / 2112 + 1 / 20) +
      3927 / 1250 * (3041 / 2000 * (14 * y / 25 - h / 5)) * (1000 * h / 2579) +
      (h - 2) * (17019 / 10000 * (14 * y / 25 - 117 * h / 100) + 64 * h / 25) +
      163 * (14 * y / 1025 - 67 / 100) := by
  unfold connBound
  field_simp
  ring

/-- Case 1 budget for `h ≥ 41`. -/
lemma budget_expand_le {y h ℓ L M : ℝ} (hh : 41 ≤ h) (hy : 16 / 5 * h ≤ y)
    (hℓ : ℓ = 14 * y / (25 * h) - 117 / 100) (hL : L = 13 * (ℓ + 1) / 20)
    (hM : M ≤ 99 * y / 50 ∨ M ≤ connBound y h) :
    (h - 2) * M + ((2 * L + 3 * ℓ + 1) * y ^ 2 + 2 * L + ℓ + 1) /
        (2 * (ℓ + 1) * (2 * L + 2 * ℓ + 1)) ≤ 16 / 5 * h * y := by
  have hh0 : 0 < h := by linarith
  refine budget_expand_of (p := 14 * y / 25 - 117 * h / 100) (u := 13 / 20) (by linarith)
    (by linarith) (by norm_num) (by rw [hℓ]; field_simp) (by rw [hL]; ring) hh0
    (mul_connBound hh0) hM ?_ ?_ <;>
  · obtain ⟨z, hz, rfl⟩ : ∃ z, 0 ≤ z ∧ y = 16 / 5 * h + z :=
      ⟨y - 16 / 5 * h, by linarith, by ring⟩
    obtain ⟨w, hw, rfl⟩ : ∃ w, 0 ≤ w ∧ h = 41 + w := ⟨h - 41, by linarith, by ring⟩
    monomial_linarith hz hw 5

/-- Cases 2 and 3 budget for `h ≥ 41`. -/
lemma budget_branch_le {y h ℓ M : ℝ} (hh : 41 ≤ h) (hy : 16 / 5 * h ≤ y)
    (hℓ : ℓ = 14 * y / (25 * h) - 117 / 100) (hM : M ≤ 99 * y / 50 ∨ M ≤ connBound y h) :
    (h - 2) * M + (y ^ 2 + 1 + 2 * ℓ * M) / (2 * (ℓ + 1)) ≤ 16 / 5 * h * y := by
  have hh0 : 0 < h := by linarith
  refine budget_branch_of (p := 14 * y / 25 - 117 * h / 100) (by linarith) (by linarith)
    (by rw [hℓ]; field_simp) hh0 (mul_connBound hh0) hM ?_ ?_ <;>
  · obtain ⟨z, hz, rfl⟩ : ∃ z, 0 ≤ z ∧ y = 16 / 5 * h + z :=
      ⟨y - 16 / 5 * h, by linarith, by ring⟩
    obtain ⟨w, hw, rfl⟩ : ∃ w, 0 ≤ w ∧ h = 41 + w := ⟨h - 41, by linarith, by ring⟩
    monomial_linarith hz hw 5

/-- The side conditions of `expPath` for `h ≥ 41`: `4S ≤ n + 1` and `β(ℓ + 1) ≤ (ℓ + 1/2)τ₀`
with `τ₀ = (n + 1)/(4(L + ℓ + 1))`. -/
lemma expPath_conditions {y h ℓ β S : ℝ} (hh : 41 ≤ h) (hy : 16 / 5 * h ≤ y)
    (hℓ : ℓ = 14 * y / (25 * h) - 117 / 100) (hβ1 : 99 * y / 50 ≤ β) (hβ2 : β ≤ 99 * y / 50 + 1)
    (hS2 : S ≤ 8 * β * (ℓ + 117 / 100) + 1) :
    4 * S ≤ y ^ 2 + 1 ∧
      β * (ℓ + 1) ≤ (ℓ + 1 / 2) * ((y ^ 2 + 1) / (4 * (13 * (ℓ + 1) / 20 + ℓ + 1))) := by
  have hy0 : 0 < y := by linarith
  obtain ⟨hℓ1, -, hℓy⟩ := ell_bounds hh hy hℓ
  have hℓ' : 0 < ℓ + 1 / 2 := by linarith
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hβ2 (by positivity : (0 : ℝ) ≤ 8 * (ℓ + 117 / 100))
    have h2 : 8 * (ℓ + 117 / 100) * (99 * y / 50 + 1) ≤ 8 * (14 * y / 1025) * (99 * y / 50 + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  · rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    have hl : ℓ + 1 ≤ 1446 / 1000 * (ℓ + 1 / 2) := by linarith
    have hl2 : ℓ + 1 ≤ 14 * y / 1025 := by linarith
    have k1 := mul_le_mul hl (mul_le_mul hl2 hβ2 (by linarith) (by positivity))
      (mul_nonneg (by linarith) (by linarith)) (by positivity)
    have k2 := mul_nonneg hℓ'.le (show 0 ≤ y ^ 2 - 26 / 100 * y ^ 2 - 14 / 100 * y by nlinarith)
    nlinarith

/-- The parameters for `h ≥ 41` and `√n > 3.2 h`. -/
lemma exists_params (n h : ℕ) (hh : 41 ≤ h) (hn : 16 / 5 * (h : ℝ) < √n) :
    ∃ P : SepParams n h, P.K ≤ 16 / 5 * h * √n := by
  obtain ⟨y, hy_def⟩ : ∃ y, y = √(n : ℝ) := ⟨_, rfl⟩
  rw [← hy_def] at hn ⊢
  have hy : y ^ 2 = n := by rw [hy_def]; exact sq_sqrt (Nat.cast_nonneg n)
  have hh41 : (41 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith
  have hy0 : 0 < y := by linarith
  obtain ⟨ℓ, hℓ_def⟩ : ∃ ℓ : ℝ, ℓ = 14 * y / (25 * h) - 117 / 100 := ⟨_, rfl⟩
  obtain ⟨hℓ1, hℓh, hℓy⟩ := ell_bounds hh41 hn.le hℓ_def
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ' : 0 < ℓ + 1 / 2 := by linarith
  obtain ⟨β, hβ_def⟩ : ∃ β : ℕ, β = ⌈99 * y / 50⌉₊ := ⟨_, rfl⟩
  obtain ⟨hβ1, hβ2⟩ : 99 * y / 50 ≤ β ∧ (β : ℝ) ≤ 99 * y / 50 + 1 :=
    hβ_def ▸ ceil_bounds (by positivity)
  have hβ0 : (0 : ℝ) < β := by linarith
  obtain ⟨S, hS_def⟩ : ∃ S : ℕ, S = ⌈8 * β * (ℓ + 117 / 100)⌉₊ := ⟨_, rfl⟩
  obtain ⟨hS1, hS2⟩ : 8 * β * (ℓ + 117 / 100) ≤ S ∧ (S : ℝ) ≤ 8 * β * (ℓ + 117 / 100) + 1 :=
    hS_def ▸ ceil_bounds (by positivity)
  have hβS : (β : ℝ) * (ℓ + 1) ≤ S := by
    have := mul_le_mul_of_nonneg_left (show ℓ + 1 ≤ 8 * (ℓ + 117 / 100) by linarith) hβ0.le
    linarith
  have hu : 1 ≤ (β : ℝ) * ℓ := by
    have := mul_le_mul (show (2 : ℝ) ≤ β by linarith) (show 1 / 2 ≤ ℓ by linarith)
      (by norm_num) (by linarith)
    linarith
  have huS : (β : ℝ) * ℓ ≤ S := by
    have := mul_le_mul_of_nonneg_left (show ℓ ≤ ℓ + 1 by linarith) hβ0.le
    linarith
  have hSR : (1 : ℝ) ≤ S := by linarith
  -- the conditions for the tent measures in the expander
  obtain ⟨h4S, hβτ⟩ := expPath_conditions hh41 hn.le hℓ_def hβ1 hβ2 hS2
  rw [hy] at h4S hβτ
  have h4S' : 4 * S ≤ n + 1 := by exact_mod_cast h4S
  have h2S : 2 * S ≤ n := by
    have : (1 : ℝ) ≤ n := by rw [← hy]; nlinarith
    have : 1 ≤ n := by exact_mod_cast this
    omega
  -- the connector size `a`
  obtain ⟨E, hE_def⟩ : ∃ E : ℝ,
      E = expPath S β ℓ ((n + 1) / (4 * (13 * (ℓ + 1) / 20 + ℓ + 1))) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := hE_def ▸ expPath_nonneg hSR hβ0 hℓ0 (by positivity) hu huS
  have hpath : (h - 2) * E ≤ (h - 2) * (17019 / 10000 * ℓ + 64 / 25) + 125 / 2112 + 1 / 20 +
      163 * (14 * y / 1025 - 117 / 100 + 1 / 2) / h := by
    rw [hE_def, ← hy]; exact path_le hh41 hn.le hℓ_def hβ1 hβ2 hS1 hS2
  have hsq : √(h * (n * (2 * (2 * S + 1) / (3 * S * (S + 1))) - 1)) ≤ 1000 * h / 2579 := by
    rw [← hy]
    refine sqrt_tour_le hh0 hy0 hSR hβ1 ?_
    rwa [show 14 * y / (25 * h) = ℓ + 117 / 100 by rw [hℓ_def]; ring]
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 1 + π * √(truncVar ℓ (13 * (ℓ + 1) / 20)) *
      √(h * (n * (2 * (2 * S + 1) / (3 * S * (S + 1))) - 1)) + (h - 2) * E := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by
    have : 0 ≤ ((h : ℝ) - 2) * E := mul_nonneg (by linarith) hE0
    have : 0 ≤ π * √(truncVar ℓ (13 * (ℓ + 1) / 20)) *
      √(h * (n * (2 * (2 * S + 1) / (3 * S * (S + 1))) - 1)) := by positivity
    linarith
  have ha : a ≤ connBound y h := by
    have h1 : π * √(truncVar ℓ (13 * (ℓ + 1) / 20)) *
        √(h * (n * (2 * (2 * S + 1) / (3 * S * (S + 1))) - 1)) ≤
        3927 / 1250 * (3041 / 2000 * (ℓ + 97 / 100)) * (1000 * h / 2579) :=
      mul_le_mul (mul_le_mul pi_le_d4 (sqrt_truncVar_le hℓ1) (sqrt_nonneg _) (by norm_num)) hsq
        (sqrt_nonneg _) (by positivity)
    rw [ha_def]
    unfold connBound
    rw [← hℓ_def]
    linarith
  have hM := max_le_or ha (show (β : ℝ) - 1 ≤ 99 * y / 50 by linarith)
  refine ⟨{ ℓ := ℓ, L := 13 * (ℓ + 1) / 20, S := S, β := β, a := a, E := E,
            K := 16 / 5 * h * y
            ℓ_pos := hℓ0
            L_nonneg := by positivity
            one_le_S := by exact_mod_cast hSR
            one_le_β := by exact_mod_cast (show (1 : ℝ) ≤ β by linarith)
            one_le_a := ha1
            two_S_le := h2S
            path := Or.inr ⟨h4S', hu, hβS, hβτ, hE_def.ge⟩
            connector := fun _ => ha_def.ge
            budget_expand := by rw [← hy]; exact budget_expand_le hh41 hn.le hℓ_def rfl hM
            budget_branch := by rw [← hy]; exact budget_branch_le hh41 hn.le hℓ_def hM },
    le_rfl⟩

end MinorFreeSeparators.LargeH
