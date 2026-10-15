import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Path costs of tent measures in expanders

Rank the vertices by their distance from an attachment set `U` and let `x_r` be the size of
the ball of radius `r` (capped at `S`). The tent measure of size `S` has mean distance
`∑_r φ(x_r)` with `φ(m) = (S - m)(S - m + 1)/(S(S + 1))`. If the balls grow by at least `β`
per layer, and also by the fraction `1/ℓ` or by `τ` (truncated expansion), then this sum is
bounded by a potential with three phases: weight `1/β` up to `u₀ = βℓ`, weight
`(ℓ + 1/2)/u` up to `m₁ = min(S, (ℓ + 1/2)τ)`, and weight `1/τ` after that.

The closed forms are `Φ(x) = ∫_x^S φ` (`tentInt`) and `Q(x) = ∫_x^S φ(u)/u du` (`tentLog`),
and the only analytic input is `log(b/a) ≥ 2(b - a)/(a + b)`. The result is
`tent_sum_le_expPath`; the last lemmas bound the pieces of `expPath`.
-/

namespace MinorFreeSeparators

open Finset

section Tent

variable (S : ℝ)

/-- `φ(m) = (S - m)(S - m + 1)/(S(S + 1))`: the tent mass beyond the `m` closest vertices. -/
noncomputable def tentTail (m : ℝ) : ℝ := (S - m) * (S - m + 1) / (S * (S + 1))

/-- `Φ(x) = ∫_x^S φ`. -/
noncomputable def tentInt (x : ℝ) : ℝ := ((S - x) ^ 3 / 3 + (S - x) ^ 2 / 2) / (S * (S + 1))

/-- `Q(x) = ∫_x^S φ(u)/u du`. -/
noncomputable def tentLog (x : ℝ) : ℝ :=
  Real.log (S / x) - (2 * S + 1) * (S - x) / (S * (S + 1)) +
    (S ^ 2 - x ^ 2) / (2 * S * (S + 1))

variable {S}

lemma tentTail_nonneg (hS : 0 < S) {b : ℝ} (hb : b ≤ S) : 0 ≤ tentTail S b := by
  unfold tentTail
  apply div_nonneg _ (by positivity)
  nlinarith

lemma tentTail_anti (hS : 0 < S) {a b : ℝ} (hab : a ≤ b) (hb : b ≤ S) :
    tentTail S b ≤ tentTail S a := by
  unfold tentTail
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

lemma tentTail_self : tentTail S S = 0 := by simp [tentTail]

/-- `Φ(a) - Φ(b) ≥ (b - a) φ(b)`. -/
lemma tentInt_sub (hS : 0 < S) {a b : ℝ} (hab : a ≤ b) (hb : b ≤ S) :
    (b - a) * tentTail S b ≤ tentInt S a - tentInt S b := by
  unfold tentTail tentInt
  rw [mul_div_assoc', ← sub_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 : 0 ≤ S - b := by linarith
  have h2 : 0 ≤ b - a := by linarith
  nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h2) h2, mul_nonneg h2 h2,
    mul_nonneg (mul_nonneg h2 h2) h2, mul_nonneg (mul_nonneg h1 h1) h2]

lemma tentInt_anti (hS : 0 < S) {a b : ℝ} (hab : a ≤ b) (hb : b ≤ S) :
    tentInt S b ≤ tentInt S a := by
  have := tentInt_sub hS hab hb
  have := mul_nonneg (by linarith : 0 ≤ b - a) (tentTail_nonneg hS hb)
  linarith

lemma tentInt_nonneg (hS : 0 < S) {x : ℝ} (hx : x ≤ S) : 0 ≤ tentInt S x := by
  unfold tentInt
  have : 0 ≤ S - x := by linarith
  positivity

/-- `log(b/a) ≥ 2(b - a)/(a + b)`. -/
lemma two_mul_div_le_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    2 * (b - a) / (a + b) ≤ Real.log (b / a) := by
  have h := Real.le_log_one_add_of_nonneg (x := (b - a) / a) (div_nonneg (by linarith) ha.le)
  have e1 : 1 + (b - a) / a = b / a := by field_simp; ring
  have e2 : 2 * ((b - a) / a) / ((b - a) / a + 2) = 2 * (b - a) / (a + b) := by
    field_simp
    ring_nf
  rw [e1, e2] at h
  exact h

/-- `log(1 + t) ≤ 4t/(3(t + 2)) + t(t + 2)/(6(t + 1))` for `t ≥ 0`: the series in
`s = t/(t + 2)`, with the tail after the first term bounded by a geometric series. -/
lemma log_one_add_le {t : ℝ} (ht : 0 ≤ t) :
    Real.log (1 + t) ≤ 4 * t / (3 * (t + 2)) + t * (t + 2) / (6 * (t + 1)) := by
  obtain ⟨s, hs⟩ : ∃ s, s = t / (t + 2) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := hs ▸ div_nonneg ht (by linarith)
  have hs1 : s < 1 := by rw [hs, div_lt_one (by linarith)]; linarith
  have hs2 : s ^ 2 < 1 := by nlinarith
  have hf := Real.hasSum_log_one_add ht
  rw [← hs] at hf
  have hg : HasSum (fun k : ℕ => 2 / 3 * s * (s ^ 2) ^ k + if k = 0 then 4 * s / 3 else 0)
      (2 / 3 * s * (1 - s ^ 2)⁻¹ + 4 * s / 3) :=
    ((hasSum_geometric_of_lt_one (sq_nonneg s) hs2).mul_left (2 / 3 * s)).add
      (hasSum_ite_eq 0 (4 * s / 3))
  have hle := hasSum_le (fun k => ?_) hf hg
  · refine hle.trans (le_of_eq ?_)
    have e1 : 1 - s ^ 2 = 4 * (t + 1) / (t + 2) ^ 2 := by rw [hs]; field_simp; ring
    rw [e1, inv_div, hs]
    field_simp
    ring
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num; linarith
    · have e : 2 / 3 * s * (s ^ 2) ^ k = 2 / 3 * s ^ (2 * k + 1) := by rw [← pow_mul]; ring
      rw [if_neg hk.ne', add_zero, e]
      have hk' : (3 : ℝ) ≤ 2 * k + 1 := by
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have hp : 0 ≤ s ^ (2 * k + 1) := pow_nonneg hs0 _
      rw [show (2 : ℝ) * (1 / (2 * k + 1)) * s ^ (2 * k + 1) =
        2 * s ^ (2 * k + 1) / (2 * k + 1) by ring, div_le_iff₀ (by linarith)]
      nlinarith

/-- `Q(a) - Q(b) ≥ 2(b - a)/(a + b) · φ(b)`. -/
lemma tentLog_sub (hS : 0 < S) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ S) :
    2 * (b - a) / (a + b) * tentTail S b ≤ tentLog S a - tentLog S b := by
  have hb0 : 0 < b := by linarith
  have hlog : Real.log (S / a) - Real.log (S / b) = Real.log (b / a) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  have hl := two_mul_div_le_log ha hab
  have hσ : tentTail S b ≤ tentTail S ((a + b) / 2) := tentTail_anti hS (by linarith) hb
  have hw : 0 ≤ 2 * (b - a) / (a + b) := div_nonneg (by linarith) (by linarith)
  -- `Q(a) - Q(b) ≥ 2(b-a)/(a+b) · φ((a+b)/2)`
  have key : 2 * (b - a) / (a + b) * tentTail S ((a + b) / 2) ≤ tentLog S a - tentLog S b := by
    have e : tentLog S a - tentLog S b = Real.log (b / a) -
        (2 * S + 1) * (b - a) / (S * (S + 1)) + (b ^ 2 - a ^ 2) / (2 * S * (S + 1)) := by
      unfold tentLog
      rw [← hlog]
      field_simp
      ring
    rw [e]
    have e2 : 2 * (b - a) / (a + b) * tentTail S ((a + b) / 2) = 2 * (b - a) / (a + b) -
        (2 * S + 1) * (b - a) / (S * (S + 1)) + (b ^ 2 - a ^ 2) / (2 * S * (S + 1)) := by
      unfold tentTail
      field_simp
      ring
    rw [e2]
    linarith
  exact le_trans (mul_le_mul_of_nonneg_left hσ hw) key

lemma tentLog_self (hS : 0 < S) : tentLog S S = 0 := by
  unfold tentLog
  rw [div_self hS.ne', Real.log_one]
  ring

lemma tentLog_anti (hS : 0 < S) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ S) :
    tentLog S b ≤ tentLog S a := by
  have := tentLog_sub hS ha hab hb
  have : 0 ≤ 2 * (b - a) / (a + b) * tentTail S b :=
    mul_nonneg (div_nonneg (by linarith) (by linarith)) (tentTail_nonneg hS hb)
  linarith

/-- The potential of the three growth phases, with `u₀ = βℓ` and a cut-off `m₁`. -/
noncomputable def tentPot (S β ℓ τ m₁ m : ℝ) : ℝ :=
  (tentInt S (min m (β * ℓ)) - tentInt S (β * ℓ)) / β +
    (ℓ + 1 / 2) * (tentLog S (max (β * ℓ) (min m m₁)) - tentLog S m₁) +
    tentInt S (max m m₁) / τ

/-- Linear phase entering the geometric phase: `(u₀ - m)/β + (2ℓ+1)v/(2u₀ + v) ≥ 1` for
`v = m' - u₀ > 0`, `m + β ≤ m'` and `u₀ = βℓ`. -/
lemma weight_lin_geo {β ℓ m m' : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ) (hmu : m ≤ β * ℓ)
    (hum : β * ℓ < m') (hstep : m + β ≤ m') :
    1 ≤ (β * ℓ - m) / β + 2 * (ℓ + 1 / 2) * (m' - β * ℓ) / (β * ℓ + m') := by
  have hd : 0 < β * ℓ + m' := by nlinarith
  have hA : 0 ≤ (β * ℓ - m) / β := div_nonneg (by linarith) hβ.le
  rcases le_or_gt (m' - β * ℓ) β with h5 | h5
  · have e1 : 1 - (m' - β * ℓ) / β ≤ (β * ℓ - m) / β := by
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hβ]; linarith
    have e2 : (m' - β * ℓ) / β ≤ 2 * (ℓ + 1 / 2) * (m' - β * ℓ) / (β * ℓ + m') := by
      rw [div_le_div_iff₀ hβ hd]
      have h0 : 0 ≤ m' - β * ℓ := by linarith
      have e : 2 * (ℓ + 1 / 2) * (m' - β * ℓ) * β = (m' - β * ℓ) * (2 * (β * ℓ) + β) := by
        ring
      rw [e]
      nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ β - (m' - β * ℓ))]
    linarith
  · have e2 : 1 ≤ 2 * (ℓ + 1 / 2) * (m' - β * ℓ) / (β * ℓ + m') := by
      rw [le_div_iff₀ hd]
      have e : 2 * (ℓ + 1 / 2) * (m' - β * ℓ) = (β * ℓ + m') + 2 * ℓ * (m' - β * ℓ - β) := by
        ring
      rw [e]
      nlinarith [mul_nonneg hℓ.le (by linarith : (0 : ℝ) ≤ m' - β * ℓ - β)]
    linarith

/-- Geometric phase: `2(ℓ + 1/2)(m' - m)/(m + m') ≥ 1` when `m' ≥ (1 + 1/ℓ) m`. -/
lemma weight_geo {ℓ m m' : ℝ} (hℓ : 0 < ℓ) (hm : 0 < m) (h : (ℓ + 1) * m ≤ ℓ * m') :
    1 ≤ 2 * (ℓ + 1 / 2) * (m' - m) / (m + m') := by
  have hm' : 0 < m' := by nlinarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- Geometric phase entering the last phase (`m₁ = (ℓ + 1/2)τ`), step `m' ≥ (1 + 1/ℓ) m`. -/
lemma weight_geo_last {ℓ τ m m₁ m' : ℝ} (hℓ : 0 < ℓ) (hm : 0 < m) (hmm : m < m₁)
    (hm₁ : m₁ = (ℓ + 1 / 2) * τ) (hm' : m₁ < m') (h : (ℓ + 1) * m ≤ ℓ * m') :
    1 ≤ 2 * (ℓ + 1 / 2) * (m₁ - m) / (m + m₁) + (m' - m₁) / τ := by
  have hℓ' : 0 < ℓ + 1 / 2 := by linarith
  have hm₁0 : 0 < m₁ := by linarith
  have hB : (m' - m₁) / τ = (ℓ + 1 / 2) * (m' - m₁) / m₁ := by
    rw [hm₁]; field_simp
  rw [hB, div_add_div _ _ (by linarith) hm₁0.ne', le_div_iff₀ (by positivity), one_mul]
  have hB0 : 0 ≤ (ℓ + 1 / 2) * (m' - m₁) := mul_nonneg hℓ'.le (by linarith)
  rcases le_or_gt ((ℓ + 1) * m) (ℓ * m₁) with hq | hq
  · have h1 : m + m₁ ≤ 2 * (ℓ + 1 / 2) * (m₁ - m) := by nlinarith
    have h2 : 0 ≤ (m + m₁) * ((ℓ + 1 / 2) * (m' - m₁)) := mul_nonneg (by linarith) hB0
    nlinarith
  · have hr : 0 ≤ (2 * ℓ + 1) * m - (2 * ℓ - 1) * m₁ := by nlinarith
    have hl : (ℓ + 1 / 2) * ((ℓ + 1) * m - ℓ * m₁) ≤ ℓ * ((ℓ + 1 / 2) * (m' - m₁)) := by
      have := mul_le_mul_of_nonneg_left (show (ℓ + 1) * m - ℓ * m₁ ≤ ℓ * m' - ℓ * m₁ by linarith)
        hℓ'.le
      linarith
    have hp : 0 ≤ ((ℓ + 1) * m - ℓ * m₁) * ((2 * ℓ + 1) * m - (2 * ℓ - 1) * m₁) :=
      mul_nonneg (by linarith) hr
    have key : ℓ * ((m + m₁) * m₁) ≤
        ℓ * (2 * (ℓ + 1 / 2) * (m₁ - m) * m₁ + (m + m₁) * ((ℓ + 1 / 2) * (m' - m₁))) := by
      have h3 := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ m + m₁)
      nlinarith
    exact le_of_mul_le_mul_left key hℓ

/-- Geometric phase entering the last phase, step `m' ≥ m + τ`. -/
lemma weight_tau_last {ℓ τ m m₁ m' : ℝ} (hℓ : 0 < ℓ) (hm : 0 < m) (hmm : m < m₁)
    (hm₁ : m₁ = (ℓ + 1 / 2) * τ) (h : m + τ ≤ m') :
    1 ≤ 2 * (ℓ + 1 / 2) * (m₁ - m) / (m + m₁) + (m' - m₁) / τ := by
  have hℓ' : 0 < ℓ + 1 / 2 := by linarith
  have hτ : 0 < τ := by
    by_contra hc; push Not at hc; nlinarith
  have e1 : (m₁ - m) / τ ≤ 2 * (ℓ + 1 / 2) * (m₁ - m) / (m + m₁) := by
    rw [div_le_div_iff₀ hτ (by linarith)]
    have : m + m₁ ≤ 2 * ((ℓ + 1 / 2) * τ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ m₁ - m)]
  have e2 : 1 - (m₁ - m) / τ ≤ (m' - m₁) / τ := by
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hτ]; linarith
  linarith

/-- The weights of the three phases add up to at least `1` along one step of growth. -/
lemma tent_weight {β ℓ τ m₁ m m' : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (hm₁ : m₁ = min S ((ℓ + 1 / 2) * τ)) (hβm₁ : β * (ℓ + 1) ≤ m₁) (hm : 0 < m)
    (hm'S : m' < S) (hstep : m + β ≤ m') (hexp : (ℓ + 1) * m ≤ ℓ * m' ∨ m + τ ≤ m') :
    1 ≤ (min m' (β * ℓ) - min m (β * ℓ)) / β +
      2 * (ℓ + 1 / 2) * (max (β * ℓ) (min m' m₁) - max (β * ℓ) (min m m₁)) /
        (max (β * ℓ) (min m m₁) + max (β * ℓ) (min m' m₁)) +
      (max m' m₁ - max m m₁) / τ := by
  have hu₀0 : 0 < β * ℓ := by positivity
  have hm₁S : m₁ ≤ S := hm₁ ▸ min_le_left _ _
  have hm₁τ : m₁ ≤ (ℓ + 1 / 2) * τ := hm₁ ▸ min_le_right _ _
  have hu₀m₁ : β * ℓ + β ≤ m₁ := by linarith
  have hmm' : m < m' := by linarith
  have hm1 : m₁ < S → m₁ = (ℓ + 1 / 2) * τ := by
    intro h
    rcases min_choice S ((ℓ + 1 / 2) * τ) with hc | hc
    · rw [← hm₁] at hc; linarith
    · rw [hm₁, hc]
  -- weights are nonnegative
  have wA0 : 0 ≤ (min m' (β * ℓ) - min m (β * ℓ)) / β :=
    div_nonneg (by have := min_le_min_right (β * ℓ) hmm'.le; linarith) hβ.le
  have wC0 : 0 ≤ (max m' m₁ - max m m₁) / τ :=
    div_nonneg (by have := max_le_max_right m₁ hmm'.le; linarith) hτ.le
  have wB0 : 0 ≤ 2 * (ℓ + 1 / 2) * (max (β * ℓ) (min m' m₁) - max (β * ℓ) (min m m₁)) /
      (max (β * ℓ) (min m m₁) + max (β * ℓ) (min m' m₁)) := by
    have h1 := le_max_left (β * ℓ) (min m m₁)
    have h2 := max_le_max_left (β * ℓ) (min_le_min_right m₁ hmm'.le)
    apply div_nonneg _ (by linarith)
    exact mul_nonneg (by linarith) (by linarith)
  rcases le_or_gt m' (β * ℓ) with h1 | h1
  · -- `m < m' ≤ u₀`: the linear phase
    rw [min_eq_left h1, min_eq_left (by linarith : m ≤ β * ℓ)]
    have : 1 ≤ (m' - m) / β := by rw [le_div_iff₀ hβ]; linarith
    linarith
  rcases le_or_gt (β * ℓ) m with h2 | h2
  · -- `u₀ ≤ m`
    rw [min_eq_right h1.le, min_eq_right h2, sub_self, zero_div, zero_add]
    rcases le_or_gt m₁ m with h3 | h3
    · -- `m₁ ≤ m`: the last phase, where the step is at least `τ`
      rw [max_eq_left (by linarith : m₁ ≤ m'), max_eq_left h3, min_eq_right h3,
        min_eq_right (by linarith : m₁ ≤ m'), sub_self, mul_zero, zero_div, zero_add]
      have hm1' := hm1 (by linarith)
      rw [le_div_iff₀ hτ, one_mul]
      rcases hexp with h | h
      · have : ℓ * τ ≤ m := by nlinarith
        nlinarith
      · linarith
    rcases le_or_gt m' m₁ with h4 | h4
    · -- `u₀ ≤ m < m' ≤ m₁`: the geometric phase
      rw [min_eq_left h3.le, min_eq_left h4, max_eq_right h2, max_eq_right h1.le,
        max_eq_right h4, max_eq_right h3.le, sub_self, zero_div, add_zero]
      rcases hexp with h | h
      · exact weight_geo hℓ hm h
      · -- the step `τ` exceeds `m/ℓ` here
        have hm' : m ≤ ℓ * τ := by nlinarith
        exact weight_geo hℓ hm (by nlinarith)
    · -- `u₀ ≤ m < m₁ < m'`: geometric, then the last phase
      rw [min_eq_left h3.le, min_eq_right h4.le, max_eq_right h2, max_eq_right (by linarith),
        max_eq_left h4.le, max_eq_right h3.le]
      have hm1' := hm1 (by linarith)
      rcases hexp with h | h
      · exact weight_geo_last hℓ hm h3 hm1' h4 h
      · exact weight_tau_last hℓ hm h3 hm1' h
  · -- `m < u₀ < m'`
    rw [min_eq_right h1.le, min_eq_left h2.le, max_eq_left (le_trans (min_le_left _ _) h2.le)]
    rcases le_or_gt m' m₁ with h4 | h4
    · rw [min_eq_left h4, max_eq_right h1.le]
      have := weight_lin_geo hβ hℓ h2.le h1 hstep
      have : 0 ≤ (max m' m₁ - max m m₁) / τ := wC0
      linarith
    · rw [min_eq_right h4.le, max_eq_right (by linarith : β * ℓ ≤ m₁)]
      have := weight_lin_geo hβ hℓ h2.le (by linarith) (by linarith : m + β ≤ m₁)
      linarith

lemma tentPot_anti (hS : 0 < S) {β ℓ τ m₁ m m' : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (hu : β * ℓ ≤ m₁) (hm₁S : m₁ ≤ S) (hmm : m ≤ m') (hm'S : m' ≤ S) :
    tentPot S β ℓ τ m₁ m' ≤ tentPot S β ℓ τ m₁ m := by
  unfold tentPot
  have hA : tentInt S (min m' (β * ℓ)) ≤ tentInt S (min m (β * ℓ)) :=
    tentInt_anti hS (min_le_min_right _ hmm) (le_trans (min_le_right _ _) (le_trans hu hm₁S))
  have hB : tentLog S (max (β * ℓ) (min m' m₁)) ≤ tentLog S (max (β * ℓ) (min m m₁)) :=
    tentLog_anti hS (lt_of_lt_of_le (by positivity) (le_max_left _ _))
      (max_le_max_left _ (min_le_min_right _ hmm))
      (max_le (le_trans hu hm₁S) (le_trans (min_le_right _ _) hm₁S))
  have hC : tentInt S (max m' m₁) ≤ tentInt S (max m m₁) :=
    tentInt_anti hS (max_le_max_right _ hmm) (max_le hm'S hm₁S)
  have e1 := div_le_div_of_nonneg_right (by linarith : tentInt S (min m' (β * ℓ)) -
    tentInt S (β * ℓ) ≤ tentInt S (min m (β * ℓ)) - tentInt S (β * ℓ)) hβ.le
  have e2 := mul_le_mul_of_nonneg_left (by linarith : tentLog S (max (β * ℓ) (min m' m₁)) -
    tentLog S m₁ ≤ tentLog S (max (β * ℓ) (min m m₁)) - tentLog S m₁)
    (by linarith : (0 : ℝ) ≤ ℓ + 1 / 2)
  have e3 := div_le_div_of_nonneg_right hC hτ.le
  linarith

lemma tentPot_nonneg (hS : 0 < S) {β ℓ τ m₁ m : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (hu : β * ℓ ≤ m₁) (hm₁S : m₁ ≤ S) (hm : m ≤ S) : 0 ≤ tentPot S β ℓ τ m₁ m := by
  unfold tentPot
  have hA : tentInt S (β * ℓ) ≤ tentInt S (min m (β * ℓ)) :=
    tentInt_anti hS (min_le_right _ _) (le_trans hu hm₁S)
  have hB : tentLog S m₁ ≤ tentLog S (max (β * ℓ) (min m m₁)) :=
    tentLog_anti hS (lt_of_lt_of_le (by positivity) (le_max_left _ _))
      (max_le hu (min_le_right _ _)) hm₁S
  have hC := tentInt_nonneg hS (max_le hm hm₁S)
  have e1 : 0 ≤ (tentInt S (min m (β * ℓ)) - tentInt S (β * ℓ)) / β :=
    div_nonneg (by linarith) hβ.le
  have e2 : 0 ≤ (ℓ + 1 / 2) * (tentLog S (max (β * ℓ) (min m m₁)) - tentLog S m₁) :=
    mul_nonneg (by linarith) (by linarith)
  have e3 : 0 ≤ tentInt S (max m m₁) / τ := div_nonneg hC hτ.le
  linarith

/-- One step of growth pays for the tent mass beyond the new ball. -/
lemma tentPot_step (hS : 0 < S) {β ℓ τ m₁ m m' : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (hm₁ : m₁ = min S ((ℓ + 1 / 2) * τ)) (hβm₁ : β * (ℓ + 1) ≤ m₁) (hm : 0 < m)
    (hmm : m ≤ m') (hm'S : m' ≤ S)
    (hgrow : m + β ≤ m' ∧ ((ℓ + 1) * m ≤ ℓ * m' ∨ m + τ ≤ m')) :
    tentTail S m' ≤ tentPot S β ℓ τ m₁ m - tentPot S β ℓ τ m₁ m' := by
  have hm₁S : m₁ ≤ S := hm₁ ▸ min_le_left _ _
  have hu : β * ℓ ≤ m₁ := by nlinarith
  rcases eq_or_lt_of_le hm'S with h | h
  · rw [h, tentTail_self]
    have := tentPot_anti hS hβ hℓ hτ hu hm₁S (h ▸ hmm) le_rfl (β := β) (m₁ := m₁)
    linarith
  set T := tentTail S m'
  have hT : 0 ≤ T := tentTail_nonneg hS hm'S
  set u₀ := β * ℓ with hu₀
  have hu₀0 : 0 < u₀ := by positivity
  -- the three decrements
  have dA : (min m' u₀ - min m u₀) * T ≤ tentInt S (min m u₀) - tentInt S (min m' u₀) := by
    have h1 := min_le_min_right u₀ hmm
    have h2 : min m' u₀ ≤ S := le_trans (min_le_right _ _) (le_trans hu hm₁S)
    have h3 : T ≤ tentTail S (min m' u₀) := tentTail_anti hS (min_le_left _ _) hm'S
    have := tentInt_sub hS h1 h2
    have := mul_le_mul_of_nonneg_left h3 (by linarith : 0 ≤ min m' u₀ - min m u₀)
    linarith
  set a₂ := max u₀ (min m m₁)
  set b₂ := max u₀ (min m' m₁)
  have ha₂ : u₀ ≤ a₂ := le_max_left _ _
  have hab₂ : a₂ ≤ b₂ := max_le_max_left _ (min_le_min_right _ hmm)
  have hb₂ : b₂ ≤ m₁ := max_le hu (min_le_right _ _)
  have dB : 2 * (b₂ - a₂) / (a₂ + b₂) * T ≤ tentLog S a₂ - tentLog S b₂ := by
    have hsub := tentLog_sub hS (by linarith) hab₂ (le_trans hb₂ hm₁S)
    by_cases hb : b₂ ≤ m'
    · have h3 : T ≤ tentTail S b₂ := tentTail_anti hS hb hm'S
      have := mul_le_mul_of_nonneg_left h3
        (div_nonneg (by linarith) (by linarith) : 0 ≤ 2 * (b₂ - a₂) / (a₂ + b₂))
      linarith
    · push Not at hb
      have hbu : b₂ = u₀ := by
        rcases max_choice u₀ (min m' m₁) with hc | hc
        · exact hc
        · have := min_le_left m' m₁; rw [← hc] at this; linarith
      have hau : a₂ = u₀ := le_antisymm (hbu ▸ hab₂) ha₂
      rw [hau, hbu, sub_self, mul_zero, zero_div, zero_mul, sub_self]
  have dC : (max m' m₁ - max m m₁) * T ≤ tentInt S (max m m₁) - tentInt S (max m' m₁) := by
    have h1 := max_le_max_right m₁ hmm
    have h2 : max m' m₁ ≤ S := max_le hm'S hm₁S
    have := tentInt_sub hS h1 h2
    rcases le_total m₁ m' with hc | hc
    · rw [max_eq_left hc] at this ⊢
      linarith
    · rw [max_eq_right hc, max_eq_right (le_trans hmm hc), sub_self, zero_mul, sub_self]
  have hw := tent_weight hβ hℓ hτ hm₁ hβm₁ hm h hgrow.1 hgrow.2
  have e : tentPot S β ℓ τ m₁ m - tentPot S β ℓ τ m₁ m' =
      (tentInt S (min m u₀) - tentInt S (min m' u₀)) / β +
        (ℓ + 1 / 2) * (tentLog S a₂ - tentLog S b₂) +
        (tentInt S (max m m₁) - tentInt S (max m' m₁)) / τ := by
    unfold tentPot; ring
  rw [e]
  have f1 : (min m' u₀ - min m u₀) / β * T ≤
      (tentInt S (min m u₀) - tentInt S (min m' u₀)) / β := by
    rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right dA hβ.le
  have f2 : 2 * (ℓ + 1 / 2) * (b₂ - a₂) / (a₂ + b₂) * T ≤
      (ℓ + 1 / 2) * (tentLog S a₂ - tentLog S b₂) := by
    have := mul_le_mul_of_nonneg_left dB (by linarith : (0 : ℝ) ≤ ℓ + 1 / 2)
    calc 2 * (ℓ + 1 / 2) * (b₂ - a₂) / (a₂ + b₂) * T =
        (ℓ + 1 / 2) * (2 * (b₂ - a₂) / (a₂ + b₂) * T) := by ring
      _ ≤ _ := this
  have f3 : (max m' m₁ - max m m₁) / τ * T ≤
      (tentInt S (max m m₁) - tentInt S (max m' m₁)) / τ := by
    rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right dC hτ.le
  have := mul_le_mul_of_nonneg_right hw hT
  nlinarith

/-- **Path cost under expansion.** If the capped ball sizes `x_r` start at `1` or more and grow
by at least `β`, and by the fraction `1/ℓ` or by `τ`, while below `S`, then
`∑_r φ(x_r) ≤ φ(1) + Ψ(1)`. -/
lemma tent_sum_le (hS : 1 ≤ S) {β ℓ τ m₁ : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (hm₁ : m₁ = min S ((ℓ + 1 / 2) * τ)) (hβm₁ : β * (ℓ + 1) ≤ m₁) (x : ℕ → ℝ)
    (hx0 : 1 ≤ x 0) (hxS : ∀ r, x r ≤ S) (hmono : ∀ r, x r ≤ x (r + 1))
    (hgrow : ∀ r, x r < S → x (r + 1) = S ∨
      (x r + β ≤ x (r + 1) ∧ ((ℓ + 1) * x r ≤ ℓ * x (r + 1) ∨ x r + τ ≤ x (r + 1))))
    (M : ℕ) :
    ∑ r ∈ range M, tentTail S (x r) ≤ tentTail S 1 + tentPot S β ℓ τ m₁ 1 := by
  have hS0 : 0 < S := by linarith
  have hm₁S : m₁ ≤ S := hm₁ ▸ min_le_left _ _
  have hu : β * ℓ ≤ m₁ := by nlinarith
  have hpos : ∀ r, 0 < x r := by
    intro r
    induction r with
    | zero => linarith
    | succ r ih => linarith [hmono r]
  have key : ∀ M : ℕ, ∑ r ∈ range (M + 1), tentTail S (x r) + tentPot S β ℓ τ m₁ (x M) ≤
      tentTail S (x 0) + tentPot S β ℓ τ m₁ (x 0) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [sum_range_succ]
      have hstep : tentTail S (x (M + 1)) ≤
          tentPot S β ℓ τ m₁ (x M) - tentPot S β ℓ τ m₁ (x (M + 1)) := by
        rcases eq_or_lt_of_le (hxS M) with h | h
        · have h1 : x (M + 1) = S := le_antisymm (hxS _) (h ▸ hmono M)
          rw [h1, h, tentTail_self, sub_self]
        rcases hgrow M h with h1 | h1
        · rw [h1, tentTail_self]
          have := tentPot_anti hS0 hβ hℓ hτ hu hm₁S (hxS M) le_rfl (β := β) (m₁ := m₁)
          linarith
        · exact tentPot_step hS0 hβ hℓ hτ hm₁ hβm₁ (hpos M) (hmono M) (hxS _) h1
      linarith
  rcases M with _ | M
  · simp only [range_zero, sum_empty]
    have := tentPot_nonneg hS0 hβ hℓ hτ hu hm₁S hS (β := β) (m₁ := m₁) (m := 1)
    have := tentTail_nonneg hS0 hS
    linarith
  have h1 := key M
  have h2 := tentPot_nonneg hS0 hβ hℓ hτ hu hm₁S (hxS M) (β := β) (m₁ := m₁)
  have h3 := tentPot_anti hS0 hβ hℓ hτ hu hm₁S hx0 (hxS 0) (β := β) (m₁ := m₁)
  have h4 := tentTail_anti hS0 hx0 (hxS 0)
  linarith

/-- The closed form of the path cost under expansion: `φ(1) + Φ(1..u₀)/β + (ℓ + 1/2) Q(u₀)`
plus an upper bound for the cost of the last phase, which is small unless `S > (ℓ + 1/2)τ`. -/
noncomputable def expPath (S β ℓ τ : ℝ) : ℝ :=
  tentTail S 1 + (tentInt S 1 - tentInt S (β * ℓ)) / β + (ℓ + 1 / 2) * tentLog S (β * ℓ) +
    ((S ^ 2 / (4 * (ℓ + 1 / 2) * τ)) ^ 3 / 3 + (S ^ 2 / (4 * (ℓ + 1 / 2) * τ)) ^ 2 / 2) /
      (τ * (S * (S + 1)))

lemma expPath_nonneg (hS : 1 ≤ S) {β ℓ τ : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (hu : 1 ≤ β * ℓ) (huS : β * ℓ ≤ S) : 0 ≤ expPath S β ℓ τ := by
  have hS0 : 0 < S := by linarith
  unfold expPath
  have h1 := tentTail_nonneg hS0 hS
  have h2 : 0 ≤ (tentInt S 1 - tentInt S (β * ℓ)) / β :=
    div_nonneg (by linarith [tentInt_anti hS0 hu huS]) hβ.le
  have h3 : 0 ≤ (ℓ + 1 / 2) * tentLog S (β * ℓ) := by
    have := tentLog_anti hS0 (by linarith) huS le_rfl
    rw [tentLog_self hS0] at this
    exact mul_nonneg (by linarith) this
  have h4 : 0 ≤ ((S ^ 2 / (4 * (ℓ + 1 / 2) * τ)) ^ 3 / 3 +
      (S ^ 2 / (4 * (ℓ + 1 / 2) * τ)) ^ 2 / 2) /
      (τ * (S * (S + 1))) := by positivity
  linarith

lemma tentPot_one_le (hS : 1 ≤ S) {β ℓ τ m₁ : ℝ} (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (hm₁ : m₁ = min S ((ℓ + 1 / 2) * τ)) (hu : 1 ≤ β * ℓ) (hum : β * ℓ ≤ m₁) :
    tentTail S 1 + tentPot S β ℓ τ m₁ 1 ≤ expPath S β ℓ τ := by
  have hS0 : 0 < S := by linarith
  have hm₁S : m₁ ≤ S := hm₁ ▸ min_le_left _ _
  have hℓ' : 0 < ℓ + 1 / 2 := by linarith
  unfold tentPot expPath
  rw [min_eq_left hu, max_eq_left (le_trans (min_le_left _ _) hu),
    max_eq_right (le_trans hu hum)]
  have hQ : 0 ≤ tentLog S m₁ := by
    have := tentLog_anti hS0 (by linarith) hm₁S le_rfl
    rw [tentLog_self hS0] at this; exact this
  -- `S - m₁ ≤ S²/(4(ℓ+1/2)τ)`
  set v := S ^ 2 / (4 * (ℓ + 1 / 2) * τ)
  have hv : S - m₁ ≤ v := by
    rcases min_choice S ((ℓ + 1 / 2) * τ) with hc | hc
    · rw [hm₁, hc, sub_self]; positivity
    · rw [hm₁, hc]
      simp only [v]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (S - 2 * ((ℓ + 1 / 2) * τ))]
  have hd : 0 ≤ S - m₁ := by linarith
  have hI : tentInt S m₁ ≤ (v ^ 3 / 3 + v ^ 2 / 2) / (S * (S + 1)) := by
    unfold tentInt
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 := pow_le_pow_left₀ hd hv 3
    have h2 := pow_le_pow_left₀ hd hv 2
    linarith
  have e : (v ^ 3 / 3 + v ^ 2 / 2) / (τ * (S * (S + 1))) =
      (v ^ 3 / 3 + v ^ 2 / 2) / (S * (S + 1)) / τ := by
    rw [div_div, mul_comm τ]
  rw [e]
  have := div_le_div_of_nonneg_right hI hτ.le
  nlinarith

/-- **Path cost under expansion**, closed form. -/
theorem tent_sum_le_expPath (hS : 1 ≤ S) {β ℓ τ : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (hu : 1 ≤ β * ℓ) (hβS : β * (ℓ + 1) ≤ S) (hβτ : β * (ℓ + 1) ≤ (ℓ + 1 / 2) * τ)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0) (hxS : ∀ r, x r ≤ S) (hmono : ∀ r, x r ≤ x (r + 1))
    (hgrow : ∀ r, x r < S → x (r + 1) = S ∨
      (x r + β ≤ x (r + 1) ∧ ((ℓ + 1) * x r ≤ ℓ * x (r + 1) ∨ x r + τ ≤ x (r + 1))))
    (M : ℕ) :
    ∑ r ∈ range M, tentTail S (x r) ≤ expPath S β ℓ τ := by
  have hβm₁ : β * (ℓ + 1) ≤ min S ((ℓ + 1 / 2) * τ) := le_min hβS hβτ
  refine (tent_sum_le hS hβ hℓ hτ rfl hβm₁ x hx0 hxS hmono hgrow M).trans ?_
  exact tentPot_one_le hS hℓ hτ rfl hu (by nlinarith)

/-- The linear phase: `(Φ(1) - Φ(βℓ))/β ≤ ℓ(1 - w + w²/3) + ℓ/S` with `w = βℓ/S`. -/
lemma expPath_lin_le {S β ℓ : ℝ} (hS : 1 ≤ S) (hβ : 0 < β) (hℓ : 0 < ℓ) (hu : β * ℓ ≤ S) :
    (tentInt S 1 - tentInt S (β * ℓ)) / β ≤
      ℓ * (1 - β * ℓ / S + (β * ℓ / S) ^ 2 / 3) + ℓ / S := by
  have hS0 : 0 < S := by linarith
  have h0 : tentInt S 1 ≤ tentInt S 0 := tentInt_anti hS0 zero_le_one hS
  have hu0 : 0 < β * ℓ := by positivity
  have e : (tentInt S 0 - tentInt S (β * ℓ)) / β =
      ℓ * ((S ^ 2 - S * (β * ℓ) + (β * ℓ) ^ 2 / 3) + (2 * S - β * ℓ) / 2) / (S * (S + 1)) := by
    unfold tentInt; field_simp; ring
  have h1 : (tentInt S 1 - tentInt S (β * ℓ)) / β ≤ (tentInt S 0 - tentInt S (β * ℓ)) / β :=
    div_le_div_of_nonneg_right (by linarith) hβ.le
  rw [e] at h1
  refine h1.trans ?_
  set u := β * ℓ
  have e2 : ℓ * (1 - u / S + (u / S) ^ 2 / 3) + ℓ / S =
      ℓ * (S ^ 2 - S * u + u ^ 2 / 3 + S) / S ^ 2 := by field_simp
  rw [e2, div_le_div_iff₀ (by positivity) (by positivity)]
  have hq : 0 ≤ S ^ 2 - S * u + u ^ 2 / 3 := by nlinarith [sq_nonneg (S - u / 2)]
  have hq2 : 0 ≤ S - u / 2 := by linarith
  nlinarith [mul_nonneg hℓ.le hq, mul_nonneg (mul_nonneg hℓ.le hq) hS0.le,
    mul_nonneg (mul_nonneg hℓ.le hq2) (sq_nonneg S), mul_nonneg hℓ.le (sq_nonneg S)]

/-- `Q(u) ≤ log(S/u) - 3/2 + 2w - w²/2 + 1/(S + 1)` with `w = u/S`. -/
lemma tentLog_le {S u : ℝ} (hS : 1 ≤ S) (hu : 0 < u) (huS : u ≤ S) :
    tentLog S u ≤ Real.log (S / u) - 3 / 2 + 2 * (u / S) - (u / S) ^ 2 / 2 + 1 / (S + 1) := by
  have hS0 : 0 < S := by linarith
  unfold tentLog
  have e : -((2 * S + 1) * (S - u) / (S * (S + 1))) + (S ^ 2 - u ^ 2) / (2 * S * (S + 1)) =
      -3 / 2 + 2 * (u / S) - (u / S) ^ 2 / 2 + (S - u) ^ 2 / (2 * S ^ 2 * (S + 1)) := by
    field_simp; ring
  have h1 : (S - u) ^ 2 / (2 * S ^ 2 * (S + 1)) ≤ 1 / (S + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hu.le (by linarith : 0 ≤ S - u), mul_nonneg hu.le hu.le]
  linarith

/-- The correction for the last phase: with `t ≥ S/((ℓ + 1/2)τ)`, it is at most
`(ℓ + 1/2) t⁴/192 + t²/(32τ)`. -/
lemma expPath_last_le {S ℓ τ t : ℝ} (hS : 1 ≤ S) (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (ht : S / ((ℓ + 1 / 2) * τ) ≤ t) :
    ((S ^ 2 / (4 * (ℓ + 1 / 2) * τ)) ^ 3 / 3 + (S ^ 2 / (4 * (ℓ + 1 / 2) * τ)) ^ 2 / 2) /
      (τ * (S * (S + 1))) ≤ (ℓ + 1 / 2) * t ^ 4 / 192 + t ^ 2 / (32 * τ) := by
  have hS0 : 0 < S := by linarith
  have hℓ' : 0 < ℓ + 1 / 2 := by linarith
  set t₀ := S / ((ℓ + 1 / 2) * τ) with ht₀
  have ht₀0 : 0 ≤ t₀ := by positivity
  have e1 : S ^ 2 / (4 * (ℓ + 1 / 2) * τ) = S * t₀ / 4 := by rw [ht₀]; field_simp
  rw [e1]
  have h1 : ((S * t₀ / 4) ^ 3 / 3 + (S * t₀ / 4) ^ 2 / 2) / (τ * (S * (S + 1))) ≤
      ((S * t₀ / 4) ^ 3 / 3 + (S * t₀ / 4) ^ 2 / 2) / (τ * S ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have e2 : ((S * t₀ / 4) ^ 3 / 3 + (S * t₀ / 4) ^ 2 / 2) / (τ * S ^ 2) =
      (ℓ + 1 / 2) * t₀ ^ 4 / 192 + t₀ ^ 2 / (32 * τ) := by
    rw [ht₀]; field_simp; ring
  rw [e2] at h1
  refine h1.trans ?_
  have h4 : t₀ ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ ht₀0 ht 4
  have h2 : t₀ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ht₀0 ht 2
  have := div_le_div_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 32 * τ)
  have := mul_le_mul_of_nonneg_left h4 hℓ'.le
  linarith

end Tent

end MinorFreeSeparators
