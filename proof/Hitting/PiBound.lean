import Mathlib

/-!
# `∑_{j=1}^{k-1} 1/√(j(k-j)) ≤ π`

This is the estimate in the proof of `thm:hitting`. The function
`F t = arccos (1 - 2t/k)` has derivative `1/√(t(k-t))` on `(0, k)`, rises from `0`
to `π`, and `1/√(t(k-t))` decreases on `(0, k/2]` and increases on `[k/2, k)`.
So each term is at most the increase of `F` over the adjacent unit interval on
the far side from the middle.
-/

namespace MinorFreeSeparators

open Finset Real

/-- The antiderivative `F t = arccos (1 - 2t/k)`. -/
noncomputable def arcF (k : ℝ) (t : ℝ) : ℝ := arccos (1 - 2 * t / k)

/-- `F' t = 1/√(t(k-t))` on `(0, k)`. -/
lemma hasDerivAt_arcF {k t : ℝ} (hk : 0 < k) (ht0 : 0 < t) (htk : t < k) :
    HasDerivAt (arcF k) (1 / √(t * (k - t))) t := by
  have hy1 : 1 - 2 * t / k ≠ 1 := by
    intro h
    have : 2 * t / k = 0 := by linarith
    rw [div_eq_zero_iff] at this
    rcases this with h | h <;> linarith
  have hy2 : 1 - 2 * t / k ≠ -1 := by
    intro h
    have : 2 * t / k = 2 := by linarith
    rw [div_eq_iff hk.ne'] at this
    linarith
  have hlin : HasDerivAt (fun t => 1 - 2 * t / k) (-(2 / k)) t := by
    have := ((hasDerivAt_id t).const_mul (2 / k)).const_sub 1
    convert this using 1
    · ext s; simp; ring
    · simp
  convert (hasDerivAt_arccos hy2 hy1).comp t hlin using 1
  have hq : 1 - (1 - 2 * t / k) ^ 2 = (2 / k) ^ 2 * (t * (k - t)) := by
    field_simp; ring
  have hpos : 0 < t * (k - t) := mul_pos ht0 (by linarith)
  have hs : √(1 - (1 - 2 * t / k) ^ 2) = 2 / k * √(t * (k - t)) := by
    rw [hq, sqrt_mul (by positivity), sqrt_sq (by positivity)]
  rw [hs]
  have : 0 < √(t * (k - t)) := sqrt_pos.mpr hpos
  field_simp

lemma arcF_zero {k : ℝ} : arcF k 0 = 0 := by simp [arcF]

lemma arcF_self {k : ℝ} (hk : 0 < k) : arcF k k = π := by
  have : 1 - 2 * k / k = -1 := by field_simp; ring
  simp [arcF, this]

lemma arcF_mono {k : ℝ} (hk : 0 < k) {s t : ℝ} (hst : s ≤ t) : arcF k s ≤ arcF k t := by
  apply arccos_le_arccos
  have : 2 * s / k ≤ 2 * t / k := div_le_div_of_nonneg_right (by linarith) hk.le
  linarith

lemma continuous_arcF (k : ℝ) : Continuous (arcF k) :=
  continuous_arccos.comp (continuous_const.sub ((continuous_const.mul continuous_id).div_const _))

/-- If `1/√(x(k-x)) ≥ c` on `(a, b) ⊆ (0, k)`, then `F` rises by at least `c (b - a)`. -/
lemma mul_sub_le_arcF_sub {k a b c : ℝ} (hk : 0 < k) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ k)
    (hc : ∀ x, a < x → x < b → c ≤ 1 / √(x * (k - x))) :
    c * (b - a) ≤ arcF k b - arcF k a := by
  have hD : Convex ℝ (Set.Icc a b) := convex_Icc a b
  refine hD.mul_sub_le_image_sub_of_le_deriv (continuous_arcF k).continuousOn ?_ ?_ a
    (Set.left_mem_Icc.mpr hab) b (Set.right_mem_Icc.mpr hab) hab
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_arcF hk (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt
      |>.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_arcF hk (by linarith [hx.1]) (by linarith [hx.2])).deriv]
    exact hc x hx.1 hx.2

/-- `1/√(t(k-t))` is largest near the ends of `(0, k)`: if `0 < x ≤ t ≤ k - x`, its value
at `t` is at most its value at `x`. -/
lemma one_div_sqrt_mul_sub_le {k x t : ℝ} (hx : 0 < x) (hxt : x ≤ t) (htk : x + t ≤ k) :
    1 / √(t * (k - t)) ≤ 1 / √(x * (k - x)) := by
  have h1 : 0 < x * (k - x) := mul_pos hx (by linarith)
  apply one_div_le_one_div_of_le (sqrt_pos.mpr h1)
  apply sqrt_le_sqrt
  nlinarith

/-- `∑_{j=1}^{k-1} 1/√(j(k-j)) ≤ π`. -/
theorem sum_inv_sqrt_le_pi (k : ℕ) :
    ∑ j ∈ Ico 1 k, 1 / √((j : ℝ) * ((k : ℝ) - j)) ≤ π := by
  rcases Nat.lt_or_ge k 1 with hk | hk
  · rw [Ico_eq_empty (by omega), sum_empty]; exact pi_pos.le
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set m := k / 2
  have hm : 2 * m ≤ k := Nat.mul_div_le k 2
  have hm' : k < 2 * (m + 1) := by omega
  set g : ℝ → ℝ := fun t => 1 / √(t * ((k : ℝ) - t))
  -- lower half: `g j ≤ F j - F (j - 1)`
  have hlow : ∑ j ∈ Ico 1 (m + 1), g j ≤ arcF k m - arcF k 0 := by
    rw [sum_Ico_eq_sum_range, show m + 1 - 1 = m by omega]
    have hrng : ∑ i ∈ range m, (arcF k ((i : ℝ) + 1) - arcF k i) = arcF k m - arcF k 0 := by
      simpa using sum_range_sub (fun i : ℕ => arcF k i) m
    rw [← hrng]
    refine sum_le_sum fun i hi => ?_
    have hi' : 2 * ((i : ℝ) + 1) ≤ k := by
      have := mem_range.mp hi
      exact_mod_cast (show 2 * (i + 1) ≤ k by omega)
    have := mul_sub_le_arcF_sub hk0 (Nat.cast_nonneg i) (by linarith) (by linarith)
      (c := g ((i : ℝ) + 1)) fun x hx1 hx2 =>
        one_div_sqrt_mul_sub_le (by linarith [Nat.cast_nonneg (α := ℝ) i]) hx2.le (by linarith)
    simp only [Nat.cast_add, Nat.cast_one, add_comm 1 (i : ℝ)] at this ⊢
    linarith
  -- upper half: `g j ≤ F (j + 1) - F j`
  have hup : ∑ j ∈ Ico (m + 1) k, g j ≤ arcF k k - arcF k ((m + 1 : ℕ) : ℝ) := by
    rw [sum_Ico_eq_sum_range]
    have hrng := sum_range_sub (fun i : ℕ => arcF k ((m + 1 + i : ℕ) : ℝ)) (k - (m + 1))
    have e1 : m + 1 + (k - (m + 1)) = k := by omega
    simp only [e1, add_zero] at hrng
    rw [← hrng]
    refine sum_le_sum fun i hi => ?_
    have hi' := mem_range.mp hi
    set a : ℝ := ((m + 1 + i : ℕ) : ℝ)
    have hb : ((m + 1 + (i + 1) : ℕ) : ℝ) = a + 1 := by simp only [a]; push_cast; ring
    have hak : a + 1 ≤ k := by
      simp only [a]; exact_mod_cast (show m + 1 + i + 1 ≤ k by omega)
    have h2 : (k : ℝ) < 2 * a := by
      simp only [a]; exact_mod_cast (show k < 2 * (m + 1 + i) by omega)
    have ha0 : 0 ≤ a := Nat.cast_nonneg _
    have := mul_sub_le_arcF_sub (a := a) (b := a + 1) (c := g a) hk0 ha0 (by linarith) hak
      fun x hx1 hx2 => by
        -- reflect `t ↦ k - t` to the decreasing branch
        have e2 : ∀ y : ℝ, y * ((k : ℝ) - y) = (k - y) * (k - (k - y)) := fun y => by ring
        simp only [g]
        rw [e2 x, e2 a]
        exact one_div_sqrt_mul_sub_le (by linarith) (by linarith) (by linarith)
    rw [hb]
    linarith
  have hsplit : ∑ j ∈ Ico 1 k, g j = ∑ j ∈ Ico 1 (m + 1), g j + ∑ j ∈ Ico (m + 1) k, g j :=
    (sum_Ico_consecutive _ (by omega) (by omega)).symm
  have hmono : arcF k m ≤ arcF k ((m : ℝ) + 1) := arcF_mono hk0 (by linarith)
  have h1 := arcF_self hk0
  have h0 : arcF k 0 = 0 := arcF_zero
  change ∑ j ∈ Ico 1 k, g j ≤ π
  rw [hsplit]
  push_cast at hup
  linarith

end MinorFreeSeparators
