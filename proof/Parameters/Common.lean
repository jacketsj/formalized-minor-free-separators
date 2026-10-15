import proof.Separator.Minimal
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Tools for the choice of parameters

Two tactics for polynomial inequalities, and small estimates used for both ranges of `h`
(`SmallH.lean` for `4 ≤ h ≤ 40`, `LargeH.lean` for `h ≥ 41`).
-/

namespace MinorFreeSeparators

open Lean Elab Tactic Real

/-- `monomial_linarith hz hw d` runs `linarith` with `0 ≤ z ^ a * w ^ b` for all `a + b ≤ d`,
where `hz : 0 ≤ z` and `hw : 0 ≤ w`. It proves `0 ≤ p z w` when `p` has nonnegative
coefficients. -/
elab "monomial_linarith " hz:term:max ppSpace hw:term:max ppSpace d:num : tactic => do
  let d := d.getNat
  let mut hints : Array Term := #[]
  for a in List.range (d + 1) do
    for b in List.range (d + 1 - a) do
      hints := hints.push
        (← `(mul_nonneg (pow_nonneg $hz $(quote a)) (pow_nonneg $hw $(quote b))))
  evalTactic (← `(tactic| linarith [$hints,*]))

/-- `bernstein_linarith hz hw hv dz dw` runs `linarith` with
`0 ≤ z ^ a * (w ^ j * v ^ (dw - j))` for all `a ≤ dz` and `j ≤ dw`, where `hz : 0 ≤ z`,
`hw : 0 ≤ w` and `hv : 0 ≤ v`. With `v = c - w` it proves `0 ≤ p z w` for `0 ≤ w ≤ c` when
the coefficients of `p` in the Bernstein basis of degree `dw` in `w` are nonnegative. -/
elab "bernstein_linarith " hz:term:max ppSpace hw:term:max ppSpace hv:term:max ppSpace
    dz:num ppSpace dw:num : tactic => do
  let dz := dz.getNat
  let dw := dw.getNat
  let mut hints : Array Term := #[]
  for a in List.range (dz + 1) do
    for j in List.range (dw + 1) do
      hints := hints.push (← `(mul_nonneg (pow_nonneg $hz $(quote a))
        (mul_nonneg (pow_nonneg $hw $(quote j)) (pow_nonneg $hv $(quote (dw - j))))))
  evalTactic (← `(tactic| linarith [$hints,*]))

lemma pi_le_d4 : π ≤ 3927 / 1250 := by
  have := pi_lt_d4; norm_num at this ⊢; linarith

lemma sqrt_le_of_sq_le {x c : ℝ} (hc : 0 ≤ c) (h : x ≤ c ^ 2) : √x ≤ c :=
  (sqrt_le_sqrt h).trans_eq (sqrt_sq hc)

lemma ceil_bounds {x : ℝ} (hx : 0 ≤ x) : x ≤ ⌈x⌉₊ ∧ (⌈x⌉₊ : ℝ) ≤ x + 1 :=
  ⟨Nat.le_ceil x, (Nat.ceil_lt_add_one hx).le⟩

lemma max_le_or {a b c m : ℝ} (ha : a ≤ c) (hb : b ≤ m) : max a b ≤ m ∨ max a b ≤ c := by
  rcases le_total a b with hab | hab
  · exact Or.inl (by rw [max_eq_right hab]; exact hb)
  · exact Or.inr (by rw [max_eq_left hab]; exact ha)

/-- `n κ' ≤ 4n/(3S)` for the tent measures, `κ' = 2(2S+1)/(3S(S+1))`. -/
lemma nkappa_le {n S : ℝ} (hS : 1 ≤ S) (hn : 0 ≤ n) :
    n * (2 * (2 * S + 1) / (3 * S * (S + 1))) ≤ 4 * n / (3 * S) := by
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The Case 1 budget, reduced to two polynomial inequalities. Write `ℓ = p/h` and
`L = u (ℓ + 1)`; then the Case 1 term is `h N / D` with
`N = ((2u+3) p + (2u+1) h) y² + (2u+1)(p + h)` and `D = 2 (p + h)((2u+2) p + (2u+1) h)`.
The connector bound `c` is given in the form `k c = A`. -/
lemma budget_expand_of {y h ℓ L M p u m c k A K : ℝ} (hh : 2 ≤ h) (hp : 0 < p) (hu : 0 ≤ u)
    (hℓ : ℓ * h = p) (hL : L = u * (ℓ + 1)) (hk : 0 < k) (hc : k * c = A)
    (hM : M ≤ m ∨ M ≤ c)
    (h₁ : (h - 2) * m * (2 * (p + h) * ((2 * u + 2) * p + (2 * u + 1) * h)) +
      h * (((2 * u + 3) * p + (2 * u + 1) * h) * y ^ 2 + (2 * u + 1) * (p + h)) ≤
      K * (2 * (p + h) * ((2 * u + 2) * p + (2 * u + 1) * h)))
    (h₂ : (h - 2) * A * (2 * (p + h) * ((2 * u + 2) * p + (2 * u + 1) * h)) +
      k * (h * (((2 * u + 3) * p + (2 * u + 1) * h) * y ^ 2 + (2 * u + 1) * (p + h))) ≤
      k * (K * (2 * (p + h) * ((2 * u + 2) * p + (2 * u + 1) * h)))) :
    (h - 2) * M + ((2 * L + 3 * ℓ + 1) * y ^ 2 + 2 * L + ℓ + 1) /
      (2 * (ℓ + 1) * (2 * L + 2 * ℓ + 1)) ≤ K := by
  have hh0 : 0 < h := by linarith
  set D := 2 * (p + h) * ((2 * u + 2) * p + (2 * u + 1) * h) with hD_def
  set N := ((2 * u + 3) * p + (2 * u + 1) * h) * y ^ 2 + (2 * u + 1) * (p + h)
  have hD : 0 < D := by positivity
  have hℓ' : ℓ = p / h := by rw [← hℓ]; field_simp
  have e : ((2 * L + 3 * ℓ + 1) * y ^ 2 + 2 * L + ℓ + 1) /
      (2 * (ℓ + 1) * (2 * L + 2 * ℓ + 1)) = h * N / D := by
    have e1 : 2 * (ℓ + 1) * (2 * L + 2 * ℓ + 1) = D / h ^ 2 := by
      rw [hL, hℓ', hD_def]; field_simp; ring
    rw [e1, div_div_eq_mul_div, div_eq_div_iff (by positivity) hD.ne', hL, hℓ']
    field_simp
    ring
  rw [e, ← le_sub_iff_add_le', div_le_iff₀ hD]
  have hh2 : 0 ≤ h - 2 := by linarith
  rcases hM with hM | hM
  · nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hh2) hD.le]
  · have h3 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hh2) hD.le) hk.le
    have e2 : k * ((h - 2) * c * D) = (h - 2) * A * D := by rw [← hc]; ring
    refine le_of_mul_le_mul_left ?_ hk
    nlinarith

/-- The budget of Cases 2 and 3, reduced to two polynomial inequalities. With `ℓ = p/h`, the
term is `(h (y² + 1) + 2p M)/(2(p + h))`; the connector bound `c` is given as `k c = A`. -/
lemma budget_branch_of {y h ℓ M p m c k A K : ℝ} (hh : 2 ≤ h) (hp : 0 < p) (hℓ : ℓ * h = p)
    (hk : 0 < k) (hc : k * c = A) (hM : M ≤ m ∨ M ≤ c)
    (h₁ : ((h - 2) * (2 * (p + h)) + 2 * p) * m + h * (y ^ 2 + 1) ≤ K * (2 * (p + h)))
    (h₂ : ((h - 2) * (2 * (p + h)) + 2 * p) * A + k * (h * (y ^ 2 + 1)) ≤
      k * (K * (2 * (p + h)))) :
    (h - 2) * M + (y ^ 2 + 1 + 2 * ℓ * M) / (2 * (ℓ + 1)) ≤ K := by
  have hh0 : 0 < h := by linarith
  have hℓ' : ℓ = p / h := by rw [← hℓ]; field_simp
  have e : (y ^ 2 + 1 + 2 * ℓ * M) / (2 * (ℓ + 1)) =
      (h * (y ^ 2 + 1) + 2 * p * M) / (2 * (p + h)) := by
    rw [hℓ', div_eq_div_iff (by positivity) (by positivity)]
    field_simp
  rw [e, ← le_sub_iff_add_le', div_le_iff₀ (by positivity)]
  have hq : 0 ≤ (h - 2) * (2 * (p + h)) + 2 * p := by
    have : 0 ≤ h - 2 := by linarith
    positivity
  rcases hM with hM | hM
  · nlinarith [mul_le_mul_of_nonneg_left hM hq]
  · have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM hq) hk.le
    have e2 : k * (((h - 2) * (2 * (p + h)) + 2 * p) * c) =
        ((h - 2) * (2 * (p + h)) + 2 * p) * A := by rw [← hc]; ring
    refine le_of_mul_le_mul_left ?_ hk
    nlinarith

end MinorFreeSeparators
