import proof.Hitting.Poincare

/-!
# Wasserstein distance (`def:wasserstein`, `lemma:wasserstein`)

Probability distributions on a finite type are nonnegative functions with sum one.
A function `f` is `1`-Lipschitz for `d` when `f x - f y ≤ d x y` for all `x, y`.

`wasserstein d p q` is the optimal value of the transport problem (Primal) of
`def:wasserstein`; `wasserstein_eq_sSup` is strong duality with (Dual). The bound of
`lemma:wasserstein` for shortest-path metrics of expanders is `wasserstein_le`.
-/

namespace MinorFreeSeparators

open Finset

variable {X : Type*} [Fintype X]

/-- `x` is a transport plan from `p` to `q`: a feasible solution of (Primal). -/
def IsCoupling (p q : X → ℝ) (x : X → X → ℝ) : Prop :=
  (∀ u v, 0 ≤ x u v) ∧ (∀ u, ∑ v, x u v = p u) ∧ ∀ v, ∑ u, x u v = q v

/-- The Wasserstein distance `W_d(p, q)`: the least cost of a transport plan. -/
noncomputable def wasserstein (d : X → X → ℝ) (p q : X → ℝ) : ℝ :=
  sInf {c | ∃ x, IsCoupling p q x ∧ ∑ u, ∑ v, d u v * x u v = c}

/-- The marginals and cost of a plan on `X × X`. -/
noncomputable def planImage (d : X → X → ℝ) :
    (X × X → ℝ) →ₗ[ℝ] (X → ℝ) × (X → ℝ) × ℝ where
  toFun Γ := (fun x => ∑ y, Γ (x, y), fun y => ∑ x, Γ (x, y), ∑ x, ∑ y, d x y * Γ (x, y))
  map_add' Γ Γ' := by
    ext <;> simp [sum_add_distrib, mul_add]
  map_smul' c Γ := by
    ext <;> simp [mul_sum, mul_left_comm]

/-- A continuous linear functional on `(X → ℝ) × (X → ℝ) × ℝ` in coordinates. -/
lemma strongDual_apply_eq [DecidableEq X] (φ : StrongDual ℝ ((X → ℝ) × (X → ℝ) × ℝ))
    (u v : X → ℝ) (s : ℝ) :
    φ (u, v, s) = ∑ x, u x * φ (Pi.single x 1, 0, 0) + ∑ y, v y * φ (0, Pi.single y 1, 0) +
      s * φ (0, 0, 1) := by
  have hu : ((u, 0, 0) : (X → ℝ) × (X → ℝ) × ℝ) = ∑ x, u x • (Pi.single x 1, 0, 0) := by
    ext z <;> simp [Prod.fst_sum, Prod.snd_sum, sum_apply, Pi.single_apply]
  have hv : ((0, v, 0) : (X → ℝ) × (X → ℝ) × ℝ) = ∑ y, v y • (0, Pi.single y 1, 0) := by
    ext z <;> simp [Prod.fst_sum, Prod.snd_sum, sum_apply, Pi.single_apply]
  have hs : ((0, 0, s) : (X → ℝ) × (X → ℝ) × ℝ) = s • (0, 0, 1) := by ext <;> simp
  have : ((u, v, s) : (X → ℝ) × (X → ℝ) × ℝ) = (u, 0, 0) + (0, v, 0) + (0, 0, s) := by
    ext <;> simp
  rw [this, map_add, map_add, hu, hv, hs, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Strong duality, in the direction used: a bound on (Dual) gives a coupling of
at most that cost. The proof separates the target point from the compact convex set
of (marginals, cost) of plans by Hahn–Banach. -/
theorem exists_coupling_of_dual (d : X → X → ℝ) (hd0 : ∀ x, d x x = 0)
    (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (α β : X → ℝ) (hα : ∀ x, 0 ≤ α x) (hβ : ∀ x, 0 ≤ β x)
    (hα1 : ∑ x, α x = 1) (hβ1 : ∑ x, β x = 1) (t : ℝ)
    (ht : ∀ f : X → ℝ, (∀ x y, f x - f y ≤ d x y) → ∑ x, (α x - β x) * f x ≤ t) :
    ∃ Γ : X → X → ℝ, (∀ x y, 0 ≤ Γ x y) ∧ (∀ x, ∑ y, Γ x y = α x) ∧
      (∀ y, ∑ x, Γ x y = β y) ∧ ∑ x, ∑ y, d x y * Γ x y ≤ t := by
  classical
  by_contra hcon
  push Not at hcon
  set L := planImage d
  set K := L '' stdSimplex ℝ (X × X)
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ _).linear_image L
  have hKclosed : IsClosed K :=
    ((isCompact_stdSimplex ℝ (X × X)).image L.continuous_of_finiteDimensional).isClosed
  have hmem : ((α, β, t) : (X → ℝ) × (X → ℝ) × ℝ) ∉ K := by
    rintro ⟨Γ, hΓ, hΓeq⟩
    simp only [L, planImage, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq] at hΓeq
    obtain ⟨h1, h2, h3⟩ := hΓeq
    have := hcon (fun x y => Γ (x, y)) (fun x y => hΓ.1 _) (fun x => congrFun h1 x)
      (fun y => congrFun h2 y)
    linarith
  obtain ⟨φ, u, hφu, hφK⟩ := geometric_hahn_banach_point_closed hKconv hKclosed hmem
  set a : X → ℝ := fun x => φ (Pi.single x 1, 0, 0)
  set b : X → ℝ := fun y => φ (0, Pi.single y 1, 0)
  set lam : ℝ := φ (0, 0, 1)
  have hφ : ∀ v w s, φ (v, w, s) = ∑ x, v x * a x + ∑ y, w y * b y + s * lam :=
    fun v w s => strongDual_apply_eq φ v w s
  -- the product coupling
  set Γ0 : X × X → ℝ := fun p => α p.1 * β p.2
  have hΓ0 : Γ0 ∈ stdSimplex ℝ (X × X) := by
    refine ⟨fun p => mul_nonneg (hα _) (hβ _), ?_⟩
    simp [Γ0, Fintype.sum_prod_type, ← mul_sum, hα1, hβ1]
  have hLΓ0 : L Γ0 = (α, β, ∑ x, ∑ y, d x y * Γ0 (x, y)) := by
    ext <;> simp [L, planImage, Γ0, ← mul_sum, ← sum_mul, hα1, hβ1]
  have hc0 := hcon (fun x y => Γ0 (x, y)) (fun x y => mul_nonneg (hα _) (hβ _))
    (fun x => by simp [Γ0, ← mul_sum, hβ1]) (fun y => by simp [Γ0, ← sum_mul, hα1])
  have hlam : 0 < lam := by
    have h1 := hφK _ ⟨Γ0, hΓ0, rfl⟩
    rw [hLΓ0, hφ] at h1
    rw [hφ] at hφu
    by_contra hneg
    push Not at hneg
    nlinarith
  have hvert : ∀ x y, u < a x + b y + d x y * lam := by
    intro x y
    have hs : (Pi.single (x, y) 1 : X × X → ℝ) ∈ stdSimplex ℝ (X × X) := single_mem_stdSimplex _ _
    have h1 := hφK _ ⟨_, hs, rfl⟩
    have hL : L (Pi.single (x, y) 1) = (Pi.single x 1, Pi.single y 1, d x y) := by
      ext z <;> simp [L, planImage, Pi.single_apply, Prod.mk.injEq, ite_and, mul_ite]
    rw [hL, hφ] at h1
    simpa [Pi.single_apply] using h1
  rw [hφ] at hφu
  have hne : (univ : Finset X).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    simp [h] at hα1
  set f : X → ℝ := fun x => univ.inf' hne (fun y => d x y + b y / lam)
  have hflow : ∀ x, (u - a x) / lam < f x := by
    intro x
    refine (lt_inf'_iff hne).2 fun y _ => ?_
    rw [div_lt_iff₀ hlam, add_mul, div_mul_cancel₀ _ hlam.ne']
    linarith [hvert x y]
  have hfup : ∀ y, f y ≤ b y / lam := fun y =>
    (inf'_le _ (mem_univ y)).trans_eq (by simp [hd0])
  have hlip : ∀ x y, f x - f y ≤ d x y := by
    intro x y
    obtain ⟨z, -, hz⟩ := exists_mem_eq_inf' hne (fun z => d y z + b z / lam)
    have : f x ≤ d x z + b z / lam := inf'_le _ (mem_univ z)
    have hfy : f y = d y z + b z / lam := hz
    linarith [htri x y z]
  have hpos : ∃ x ∈ univ, (0 : ℝ) < α x := by
    apply exists_lt_of_sum_lt
    simp [hα1]
  have hA : ∑ x, α x * ((u - a x) / lam) < ∑ x, α x * f x := by
    refine sum_lt_sum (fun x _ => mul_le_mul_of_nonneg_left (hflow x).le (hα x)) ?_
    obtain ⟨x, hx, hx0⟩ := hpos
    exact ⟨x, hx, mul_lt_mul_of_pos_left (hflow x) hx0⟩
  have hB : ∑ y, β y * f y ≤ ∑ y, β y * (b y / lam) :=
    sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hfup y) (hβ y)
  have hA' : ∑ x, α x * ((u - a x) / lam) = (u - ∑ x, α x * a x) / lam := by
    simp_rw [mul_div_assoc', ← sum_div, mul_sub, sum_sub_distrib, ← sum_mul, hα1, one_mul]
  have hB' : ∑ y, β y * (b y / lam) = (∑ y, β y * b y) / lam := by
    simp_rw [mul_div_assoc', ← sum_div]
  have key : t < (u - ∑ x, α x * a x) / lam - (∑ y, β y * b y) / lam := by
    rw [← sub_div, lt_div_iff₀ hlam]
    linarith
  have := ht f hlip
  simp_rw [sub_mul, sum_sub_distrib] at this
  linarith

/-- A variance bound for `d`-Lipschitz functions under a positive weighting `w` bounds
transport costs: there is a coupling of cost at most `σ ‖α/w - β/w‖_{2,w}`. -/
theorem exists_coupling_le (d : X → X → ℝ) (hd0 : ∀ x, d x x = 0)
    (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (w : X → ℝ) (hw : ∀ x, 0 < w x) (σ : ℝ) (hσ : 0 ≤ σ)
    (hvar : ∀ f : X → ℝ, (∀ x y, f x - f y ≤ d x y) →
      ∑ x, w x * (f x - ∑ y, w y * f y) ^ 2 ≤ σ ^ 2)
    (α β : X → ℝ) (hα : ∀ x, 0 ≤ α x) (hβ : ∀ x, 0 ≤ β x)
    (hα1 : ∑ x, α x = 1) (hβ1 : ∑ x, β x = 1) :
    ∃ Γ : X → X → ℝ, (∀ x y, 0 ≤ Γ x y) ∧ (∀ x, ∑ y, Γ x y = α x) ∧
      (∀ y, ∑ x, Γ x y = β y) ∧
      ∑ x, ∑ y, d x y * Γ x y ≤ σ * √(∑ x, w x * (α x / w x - β x / w x) ^ 2) := by
  refine exists_coupling_of_dual d hd0 htri α β hα hβ hα1 hβ1 _ fun f hf => ?_
  set m := ∑ y, w y * f y
  set g : X → ℝ := fun x => α x / w x - β x / w x
  have hg : ∀ x, w x * g x = α x - β x := fun x => by
    simp only [g, mul_sub, mul_div_cancel₀ _ (hw x).ne']
  have h1 : ∑ x, (α x - β x) * f x = ∑ x, w x * g x * (f x - m) := by
    have : ∑ x, (α x - β x) * m = 0 := by
      rw [← sum_mul, sum_sub_distrib, hα1, hβ1]; ring
    simp_rw [hg, mul_sub, sum_sub_distrib, this, sub_zero]
  have hN : 0 ≤ ∑ x, w x * g x ^ 2 := sum_nonneg fun x _ => mul_nonneg (hw x).le (sq_nonneg _)
  have hcs : (∑ x, w x * g x * (f x - m)) ^ 2 ≤
      (∑ x, w x * g x ^ 2) * ∑ x, w x * (f x - m) ^ 2 :=
    sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun x _ => mul_nonneg (hw x).le (sq_nonneg _))
      (fun x _ => mul_nonneg (hw x).le (sq_nonneg _)) (fun x _ => le_of_eq (by ring))
  rw [h1]
  calc ∑ x, w x * g x * (f x - m) ≤ |∑ x, w x * g x * (f x - m)| := le_abs_self _
    _ ≤ √((∑ x, w x * g x ^ 2) * σ ^ 2) :=
      Real.abs_le_sqrt (hcs.trans (mul_le_mul_of_nonneg_left (hvar f hf) hN))
    _ = σ * √(∑ x, w x * g x ^ 2) := by rw [Real.sqrt_mul hN, Real.sqrt_sq hσ, mul_comm]

/-- Weak duality: the cost of a plan bounds the objective of (Dual). -/
lemma sum_mul_le_cost {d : X → X → ℝ} {p q : X → ℝ} {x : X → X → ℝ} (hx : IsCoupling p q x)
    {f : X → ℝ} (hf : ∀ u v, f u - f v ≤ d u v) :
    ∑ u, (p u - q u) * f u ≤ ∑ u, ∑ v, d u v * x u v := by
  have e1 : ∑ u, p u * f u = ∑ u, ∑ v, f u * x u v := by
    refine sum_congr rfl fun u _ => ?_
    rw [← hx.2.1 u, sum_mul]
    exact sum_congr rfl fun v _ => by ring
  have e2 : ∑ v, q v * f v = ∑ u, ∑ v, f v * x u v := by
    rw [sum_comm]
    refine sum_congr rfl fun v _ => ?_
    rw [← hx.2.2 v, sum_mul]
    exact sum_congr rfl fun u _ => by ring
  have h : ∑ u, (p u - q u) * f u = ∑ u, ∑ v, (f u - f v) * x u v := by
    simp only [sub_mul, sum_sub_distrib, e1, e2]
  rw [h]
  exact sum_le_sum fun u _ => sum_le_sum fun v _ => mul_le_mul_of_nonneg_right (hf u v) (hx.1 u v)

variable {d : X → X → ℝ} {p q : X → ℝ}

lemma exists_isCoupling (hp : ∀ u, 0 ≤ p u) (hq : ∀ u, 0 ≤ q u) (hp1 : ∑ u, p u = 1)
    (hq1 : ∑ u, q u = 1) : ∃ x, IsCoupling p q x :=
  ⟨fun u v => p u * q v, fun u v => mul_nonneg (hp u) (hq v),
    fun u => by rw [← mul_sum, hq1, mul_one], fun v => by rw [← sum_mul, hp1, one_mul]⟩

lemma wasserstein_le_cost (hd : ∀ u v, 0 ≤ d u v) {x : X → X → ℝ} (hx : IsCoupling p q x) :
    wasserstein d p q ≤ ∑ u, ∑ v, d u v * x u v :=
  csInf_le ⟨0, fun _ ⟨_, hy, hc⟩ => hc ▸ sum_nonneg fun u _ =>
    sum_nonneg fun v _ => mul_nonneg (hd u v) (hy.1 u v)⟩ ⟨x, hx, rfl⟩

/-- Strong duality for `def:wasserstein`: (Primal) equals (Dual). -/
theorem wasserstein_eq_sSup (hd : ∀ u v, 0 ≤ d u v) (hd0 : ∀ x, d x x = 0)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) (hp : ∀ u, 0 ≤ p u) (hq : ∀ u, 0 ≤ q u)
    (hp1 : ∑ u, p u = 1) (hq1 : ∑ u, q u = 1) :
    wasserstein d p q = sSup {c | ∃ f : X → ℝ, (∀ u v, f u - f v ≤ d u v) ∧
      ∑ u, (p u - q u) * f u = c} := by
  obtain ⟨x₀, hx₀⟩ := exists_isCoupling hp hq hp1 hq1
  have hne : {c | ∃ f : X → ℝ, (∀ u v, f u - f v ≤ d u v) ∧ ∑ u, (p u - q u) * f u = c}.Nonempty :=
    ⟨_, 0, (fun u v => by simpa using hd u v), rfl⟩
  have hbdd : BddAbove {c | ∃ f : X → ℝ, (∀ u v, f u - f v ≤ d u v) ∧
      ∑ u, (p u - q u) * f u = c} :=
    ⟨_, (by rintro _ ⟨f, hf, rfl⟩; exact sum_mul_le_cost hx₀ hf)⟩
  refine le_antisymm ?_ (csSup_le hne ?_)
  · obtain ⟨Γ, h0, h1, h2, hc⟩ := exists_coupling_of_dual d hd0 htri p q hp hq hp1 hq1 _
      fun f hf => le_csSup hbdd ⟨f, hf, rfl⟩
    exact (wasserstein_le_cost hd ⟨h0, h1, h2⟩).trans hc
  · rintro _ ⟨f, hf, rfl⟩
    refine le_csInf ⟨_, x₀, hx₀, rfl⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact sum_mul_le_cost hx hf

section Graph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
/-- The shortest-path metric of a connected graph satisfies the triangle inequality. -/
lemma dist_triangle_real (hG : G.Connected) (x y z : V) :
    (G.dist x z : ℝ) ≤ G.dist x y + G.dist y z := by
  exact_mod_cast hG.dist_triangle

/-- **`lemma:wasserstein`.** On a connected `ψ`-vertex expander, a coupling of `p` and `q`
for the shortest-path metric costs at most `√(n (1 + ψ)(2 + ψ)) / ψ · ‖p - q‖₂`. -/
theorem exists_coupling_dist_le (hG : G.Connected) {ψ : ℝ} (hψ : 0 < ψ)
    (hexp : IsVertexExpander G ψ) {p q : V → ℝ} (hp : ∀ u, 0 ≤ p u) (hq : ∀ u, 0 ≤ q u)
    (hp1 : ∑ u, p u = 1) (hq1 : ∑ u, q u = 1) :
    ∃ x, IsCoupling p q x ∧ ∑ u, ∑ v, (G.dist u v : ℝ) * x u v ≤
      √(Fintype.card V * ((1 + ψ) * (2 + ψ) / ψ ^ 2)) * √(∑ u, (p u - q u) ^ 2) := by
  have := hG.nonempty
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast Fintype.card_pos
  set σ := √((1 + ψ) * (2 + ψ) / ψ ^ 2)
  obtain ⟨Γ, h0, h1, h2, hc⟩ := exists_coupling_le (fun u v => (G.dist u v : ℝ))
    (fun x => by simp) (dist_triangle_real hG) (fun _ => 1 / n) (fun _ => by positivity) σ
    (Real.sqrt_nonneg _) (fun f hf => by
      rw [Real.sq_sqrt (by positivity)]
      have := poincare hG hψ hexp f hf
      have hmean : ∑ y, 1 / n * f y = (∑ u, f u) / n := by rw [← mul_sum]; ring
      rw [hmean, ← mul_sum, one_div_mul_eq_div, div_le_iff₀ hn]
      linarith)
    p q hp hq hp1 hq1
  refine ⟨Γ, ⟨h0, h1, h2⟩, hc.trans (le_of_eq ?_)⟩
  have : ∑ x, 1 / n * (p x / (1 / n) - q x / (1 / n)) ^ 2 = n * ∑ u, (p u - q u) ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun u _ => ?_
    field_simp
  rw [this, Real.sqrt_mul hn.le, Real.sqrt_mul hn.le]
  ring

/-- **`lemma:wasserstein`**, in terms of `W`. -/
theorem wasserstein_le (hG : G.Connected) {ψ : ℝ} (hψ : 0 < ψ)
    (hexp : IsVertexExpander G ψ) {p q : V → ℝ} (hp : ∀ u, 0 ≤ p u) (hq : ∀ u, 0 ≤ q u)
    (hp1 : ∑ u, p u = 1) (hq1 : ∑ u, q u = 1) :
    wasserstein (fun u v => (G.dist u v : ℝ)) p q ≤
      √(Fintype.card V * ((1 + ψ) * (2 + ψ) / ψ ^ 2)) * √(∑ u, (p u - q u) ^ 2) := by
  obtain ⟨x, hx, hc⟩ := exists_coupling_dist_le hG hψ hexp hp hq hp1 hq1
  exact (wasserstein_le_cost (fun _ _ => Nat.cast_nonneg _) hx).trans hc

end Graph

end MinorFreeSeparators
