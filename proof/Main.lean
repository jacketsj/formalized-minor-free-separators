import proof.Parameters.SmallH
import proof.Parameters.LargeH

/-!
# The main theorem

If `√n ≤ 3.2 h`, deleting every vertex works. Otherwise `separator_of_params` gives the
separator, with parameters from `exists_params_le_three` (`h ≤ 3`), `SmallH.exists_params`
(`4 ≤ h ≤ 40`) or `LargeH.exists_params` (`h ≥ 41`).
-/

namespace MinorFreeSeparators

open Real

/-- Every graph has a `K_0` minor. -/
lemma hasCliqueMinor_zero {V : Type*} (G : SimpleGraph V) : HasCliqueMinor G 0 :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

/-- Every nonempty graph has a `K_1` minor. -/
lemma hasCliqueMinor_one {V : Type*} (G : SimpleGraph V) (v : V) : HasCliqueMinor G 1 :=
  ⟨fun _ => {v}, fun _ => Set.singleton_nonempty v, fun _ => by simp,
    fun i j hij => absurd (Subsingleton.elim i j) hij,
    fun i j hij => absurd (Subsingleton.elim i j) hij⟩

/-- Deleting every vertex is a balanced separator. -/
lemma isBalancedSeparator_univ {V : Type*} [Fintype V] (G : SimpleGraph V) :
    IsBalancedSeparator G (Finset.univ : Finset V) := by
  intro C
  obtain ⟨v, -⟩ := C.nonempty_supp
  exact absurd v.property (by simp)

/-- The parameters for `2 ≤ h ≤ 3` and `√n > 3.2 h`. There is at most one branch set, so no
connector is needed (`ℓ = n`, `S = β = a = 1`). -/
lemma exists_params_le_three (n h : ℕ) (hh2 : 2 ≤ h) (hh3 : h ≤ 3)
    (hn : 16 / 5 * (h : ℝ) < √n) : ∃ P : SepParams n h, P.K ≤ 16 / 5 * h * √n := by
  have hh2' : (2 : ℝ) ≤ h := by exact_mod_cast hh2
  have hn40 : (40 : ℝ) ≤ n := by
    have := mul_self_le_mul_self (by norm_num) (show (32 / 5 : ℝ) ≤ √n by linarith)
    rw [mul_self_sqrt (Nat.cast_nonneg n)] at this
    linarith
  have hK : (5 / 2 : ℝ) ≤ 16 / 5 * h * √n := by nlinarith
  have e1 : max (1 : ℝ) (((1 : ℕ) : ℝ) - 1) = 1 := by norm_num
  refine ⟨{ ℓ := n, L := 0, S := 1, β := 1, a := 1, E := 1, K := 16 / 5 * h * √n
            ℓ_pos := by linarith
            L_nonneg := le_rfl
            one_le_S := le_rfl
            one_le_β := le_rfl
            one_le_a := le_rfl
            two_S_le := by
              have : 40 ≤ n := by exact_mod_cast hn40
              omega
            path := Or.inl (by norm_num)
            connector := fun h4 => absurd h4 (by omega)
            budget_expand := ?_
            budget_branch := ?_ }, le_rfl⟩
  · rw [e1]
    simp only [mul_zero, zero_add, add_zero]
    have : ((3 * (n : ℝ) + 1) * n + n + 1) / (2 * (n + 1) * (2 * n + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have : (h : ℝ) ≤ 3 := by exact_mod_cast hh3
    linarith
  · rw [e1]
    have : ((n : ℝ) + 1 + 2 * n * 1) / (2 * (n + 1)) ≤ 3 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have : (h : ℝ) ≤ 3 := by exact_mod_cast hh3
    linarith

/-- **`thm:sep-main`.** Every `K_h`-minor-free graph on `n` vertices has a balanced separator
with at most `3.2 h √n` vertices. -/
theorem balanced_separator (V : Type) [Fintype V] (G : SimpleGraph V) (h : ℕ)
    (hG : ¬HasCliqueMinor G h) :
    ∃ S : Finset V, IsBalancedSeparator G S ∧
      (S.card : ℝ) ≤ 16 / 5 * h * √(Fintype.card V) := by
  classical
  set n := Fintype.card V
  -- if `√n ≤ 3.2 h`, delete everything
  by_cases hsmall : √(n : ℝ) ≤ 16 / 5 * h
  · refine ⟨Finset.univ, isBalancedSeparator_univ G, ?_⟩
    rw [Finset.card_univ]
    calc (n : ℝ) = √n * √n := (mul_self_sqrt (Nat.cast_nonneg n)).symm
      _ ≤ 16 / 5 * h * √n := mul_le_mul_of_nonneg_right hsmall (sqrt_nonneg _)
  push Not at hsmall
  have hn0 : 0 < n := by
    by_contra h0
    rw [show n = 0 by omega, Nat.cast_zero, sqrt_zero] at hsmall
    linarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp hn0
  have hh2 : 2 ≤ h := by
    rcases h with _ | _ | h
    · exact absurd (hasCliqueMinor_zero G) hG
    · exact absurd (hasCliqueMinor_one G v) hG
    · omega
  obtain ⟨P, hP⟩ : ∃ P : SepParams n h, P.K ≤ 16 / 5 * h * √n := by
    rcases Nat.lt_or_ge h 4 with hh4 | hh4
    · exact exists_params_le_three n h hh2 (by omega) hsmall
    rcases Nat.lt_or_ge h 41 with hh41 | hh41
    · exact SmallH.exists_params n h hh4 (by omega) hsmall
    · exact LargeH.exists_params n h hh41 hsmall
  obtain ⟨S, hS, hcard⟩ := separator_of_params G hh2 hG P
  exact ⟨S, hS, hcard.trans hP⟩

end MinorFreeSeparators
