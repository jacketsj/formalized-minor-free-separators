import definitions
import proof.Main

/-!
The main theorem. To audit it, read this file and `definitions.lean`.
-/

namespace MinorFreeSeparators

/-- Every finite `K_h`-minor-free graph with `n` vertices has a balanced separator (every
component left after deleting it has at most `n/2` vertices) with at most `3.2 h √n`
vertices. -/
theorem balanced_separator_sqrt :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (h : ℕ), ¬HasCliqueMinor G h →
      ∃ S : Finset V, IsBalancedSeparator G S ∧
        (S.card : ℝ) ≤ 16 / 5 * h * Real.sqrt (Fintype.card V) :=
  balanced_separator

#print axioms balanced_separator_sqrt

end MinorFreeSeparators
