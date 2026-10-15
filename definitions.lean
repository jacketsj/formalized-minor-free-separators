import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

/-!
The two graph predicates needed to read `statement.lean`.
All graphs are finite, simple and unweighted.
-/

namespace MinorFreeSeparators

variable {V : Type*}

/-- `G` has a `K_h` minor: there are `h` nonempty, connected, pairwise disjoint
branch sets, any two of which are joined by an edge. -/
def HasCliqueMinor (G : SimpleGraph V) (h : ℕ) : Prop :=
  ∃ bags : Fin h → Set V,
    (∀ i, (bags i).Nonempty) ∧
    (∀ i, (G.induce (bags i)).Connected) ∧
    (∀ i j, i ≠ j → Disjoint (bags i) (bags j)) ∧
    (∀ i j, i ≠ j → ∃ u ∈ bags i, ∃ v ∈ bags j, G.Adj u v)

/-- Deleting `S` leaves every connected component with at most half of the
vertices of `G`. -/
def IsBalancedSeparator [Fintype V] (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ C : (G.induce ((S : Set V)ᶜ)).ConnectedComponent,
    2 * C.supp.ncard ≤ Fintype.card V

end MinorFreeSeparators
