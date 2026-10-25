/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiChain

/-!
# Bound for the diagrams with a `Q²`-link

The chain integrand `i3PsiChain K Q z z' u u'` for `(u, u') ∈ {(z, z'), (z', z)}` is integrable on
`SpaceTime × SpaceTime` and its iterated integral is bounded by
`C (s(z - z')^(-δ) + s(z)^(-δ) + s(z')^(-δ))`.

Source: [Hai14] = arXiv:1303.5113v4, p. 167--168.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- Case analysis for the outer leaves of the chain diagram. -/
theorem chain_outer_case {z z' u u' : SpaceTime} (y c : SpaceTime)
    (pzz : 0 < torusParabolicSize (z - z')) (pz'z : 0 < torusParabolicSize (z' - z))
    (pz0 : 0 < torusParabolicSize (z - 0)) (p0z : 0 < torusParabolicSize (0 - z))
    (pz'0 : 0 < torusParabolicSize (z' - 0)) (p0z' : 0 < torusParabolicSize (0 - z'))
    (hu : (u = z ∧ u' = z') ∨ (u = z' ∧ u' = z)) (hy : y = z ∨ y = 0)
    (hc : c = z' ∨ c = 0 ∨ c = u') :
    (0 < torusParabolicSize (y - c) ∧ 0 < torusParabolicSize (u - c)) ∨
      (y = c ∧ 0 < torusParabolicSize (y - u) ∧ 0 < torusParabolicSize (u - y)) ∨
      (u = c ∧ 0 < torusParabolicSize (y - u) ∧ 0 < torusParabolicSize (u - y)) := by
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hy with h3 | h3 <;>
    rcases hc with h4 | h4 | h4 <;> subst h1 h2 h3 h4 <;>
    first
    | exact Or.inl ⟨by assumption, by assumption⟩
    | exact Or.inr (Or.inl ⟨rfl, by assumption, by assumption⟩)
    | exact Or.inr (Or.inr ⟨rfl, by assumption, by assumption⟩)

end RegularityStructures

end
