/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.QuadraticPolynomialSector
public import Phi43.Structure.AbstractIntegration

/-!
# Abstract integration with the degree≤2 polynomial sector

The integration map and its source sector are unchanged. The larger
polynomial sector contains all the commutator remainders and is disjoint
from the four integration sources [Hai14, Definition 5.7].
-/

public noncomputable section

namespace RegularityStructures.Phi43

theorem phi43PolynomialSubspace_le_quadratic (κ : Kappa) :
    (phi43PolynomialSector κ).subspace ≤ (phi43PolynomialSectorQuadratic κ).subspace := by
  intro a ha τ hτ
  apply ha τ
  rintro ⟨k, hk⟩
  apply hτ
  change τ ∈ Set.range phi43QuadraticPolyEmb
  rw [← hk, phi43PolynomialSector_emb, phi43QuadraticPolyEmb_range]
  rcases polyIndex_two_cases k with hk | hk | hk | hk <;> simp [phi43PolyEmb, hk]

/-- Definition 5.7 for the fixed-point polynomial cutoff 3. -/
theorem phi43AbstractIntegration_isAbstractIntegration_quadratic (κ : Kappa) :
    IsAbstractIntegration (phi43PolynomialSectorQuadratic κ) phi43IntegrationSector
      phi43AbstractIntegration 2 := by
  have hI := phi43AbstractIntegration_isAbstractIntegration κ
  refine ⟨hI.pos, hI.map_homogeneous, ?_, ?_⟩
  · intro a ha haP
    have ha0 : a = 0 := by
      funext τ
      by_cases hn : τ = .noise
      · subst τ
        exact haP .noise (by
          change .noise ∉ Set.range phi43QuadraticPolyEmb
          rw [phi43QuadraticPolyEmb_range]
          simp)
      by_cases hp : τ = .psi
      · subst τ
        exact haP .psi (by
          change .psi ∉ Set.range phi43QuadraticPolyEmb
          rw [phi43QuadraticPolyEmb_range]
          simp)
      by_cases hs : τ = .psiSq
      · subst τ
        exact haP .psiSq (by
          change .psiSq ∉ Set.range phi43QuadraticPolyEmb
          rw [phi43QuadraticPolyEmb_range]
          simp)
      by_cases hc : τ = .psiCube
      · subst τ
        exact haP .psiCube (by
          change .psiCube ∉ Set.range phi43QuadraticPolyEmb
          rw [phi43QuadraticPolyEmb_range]
          simp)
      exact ha τ hn hp hs hc
    rw [ha0, map_zero]
  · intro g hg a ha
    exact phi43PolynomialSubspace_le_quadratic κ (hI.comm g hg a ha)

end RegularityStructures.Phi43

end
