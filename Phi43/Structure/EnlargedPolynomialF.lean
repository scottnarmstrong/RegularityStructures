/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedAbstractF

/-!
# The degree-two polynomial sector of the planted completion

Hairer [Hai14, Section 2.2, Definition 5.7]. This embedding retains every
parabolic monomial of degree at most two, including time and symmetric
spatial quadratic monomials. Its invariance follows from the old action.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The enlarged polynomial embedding is the literal old monomial embedding. -/
def phi43PolyEmbF (k : PolyIndex 3) : SymbolF := .old (phi43QuadraticPolyEmb k)

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem phi43PolyEmbF_injective : Function.Injective phi43PolyEmbF := by
  intro k l h
  exact phi43QuadraticPolyEmb_injective (SymbolF.old.inj h)

theorem phi43PolyEmbF_old_range (τ : Symbol) :
    SymbolF.old τ ∈ Set.range phi43PolyEmbF ↔ τ ∈ Set.range phi43QuadraticPolyEmb := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, SymbolF.old.inj hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

theorem phi43PolyEmbF_planted_not_mem (τ : Phi43PlantSource) :
    SymbolF.planted τ ∉ Set.range phi43PolyEmbF := by
  rintro ⟨k, hk⟩
  cases hk

theorem phi43PolynomialSubspaceF_mem (κ : Kappa) (a : SymbolF → ℝ) :
    a ∈ phi43PolynomialSubspaceF κ ↔
      ∀ τ, τ ∉ Set.range phi43PolyEmbF → a τ = 0 := by
  constructor
  · rintro ⟨v, hv, rfl⟩ τ hτ
    cases τ with
    | old τ =>
      exact hv τ (fun h => hτ ((phi43PolyEmbF_old_range τ).2 h))
    | planted τ => rfl
  · intro ha
    have hr : phi43OldRestrictF a ∈ (phi43PolynomialSectorQuadratic κ).subspace := by
      intro τ hτ
      exact ha (.old τ) (fun h => hτ ((phi43PolyEmbF_old_range τ).1 h))
    refine Submodule.mem_map.2 ⟨phi43OldRestrictF a, hr, ?_⟩
    funext τ
    cases τ with
    | old τ => rfl
    | planted τ => exact (ha _ (phi43PolyEmbF_planted_not_mem τ)).symm

end RegularityStructures.Phi43

end

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The full degree-at-most-two polynomial sector in the enlarged structure. -/
def phi43PolynomialSectorF (κ : Kappa) : PolynomialSector (phi43RegularityStructureF κ) 3 where
  emb := phi43PolyEmbF
  emb_injective := phi43PolyEmbF_injective
  deg_emb := phi43QuadraticPolyEmb_deg κ
  invariant := by
    intro g hg a ha
    obtain ⟨g₀, hg₀, h⟩ := phi43ExtensionGroupF_old_action κ g hg
    exact (phi43PolynomialSubspaceF_mem κ _).1
      (phi43OldCompatibleF_polynomial κ g g₀ hg₀ h
        ((phi43PolynomialSubspaceF_mem κ a).2 ha))

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem phi43PolynomialSectorF_subspace (κ : Kappa) :
    (phi43PolynomialSectorF κ).subspace = phi43PolynomialSubspaceF κ := by
  ext a
  exact (phi43PolynomialSubspaceF_mem κ a).symm

end RegularityStructures.Phi43

end
