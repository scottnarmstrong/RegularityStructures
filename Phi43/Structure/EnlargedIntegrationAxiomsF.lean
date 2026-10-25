/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedPolynomialF
public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlock

/-!
# Abstract integration on the whole enlarged Xi-free sector

Hairer [Hai14, Definition 5.7]. The finite planted integration raises
degree by two and annihilates all polynomials. Its commutation modulo
polynomials is valid for the extension subgroup constructed earlier.
No analytic model or model-extension existence is asserted here.
-/

public section

namespace RegularityStructures.Phi43

theorem phi43IntegrationF_homogeneous (κ : Kappa) (α : ℝ) (a : SymbolF → ℝ)
    (ha : a ∈ RegularityStructures.homogeneousSubspace (phi43DegreeF κ) α) :
    phi43IntegrationF a ∈ RegularityStructures.homogeneousSubspace (phi43DegreeF κ) (α + 2) := by
  rw [eq_sum_single a, map_sum]
  apply Submodule.sum_mem
  intro τ _
  rw [map_smul]
  by_cases hτ : phi43DegreeF κ τ = α
  · apply Submodule.smul_mem
    rw [phi43IntegrationF_single]
    cases hi : phi43IntegrationSymbolF τ with
    | none => exact Submodule.zero_mem _
    | some σ =>
      have hdeg := phi43IntegrationSymbolF_degree κ hi
      rw [hτ] at hdeg
      rw [← hdeg]
      exact single_mem_homogeneousSubspace σ 1
  · rw [ha τ hτ, zero_smul]
    exact Submodule.zero_mem _

private theorem source_not_polynomial (τ : Phi43PlantSource) :
    τ.symbol ∉ Set.range phi43QuadraticPolyEmb := by
  rw [phi43QuadraticPolyEmb_range]
  cases τ <;> simp [Phi43PlantSource.symbol]

theorem phi43IntegrationF_polynomial_zero (κ : Kappa) (a : SymbolF → ℝ)
    (ha : a ∈ (phi43PolynomialSectorF κ).subspace) : phi43IntegrationF a = 0 := by
  have hn : ∀ τ, τ ∉ Set.range phi43QuadraticPolyEmb → a (.old τ) = 0 := by
    intro τ hτ
    exact ha (.old τ) (fun h => hτ ((phi43PolyEmbF_old_range τ).1 h))
  funext σ
  cases σ with
  | old σ =>
    cases σ <;> simp only [phi43IntegrationF, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    all_goals apply hn
    all_goals rw [phi43QuadraticPolyEmb_range]
    all_goals simp
  | planted σ => exact hn σ.symbol (source_not_polynomial σ)

theorem phi43IntegrationF_isAbstractIntegration (κ : Kappa) :
    IsAbstractIntegration (phi43PolynomialSectorF κ) (blockSpan phi43XiFreeF)
      phi43IntegrationF 2 where
  pos := by norm_num
  map_homogeneous := fun α a _ ha => phi43IntegrationF_homogeneous κ α a ha
  map_poly := fun a _ ha => phi43IntegrationF_polynomial_zero κ a ha
  comm := by
    intro g hg a _
    rw [phi43PolynomialSectorF_subspace]
    exact hg.2.choose_spec.2.2.1 a

end RegularityStructures.Phi43

end
