/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Basic
public import RegularityStructures.Abstract.Model

/-!
# Polynomial facts for two polynomial-compatible models

For `M₁, M₂ : Model 𝒯 parabolicSemigroup`, both polynomial-compatible with `P`:

* `Γ¹_{xy}` and `Γ²_{xy}` agree on `P.subspace` (`gammaMap_eq_of_mem_subspace`), and both
  preserve it (`gammaMap_mem_subspace`);
* `Π¹_x` and `Π²_x` agree on `P.subspace` (`pi_eq_of_mem_subspace`);
* hence `Γ¹ - Γ²` and `Π¹ - Π²` only see the non-polynomial part `E₀ Q w` of a vector `w`
  (`gammaMap_sub_extendNP_restrictNP`, `pi_sub_extendNP_restrictNP`), and
  `Q Γ¹ E₀ Q = Q Γ¹` (`restrictNP_gammaMap_extendNP_restrictNP`).
-/

public section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

/-- Every `Γ_{xy}` preserves `T̄`. -/
theorem gammaMap_mem_subspace (M : Model 𝒯 parabolicSemigroup) (x y : ParabolicSpace)
    {p : ι → ℝ} (hp : p ∈ P.subspace) : M.gammaMap x y p ∈ P.subspace :=
  fun i hi => P.invariant (M.gamma x y).1 (M.gamma x y).2 p hp i hi

/-- Polynomial-compatible models have the same `Γ` on `T̄`. -/
theorem gammaMap_eq_of_mem_subspace (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (x y : ParabolicSpace) {p : ι → ℝ} (hp : p ∈ P.subspace) :
    M₁.gammaMap x y p = M₂.gammaMap x y p := by
  rw [P.eq_polyEmbed_of_mem hp]
  simp only [PolynomialSector.polyEmbed, map_sum, map_smul, Model.gammaMap_single_emb h₁,
    Model.gammaMap_single_emb h₂]

/-- Polynomial-compatible models have the same `Π` on `T̄`. -/
theorem pi_eq_of_mem_subspace (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (x : ParabolicSpace) {p : ι → ℝ} (hp : p ∈ P.subspace) : M₁.pi x p = M₂.pi x p := by
  refine Subtype.ext (funext fun t => funext fun z => ?_)
  have := Model.regPi_polyEmbed h₁ x (fun k => p (P.emb k)) t z
  have h' := Model.regPi_polyEmbed h₂ x (fun k => p (P.emb k)) t z
  rw [← P.eq_polyEmbed_of_mem hp] at this h'
  exact this.trans h'.symm

theorem restrictNP_gammaMap_of_mem_subspace (M : Model 𝒯 parabolicSemigroup)
    (x y : ParabolicSpace) {p : ι → ℝ} (hp : p ∈ P.subspace) :
    restrictNP P (M.gammaMap x y p) = 0 :=
  restrictNP_eq_zero_of_mem_subspace P (gammaMap_mem_subspace M x y hp)

/-- `Q Γ_{xy} E₀ Q = Q Γ_{xy}`. -/
theorem restrictNP_gammaMap_extendNP_restrictNP (M : Model 𝒯 parabolicSemigroup)
    (x y : ParabolicSpace) (w : ι → ℝ) :
    restrictNP P (M.gammaMap x y (extendNP P (restrictNP P w))) =
      restrictNP P (M.gammaMap x y w) := by
  have h := restrictNP_gammaMap_of_mem_subspace M x y (sub_extendNP_restrictNP_mem P w)
  rw [map_sub, map_sub] at h
  exact (sub_eq_zero.1 h).symm

/-- `(Γ¹ - Γ²) E₀ Q = Γ¹ - Γ²`. -/
theorem gammaMap_sub_extendNP_restrictNP (h₁ : M₁.IsPolyCompatible P)
    (h₂ : M₂.IsPolyCompatible P) (x y : ParabolicSpace) (w : ι → ℝ) :
    M₁.gammaMap x y (extendNP P (restrictNP P w)) - M₂.gammaMap x y (extendNP P (restrictNP P w)) =
      M₁.gammaMap x y w - M₂.gammaMap x y w := by
  have h := gammaMap_eq_of_mem_subspace h₁ h₂ x y (sub_extendNP_restrictNP_mem P w)
  rw [map_sub, map_sub] at h
  linear_combination (norm := module) (-1 : ℝ) • h

/-- `(Π¹ - Π²) E₀ Q = Π¹ - Π²`. -/
theorem pi_sub_extendNP_restrictNP (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (x : ParabolicSpace) (w : ι → ℝ) :
    M₁.pi x (extendNP P (restrictNP P w)) - M₂.pi x (extendNP P (restrictNP P w)) =
      M₁.pi x w - M₂.pi x w := by
  have h := pi_eq_of_mem_subspace h₁ h₂ x (sub_extendNP_restrictNP_mem P w)
  rw [map_sub, map_sub] at h
  linear_combination (norm := module) (-1 : ℝ) • h

end TwoModel

end RegularityStructures

end
