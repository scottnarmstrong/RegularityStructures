/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CanonicalBridgeTrees
public import Phi43.Structure.CanonicalModel

/-!
# Bridge theorems: `hairerCanonicalData` realises the pathwise tree fields

Main results (for `D = hairerCanonicalData N noise`, `noise.zeta = ξ ω ∘ proj`, `ξ ω` smooth on
`ℝ × T³`, constants `C = (C₁ C, C₂ C)` arbitrary):

* `hairerCanonicalData_renormalisedPi_basis_<tree>_eq_treeField` for the seven trees
  `Ξ, Ψ, Ψ², Ψ³, I(Ψ³)Ψ, I(Ψ²)Ψ², I(Ψ³)Ψ²` of `F₋` other than `Ψ²Xᵢ`;
* `hairerCanonicalData_renormalisedPi_basis_eq_treeField`, the combined statement for `τ ∈ fMinus`,
  `τ ≠ Ψ²Xᵢ`;
* the specialisations to the Hairer constants, equal to the named fields.

The tree `Ψ²Xᵢ` is handled separately: its realisation uses `ℝ³`-coordinates `yᵢ - zᵢ` and is not a
function of `proj y` and `proj z` alone.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

local notation "E" => ParabolicSpace

namespace CanonicalData

variable {κ : Kappa} {Ω : Type*} {N : ℕ} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
  {noise : CanonicalNoise}

private theorem bridge_cube_hom : 0 < homogeneity κ .iPsiCube ∧ ¬ 1 < homogeneity κ .iPsiCube := by
  have h1 := κ.2.1
  have h2 := κ.2.2
  constructor
  · simp only [homogeneity]; linarith
  · simp only [homogeneity]; linarith

private theorem bridge_sq_hom : 0 < homogeneity κ .iPsiSq ∧ ¬ 1 < homogeneity κ .iPsiSq := by
  have h1 := κ.2.1
  have h2 := κ.2.2
  constructor
  · simp only [homogeneity]; linarith
  · simp only [homogeneity]; linarith

private theorem bridge_continuous_psi (hξ : IsSmoothOnSpaceTime (ξ ω)) :
    Continuous (hairerPsiField N ξ ω) :=
  continuous_hairerKernelTorus_convolution N (IsSmoothOnSpaceTime.continuous hξ)

/-- Core of the two cubic trees: the combination of the two integrated pieces is the convolution of
the Wick cube with the kernel increment. -/
private theorem bridge_core_cube (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z))
    (hξ : IsSmoothOnSpaceTime (ξ ω)) (C : RenormalisationConstants) (x y : E) :
    (hairerCanonicalData (κ := κ) N noise).integrate (homogeneity κ .iPsiCube)
        (hairerCanonicalData (κ := κ) N noise).localPsiCube x y -
      3 * C₁ C * (hairerCanonicalData (κ := κ) N noise).integrate (homogeneity κ .iPsiCube)
        (hairerCanonicalData (κ := κ) N noise).localPsi x y =
    ∫ w, hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y) w *
      hairerTreePsiCube N ξ (C₁ C) ω w := by
  obtain ⟨h0, h1⟩ := bridge_cube_hom (κ := κ)
  have hΨ := bridge_continuous_psi (N := N) hξ
  have hg3 : Continuous (fun u => hairerPsiField N ξ ω u * hairerPsiField N ξ ω u *
      hairerPsiField N ξ ω u) := by fun_prop
  rw [hairerCanonicalData_integrate_eq h0 h1, hairerCanonicalData_integrate_eq h0 h1]
  have hcube : (hairerCanonicalData (κ := κ) N noise).localPsiCube =
      fun w => (fun u => hairerPsiField N ξ ω u * hairerPsiField N ξ ω u *
        hairerPsiField N ξ ω u) (spaceTimeProj w) := by
    funext w
    simp only [localPsiCube, localPsiSq, hairerCanonicalData_localPsi_eq κ N ξ ω hn hξ]
  rw [hcube, hairerCanonicalData_localPsi_eq κ N ξ ω hn hξ,
    hairerConvolution_comp_proj_eq N hg3, hairerConvolution_comp_proj_eq N hg3,
    hairerConvolution_comp_proj_eq N hΨ, hairerConvolution_comp_proj_eq N hΨ]
  have hfun : (fun w => hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y) w *
      hairerTreePsiCube N ξ (C₁ C) ω w) = fun w =>
      hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y) w *
        ((hairerPsiField N ξ ω w * hairerPsiField N ξ ω w * hairerPsiField N ξ ω w) -
          (3 * C₁ C) * hairerPsiField N ξ ω w) := by
    funext w
    unfold hairerTreePsiCube
    ring
  rw [hfun, integral_hairerI2Psi2Kernel_mul_sub_const_mul N _ _ hg3 hΨ]

/-- Core of `I(Ψ²)Ψ²`: the recentred convolution of `Ψ²` is the convolution of `Ψ² - C₁` with the
kernel increment, because the increment has integral zero. -/
private theorem bridge_core_sq (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z))
    (hξ : IsSmoothOnSpaceTime (ξ ω)) (C : RenormalisationConstants) (x y : E) :
    (hairerCanonicalData (κ := κ) N noise).integrate (homogeneity κ .iPsiSq)
        (hairerCanonicalData (κ := κ) N noise).localPsiSq x y =
    ∫ w, hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y) w *
      hairerTreePsiSq N ξ (C₁ C) ω w := by
  obtain ⟨h0, h1⟩ := bridge_sq_hom (κ := κ)
  have hΨ := bridge_continuous_psi (N := N) hξ
  have hg2 : Continuous (fun u => hairerPsiField N ξ ω u * hairerPsiField N ξ ω u) := by
    fun_prop
  rw [hairerCanonicalData_integrate_eq h0 h1]
  have hsq : (hairerCanonicalData (κ := κ) N noise).localPsiSq =
      fun w => (fun u => hairerPsiField N ξ ω u * hairerPsiField N ξ ω u) (spaceTimeProj w) := by
    funext w
    simp only [localPsiSq, hairerCanonicalData_localPsi_eq κ N ξ ω hn hξ]
  rw [hsq, hairerConvolution_comp_proj_eq N hg2, hairerConvolution_comp_proj_eq N hg2]
  have hfun : (fun w => hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y) w *
      hairerTreePsiSq N ξ (C₁ C) ω w) = fun w =>
      hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y) w *
        ((hairerPsiField N ξ ω w * hairerPsiField N ξ ω w) - C₁ C * (fun _ => (1 : ℝ)) w) := by
    funext w
    unfold hairerTreePsiSq
    ring
  rw [hfun, integral_hairerI2Psi2Kernel_mul_sub_const_mul N _ _ hg2
    (continuous_const (y := (1 : ℝ))), integral_hairerKernelTorus_sub_mul_one_sub]
  ring

variable (C : RenormalisationConstants) (x : E)

/-- `Ξ`: the realisation of the noise symbol is the lifted noise. -/
theorem hairerCanonicalData_renormalisedPi_basis_noise_eq_treeField
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis .noise) =
      fun y => ξ ω (spaceTimeProj y) := by
  rw [renormalisedPi_basis_noise_eq]
  exact funext hn

/-- `Ψ`: the realisation is `K ∗ ζ = Ψ ∘ proj`. -/
theorem hairerCanonicalData_renormalisedPi_basis_psi_eq_treeField
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis .psi) =
      fun y => hairerPsiField N ξ ω (spaceTimeProj y) := by
  rw [renormalisedPi_basis_psi_eq, hairerCanonicalData_localPsi_eq κ N ξ ω hn hξ]

/-- `Ψ²`: the realisation is `Ψ² - C₁` at `proj y`. -/
theorem hairerCanonicalData_renormalisedPi_basis_psiSq_eq_treeField
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis .psiSq) =
      fun y => hairerTreePsiSq N ξ (C₁ C) ω (spaceTimeProj y) := by
  rw [renormalisedPi_basis_psiSq_eq, hairerCanonicalData_localPsi_eq κ N ξ ω hn hξ]
  funext y
  simp only [hairerTreePsiSq]
  ring

/-- `Ψ³`: the realisation is `Ψ³ - 3 C₁ Ψ` at `proj y`. -/
theorem hairerCanonicalData_renormalisedPi_basis_psiCube_eq_treeField
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis .psiCube) =
      fun y => hairerTreePsiCube N ξ (C₁ C) ω (spaceTimeProj y) := by
  rw [renormalisedPi_basis_psiCube_eq, hairerCanonicalData_localPsi_eq κ N ξ ω hn hξ]
  funext y
  simp only [hairerTreePsiCube]
  ring

/-- `I(Ψ³)Ψ`. -/
theorem hairerCanonicalData_renormalisedPi_basis_iPsiCubePsi_eq_treeField
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis .iPsiCubePsi) =
      fun y => hairerTreeI3Psi N ξ (C₁ C) (spaceTimeProj x) ω (spaceTimeProj y) := by
  rw [renormalisedPi_basis_iPsiCubePsi_eq]
  funext y
  rw [bridge_core_cube hn hξ C x y, hairerCanonicalData_localPsi_eq κ N ξ ω hn hξ]
  simp only [hairerTreeI3Psi]
  ring

/-- `I(Ψ²)Ψ²`. -/
theorem hairerCanonicalData_renormalisedPi_basis_iPsiSqPsiSq_eq_treeField
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis .iPsiSqPsiSq) =
      fun y => hairerTreeI2Psi2 N ξ (C₁ C) (C₂ C) (spaceTimeProj x) ω (spaceTimeProj y) := by
  rw [renormalisedPi_basis_iPsiSqPsiSq_eq]
  funext y
  rw [bridge_core_sq hn hξ C x y, hairerCanonicalData_localPsi_eq κ N ξ ω hn hξ]
  simp only [hairerTreeI2Psi2, hairerTreePsiSq]
  ring

/-- `I(Ψ³)Ψ²`. -/
theorem hairerCanonicalData_renormalisedPi_basis_iPsiCubePsiSq_eq_treeField
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis .iPsiCubePsiSq) =
      fun y => hairerTreeI3Psi2 N ξ (C₁ C) (C₂ C) (spaceTimeProj x) ω (spaceTimeProj y) := by
  rw [renormalisedPi_basis_iPsiCubePsiSq_eq]
  funext y
  rw [bridge_core_cube hn hξ C x y, hairerCanonicalData_localPsi_eq κ N ξ ω hn hξ]
  simp only [hairerTreeI3Psi2, hairerTreePsiSq]
  ring

/-- **Bridge theorem.**  For every `τ ∈ F₋` other than `Ψ²Xᵢ`, the renormalised realisation of the
concrete canonical data on `ℝ⁴` is the pathwise tree field on `ℝ × T³` evaluated at the projections
of the base point and of the evaluation point, with the constants `(C₁ C, C₂ C)`. -/
theorem hairerCanonicalData_renormalisedPi_basis_eq_treeField
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω))
    {τ : Symbol} (hτ : τ ∈ fMinus) (hX : ∀ i, τ ≠ .psiSqX i) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis τ) =
      fun y => hairerTreeField N ξ (C₁ C) (C₂ C) (spaceTimeProj x) ω τ (spaceTimeProj y) := by
  rw [mem_fMinus_iff_isFMinus] at hτ
  cases τ <;> simp only [isFMinus] at hτ
  · exact hairerCanonicalData_renormalisedPi_basis_noise_eq_treeField C x hn
  · exact hairerCanonicalData_renormalisedPi_basis_psi_eq_treeField C x hn hξ
  · exact hairerCanonicalData_renormalisedPi_basis_psiSq_eq_treeField C x hn hξ
  · exact hairerCanonicalData_renormalisedPi_basis_psiCube_eq_treeField C x hn hξ
  · exact absurd rfl (hX _)
  · exact hairerCanonicalData_renormalisedPi_basis_iPsiSqPsiSq_eq_treeField C x hn hξ
  · exact hairerCanonicalData_renormalisedPi_basis_iPsiCubePsi_eq_treeField C x hn hξ
  · exact hairerCanonicalData_renormalisedPi_basis_iPsiCubePsiSq_eq_treeField C x hn hξ

end CanonicalData

end RegularityStructures.Phi43

end
