/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositiveTreeFormulas
public import Phi43.BPHZ.CanonicalBridgeRealises
import Mathlib.Tactic

/-!
# Bridge for the positive-degree trees

For `D = hairerCanonicalData N noise` with `noise.zeta = ξ ω ∘ proj` and `ξ ω` smooth, the
formulas of `Phi43.BPHZ.PositiveTreeFormulas` are expressed through `SpaceTime` fields.
With `K̃ x y w = hairerI2Psi2Kernel N x y w` the kernel increment and
`⟨K̃ x y, g⟩ = ∫ K̃ x y w * g w dw` (`hairerKernelIncrementPairing`):

* `I(Ψ²) ↦ ⟨K̃, Ψ²⟩`, `I(Ψ²)Ψ ↦ ⟨K̃, Ψ²⟩ Ψ`;
* `I(Ψ³) ↦ ⟨K̃, Ψ³ - 3 C₁ Ψ⟩`, `I(Ψ³)² ↦ ⟨K̃, Ψ³⟩²`;
* `ΨXᵢ ↦ Ψ (yᵢ - xᵢ)`;
* `I(Ψ)`, `I(Ψ)Ψ`, `I(Ψ)Ψ²`: the order of `I(Ψ)` is above `1`, so the recentred convolution of
  `Ψ` contains the first-order Taylor term; it is written with the kernel convolutions of
  `Ψ` and the spatial gradient `hairerSpatialGradient` at the base point.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- Pairing of the kernel increment `K̃ x y` with a function `g` on `ℝ × T³`. -/
def hairerKernelIncrementPairing (N : ℕ) (x y : SpaceTime) (g : SpaceTime → ℝ) : ℝ :=
  ∫ w, hairerI2Psi2Kernel N x y w * g w

/-- The recentred convolution of the periodic lift of `Ψ`, `K * Ψ (y) - K * Ψ (x)` minus the
first-order spatial Taylor term at the base point `x : ℝ⁴`, in `ℝ⁴`-coordinates. -/
def hairerIPsiRecentred {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (ω : Ω)
    (x y : ParabolicSpace) : ℝ :=
  hairerConvolution N (fun w => hairerPsiField N ξ ω (spaceTimeProj w)) y -
    hairerConvolution N (fun w => hairerPsiField N ξ ω (spaceTimeProj w)) x -
    ∑ i : Fin 3, hairerSpatialGradient N (fun w => hairerPsiField N ξ ω (spaceTimeProj w)) i x *
      CanonicalData.relCoord x y i.succ

theorem hairerKernelIncrementPairing_eq (N : ℕ) (x y : SpaceTime) {g : SpaceTime → ℝ}
    (hg : Continuous g) :
    hairerKernelIncrementPairing N x y g =
      (∫ w, hairerKernelTorus N (y - w) * g w) - ∫ w, hairerKernelTorus N (x - w) * g w := by
  have hy := integrable_hairerKernelTorus_sub_mul_continuous N y hg
  have hx := integrable_hairerKernelTorus_sub_mul_continuous N x hg
  unfold hairerKernelIncrementPairing hairerI2Psi2Kernel
  simp_rw [sub_mul]
  exact integral_sub hy hx

theorem hairerKernelIncrementPairing_sub_const_mul (N : ℕ) (x y : SpaceTime)
    {f g : SpaceTime → ℝ} (hf : Continuous f) (hg : Continuous g) (c : ℝ) :
    hairerKernelIncrementPairing N x y (fun w => f w - c * g w) =
      hairerKernelIncrementPairing N x y f - c * hairerKernelIncrementPairing N x y g := by
  unfold hairerKernelIncrementPairing
  rw [integral_hairerI2Psi2Kernel_mul_sub_const_mul N x y hf hg c,
    ← hairerKernelIncrementPairing_eq N x y hf, ← hairerKernelIncrementPairing_eq N x y hg]
  rfl

namespace CanonicalData

local notation "E" => ParabolicSpace

variable {κ : Kappa} {Ω : Type*} {N : ℕ} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
  {noise : CanonicalNoise}

private theorem posBridge_psi_continuous (hξ : IsSmoothOnSpaceTime (ξ ω)) :
    Continuous (hairerPsiField N ξ ω) :=
  continuous_hairerKernelTorus_convolution N (IsSmoothOnSpaceTime.continuous hξ)

/-- Integration at a constant order of a periodic lift is the kernel-increment pairing. -/
theorem hairerCanonicalData_integrate_comp_proj_eq {r : ℝ} (h0 : 0 < r) (h1 : ¬ 1 < r)
    {g : SpaceTime → ℝ} (hg : Continuous g) (x y : E) :
    (hairerCanonicalData (κ := κ) N noise).integrate r (fun w => g (spaceTimeProj w)) x y =
      hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y) g := by
  rw [hairerCanonicalData_integrate_eq h0 h1, hairerConvolution_comp_proj_eq N hg,
    hairerConvolution_comp_proj_eq N hg, hairerKernelIncrementPairing_eq N _ _ hg]

private theorem posBridge_iPsiSq_hom : 0 < homogeneity κ .iPsiSq ∧ ¬ 1 < homogeneity κ .iPsiSq := by
  have h1 := κ.2.1
  have h2 := κ.2.2
  constructor
  · simp only [homogeneity]; linarith
  · simp only [homogeneity]; linarith

private theorem posBridge_iPsiCube_hom :
    0 < homogeneity κ .iPsiCube ∧ ¬ 1 < homogeneity κ .iPsiCube := by
  have h1 := κ.2.1
  have h2 := κ.2.2
  constructor
  · simp only [homogeneity]; linarith
  · simp only [homogeneity]; linarith

private theorem posBridge_iPsi_gt_one : 1 < homogeneity κ .iPsi := by
  have := κ.2.2
  simp only [homogeneity]; linarith

private theorem posBridge_localPsiSq (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z))
    (hξ : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N noise).localPsiSq =
      fun w => (fun u => hairerPsiField N ξ ω u * hairerPsiField N ξ ω u) (spaceTimeProj w) := by
  funext w
  simp only [localPsiSq, hairerCanonicalData_localPsi_eq κ N ξ ω hn hξ]

private theorem posBridge_localPsiCube (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z))
    (hξ : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N noise).localPsiCube =
      fun w => (fun u => hairerPsiField N ξ ω u * hairerPsiField N ξ ω u *
        hairerPsiField N ξ ω u) (spaceTimeProj w) := by
  funext w
  simp only [localPsiCube, localPsiSq, hairerCanonicalData_localPsi_eq κ N ξ ω hn hξ]

private theorem posBridge_integrate_iPsi (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z))
    (hξ : IsSmoothOnSpaceTime (ξ ω)) (x y : E) :
    (hairerCanonicalData (κ := κ) N noise).integrate (homogeneity κ .iPsi)
        (hairerCanonicalData (κ := κ) N noise).localPsi x y =
      hairerIPsiRecentred N ξ ω x y := by
  rw [integrate_eq_of_one_lt _ posBridge_iPsi_gt_one,
    hairerCanonicalData_localPsi_eq κ N ξ ω hn hξ]
  rfl

variable (C : RenormalisationConstants) (x : E)

/-- `I(Ψ)`. -/
theorem hairerCanonicalData_renormalisedPi_basis_iPsi_eq_treeField
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis .iPsi) =
      fun y => hairerIPsiRecentred N ξ ω x y := by
  rw [renormalisedPi_basis_iPsi_eq]
  funext y
  exact posBridge_integrate_iPsi hn hξ x y

/-- `I(Ψ²)`. -/
theorem hairerCanonicalData_renormalisedPi_basis_iPsiSq_eq_treeField
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis .iPsiSq) =
      fun y => hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (fun w => hairerPsiField N ξ ω w * hairerPsiField N ξ ω w) := by
  obtain ⟨h0, h1⟩ := posBridge_iPsiSq_hom (κ := κ)
  have hΨ := posBridge_psi_continuous (N := N) hξ
  have hc2 : Continuous (fun u => hairerPsiField N ξ ω u * hairerPsiField N ξ ω u) := by
    fun_prop
  rw [renormalisedPi_basis_iPsiSq_eq]
  funext y
  rw [posBridge_localPsiSq hn hξ]
  exact hairerCanonicalData_integrate_comp_proj_eq h0 h1 hc2 x y

/-- `I(Ψ³)`. -/
theorem hairerCanonicalData_renormalisedPi_basis_iPsiCube_eq_treeField
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis .iPsiCube) =
      fun y => hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (hairerTreePsiCube N ξ (C₁ C) ω) := by
  obtain ⟨h0, h1⟩ := posBridge_iPsiCube_hom (κ := κ)
  have hΨ := posBridge_psi_continuous (N := N) hξ
  have hc3 : Continuous (fun u => hairerPsiField N ξ ω u * hairerPsiField N ξ ω u *
      hairerPsiField N ξ ω u) := by fun_prop
  rw [renormalisedPi_basis_iPsiCube_eq]
  funext y
  rw [posBridge_localPsiCube hn hξ, hairerCanonicalData_localPsi_eq κ N ξ ω hn hξ,
    hairerCanonicalData_integrate_comp_proj_eq h0 h1 hc3,
    hairerCanonicalData_integrate_comp_proj_eq h0 h1 hΨ,
    ← hairerKernelIncrementPairing_sub_const_mul N _ _ hc3 hΨ]
  congr 1
  funext w
  simp only [hairerTreePsiCube]
  ring

end CanonicalData

end RegularityStructures.Phi43

end
