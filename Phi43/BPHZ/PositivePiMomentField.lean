/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositivePiMomentExt
public import Phi43.BPHZ.RandomCanonicalModel
public import Phi43.BPHZ.RandomCanonicalContinuity
import Mathlib.Tactic

/-!
# `Q_t Π_x τ (x)` of the canonical model on the positive-degree symbols

For a smooth noise `f` with the polynomial growth of `HasPhi43NoiseGrowth`,
`(canonicalModelOfLift N κ C f).regPi x (Pi.single τ 1) t x = ∫_{ℝ⁴} Q_t(x, y) G_τ(x, y) dy`
(`regPi_canonicalModelOfLift_eq_integral`), where `G_τ` is the extension `Π` of `τ`; for the eight
positive-degree symbols `τ ∈ {I(Ψ), ΨXᵢ, I(Ψ²), I(Ψ³), I(Ψ)Ψ, I(Ψ)Ψ², I(Ψ²)Ψ, I(Ψ³)²}` the
fields `G_τ` are explicit functions of the tree fields `Ψ`, `Ψ²`, `Ψ³ - 3 C₁ Ψ`
(`extensionPi_iPsi_eq`, …, `extensionPi_iPsiCubeSq_eq`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {C : RenormalisationConstants} {f : SpaceTime → ℝ}

/-- The exponent `(deg τ + κ̄) / order` of the Kolmogorov criterion is `(homogeneity τ + κ̄) / 4`. -/
theorem posPi_exponent_eq (κ : Kappa) (σ : Symbol) (κbar : ℝ) :
    ((phi43RegularityStructure κ).deg σ + κbar) / parabolicSemigroup.order =
      (homogeneity κ σ + κbar) / 4 := rfl

/-- `Q_t Π_x τ (x)` of the canonical model is the semigroup average of the extension `Π`. -/
theorem regPi_canonicalModelOfLift_eq_integral (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) (τ : Symbol) {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    (canonicalModelOfLift N κ C f).regPi x (Pi.single τ (1 : ℝ) : Symbol → ℝ) t x =
      ∫ y, parabolicSemigroup.kernel t x y *
        (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime f hf)).renormalisedExtensionPi
          C x (basis τ) y := by
  obtain ⟨Cg, q, hg', hE⟩ := canonicalModelOfLift_eq (N := N) (κ := κ) (C := C) hf hg
  rw [hE]
  have he : phi43CoordinateEquiv.symm (Pi.single τ (1 : ℝ) : Symbol → ℝ) = basis τ := by
    apply phi43CoordinateEquiv.injective
    simp [phi43CoordinateEquiv_basis]
  change (renormalisedExtensionDistribution N (κ := κ) (canonicalNoiseOfSpaceTime f hf)
    (canonicalNoise_polyBounded_of_derivatives _ Cg q hg') C x
    (phi43CoordinateEquiv.symm (Pi.single τ (1 : ℝ) : Symbol → ℝ)) : ℝ → ParabolicSpace → ℝ) t x = _
  rw [he]
  change (if 0 < t then parabolicSemigroup.apply t _ x else 0) = _
  rw [ite_eq_left ht]
  rfl

/-- The kernel times the extension `Π` is integrable. -/
theorem integrable_kernel_mul_extensionPi (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) (τ : Symbol) {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    Integrable (fun y => parabolicSemigroup.kernel t x y *
      (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime f hf)).renormalisedExtensionPi
        C x (basis τ) y) := by
  obtain ⟨Cg, q, hg', -⟩ := canonicalModelOfLift_eq (N := N) (κ := κ) (C := C) hf hg
  exact (renormalisedExtensionPi_growth N (κ := κ) (canonicalNoiseOfSpaceTime f hf)
    (canonicalNoise_polyBounded_of_derivatives _ Cg q hg') C x (basis τ)
    ).integrable_parabolicKernel_mul ht x

/-- The difference of `Q_t Π_x τ (x)` of two canonical models is the semigroup average of the
difference of the extension `Π`. -/
theorem regPi_sub_canonicalModelOfLift_eq_integral {f' : SpaceTime → ℝ}
    {C' : RenormalisationConstants} (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    (hf' : IsSmoothOnSpaceTime f') (hg' : Statements.HasPhi43NoiseGrowth f') (τ : Symbol) {t : ℝ}
    (ht : 0 < t) (x : ParabolicSpace) :
    (canonicalModelOfLift N κ C f).regPi x (Pi.single τ (1 : ℝ) : Symbol → ℝ) t x -
      (canonicalModelOfLift N κ C' f').regPi x (Pi.single τ (1 : ℝ) : Symbol → ℝ) t x =
      ∫ y, parabolicSemigroup.kernel t x y *
        ((hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime f hf)).renormalisedExtensionPi
          C x (basis τ) y -
        (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime f' hf')).renormalisedExtensionPi
          C' x (basis τ) y) := by
  rw [regPi_canonicalModelOfLift_eq_integral hf hg τ ht x,
    regPi_canonicalModelOfLift_eq_integral hf' hg' τ ht x, ← integral_sub
      (integrable_kernel_mul_extensionPi hf hg τ ht x)
      (integrable_kernel_mul_extensionPi hf' hg' τ ht x)]
  simp only [mul_sub]

section Fields

variable {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}

private theorem posPi_psi_global (hf : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).globalPsi =
      fun y => hairerPsiField N ξ ω (spaceTimeProj y) := by
  rw [← CanonicalData.localPsi_eq_globalPsi]
  exact CanonicalData.hairerCanonicalData_localPsi_eq κ N ξ ω (fun _ => rfl) hf

/-- `Π_x I(Ψ)` of the extension. -/
theorem extensionPi_iPsi_eq (hf : IsSmoothOnSpaceTime (ξ ω)) (x : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsi) = fun y => hairerIPsiRecentred N ξ ω x y := by
  rw [renormalisedExtensionPi_tensor_iPsi,
    CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsi_eq_treeField C x
      (fun _ => rfl) hf]

/-- `Π_x ΨXᵢ` of the extension. -/
theorem extensionPi_psiX_eq (hf : IsSmoothOnSpaceTime (ξ ω)) (i : Fin 3) (x : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis (.psiX i)) =
      fun y => hairerPsiField N ξ ω (spaceTimeProj y) * (y.2 i - x.2 i) := by
  funext y
  rw [renormalisedExtensionPi_psiX, posPi_psi_global hf]
  have hc : ∀ (z : ParabolicSpace) (j : Fin 3), parabolicCoords z j.succ = z.2 j := by
    intro z j
    fin_cases j <;> rfl
  simp only [hc]

/-- `Π_x I(Ψ²)` of the extension. -/
theorem extensionPi_iPsiSq_eq (hf : IsSmoothOnSpaceTime (ξ ω)) (x : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiSq) =
      fun y => hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (fun w => hairerPsiField N ξ ω w * hairerPsiField N ξ ω w) := by
  rw [renormalisedExtensionPi_tensor_iPsiSq,
    CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsiSq_eq_treeField C x
      (fun _ => rfl) hf]

/-- `Π_x I(Ψ³)` of the extension. -/
theorem extensionPi_iPsiCube_eq (hf : IsSmoothOnSpaceTime (ξ ω)) (x : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiCube) =
      fun y => hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (hairerTreePsiCube N ξ (C₁ C) ω) := by
  rw [renormalisedExtensionPi_tensor_iPsiCube,
    CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsiCube_eq_treeField C x
      (fun _ => rfl) hf]

/-- `Π_x I(Ψ)Ψ` of the extension. -/
theorem extensionPi_iPsiPsi_eq (hf : IsSmoothOnSpaceTime (ξ ω)) (x : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiPsi) =
      fun y => hairerIPsiRecentred N ξ ω x y * hairerPsiField N ξ ω (spaceTimeProj y) := by
  funext y
  rw [renormalisedExtensionPi_iPsiPsi, renormalisedExtensionPi_tensor_iPsi,
    CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsi_eq_treeField C x
      (fun _ => rfl) hf, posPi_psi_global hf]

/-- `Π_x I(Ψ)Ψ²` of the extension. -/
theorem extensionPi_iPsiPsiSq_eq (hf : IsSmoothOnSpaceTime (ξ ω)) (x : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiPsiSq) =
      fun y => hairerIPsiRecentred N ξ ω x y * hairerTreePsiSq N ξ (C₁ C) ω (spaceTimeProj y) := by
  funext y
  rw [renormalisedExtensionPi_iPsiPsiSq, renormalisedExtensionPi_tensor_iPsi,
    CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsi_eq_treeField C x
      (fun _ => rfl) hf]
  simp only [CanonicalData.globalPsiSq, posPi_psi_global hf, hairerTreePsiSq]
  ring

/-- `Π_x I(Ψ²)Ψ` of the extension. -/
theorem extensionPi_iPsiSqPsi_eq (hf : IsSmoothOnSpaceTime (ξ ω)) (x : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiSqPsi) =
      fun y => hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (fun w => hairerPsiField N ξ ω w * hairerPsiField N ξ ω w) *
          hairerPsiField N ξ ω (spaceTimeProj y) := by
  funext y
  rw [renormalisedExtensionPi_iPsiSqPsi, renormalisedExtensionPi_tensor_iPsiSq,
    CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsiSq_eq_treeField C x
      (fun _ => rfl) hf, posPi_psi_global hf]

/-- `Π_x I(Ψ³)²` of the extension. -/
theorem extensionPi_iPsiCubeSq_eq (hf : IsSmoothOnSpaceTime (ξ ω)) (x : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiCubeSq) =
      fun y => (hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (hairerTreePsiCube N ξ (C₁ C) ω)) ^ 2 := by
  funext y
  rw [renormalisedExtensionPi_iPsiCubeSq, renormalisedExtensionPi_tensor_iPsiCube,
    CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsiCube_eq_treeField C x
      (fun _ => rfl) hf]

end Fields

end RegularityStructures.Phi43

end
