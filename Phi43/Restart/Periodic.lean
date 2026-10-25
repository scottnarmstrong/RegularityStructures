/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.LiftBounds.Periodic
public import Phi43.Structure.RenormalisedExtensionModel
public import Phi43.Structure.RenormalisedGammaLocal
public import Phi43.Structure.CanonicalSpatialTranslationKernel
public import Phi43.Structure.CanonicalGammaPrimitiveBounds
public import Phi43.Structure.RenormalisedExtensionBasedForm
import Mathlib.Tactic.FinCases
import Mathlib.MeasureTheory.Group.Integral
public import Phi43.Structure.CanonicalSpatialTranslationPi

/-!
# Spatial periodicity of the renormalised canonical model

For `n : Fin 3 → ℤ` and the lattice shift `(0, n)`:

* `canonicalRenormalisedModel_regPi_translate`:
  `Q_t Π_{x+(0,n)} e_τ (z + (0,n)) = Q_t Π_x e_τ (z)`;
* `canonicalRenormalisedModel_piSpatialPeriodic`: the diagonal version (`PiSpatialPeriodic`);
* `canonicalRenormalisedModel_gammaSpatialPeriodic`:
  `Γ_{x+(0,n), y+(0,n)} = Γ_{x,y}` (`GammaSpatialPeriodic`).

The proofs go through the explicit corrected lift (`renormalisedExtensionPi`): its based basis is
invariant under integer spatial shifts because the noise, the convolution and the Taylor
subtraction are.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43.Restart

open RegularityStructures.Phi43.LiftBounds

/-- The spatial translation by `(0, n)` as a function. -/
private def spatialTranslate (n : Fin 3 → ℤ) (z : ParabolicSpace) : ParabolicSpace :=
  (z.1, fun i => z.2 i + (n i : ℝ))

private theorem spatialTranslate_eq_add (n : Fin 3 → ℤ) (z : ParabolicSpace) :
    spatialTranslate n z = z + latticeShift n := by
  apply Prod.ext
  · simp [spatialTranslate, latticeShift]
  · funext i
    simp [spatialTranslate, latticeShift]

private theorem localPiBasis_spatialTranslate (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (n : Fin 3 → ℤ) (x y : ParabolicSpace) (τ : Symbol) :
    (hairerCanonicalData (κ := κ) N noise).localPiBasis
        (spatialTranslate n x) τ (spatialTranslate n y) =
      (hairerCanonicalData (κ := κ) N noise).localPiBasis x τ y := by
  simpa only [CanonicalData.canonicalPi_basis, spatialTranslate] using
    (canonicalPi_spatial_translation N κ noise n x y τ)

private theorem relCoord_spatialTranslate (n : Fin 3 → ℤ) (x y : ParabolicSpace) (i : Fin 4) :
    CanonicalData.relCoord (spatialTranslate n x) (spatialTranslate n y) i =
      CanonicalData.relCoord x y i := by
  fin_cases i <;> simp [CanonicalData.relCoord, spatialTranslate, parabolicCoords]

private theorem globalPsi_spatialTranslate (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (n : Fin 3 → ℤ) (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).globalPsi (spatialTranslate n y) =
      (hairerCanonicalData (κ := κ) N noise).globalPsi y := by
  let D := hairerCanonicalData (κ := κ) N noise
  have h := localPiBasis_spatialTranslate N κ noise n 0 y .psi
  have hlocal : D.localPsi (spatialTranslate n y) = D.localPsi y := by
    simpa only [CanonicalData.localPiBasis] using h
  simpa only [CanonicalData.localPsi_eq_globalPsi D] using hlocal

private theorem globalIPsi_spatialTranslate (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (n : Fin 3 → ℤ) (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).globalIPsi (spatialTranslate n y) =
      (hairerCanonicalData (κ := κ) N noise).globalIPsi y := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hψ : ∀ z, D.globalPsi (z + latticeShift n) = D.globalPsi z := by
    intro z
    rw [← spatialTranslate_eq_add n z]
    exact globalPsi_spatialTranslate N κ noise n z
  change hairerConvolution N D.globalPsi (spatialTranslate n y) =
    hairerConvolution N D.globalPsi y
  rw [spatialTranslate_eq_add]
  exact hairerConvolution_translate_of_periodic N D.globalPsi _ hψ y

private theorem globalPsiSq_spatialTranslate (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (n : Fin 3 → ℤ) (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).globalPsiSq (spatialTranslate n y) =
      (hairerCanonicalData (κ := κ) N noise).globalPsiSq y := by
  simp only [CanonicalData.globalPsiSq]
  rw [globalPsi_spatialTranslate N κ noise n y]

private theorem globalPsiCube_spatialTranslate (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (n : Fin 3 → ℤ) (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).globalPsiCube (spatialTranslate n y) =
      (hairerCanonicalData (κ := κ) N noise).globalPsiCube y := by
  simp only [CanonicalData.globalPsiCube]
  rw [globalPsiSq_spatialTranslate N κ noise n y, globalPsi_spatialTranslate N κ noise n y]

private theorem globalIPsiSq_spatialTranslate (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (n : Fin 3 → ℤ) (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).globalIPsiSq (spatialTranslate n y) =
      (hairerCanonicalData (κ := κ) N noise).globalIPsiSq y := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hψ : ∀ z, D.globalPsiSq (z + latticeShift n) = D.globalPsiSq z := by
    intro z
    rw [← spatialTranslate_eq_add n z]
    exact globalPsiSq_spatialTranslate N κ noise n z
  change hairerConvolution N D.globalPsiSq (spatialTranslate n y) =
    hairerConvolution N D.globalPsiSq y
  rw [spatialTranslate_eq_add]
  exact hairerConvolution_translate_of_periodic N D.globalPsiSq _ hψ y

private theorem globalIPsiCube_spatialTranslate (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (n : Fin 3 → ℤ) (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).globalIPsiCube (spatialTranslate n y) =
      (hairerCanonicalData (κ := κ) N noise).globalIPsiCube y := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hψ : ∀ z, D.globalPsiCube (z + latticeShift n) = D.globalPsiCube z := by
    intro z
    rw [← spatialTranslate_eq_add n z]
    exact globalPsiCube_spatialTranslate N κ noise n z
  change hairerConvolution N D.globalPsiCube (spatialTranslate n y) =
    hairerConvolution N D.globalPsiCube y
  rw [spatialTranslate_eq_add]
  exact hairerConvolution_translate_of_periodic N D.globalPsiCube _ hψ y

/-- The corrected lift is invariant under simultaneous integer spatial translation of base and
evaluation point. -/
private theorem renormalisedExtensionPi_spatialTranslate (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (n : Fin 3 → ℤ) (x y : ParabolicSpace) (τ : Symbol) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C
        (spatialTranslate n x) (basis τ) (spatialTranslate n y) =
      (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis τ) y := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hl (τ : Symbol) : D.localPiBasis (spatialTranslate n x) τ (spatialTranslate n y) =
      D.localPiBasis x τ y := localPiBasis_spatialTranslate N κ noise n x y τ
  have hp : D.globalPsi (spatialTranslate n y) = D.globalPsi y :=
    globalPsi_spatialTranslate N κ noise n y
  have hps : D.globalPsiSq (spatialTranslate n y) = D.globalPsiSq y :=
    globalPsiSq_spatialTranslate N κ noise n y
  have hpc : D.globalPsiCube (spatialTranslate n y) = D.globalPsiCube y :=
    globalPsiCube_spatialTranslate N κ noise n y
  have hi : D.globalIPsi (spatialTranslate n y) = D.globalIPsi y :=
    globalIPsi_spatialTranslate N κ noise n y
  have hiX : D.globalIPsi (spatialTranslate n x) = D.globalIPsi x :=
    globalIPsi_spatialTranslate N κ noise n x
  have his : D.globalIPsiSq (spatialTranslate n y) = D.globalIPsiSq y :=
    globalIPsiSq_spatialTranslate N κ noise n y
  have hic : D.globalIPsiCube (spatialTranslate n y) = D.globalIPsiCube y :=
    globalIPsiCube_spatialTranslate N κ noise n y
  have hli : D.localIPsi (spatialTranslate n x) (spatialTranslate n y) = D.localIPsi x y := by
    simpa only [CanonicalData.localPiBasis] using hl .iPsi
  have hlis : D.localIPsiSq (spatialTranslate n x) (spatialTranslate n y) =
      D.localIPsiSq x y := by
    simpa only [CanonicalData.localPiBasis] using hl .iPsiSq
  have hlic : D.localIPsiCube (spatialTranslate n x) (spatialTranslate n y) =
      D.localIPsiCube x y := by
    simpa only [CanonicalData.localPiBasis] using hl .iPsiCube
  rw [renormalisedExtensionPi_basis_form, renormalisedExtensionPi_basis_form]
  change D.renormalisedBasedBasis C (spatialTranslate n x) τ (spatialTranslate n y) =
    D.renormalisedBasedBasis C x τ y
  cases τ with
  | psiSq => simpa [CanonicalData.renormalisedBasedBasis] using hps
  | psiCube => simp [CanonicalData.renormalisedBasedBasis, hpc, hp]
  | psiSqX i =>
      simp only [CanonicalData.renormalisedBasedBasis, hps, relCoord_spatialTranslate]
  | iPsiCube =>
      simp only [CanonicalData.renormalisedBasedBasis, CanonicalData.renormalisedBasedCube,
        hlic, hi, hiX]
  | iPsiPsiSq => simp only [CanonicalData.renormalisedBasedBasis, hli, hps]
  | iPsiSqPsiSq => simp only [CanonicalData.renormalisedBasedBasis, hlis, hps]
  | iPsiCubePsi =>
      simp only [CanonicalData.renormalisedBasedBasis, CanonicalData.renormalisedBasedCube,
        hlic, hi, hiX, hp]
  | iPsiCubePsiSq =>
      simp only [CanonicalData.renormalisedBasedBasis, CanonicalData.renormalisedBasedCube,
        hlic, hi, hiX, hps, hp]
  | iPsiCubeSq =>
      simp only [CanonicalData.renormalisedBasedBasis, CanonicalData.renormalisedBasedCube,
        hlic, hi, hiX]
  | one => exact hl .one
  | noise => exact hl .noise
  | x0 => exact hl .x0
  | x i => exact hl (.x i)
  | xMul p => exact hl (.xMul p)
  | psi => exact hl .psi
  | iPsi => exact hl .iPsi
  | psiX i => exact hl (.psiX i)
  | iPsiSq => exact hl .iPsiSq
  | iPsiPsi => exact hl .iPsiPsi
  | iPsiSqPsi => exact hl .iPsiSqPsi

variable (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
  (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
  (C : RenormalisationConstants)

/-- **R1 (`Π`).** `Q_t Π_{x+(0,n)} e_τ (z + (0,n)) = Q_t Π_x e_τ (z)` for the renormalised
canonical model. -/
theorem canonicalRenormalisedModel_regPi_translate (n : Fin 3 → ℤ) (x z : ParabolicSpace)
    (τ : Symbol) {t : ℝ} (ht : 0 < t) :
    (canonicalRenormalisedModel N κ noise Cg q hg C).regPi (x + latticeShift n)
        (Pi.single τ 1) t (z + latticeShift n) =
      (canonicalRenormalisedModel N κ noise Cg q hg C).regPi x (Pi.single τ 1) t z := by
  rw [canonicalRenormalisedModel_regPi N κ noise Cg q hg C _ _ ht,
    canonicalRenormalisedModel_regPi N κ noise Cg q hg C _ _ ht]
  have he : phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
    apply phi43CoordinateEquiv.injective
    simp [phi43CoordinateEquiv_basis]
  rw [he]
  set a : ParabolicSpace := latticeShift n with ha
  have hp (y : ParabolicSpace) :
      (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C
          (x + a) (basis τ) (y + a) =
        (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis τ) y := by
    rw [← spatialTranslate_eq_add n y, ← spatialTranslate_eq_add n x]
    exact renormalisedExtensionPi_spatialTranslate N κ noise C n x y τ
  change (∫ y, parabolicKernel t (z + a - y) *
      (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C
        (x + a) (basis τ) y) = _
  rw [← integral_add_right_eq_self (fun y => parabolicKernel t (z + a - y) *
    (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C
      (x + a) (basis τ) y) a]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change parabolicKernel t (z + a - (y + a)) *
        (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C
          (x + a) (basis τ) (y + a) =
      parabolicKernel t (z - y) *
        (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis τ) y
    rw [show z + a - (y + a) = z - y by abel, hp]

/-- **R1 (`Π`, diagonal).** -/
theorem canonicalRenormalisedModel_piSpatialPeriodic :
    PiSpatialPeriodic (canonicalRenormalisedModel N κ noise Cg q hg C) := by
  intro n x i t
  by_cases ht : 0 < t
  · exact canonicalRenormalisedModel_regPi_translate N κ noise Cg q hg C n x x i ht
  · have h0 (y : ParabolicSpace) (z : ParabolicSpace) :
        (canonicalRenormalisedModel N κ noise Cg q hg C).regPi y (Pi.single i 1) t z = 0 :=
      congrFun (((canonicalRenormalisedModel N κ noise Cg q hg C).pi y (Pi.single i 1)).2.1
        (not_lt.1 ht)) z
    rw [h0, h0]

private theorem parameters_ext {g h : G} (hx : g.shift = h.shift) (hp : g.cPsi = h.cPsi)
    (hg : g.cPsiGrad = h.cPsiGrad) (hs : g.cPsiSq = h.cPsiSq) (hc : g.cPsiCube = h.cPsiCube) :
    g = h := by
  cases g
  cases h
  simp_all only

open scoped ContDiff in
/-- The corrected transition parameter is invariant under simultaneous integer spatial
translation. -/
theorem renormalisedExtensionGammaParameter_translate (n : Fin 3 → ℤ) (x y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C
        (y + latticeShift n) (x + latticeShift n) =
      (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C y x := by
  let D := hairerCanonicalData (κ := κ) N noise
  let a : ParabolicSpace := latticeShift n
  have hn (z : ParabolicSpace) : noise.zeta (z + a) = noise.zeta z := by
    rw [← spatialTranslate_eq_add n z]
    exact noise.periodic n z
  have hp (z : ParabolicSpace) : D.localPsi (z + a) = D.localPsi z := by
    rw [CanonicalData.localPsi_eq_globalPsi]
    exact hairerConvolution_translate_of_periodic N noise.zeta a hn z
  have hps : ContDiff ℝ ∞ D.localPsi := by
    rw [CanonicalData.localPsi_eq_globalPsi]
    exact canonicalGlobalPiBasis_smooth N noise .psi
  have hπ (τ : Symbol) (u v : ParabolicSpace) :
      D.canonicalPi (u + a) (basis τ) (v + a) = D.canonicalPi u (basis τ) v := by
    rw [← spatialTranslate_eq_add n u, ← spatialTranslate_eq_add n v]
    exact canonicalPi_spatial_translation N κ noise n u v τ
  apply parameters_ext
  · funext i
    have h1 := canonicalGamma_shift_eq_coords_sub N κ noise (x + a) (y + a) i
    have h2 := canonicalGamma_shift_eq_coords_sub N κ noise x y i
    change (D.canonicalGammaParameter (y + a) (x + a)).shift i =
      (D.canonicalGammaParameter y x).shift i
    rw [h1, h2]
    simp only [parabolicCoords_add, Pi.add_apply]
    ring
  · have h1 := canonicalGamma_cPsi_eq_iPsi N κ noise (x + a) (y + a)
    have h2 := canonicalGamma_cPsi_eq_iPsi N κ noise x y
    change (D.canonicalGammaParameter (y + a) (x + a)).cPsi =
      (D.canonicalGammaParameter y x).cPsi
    rw [h1, h2, hπ]
  · funext i
    have h1 := canonicalGamma_cPsiGrad_eq_gradient_sub N κ noise (x + a) (y + a) i
    have h2 := canonicalGamma_cPsiGrad_eq_gradient_sub N κ noise x y i
    change (D.canonicalGammaParameter (y + a) (x + a)).cPsiGrad i =
      (D.canonicalGammaParameter y x).cPsiGrad i
    have hg := hairerSpatialGradient_translate_of_periodic N hps a hp i
    rw [h1, h2, hg, hg]
  · have h1 := canonicalGamma_cPsiSq_eq_iPsiSq N κ noise (x + a) (y + a)
    have h2 := canonicalGamma_cPsiSq_eq_iPsiSq N κ noise x y
    change (D.canonicalGammaParameter (y + a) (x + a)).cPsiSq =
      (D.canonicalGammaParameter y x).cPsiSq
    rw [h1, h2, hπ]
  · rw [renormalisedGamma_cPsiCube_eq N κ noise C (x + a) (y + a),
      renormalisedGamma_cPsiCube_eq N κ noise C x y,
      ← spatialTranslate_eq_add n y, ← spatialTranslate_eq_add n x]
    exact renormalisedExtensionPi_spatialTranslate N κ noise C n x y .iPsiCube

/-- **R1 (`Γ`).** `Γ_{x+(0,n), y+(0,n)} = Γ_{x,y}` for the renormalised canonical model. -/
theorem canonicalRenormalisedModel_gammaSpatialPeriodic :
    GammaSpatialPeriodic (canonicalRenormalisedModel N κ noise Cg q hg C) := by
  intro n x y
  change ((phi43StructureGroupElement
      ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C
        (y + latticeShift n) (x + latticeShift n)) :
      LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ)) : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) =
    ((phi43StructureGroupElement
      ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C y x) :
      LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ)) : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
  rw [renormalisedExtensionGammaParameter_translate N κ noise C n x y]

end RegularityStructures.Phi43.Restart

end
