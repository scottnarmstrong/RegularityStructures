/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.RandomCanonical
public import Phi43.BPHZ.PositiveTreeFormulasBridge
public import Phi43.BPHZ.GammaMomentGradBridgeIncrements
import Mathlib.Tactic
public import Phi43.BPHZ.GammaEntryRecentred

/-!
# The `Γ`-map of `canonicalModelOfLift` is the structure-group map of explicit parameters

`canonicalModelOfLift N κ C f = canonicalRenormalisedModel ...` (for `f` smooth with polynomial
growth) is `renormalisedSmoothExtensionModel`, whose `gamma y x` is *by definition*
`phi43StructureGroupElement (D.renormalisedExtensionGammaParameter C y x)` for
`D = hairerCanonicalData N (canonicalNoiseOfSpaceTime f _)`.  Hence
`Γ_{yx} e_i (j) = structureGroupMap g (basis i) j` with
`g = gammaFullParam N κ C f y x` (`canonicalModelOfLift_gammaMap_single_apply`), so the entries of
`Γ_{yx}` are read off from the explicit parameters, symbol by symbol.

The five parameters of `g = gammaFullParam ... f y x` (`ξ ω = f`, `x' = proj x`, `y' = proj y`):
* `g.shift i.succ = y_i - x_i` (`gammaFullParam_shift`);
* `g.cPsiGrad i = gammaGrad N ξ i x' y' ω` (`gammaFullParam_cPsiGrad`);
* `g.cPsi = - gammaPsiTaylor N ξ y' (x.1 - y.1) (x.2 - y.2) ω - ∑ᵢ g.cPsiGrad i (x - y)ᵢ`
  (`gammaFullParam_cPsi`);
* `g.cPsiSq`, `g.cPsiCube` are the `1`-entries of `I(Ψ²)`, `I(Ψ³)`, that is `v₂`, `v₃`
  (identified through the existing `gammaMap_iPsiSq_one_eq_gammaWickSq`, `gammaMap_iPsiCube_one_eq_gammaWickCube`).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

open Classical in
/-- The structure-group parameter of `Γ_{yx}` for the canonical model of the lift of `f`. -/
def gammaFullParam (N : ℕ) (κ : Kappa) (C : RenormalisationConstants) (f : SpaceTime → ℝ)
    (y x : ParabolicSpace) : G :=
  if h : IsSmoothOnSpaceTime f then
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime f h)).renormalisedExtensionGammaParameter
      C y x
  else 0

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {C : RenormalisationConstants} {f : SpaceTime → ℝ}

/-- **The `Γ`-map of `canonicalModelOfLift` is a structure-group map.** -/
theorem canonicalModelOfLift_gammaMap_single_apply (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) (y x : ParabolicSpace) (i j : Symbol) :
    (canonicalModelOfLift N κ C f).gammaMap y x (Pi.single i (1 : ℝ) : Symbol → ℝ) j =
      structureGroupMap (gammaFullParam N κ C f y x) (basis i) j := by
  unfold canonicalModelOfLift
  simp only [gammaFullParam, hf, hg, and_self, ↓reduceDIte]
  change (phi43StructureGroupElement
    ((hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime f hf)).renormalisedExtensionGammaParameter
      C y x) : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) (Pi.single i (1 : ℝ)) j = _
  rw [phi43StructureGroupElement_apply_single]
  rfl

section Parameters

variable {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}

theorem gammaFullParam_shift (hf : IsSmoothOnSpaceTime f) (y x : ParabolicSpace) (i : Fin 4) :
    (gammaFullParam N κ C f y x).shift i = parabolicCoords y i - parabolicCoords x i := by
  simp only [gammaFullParam, hf, ↓reduceDIte]
  exact CanonicalData.canonicalGammaParameter_shift
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime f hf)) y x i

theorem parabolicCoords_succ_eq (z : ParabolicSpace) (j : Fin 3) :
    parabolicCoords z j.succ = z.2 j := by
  fin_cases j <;> rfl

private theorem canon_cPsiGrad (hf : IsSmoothOnSpaceTime (ξ ω)) (y x : ParabolicSpace)
    (i : Fin 3) :
    ((hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).canonicalGammaParameter
      y x).cPsiGrad i = gammaGrad N ξ i (spaceTimeProj x) (spaceTimeProj y) ω := by
  rw [CanonicalData.canonicalGammaParameter_cPsiGrad,
    CanonicalData.hairerCanonicalData_localPsi_eq κ N ξ ω (fun _ => rfl) hf]
  exact hairerSpatialGradient_sub_eq_gammaGrad N hf i x y

theorem gammaFullParam_cPsiGrad (hf : IsSmoothOnSpaceTime (ξ ω)) (y x : ParabolicSpace)
    (i : Fin 3) :
    (gammaFullParam N κ C (ξ ω) y x).cPsiGrad i =
      gammaGrad N ξ i (spaceTimeProj x) (spaceTimeProj y) ω := by
  simp only [gammaFullParam, hf, ↓reduceDIte]
  exact canon_cPsiGrad hf y x i

theorem gammaFullParam_cPsi (hf : IsSmoothOnSpaceTime (ξ ω)) (y x : ParabolicSpace) :
    (gammaFullParam N κ C (ξ ω) y x).cPsi =
      -gammaPsiTaylor N ξ (spaceTimeProj y) (x.1 - y.1) (x.2 - y.2) ω -
        ∑ i : Fin 3, gammaGrad N ξ i (spaceTimeProj x) (spaceTimeProj y) ω *
          CanonicalData.relCoord y x i.succ := by
  simp only [gammaFullParam, hf, ↓reduceDIte]
  set D := hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf) with hD
  have h := CanonicalData.canonicalGammaParameter_cPsi_eq_neg_integrate D (fun _ _ => rfl) y x
  have hI : D.integrate (homogeneity κ .iPsi) D.localPsi y x =
      gammaPsiTaylor N ξ (spaceTimeProj y) (x.1 - y.1) (x.2 - y.2) ω := by
    have h1 := congrFun (CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsi_eq_treeField
      (κ := κ) (N := N) (ξ := ξ) (ω := ω) (noise := canonicalNoiseOfSpaceTime (ξ ω) hf)
      (C := C) (x := y) (fun _ => rfl) hf) x
    have h2 := congrFun (CanonicalData.renormalisedPi_basis_iPsi_eq D C y) x
    rw [h1] at h2
    rw [← h2]
    exact hairerIPsiRecentred_eq_gammaPsiTaylor N hf y x
  have hg : ∀ i : Fin 3, (D.canonicalGammaParameter y x).cPsiGrad i =
      gammaGrad N ξ i (spaceTimeProj x) (spaceTimeProj y) ω := fun i => canon_cPsiGrad hf y x i
  rw [hI] at h
  simp only [hg] at h
  exact h

theorem abs_relCoord_succ_le (y x : ParabolicSpace) (i : Fin 3) :
    |CanonicalData.relCoord y x i.succ| ≤ parabolicSemigroup.scaleDist y x := by
  have h1 : CanonicalData.relCoord y x i.succ = -(y - x).2 i := by
    simp only [CanonicalData.relCoord, parabolicCoords_succ_eq]
    simp
  have h2 : |(y - x).2 i| ≤ parabolicNorm (y - x) := by
    have := Finset.single_le_sum (f := fun j => |(y - x).2 j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
    have h3 := Real.sqrt_nonneg |(y - x).1|
    unfold parabolicNorm
    linarith
  rw [h1, abs_neg]
  exact h2

theorem structureGroupMap_basis_apply_one_iPsiSq (g : G) :
    structureGroupMap g (basis .iPsiSq) .one = g.cPsiSq := by
  rw [structureGroupMap_basis_iPsiSq_eq]
  simp [basis]

theorem structureGroupMap_basis_apply_one_iPsiCube (g : G) :
    structureGroupMap g (basis .iPsiCube) .one = g.cPsiCube := by
  rw [structureGroupMap_basis_iPsiCube_eq]
  simp [basis]

/-- `g.cPsiSq` is `v₂`. -/
theorem gammaFullParam_cPsiSq {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
    (hf : IsSmoothOnSpaceTime (ξ ω)) (hg : Statements.HasPhi43NoiseGrowth (ξ ω))
    (y x : ParabolicSpace) :
    (gammaFullParam N κ C (ξ ω) y x).cPsiSq =
      gammaWickSq N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω := by
  obtain ⟨Cg, q, hg'⟩ := hg
  have h1 := gammaMap_iPsiSq_one_eq_gammaWickSq (ρ := ρ) (ε := ε) (N := N) (κ := κ) (C := C)
    (ξ := ξ) (ω := ω) (noise := canonicalNoiseOfSpaceTime (ξ ω) hf)
    (Z := canonicalModelOfLift N κ C (ξ ω)) Cg q hg' (fun _ => rfl) hf
    (canonicalModelOfLift_isRenormalisedCanonicalModel hf ⟨Cg, q, hg'⟩) y x
  rw [canonicalModelOfLift_gammaMap_single_apply hf ⟨Cg, q, hg'⟩,
    structureGroupMap_basis_apply_one_iPsiSq] at h1
  exact h1

/-- `g.cPsiCube` is `v₃` (for the Wick constant). -/
theorem gammaFullParam_cPsiCube {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
    (hC : C₁ C = hairerWickConstant N ρ ε)
    (hf : IsSmoothOnSpaceTime (ξ ω)) (hg : Statements.HasPhi43NoiseGrowth (ξ ω))
    (y x : ParabolicSpace) :
    (gammaFullParam N κ C (ξ ω) y x).cPsiCube =
      gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω := by
  obtain ⟨Cg, q, hg'⟩ := hg
  have h1 := gammaMap_iPsiCube_one_eq_gammaWickCube (ρ := ρ) (ε := ε) (N := N) (κ := κ) (C := C)
    (ξ := ξ) (ω := ω) (noise := canonicalNoiseOfSpaceTime (ξ ω) hf)
    (Z := canonicalModelOfLift N κ C (ξ ω)) hC Cg q hg' (fun _ => rfl) hf
    (canonicalModelOfLift_isRenormalisedCanonicalModel hf ⟨Cg, q, hg'⟩) y x
  rw [canonicalModelOfLift_gammaMap_single_apply hf ⟨Cg, q, hg'⟩,
    structureGroupMap_basis_apply_one_iPsiCube] at h1
  exact h1

end Parameters

end RegularityStructures.Phi43

end
