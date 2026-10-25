/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaFullParam
public import Phi43.BPHZ.GammaFullGrad
import Mathlib.Tactic

/-!
# Pathwise effect of a shift of the Wick constant on the `Γ`-parameter

For `C : RenormalisationConstants` and smooth noise `f`, the `Γ`-parameter
`gammaFullParam N κ C f y x` depends on `C` only through the `cPsiCube` component, which changes by
`3 (C₁ C - C₁ C') (I(Ψ)(x) - I(Ψ)(y))` (`gammaFullParam_cPsiCube_sub_of_C₁`).  In terms of the
pathwise convolution `T₀ = gammaFullConv`, the increment `T₀(x) - T₀(y)` is
`-cPsi + ∑ᵢ relCoordᵢ Tᵢ(x)` (`gammaFullConv_sub_eq`).
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}

/-- `I(Ψ)` of the canonical data of a smooth noise is the convolution `T₀`. -/
theorem globalIPsi_hairerCanonicalData_eq (hf : IsSmoothOnSpaceTime (ξ ω)) (z : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).globalIPsi z =
      gammaFullConv N ξ (spaceTimeProj z) ω := by
  have hψ := isSmoothOnSpaceTime_hairerPsiField N hf
  have hc := IsSmoothOnSpaceTime.continuous hψ
  have hP : (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).globalPsi =
      fun w => hairerPsiField N ξ ω (spaceTimeProj w) := by
    funext w
    change hairerConvolution N (fun z => ξ ω (spaceTimeProj z)) w = _
    exact hairerConvolution_xi_eq_hairerPsiField N hf w
  change hairerConvolution N (hairerCanonicalData (κ := κ) N
    (canonicalNoiseOfSpaceTime (ξ ω) hf)).globalPsi z = _
  rw [hP]
  exact hairerConvolution_comp_proj_eq N hc z

/-- The `cPsiCube` component of `Γ_{yx}` for two constants with the same smooth noise. -/
theorem gammaFullParam_cPsiCube_sub_of_C₁ {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (C C' : RenormalisationConstants) (y x : ParabolicSpace) :
    (gammaFullParam N κ C f y x).cPsiCube =
      (gammaFullParam N κ C' f y x).cPsiCube +
        3 * (C₁ C - C₁ C') * ((hairerCanonicalData (κ := κ) N
          (canonicalNoiseOfSpaceTime f hf)).globalIPsi x -
          (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime f hf)).globalIPsi y) := by
  simp only [gammaFullParam, hf, ↓reduceDIte, CanonicalData.renormalisedExtensionGammaParameter,
    CanonicalData.renormalisedExtensionCharacter, structureGroupInv, structureGroupMul_cPsiCube]
  ring

/-- **The shifted `cPsiCube` is `v₃` plus `3 s` times the increment of `T₀`.** -/
theorem gammaFullParam_cPsiCube_shift {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε s : ℝ}
    {C : RenormalisationConstants} (hC : C₁ C = hairerWickConstant N ρ ε + s)
    (hf : IsSmoothOnSpaceTime (ξ ω)) (hg : Statements.HasPhi43NoiseGrowth (ξ ω))
    (y x : ParabolicSpace) :
    (gammaFullParam N κ C (ξ ω) y x).cPsiCube =
      gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω +
        3 * s * (gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ (spaceTimeProj y) ω) := by
  have h0 : C₁ ((hairerWickConstant N ρ ε, C.2) : RenormalisationConstants) =
      hairerWickConstant N ρ ε := rfl
  rw [gammaFullParam_cPsiCube_sub_of_C₁ hf C (hairerWickConstant N ρ ε, C.2) y x,
    gammaFullParam_cPsiCube h0 hf hg y x, globalIPsi_hairerCanonicalData_eq hf,
    globalIPsi_hairerCanonicalData_eq hf, hC, h0]
  ring

theorem relCoord_succ_eq_sub (y x : ParabolicSpace) (i : Fin 3) :
    CanonicalData.relCoord y x i.succ = (x.2 - y.2) i := by
  have hc4 : ∀ (z : ParabolicSpace) (j : Fin 3), parabolicCoords z j.succ = z.2 j := by
    intro z j
    fin_cases j <;> rfl
  simp [CanonicalData.relCoord, hc4]

/-- **The increment of `T₀`** in terms of `cPsi` and the gradients `Tᵢ(x)`. -/
theorem gammaFullConv_sub_eq {C : RenormalisationConstants} (hf : IsSmoothOnSpaceTime (ξ ω))
    (y x : ParabolicSpace) :
    gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ (spaceTimeProj y) ω =
      -(gammaFullParam N κ C (ξ ω) y x).cPsi +
        ∑ i : Fin 3, CanonicalData.relCoord y x i.succ *
          gammaFullGrad N ξ i (spaceTimeProj x) ω := by
  have hy : spaceTimeProj y + (x.1 - y.1, torusProj (x.2 - y.2)) = spaceTimeProj x := by
    refine Prod.ext (by simp [spaceTimeProj]) ?_
    funext j
    simp [spaceTimeProj, torusProj]
  rw [gammaFullParam_cPsi hf, gammaPsiTaylor_eq_gammaFullConv_sub hf, hy]
  simp only [gammaGrad_eq_gammaFullGrad_sub hf, relCoord_succ_eq_sub, sub_mul,
    Finset.sum_sub_distrib, neg_sub]
  simp only [mul_comm (gammaFullGrad N ξ _ (spaceTimeProj y) ω),
    mul_comm (gammaFullGrad N ξ _ (spaceTimeProj x) ω)]
  ring

end RegularityStructures.Phi43

end
