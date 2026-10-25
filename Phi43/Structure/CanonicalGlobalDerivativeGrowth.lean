/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalDerivativeGrowthAlgebra
public import Phi43.Structure.CanonicalGrowthPremise
public import Phi43.Structure.CanonicalSmoothBasis

/-!
# Derivative growth of all unbased retained trees

Hairer [Hai14, Proposition 8.27], under the explicit polynomial derivative
growth hypothesis of Hoshino's weighted framework [Hos25, Definition 2.1].
The derivative envelopes of the global trees are derived by their actual
product and causal-convolution construction.
-/

public noncomputable section

namespace RegularityStructures.Phi43

private def coordL (i : Fin 4) : ParabolicSpace →L[ℝ] ℝ :=
  ![ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ),
    (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)),
    (ContinuousLinearMap.proj 1).comp (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)),
    (ContinuousLinearMap.proj 2).comp (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))] i

private theorem coordL_eq (i : Fin 4) :
    (coordL i : ParabolicSpace → ℝ) = fun z => parabolicCoords z i := by
  funext z
  fin_cases i <;> rfl

private theorem coord_derivative_growth (i : Fin 4) :
    PolyBounded (fun z => ‖fderiv ℝ (fun z => parabolicCoords z i) z‖) := by
  rw [← coordL_eq i]
  simp only [ContinuousLinearMap.fderiv]
  exact ⟨measurable_const, ‖coordL i‖, 0, fun _ => by simp⟩

private theorem one_derivative_growth :
    PolyBounded (fun z : ParabolicSpace => ‖fderiv ℝ (fun _ => (1 : ℝ)) z‖) := by
  have he : (fun z : ParabolicSpace => ‖fderiv ℝ (fun _ => (1 : ℝ)) z‖) =
      fun _ => 0 := by
    funext z
    rw [(hasFDerivAt_const (1 : ℝ) z).fderiv, norm_zero]
  rw [he]
  exact ⟨measurable_const, 0, 0, fun _ => by simp⟩

/-- Every actual unbased tree has a polynomially growing first derivative,
derived from the explicit growth of finitely many derivatives of the noise. -/
theorem canonicalGlobalPiBasis_derivative_growth (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (C : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C * (1 + parabolicNorm z) ^ p)
    (τ : Symbol) :
    PolyBounded (fun z => ‖fderiv ℝ
      ((hairerCanonicalData (κ := κ) N noise).globalPiBasis τ) z‖) := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hn := canonicalNoise_polyBounded_of_derivatives noise C p hg
  have hdn : PolyBounded (fun z => ‖fderiv ℝ noise.zeta z‖) := by
    refine ⟨(noise.smooth.continuous_fderiv (by simp)).norm.measurable, C, p, fun z => ?_⟩
    simpa only [norm_iteratedFDeriv_one, abs_of_nonneg (norm_nonneg _)] using hg 1 (by omega) z
  have hsmooth := canonicalGlobalPiBasis_smooth N (κ := κ) noise
  have hgrowth := canonicalGlobalPiBasis_growth N (κ := κ) noise hn
  have hp : PolyBounded (fun z => ‖fderiv ℝ D.globalPsi z‖) :=
    canonicalPolyBounded_norm_fderiv_convolution N noise.smooth hdn
  have hs : PolyBounded (fun z => ‖fderiv ℝ D.globalPsiSq z‖) :=
    canonicalPolyBounded_norm_fderiv_mul (hsmooth .psi) (hsmooth .psi)
      (hgrowth .psi) (hgrowth .psi) hp hp
  have hc : PolyBounded (fun z => ‖fderiv ℝ D.globalPsiCube z‖) :=
    canonicalPolyBounded_norm_fderiv_mul (hsmooth .psiSq) (hsmooth .psi)
      (hgrowth .psiSq) (hgrowth .psi) hs hp
  have hi : PolyBounded (fun z => ‖fderiv ℝ D.globalIPsi z‖) :=
    canonicalPolyBounded_norm_fderiv_convolution N (hsmooth .psi) hp
  have his : PolyBounded (fun z => ‖fderiv ℝ D.globalIPsiSq z‖) :=
    canonicalPolyBounded_norm_fderiv_convolution N (hsmooth .psiSq) hs
  have hic : PolyBounded (fun z => ‖fderiv ℝ D.globalIPsiCube z‖) :=
    canonicalPolyBounded_norm_fderiv_convolution N (hsmooth .psiCube) hc
  have hcoord (i : Fin 4) :
      ContDiff ℝ (⊤ : ℕ∞) (fun z => parabolicCoords z i) := by
    rw [← coordL_eq i]
    exact (coordL i).contDiff
  have hcoordg (i : Fin 4) : PolyBounded (fun z => parabolicCoords z i) := by
    fin_cases i
    · exact hgrowth .x0
    · exact hgrowth (.x 0)
    · exact hgrowth (.x 1)
    · exact hgrowth (.x 2)
  change PolyBounded (fun z => ‖fderiv ℝ (D.globalPiBasis τ) z‖)
  cases τ with
  | one => exact one_derivative_growth
  | noise => exact hdn
  | x0 => exact coord_derivative_growth 0
  | x i => exact coord_derivative_growth i.succ
  | xMul q =>
      refine Sym2.inductionOn q ?_
      intro i j
      exact canonicalPolyBounded_norm_fderiv_mul (hcoord i.succ) (hcoord j.succ)
        (hcoordg i.succ) (hcoordg j.succ)
        (coord_derivative_growth i.succ) (coord_derivative_growth j.succ)
  | psi => exact hp
  | psiSq => exact hs
  | psiCube => exact hc
  | psiX i =>
      exact canonicalPolyBounded_norm_fderiv_mul
        (hsmooth .psi) (hcoord i.succ) (hgrowth .psi) (hcoordg i.succ)
        hp (coord_derivative_growth i.succ)
  | psiSqX i =>
      exact canonicalPolyBounded_norm_fderiv_mul
        (hsmooth .psiSq) (hcoord i.succ) (hgrowth .psiSq) (hcoordg i.succ)
        hs (coord_derivative_growth i.succ)
  | iPsi => exact hi
  | iPsiSq => exact his
  | iPsiCube => exact hic
  | iPsiPsi =>
      exact canonicalPolyBounded_norm_fderiv_mul
        (hsmooth .iPsi) (hsmooth .psi) (hgrowth .iPsi) (hgrowth .psi) hi hp
  | iPsiPsiSq =>
      exact canonicalPolyBounded_norm_fderiv_mul
        (hsmooth .iPsi) (hsmooth .psiSq) (hgrowth .iPsi) (hgrowth .psiSq) hi hs
  | iPsiSqPsi =>
      exact canonicalPolyBounded_norm_fderiv_mul
        (hsmooth .iPsiSq) (hsmooth .psi) (hgrowth .iPsiSq) (hgrowth .psi) his hp
  | iPsiSqPsiSq =>
      exact canonicalPolyBounded_norm_fderiv_mul
        (hsmooth .iPsiSq) (hsmooth .psiSq) (hgrowth .iPsiSq) (hgrowth .psiSq) his hs
  | iPsiCubePsi =>
      exact canonicalPolyBounded_norm_fderiv_mul
        (hsmooth .iPsiCube) (hsmooth .psi) (hgrowth .iPsiCube) (hgrowth .psi) hic hp
  | iPsiCubePsiSq =>
      exact canonicalPolyBounded_norm_fderiv_mul
        (hsmooth .iPsiCube) (hsmooth .psiSq) (hgrowth .iPsiCube) (hgrowth .psiSq) hic hs
  | iPsiCubeSq =>
      exact canonicalPolyBounded_norm_fderiv_mul
        (hsmooth .iPsiCube) (hsmooth .iPsiCube) (hgrowth .iPsiCube) (hgrowth .iPsiCube) hic hic

end RegularityStructures.Phi43

end
