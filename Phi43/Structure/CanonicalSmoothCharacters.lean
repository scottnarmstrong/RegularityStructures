/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothRealisation
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!+# Continuity of the actual canonical Taylor characters

The spatial Taylor coefficient is the corresponding directional derivative
of the actual kernel convolution, not an independent input
[Hai14, (5.12), (8.20)].
-/

public noncomputable section

namespace RegularityStructures.Phi43

open scoped ContDiff in
/-- The spatial-section definition is exactly the space-time directional
derivative of the convolution in a spatial direction. -/
theorem hairerSpatialGradient_eq_fderiv (N : ℕ) {f : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin 3) (z : ParabolicSpace) :
    hairerSpatialGradient N f i z =
      fderiv ℝ (hairerConvolution N f) z (0, Pi.single i 1) := by
  have hd := (contDiff_hairerConvolution N hf).differentiable (by simp)
  have hh := (hd z).hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  have he : fderiv ℝ (hairerSpatialSection N f z) z.2 =
      (fderiv ℝ (hairerConvolution N f) z).comp
        (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ)) := hh.fderiv
  rw [hairerSpatialGradient, he]
  rfl

open scoped ContDiff in
theorem continuous_hairerSpatialGradient (N : ℕ) {f : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    Continuous (hairerSpatialGradient N f i) := by
  have he : hairerSpatialGradient N f i =
      fun z => fderiv ℝ (hairerConvolution N f) z (0, Pi.single i 1) :=
    funext (hairerSpatialGradient_eq_fderiv N hf i)
  rw [he]
  exact ((contDiff_hairerConvolution N hf).continuous_fderiv (by simp)).clm_apply
    continuous_const

private theorem multiply_coord (a b : T) (σ : Symbol) :
    (a * b) σ = ∑ τ : Symbol, ∑ υ : Symbol, a τ * b υ * (basisProduct τ υ) σ := by
  change (multiply a b) σ = _
  unfold multiply basisProductLinear
  simp only [Finsupp.linearCombination_apply]
  have ha : (a.sum fun τ c => c • (b.sum fun υ d => d • basisProduct τ υ)) =
      ∑ τ : Symbol, a τ • (b.sum fun υ d => d • basisProduct τ υ) :=
    Finsupp.sum_fintype _ _ (fun _ => by simp)
  have hb (τ : Symbol) : (b.sum fun υ d => d • basisProduct τ υ) =
      ∑ υ : Symbol, b υ • basisProduct τ υ :=
    Finsupp.sum_fintype _ _ (fun _ => by simp)
  rw [ha]
  simp_rw [hb]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, mul_assoc]

private theorem continuous_multiply_coord {X : Type*} [TopologicalSpace X]
    {a b : X → T} (ha : ∀ τ, Continuous (fun x => a x τ))
    (hb : ∀ τ, Continuous (fun x => b x τ)) (σ : Symbol) :
    Continuous (fun x => (a x * b x) σ) := by
  simp_rw [multiply_coord]
  exact continuous_finsetSum _ fun τ _ => continuous_finsetSum _ fun υ _ =>
    ((ha τ).mul (hb υ)).mul continuous_const

/-- Coordinatewise continuity of the finite structure-group action follows
from continuity of its primitive Taylor characters. -/
theorem continuous_structureGroupMap_basis {X : Type*} [TopologicalSpace X]
    (g : X → G) (hx : ∀ i, Continuous (fun z => (g z).shift i))
    (hp : Continuous (fun z => (g z).cPsi))
    (hpg : ∀ i, Continuous (fun z => (g z).cPsiGrad i))
    (hs : Continuous (fun z => (g z).cPsiSq))
    (hc : Continuous (fun z => (g z).cPsiCube)) (τ σ : Symbol) :
    Continuous (fun z => structureGroupMap (g z) (basis τ) σ) := by
  have hprim (υ σ : Symbol) : Continuous (fun z => primitiveAction (g z) υ σ) := by
    cases υ <;> simp only [primitiveAction, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.finsetSum_apply, smul_eq_mul] <;> fun_prop
  simp only [structureGroupMap_basis]
  cases τ with
  | one => exact hprim .one σ
  | noise => exact hprim .noise σ
  | x0 => exact hprim .x0 σ
  | x i => exact hprim (.x i) σ
  | xMul p =>
      refine Sym2.inductionOn p ?_
      intro i j
      exact continuous_multiply_coord (hprim (.x i)) (hprim (.x j)) σ
  | psi => exact hprim .psi σ
  | iPsi => exact hprim .iPsi σ
  | psiSq => exact continuous_multiply_coord (hprim .psi) (hprim .psi) σ
  | psiCube =>
      exact continuous_multiply_coord
        (continuous_multiply_coord (hprim .psi) (hprim .psi)) (hprim .psi) σ
  | psiX i => exact continuous_multiply_coord (hprim .psi) (hprim (.x i)) σ
  | psiSqX i =>
      exact continuous_multiply_coord (hprim (.x i))
        (continuous_multiply_coord (hprim .psi) (hprim .psi)) σ
  | iPsiSq => exact hprim .iPsiSq σ
  | iPsiCube => exact hprim .iPsiCube σ
  | iPsiPsi =>
      change Continuous (fun z => (basis .iPsiPsi + (g z).cPsi • basis .psi +
        ∑ i, (g z).cPsiGrad i • basis (.psiX i)) σ)
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul]
      fun_prop
  | iPsiPsiSq =>
      change Continuous (fun z => (basis .iPsiPsiSq + (g z).cPsi • basis .psiSq +
        ∑ i, (g z).cPsiGrad i • basis (.psiSqX i)) σ)
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul]
      fun_prop
  | iPsiSqPsi => exact continuous_multiply_coord (hprim .iPsiSq) (hprim .psi) σ
  | iPsiSqPsiSq =>
      exact continuous_multiply_coord (hprim .iPsiSq)
        (continuous_multiply_coord (hprim .psi) (hprim .psi)) σ
  | iPsiCubePsi => exact continuous_multiply_coord (hprim .iPsiCube) (hprim .psi) σ
  | iPsiCubePsiSq =>
      exact continuous_multiply_coord (hprim .iPsiCube)
        (continuous_multiply_coord (hprim .psi) (hprim .psi)) σ
  | iPsiCubeSq => exact continuous_multiply_coord (hprim .iPsiCube) (hprim .iPsiCube) σ

/-- Continuity of every matrix coefficient of the actual canonical
base-point character. This supplies measurability, not analytic bounds. -/
theorem continuous_canonicalStructureGroup_coeff (N : ℕ) {κ : Kappa}
    (noise : CanonicalNoise) (τ σ : Symbol) :
    Continuous (fun z => structureGroupMap
      ((hairerCanonicalData (κ := κ) N noise).canonicalCharacter z) (basis τ) σ) := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hcoord (i : Fin 4) : Continuous (fun z : ParabolicSpace => parabolicCoords z i) := by
    fin_cases i
    · exact continuous_fst
    · change Continuous (fun z : ParabolicSpace => z.2 0)
      fun_prop
    · change Continuous (fun z : ParabolicSpace => z.2 1)
      fun_prop
    · change Continuous (fun z : ParabolicSpace => z.2 2)
      fun_prop
  have hps : ContDiff ℝ (↑(⊤ : ℕ∞)) (CanonicalData.localPsi D) := by
    rw [CanonicalData.localPsi_eq_globalPsi]
    exact canonicalGlobalPiBasis_smooth N noise .psi
  have hx (i : Fin 4) : Continuous (fun z => (D.canonicalCharacter z).shift i) :=
    (hcoord i).neg
  have hg (i : Fin 3) : Continuous (fun z => (D.canonicalCharacter z).cPsiGrad i) :=
    (continuous_hairerSpatialGradient N hps i).neg
  have hp : Continuous (fun z => (D.canonicalCharacter z).cPsi) := by
    change Continuous (fun z => -hairerConvolution N (CanonicalData.localPsi D) z +
      ∑ i, (D.canonicalCharacter z).shift i.succ * (D.canonicalCharacter z).cPsiGrad i)
    exact (contDiff_hairerConvolution N hps).continuous.neg.add
      (continuous_finsetSum _ fun i _ => (hx i.succ).mul (hg i))
  have hs : Continuous (fun z => (D.canonicalCharacter z).cPsiSq) :=
    (contDiff_hairerConvolution N (hps.mul hps)).continuous.neg
  have hc : Continuous (fun z => (D.canonicalCharacter z).cPsiCube) :=
    (contDiff_hairerConvolution N ((hps.mul hps).mul hps)).continuous.neg
  exact continuous_structureGroupMap_basis D.canonicalCharacter hx hp hg hs hc τ σ

end RegularityStructures.Phi43

end
