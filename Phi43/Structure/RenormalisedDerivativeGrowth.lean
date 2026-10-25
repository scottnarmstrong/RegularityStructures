/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionFunctions
public import Phi43.Structure.CanonicalGlobalDerivativeGrowth
import Mathlib.Tactic.Ring
public import RegularityStructures.Abstract.Integration.Commute.Reg
public import RegularityStructures.Abstract.Integration.Theorem512.Helpers

/-!
# Polynomial derivative growth of corrected global trees

The renormalised global basis differs from the canonical basis by the finite
counterterm formulas of [Hai14, (9.3)].  Differentiating those formulas and
using the canonical derivative envelopes gives the polynomial derivative bound
needed for weighted positive-sector cancellation.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

private theorem polyBounded_norm_fderiv_sub_const
    {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hdf : PolyBounded (fun z => ‖fderiv ℝ f z‖)) (c : ℝ) :
    PolyBounded (fun z => ‖fderiv ℝ (fun z => f z - c) z‖) := by
  have hm : Measurable (fun z => ‖fderiv ℝ (fun z => f z - c) z‖) :=
    ((hf.sub contDiff_const).continuous_fderiv (by simp)).norm.measurable
  apply canonicalPolyBounded_of_domination hm hdf
  intro z
  rw [fderiv_sub_const]

private theorem polyBounded_norm_fderiv_sub_const_mul
    {f g : ParabolicSpace → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hdf : PolyBounded (fun z => ‖fderiv ℝ f z‖))
    (hdg : PolyBounded (fun z => ‖fderiv ℝ g z‖)) (c : ℝ) :
    PolyBounded (fun z => ‖fderiv ℝ (fun z => f z - c * g z) z‖) := by
  have hfun : ContDiff ℝ (⊤ : ℕ∞) (fun z => f z - c * g z) :=
    hf.sub (contDiff_const.mul hg)
  have hm : Measurable (fun z => ‖fderiv ℝ (fun z => f z - c * g z) z‖) :=
    (hfun.continuous_fderiv (by simp)).norm.measurable
  have hdom := hdf.add (hdg.const_mul |c|)
  apply canonicalPolyBounded_of_domination hm hdom
  intro z
  rw [abs_of_nonneg (norm_nonneg _)]
  rw [show (fun z => f z - c * g z) = f - (fun z => c * g z) by rfl,
    fderiv_sub (hf.differentiable (by simp) z)
      ((contDiff_const.mul hg).differentiable (by simp) z),
    fderiv_const_mul (hg.differentiable (by simp) z) c]
  calc
    ‖fderiv ℝ f z - c • fderiv ℝ g z‖ ≤
        ‖fderiv ℝ f z‖ + ‖c • fderiv ℝ g z‖ := norm_sub_le _ _
    _ = ‖fderiv ℝ f z‖ + |c| * ‖fderiv ℝ g z‖ := by
      rw [norm_smul]
      simp only [Real.norm_eq_abs]
    _ ≤ |‖fderiv ℝ f z‖ + |c| * ‖fderiv ℝ g z‖| := le_abs_self _

theorem renormalisedExtensionGlobalBasis_derivative_growth (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) (τ : Symbol) :
    PolyBounded (fun z => ‖fderiv ℝ
      ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGlobalBasis C τ) z‖) := by
  let D := hairerCanonicalData (κ := κ) N noise
  let hf := canonicalNoise_polyBounded_of_derivatives noise Cg q hg
  have hglob := canonicalGlobalPiBasis_growth N (κ := κ) noise hf
  have hsmooth := canonicalGlobalPiBasis_smooth N (κ := κ) noise
  have hder := canonicalGlobalPiBasis_derivative_growth N κ noise Cg q hg
  have hsq := polyBounded_norm_fderiv_sub_const (hsmooth .psiSq) (hder .psiSq) (C₁ C)
  have hcube := polyBounded_norm_fderiv_sub_const_mul
    (hsmooth .psiCube) (hsmooth .psi) (hder .psiCube) (hder .psi) (3 * C₁ C)
  have hpot := polyBounded_norm_fderiv_sub_const_mul
    (hsmooth .iPsiCube) (hsmooth .iPsi) (hder .iPsiCube) (hder .iPsi) (3 * C₁ C)
  have hsqg : PolyBounded (fun z => D.globalPsiSq z - C₁ C) :=
    (hglob .psiSq).sub (⟨measurable_const, |C₁ C|, 0, fun _ => by simp⟩)
  have hpotg : PolyBounded (fun z => D.renormalisedExtensionPotential C z) := by
    change PolyBounded (fun z => D.globalIPsiCube z - 3 * C₁ C * D.globalIPsi z)
    exact (hglob .iPsiCube).sub ((hglob .iPsi).const_mul (3 * C₁ C))
  have hsqSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z => D.globalPsiSq z - C₁ C) := by
    simpa [D, CanonicalData.globalPiBasis] using
      (hsmooth .psiSq).sub contDiff_const
  have hpotSmooth : ContDiff ℝ (⊤ : ℕ∞) (D.renormalisedExtensionPotential C) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun z => D.globalIPsiCube z - 3 * C₁ C * D.globalIPsi z)
    exact (hsmooth .iPsiCube).sub (contDiff_const.mul (hsmooth .iPsi))
  have hsqD : PolyBounded (fun z => ‖fderiv ℝ (fun z => D.globalPsiSq z - C₁ C) z‖) := by
    simpa [D, CanonicalData.globalPiBasis] using hsq
  have hpotD : PolyBounded (fun z => ‖fderiv ℝ (D.renormalisedExtensionPotential C) z‖) := by
    change PolyBounded (fun z => ‖fderiv ℝ
      (fun z => D.globalIPsiCube z - 3 * C₁ C * D.globalIPsi z) z‖)
    exact hpot
  have hsqSq := canonicalPolyBounded_norm_fderiv_mul
    (hsmooth .iPsiSq) hsqSmooth (hglob .iPsiSq) hsqg (hder .iPsiSq) hsqD
  have hsqSqSq := polyBounded_norm_fderiv_sub_const
    ((hsmooth .iPsiSq).mul hsqSmooth) hsqSq (C₂ C)
  have hpotPsi : PolyBounded (fun z => ‖fderiv ℝ
      (fun y => D.renormalisedExtensionPotential C y * D.globalPsi y) z‖) := by
    have h := canonicalPolyBounded_norm_fderiv_mul
      hpotSmooth (hsmooth .psi) hpotg (hglob .psi) hpotD (hder .psi)
    convert h using 1
    have he : (fun y => D.renormalisedExtensionPotential C y * D.globalPsi y) =
        D.renormalisedExtensionPotential C * D.globalPsi := by
      funext y
      rfl
    rw [he]
    have he' : D.globalPsi = D.globalPiBasis .psi := by rfl
    rw [he']
  have hpotSq := canonicalPolyBounded_norm_fderiv_mul
    hpotSmooth hsqSmooth hpotg hsqg hpotD hsqD
  have hpotPsiSq : PolyBounded (fun z => ‖fderiv ℝ
      (fun y => D.renormalisedExtensionPotential C y *
        (D.globalPsiSq y - C₁ C) - 3 * C₂ C * D.globalPsi y) z‖) := by
    simpa [D, CanonicalData.globalPiBasis] using polyBounded_norm_fderiv_sub_const_mul
      (hpotSmooth.mul hsqSmooth) (hsmooth .psi) hpotSq (hder .psi) (3 * C₂ C)
  have hpotSqSq : PolyBounded (fun z => ‖fderiv ℝ
      (fun y => D.renormalisedExtensionPotential C y *
        D.renormalisedExtensionPotential C y) z‖) := by
    have h := canonicalPolyBounded_norm_fderiv_mul
      hpotSmooth hpotSmooth hpotg hpotg hpotD hpotD
    convert h using 1
  change PolyBounded (fun z => ‖fderiv ℝ
    (D.renormalisedExtensionGlobalBasis C τ) z‖)
  cases τ with
  | psiSq => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hsq
  | psiCube => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hcube
  | psiSqX i =>
      exact canonicalPolyBounded_norm_fderiv_mul
        hsqSmooth (hsmooth (.x i)) hsqg (hglob (.x i)) hsqD (hder (.x i))
  | iPsiCube => exact hpotD
  | iPsiPsiSq =>
      exact canonicalPolyBounded_norm_fderiv_mul
        (hsmooth .iPsi) hsqSmooth (hglob .iPsi) hsqg (hder .iPsi) hsqD
  | iPsiSqPsiSq => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hsqSqSq
  | iPsiCubePsi => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hpotPsi
  | iPsiCubePsiSq =>
      simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
        CanonicalData.globalPiBasis] using hpotPsiSq
  | iPsiCubeSq => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hpotSqSq
  | one => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hder .one
  | noise => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hder .noise
  | x0 => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hder .x0
  | x i => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hder (.x i)
  | xMul p => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hder (.xMul p)
  | psi => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hder .psi
  | iPsi => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hder .iPsi
  | psiX i => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hder (.psiX i)
  | iPsiSq => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hder .iPsiSq
  | iPsiPsi => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hder .iPsiPsi
  | iPsiSqPsi => simpa [CanonicalData.renormalisedExtensionGlobalBasis, D,
      CanonicalData.globalPiBasis] using hder .iPsiSqPsi

end RegularityStructures.Phi43

end
