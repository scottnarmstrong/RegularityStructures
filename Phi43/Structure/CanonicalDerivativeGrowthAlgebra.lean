/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalConvolutionDerivativeGrowth
public import Phi43.Structure.CanonicalSmoothGrowth
import RegularityStructures.Abstract.Integration.Theorem512.Helpers

/-!
# Polynomial derivative growth for canonical tree operations

Hairer [Hai14, Proposition 8.27] in the polynomially weighted framework
[Hos25, Definition 2.1]. These closure lemmas derive derivative envelopes
through multiplication and actual causal convolution, rather than accepting
analytic bounds on the resulting model.
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- Absolute values preserve the explicit polynomial envelope. -/
theorem canonicalPolyBounded_norm {f : ParabolicSpace → ℝ} (hf : PolyBounded f) :
    PolyBounded (fun z => ‖f z‖) := by
  obtain ⟨hm, C, p, hp⟩ := hf
  refine ⟨hm.norm, C, p, fun z => ?_⟩
  simpa only [Real.norm_eq_abs, abs_abs] using hp z

/-- A measurable function dominated by a polynomially bounded function has
the same envelope. This is a pointwise domination lemma, not model-bound data. -/
theorem canonicalPolyBounded_of_domination {f g : ParabolicSpace → ℝ}
    (hf : Measurable f) (hg : PolyBounded g) (hfg : ∀ z, |f z| ≤ |g z|) :
    PolyBounded f := by
  obtain ⟨_, C, p, hp⟩ := hg
  exact ⟨hf, C, p, fun z => (hfg z).trans (hp z)⟩

open scoped ContDiff in
/-- The norm of the derivative remains polynomially bounded through the
actual causal convolution; its envelope is supplied by the explicit L1 bound. -/
theorem canonicalPolyBounded_norm_fderiv_convolution (N : ℕ)
    {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (hdf : PolyBounded (fun z => ‖fderiv ℝ f z‖)) :
    PolyBounded (fun z => ‖fderiv ℝ (hairerConvolution N f) z‖) := by
  obtain ⟨_, C, p, hp⟩ := hdf
  have hder (z : ParabolicSpace) :
      ‖fderiv ℝ f z‖ ≤ C * (1 + parabolicNorm z) ^ p := by
    simpa only [abs_of_nonneg (norm_nonneg _)] using hp z
  refine ⟨((contDiff_hairerConvolution N hf).continuous_fderiv (by simp)).norm.measurable,
    (∫ w, |hairerKernel N w|) * C * 2 ^ p, p, fun z => ?_⟩
  simpa only [abs_of_nonneg (norm_nonneg _)] using
    norm_fderiv_hairerConvolution_le N hf C p hder z

open scoped ContDiff in
/-- First-derivative growth is preserved by the actual tree product. -/
theorem canonicalPolyBounded_norm_fderiv_mul {f g : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfg : PolyBounded f) (hgg : PolyBounded g)
    (hdf : PolyBounded (fun z => ‖fderiv ℝ f z‖))
    (hdg : PolyBounded (fun z => ‖fderiv ℝ g z‖)) :
    PolyBounded (fun z => ‖fderiv ℝ (f * g) z‖) := by
  have hdom := (canonicalPolyBounded_mul (canonicalPolyBounded_norm hfg) hdg).add
    (canonicalPolyBounded_mul (canonicalPolyBounded_norm hgg) hdf)
  apply canonicalPolyBounded_of_domination
    (((hf.mul hg).continuous_fderiv (by simp)).norm.measurable) hdom
  intro z
  rw [abs_of_nonneg (norm_nonneg _),
    fderiv_fun_mul (hf.differentiable (by simp) z) (hg.differentiable (by simp) z)]
  calc
    _ ≤ ‖f z • fderiv ℝ g z‖ + ‖g z • fderiv ℝ f z‖ := norm_add_le _ _
    _ = ‖f z‖ * ‖fderiv ℝ g z‖ + ‖g z‖ * ‖fderiv ℝ f z‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ _ := le_abs_self _

end RegularityStructures.Phi43

end
