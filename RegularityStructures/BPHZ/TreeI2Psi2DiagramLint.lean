/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import RegularityStructures.Probability.SpaceTimeMeasure

/-!
# Lower-integral bounds: a small calculus

`i2Psi2LintBound μ f M` says `∫⁻ ofReal (f a) ∂μ ≤ ofReal M`.  It is the form in which the
singular-integral estimates of the tree `I(Ψ²) Ψ²` ([Hai14, (10.39)-(10.42)]) are chained: it needs
no integrability bookkeeping, is monotone, additive, scales by constants, and passes through
Tonelli (`i2Psi2LintBound.of_prod_symm`) and products of independent factors.  The final
`abs_integral_le_of_i2Psi2LintBound` turns such a bound on `|f|` into integrability of `f` and a
bound on `|∫ f|`.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures

/-- `f` has lower integral at most `M`: `∫⁻ ofReal (f a) ∂μ ≤ ofReal M`. -/
def i2Psi2LintBound {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (M : ℝ) :
    Prop :=
  ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≤ ENNReal.ofReal M

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem i2Psi2LintBound.mono_ae {f g : α → ℝ} {M M' : ℝ}
    (h : i2Psi2LintBound μ g M) (hfg : ∀ᵐ a ∂μ, f a ≤ g a) (hM : M ≤ M') :
    i2Psi2LintBound μ f M' := by
  unfold i2Psi2LintBound at *
  refine (lintegral_mono_ae ?_).trans (h.trans (ENNReal.ofReal_le_ofReal hM))
  filter_upwards [hfg] with a ha using ENNReal.ofReal_le_ofReal ha

theorem i2Psi2LintBound.mono {f g : α → ℝ} {M M' : ℝ}
    (h : i2Psi2LintBound μ g M) (hfg : ∀ a, f a ≤ g a) (hM : M ≤ M') :
    i2Psi2LintBound μ f M' :=
  h.mono_ae (Filter.Eventually.of_forall hfg) hM

theorem i2Psi2LintBound.add {f g : α → ℝ} {M N : ℝ} (hf : AEMeasurable f μ)
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ a, 0 ≤ g a) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hfM : i2Psi2LintBound μ f M) (hgN : i2Psi2LintBound μ g N) :
    i2Psi2LintBound μ (fun a => f a + g a) (M + N) := by
  unfold i2Psi2LintBound at *
  have h1 : ∫⁻ a, ENNReal.ofReal (f a + g a) ∂μ =
      ∫⁻ a, ENNReal.ofReal (f a) ∂μ + ∫⁻ a, ENNReal.ofReal (g a) ∂μ := by
    rw [← lintegral_add_left' hf.ennreal_ofReal]
    exact lintegral_congr fun a => ENNReal.ofReal_add (hf0 a) (hg0 a)
  rw [h1, ENNReal.ofReal_add hM hN]
  exact add_le_add hfM hgN

theorem i2Psi2LintBound.add_three {f g h : α → ℝ} {M N P : ℝ} (hf : Measurable f)
    (hg : Measurable g) (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ a, 0 ≤ g a) (hh0 : ∀ a, 0 ≤ h a)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hP : 0 ≤ P) (hfM : i2Psi2LintBound μ f M)
    (hgN : i2Psi2LintBound μ g N) (hhP : i2Psi2LintBound μ h P) :
    i2Psi2LintBound μ (fun a => f a + g a + h a) (M + N + P) := by
  have h1 := hfM.add hf.aemeasurable hf0 hg0 hM hN hgN
  exact h1.add (f := fun a => f a + g a) (hf.add hg).aemeasurable
    (fun a => add_nonneg (hf0 a) (hg0 a)) hh0 (add_nonneg hM hN) hP hhP

theorem i2Psi2LintBound.const_mul {f : α → ℝ} {M c : ℝ} (hc : 0 ≤ c)
    (h : i2Psi2LintBound μ f M) : i2Psi2LintBound μ (fun a => c * f a) (c * M) := by
  unfold i2Psi2LintBound at *
  have h1 : ∫⁻ a, ENNReal.ofReal (c * f a) ∂μ = ENNReal.ofReal c * ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun a => ENNReal.ofReal_mul hc
  rw [h1, ENNReal.ofReal_mul hc]
  exact mul_le_mul_right h _

variable {β : Type*} [MeasurableSpace β] {ν : Measure β}

/-- Tonelli, integrating first over the first variable. -/
theorem i2Psi2LintBound.of_prod_symm [SFinite μ] [SFinite ν] {F : α × β → ℝ}
    (hF : Measurable F) {G : β → ℝ} {M : ℝ}
    (h1 : ∀ᵐ b ∂ν, i2Psi2LintBound μ (fun a => F (a, b)) (G b))
    (h2 : i2Psi2LintBound ν G M) : i2Psi2LintBound (μ.prod ν) F M := by
  unfold i2Psi2LintBound at *
  rw [lintegral_prod_symm _ (hF.ennreal_ofReal.aemeasurable)]
  refine le_trans (lintegral_mono_ae ?_) h2
  filter_upwards [h1] with b hb using hb

/-- A product of functions of the two variables. -/
theorem i2Psi2LintBound.prod_mul [SFinite μ] [SFinite ν] {f : α → ℝ} {g : β → ℝ} {M N : ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) (hf0 : ∀ a, 0 ≤ f a) (hM : 0 ≤ M)
    (hfM : i2Psi2LintBound μ f M) (hgN : i2Psi2LintBound ν g N) :
    i2Psi2LintBound (μ.prod ν) (fun q => f q.1 * g q.2) (M * N) := by
  unfold i2Psi2LintBound at *
  have h1 : ∫⁻ q, ENNReal.ofReal (f q.1 * g q.2) ∂μ.prod ν =
      (∫⁻ a, ENNReal.ofReal (f a) ∂μ) * ∫⁻ b, ENNReal.ofReal (g b) ∂ν := by
    rw [← lintegral_prod_mul hf.ennreal_ofReal hg.ennreal_ofReal]
    exact lintegral_congr fun q => ENNReal.ofReal_mul (hf0 q.1)
  rw [h1, ENNReal.ofReal_mul hM]
  exact mul_le_mul' hfM hgN

/-- A lower-integral bound on `|f|` gives integrability of `f` and a bound on `|∫ f|`. -/
theorem abs_integral_le_of_i2Psi2LintBound {f : α → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f μ) (h : i2Psi2LintBound μ (fun a => |f a|) M) (hM : 0 ≤ M) :
    Integrable f μ ∧ |∫ a, f a ∂μ| ≤ M := by
  unfold i2Psi2LintBound at h
  have hfin : ∫⁻ a, ‖f a‖ₑ ∂μ < ⊤ := by
    have : ∫⁻ a, ‖f a‖ₑ ∂μ = ∫⁻ a, ENNReal.ofReal (|f a|) ∂μ :=
      lintegral_congr fun a => by rw [Real.enorm_eq_ofReal_abs]
    rw [this]
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  refine ⟨⟨hf, hfin⟩, ?_⟩
  have hnn : 0 ≤ᵐ[μ] fun a => |f a| := Filter.Eventually.of_forall fun a => abs_nonneg _
  have h2 : ∫ a, |f a| ∂μ = (∫⁻ a, ENNReal.ofReal (|f a|) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hnn (by simpa only [Real.norm_eq_abs] using hf.norm)
  calc |∫ a, f a ∂μ| = ‖∫ a, f a ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ a, ‖f a‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ a, |f a| ∂μ := by simp only [Real.norm_eq_abs]
    _ = (∫⁻ a, ENNReal.ofReal (|f a|) ∂μ).toReal := h2
    _ ≤ (ENNReal.ofReal M).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = M := ENNReal.toReal_ofReal hM

end RegularityStructures

end
