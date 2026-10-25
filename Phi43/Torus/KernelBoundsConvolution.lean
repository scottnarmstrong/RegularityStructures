/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsPeriodiseL1
public import Phi43.Constants.Finite

/-!
# Real-valued `L¹` bounds for the rescaled periodised mollifier

The fundamental-domain estimate for the periodisation is stated first for lower integrals.  This
file records the corresponding Bochner integral estimate, together with the scale invariance of
the Euclidean rescaling, in the form used by the singular convolution bounds.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

namespace Phi43

theorem integral_abs_periodise_le (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ z, |periodise ρ ε z| ≤ ∫ y, |rescale ρ ε y| := by
  have hP : Integrable (fun z : SpaceTime => |periodise ρ ε z|) :=
    (integrable_periodise ρ hρ hε).norm
  have hR : Integrable (fun y : ParabolicSpace => |rescale ρ ε y|) :=
    integrable_abs_rescale ρ hρ hε
  have hP' : ENNReal.ofReal (∫ z, |periodise ρ ε z|) =
      ∫⁻ z, ENNReal.ofReal |periodise ρ ε z| :=
    ofReal_integral_eq_lintegral_ofReal hP (Filter.Eventually.of_forall fun z => abs_nonneg _)
  have hR' : ENNReal.ofReal (∫ y, |rescale ρ ε y|) =
      ∫⁻ y, ENNReal.ofReal |rescale ρ ε y| :=
    ofReal_integral_eq_lintegral_ofReal hR (Filter.Eventually.of_forall fun y => abs_nonneg _)
  have hle := lintegral_periodise_le ρ hρ hε hε1
  rw [← hP', ← hR'] at hle
  exact (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg_of_ae (Filter.Eventually.of_forall fun z => abs_nonneg _))).mp hle

theorem integral_abs_rescale_eq (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ y, |rescale ρ ε y| = ∫ y, |ρ y| := by
  exact integral_abs_rescale ρ hε

end Phi43

end RegularityStructures

end
