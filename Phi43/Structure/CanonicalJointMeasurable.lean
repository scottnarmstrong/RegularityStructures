/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothJoint
public import Phi43.Structure.CanonicalGrowthPremise
public import Phi43.Structure.RenormalisedExtensionModel
public import Phi43.Structure.RenormalisedExtensionJoint
public import RegularityStructures.Abstract.IntExt.Measurable

/-!
# Joint measurability of the smooth canonical Q-family

For the explicit polynomial-growth canonical model, the Q-family is the
semigroup integral of the jointly smooth actual canonical lift.  This is the
measurability input needed by the abstract planted integration extension;
no analytic model bound is used. It is part of the construction of the
canonical model [Hai14, Proposition 8.27].
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

theorem canonicalRenormalisedModel_isJointMeasurable
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    (canonicalRenormalisedModel N κ noise Cg q hg C).IsJointMeasurable := by
  intro i t ht
  let hf := canonicalNoise_polyBounded_of_derivatives noise Cg q hg
  have hF : Measurable (fun r : ParabolicSpace × ParabolicSpace =>
      (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C
        r.1 (basis i) r.2) :=
    (renormalisedExtensionPi_joint_smooth N κ noise C i).continuous.measurable
  have hK := RegularityStructures.measurable_integral_parabolicKernel_mul hF t
  have he : (fun r : ParabolicSpace × ParabolicSpace =>
      (canonicalRenormalisedModel N κ noise Cg q hg C).regPi r.1
        (Pi.single i 1) t r.2) =
      fun r => ∫ y, parabolicKernel t (r.2 - y) *
        (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C
          r.1 (basis i) y := by
    funext r
    have hi : phi43CoordinateEquiv.symm (Pi.single i 1) = basis i := by
      apply phi43CoordinateEquiv.injective
      simp [phi43CoordinateEquiv_basis]
    rw [canonicalRenormalisedModel_regPi N κ noise Cg q hg C r.1
      (Pi.single i 1) ht r.2, hi]
    rfl
  rw [he]
  exact hK

end RegularityStructures.Phi43

end
