/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CanonicalBridgeConvolution
public import Phi43.BPHZ.TreeFormulas

/-!
# `hairerCanonicalData`: the local fields

For `D = hairerCanonicalData N noise` with `noise.zeta = ξ ∘ proj`, we prove

* `D.localPsi = Ψ ∘ proj` (via the periodisation identity),
* the integrated-tree integrals are differences of convolutions.

These facts need no hypothesis on the noise other than smoothness.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

local notation "E" => ParabolicSpace

/-- The smooth periodic noise `ζ = ξ ∘ proj` as a `CanonicalNoise`. -/
@[expose] def canonicalNoiseOfSpaceTime (ξ : SpaceTime → ℝ) (hξ : IsSmoothOnSpaceTime ξ) : CanonicalNoise where
  zeta := fun z => ξ (spaceTimeProj z)
  smooth := hξ
  periodic := by
    intro n z
    simp only [spaceTimeProj]
    congr 2
    funext i
    simp [torusProj]

namespace CanonicalData

variable {κ : Kappa} {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (ω : Ω)
  (noise : CanonicalNoise)

variable {N noise}

/-- Taylor-subtracted integration of `hairerCanonicalData` at a constant-order homogeneity is a
difference of two convolutions. -/
theorem hairerCanonicalData_integrate_eq {r : ℝ} (h0 : 0 < r) (h1 : ¬ 1 < r) (f : E → ℝ)
    (z y : E) :
    (hairerCanonicalData (κ := κ) N noise).integrate r f z y =
      hairerConvolution N f y - hairerConvolution N f z :=
  integrate_eq_of_pos_of_not_gt_one _ h0 h1 f z y

variable (κ N)

/-- `localPsi = Ψ ∘ proj` for the lifted noise. -/
theorem hairerCanonicalData_localPsi_eq (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z))
    (hξ : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N noise).localPsi =
      fun y => hairerPsiField N ξ ω (spaceTimeProj y) := by
  funext y
  have hpsi : homogeneity κ .psi ≤ 0 := by
    have := κ.2.1
    have := κ.2.2
    simp only [homogeneity]
    linarith
  change CanonicalKernel.convolution (hairerCanonicalKernel N) noise.zeta y -
      (hairerCanonicalKernel N).taylorPolynomial (homogeneity κ .psi) noise.zeta 0 y = _
  rw [CanonicalKernel.taylorPolynomial_of_nonpos _ hpsi, sub_zero]
  have hz : noise.zeta = fun z => ξ ω (spaceTimeProj z) := funext hn
  change hairerConvolution N noise.zeta y = _
  rw [hz]
  exact hairerConvolution_comp_proj_eq N (IsSmoothOnSpaceTime.continuous hξ) y

end CanonicalData

end RegularityStructures.Phi43

end
