/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupJointContinuity
public import Phi43.BPHZ.RandomCanonical
public import Phi43.Structure.RenormalisedExtensionModel
public import Phi43.Structure.RenormalisedGammaBounds
import Mathlib.Tactic

/-!
# Pathwise continuity of the canonical model

For the canonical renormalised model `M = canonicalRenormalisedModel N κ noise Cg q hg C` and EVERY
symbol `i, j`:

* `regPi_single_canonicalRenormalisedModel_eq_sum`:
  `Q_t Π_x e_i (z) = Σ_τ coeff_{iτ}(x) Q_t(basis_τ)(z)`;
* `continuousOn_regPi_diag_canonicalRenormalisedModel`: `(t, x) ↦ (Q_t Π_x e_i)(x)` is continuous
  on `t > 0`;
* `continuous_gammaMap_entry_canonicalRenormalisedModel`: `(x, y) ↦ (Γ_{yx} e_i)(j)` is continuous.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
  (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
  (C : RenormalisationConstants)

theorem regPi_single_canonicalRenormalisedModel_eq_sum (x : ParabolicSpace) (i : Symbol) {t : ℝ}
    (ht : 0 < t) (z : ParabolicSpace) :
    (canonicalRenormalisedModel N κ noise Cg q hg C).regPi x (Pi.single i (1 : ℝ) : Symbol → ℝ) t z =
      ∑ τ : Symbol, structureGroupMap
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionCharacter C x) (basis i) τ *
        parabolicSemigroup.apply t
          ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGlobalBasis C τ) z := by
  have he : phi43CoordinateEquiv.symm (Pi.single i (1 : ℝ) : Symbol → ℝ) = basis i := by
    apply phi43CoordinateEquiv.injective
    simp [phi43CoordinateEquiv_basis]
  change (renormalisedExtensionDistribution N (κ := κ) noise
    (canonicalNoise_polyBounded_of_derivatives noise Cg q hg) C x
    (phi43CoordinateEquiv.symm (Pi.single i (1 : ℝ) : Symbol → ℝ)) : ℝ → ParabolicSpace → ℝ) t z = _
  rw [he, renormalisedExtensionDistribution_reg_eq_sum N noise _ C x _ ht]

theorem continuousOn_regPi_diag_canonicalRenormalisedModel (i : Symbol) :
    ContinuousOn (fun w : ℝ × ParabolicSpace =>
      (canonicalRenormalisedModel N κ noise Cg q hg C).regPi w.2 (Pi.single i (1 : ℝ) : Symbol → ℝ)
        w.1 w.2) (Set.Ioi 0 ×ˢ Set.univ) := by
  have hf := canonicalNoise_polyBounded_of_derivatives noise Cg q hg
  have hsum : ContinuousOn (fun w : ℝ × ParabolicSpace => ∑ τ : Symbol, structureGroupMap
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionCharacter C w.2) (basis i) τ *
        parabolicSemigroup.apply w.1
          ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGlobalBasis C τ) w.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
    refine continuousOn_finsetSum _ fun τ _ => ?_
    refine ContinuousOn.mul ?_ ?_
    · exact ((continuous_renormalisedExtensionStructureGroup_coeff N noise C i τ).comp
        continuous_snd).continuousOn
    · exact continuousOn_semigroup_apply (renormalisedExtensionGlobalBasis_growth N κ noise hf C τ)
        (renormalisedExtensionGlobalBasis_smooth N κ noise C τ).continuous
  refine hsum.congr fun w hw => ?_
  exact regPi_single_canonicalRenormalisedModel_eq_sum N κ noise Cg q hg C w.2 i hw.1 w.2

theorem continuous_gammaMap_entry_canonicalRenormalisedModel (i j : Symbol) :
    Continuous (fun w : ParabolicSpace × ParabolicSpace =>
      (canonicalRenormalisedModel N κ noise Cg q hg C).gammaMap w.2 w.1
        (Pi.single i (1 : ℝ) : Symbol → ℝ) j) := by
  have h := continuous_renormalisedGamma_coeff N κ noise C i j
  refine h.congr fun w => ?_
  change _ = (phi43StructureGroupElement
    ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C w.2 w.1) :
      (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) (Pi.single i (1 : ℝ)) j
  rw [phi43StructureGroupElement_apply_single]
  rfl

end RegularityStructures.Phi43

end
