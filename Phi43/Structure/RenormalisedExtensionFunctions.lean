/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionData
public import Phi43.Structure.CanonicalSmoothBasis
import RegularityStructures.Abstract.Integration.Theorem512.Helpers
public import RegularityStructures.Abstract.Integration.Commute.Reg

/-!
# Actual smooth renormalised global trees and their polynomial growth

Hairer [Hai14, (9.3)–(9.5), Theorem 8.44]. These properties are proved
for the explicit global tree functions and the actual causal kernel.
No analytic model-bound hypotheses or certificate bundles are inputs.
Agreement with the H0 tensor formula remains a separate obligation.
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

private theorem const_growth (a : ℝ) : PolyBounded (fun _ : ParabolicSpace => a) :=
  ⟨measurable_const, |a|, 0, fun _ => by simp⟩

open scoped ContDiff in
/-- Every explicit global renormalised tree is smooth. -/
theorem renormalisedExtensionGlobalBasis_smooth (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (c : RenormalisationConstants) (τ : Symbol) :
    ContDiff ℝ ∞ ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGlobalBasis c τ) := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hs := canonicalGlobalPiBasis_smooth N (κ := κ) noise
  have hsq : ContDiff ℝ ∞ (fun y => D.globalPsiSq y - C₁ c) :=
    (hs .psiSq).sub contDiff_const
  have hcube : ContDiff ℝ ∞ (fun y => D.globalPsiCube y - 3 * C₁ c * D.globalPsi y) :=
    (hs .psiCube).sub (contDiff_const.mul (hs .psi))
  have hpot : ContDiff ℝ ∞ (D.renormalisedExtensionPotential c) :=
    (hs .iPsiCube).sub (contDiff_const.mul (hs .iPsi))
  change ContDiff ℝ ∞ (D.renormalisedExtensionGlobalBasis c τ)
  cases τ with
  | psiSq => exact hsq
  | psiCube => exact hcube
  | psiSqX i => exact hsq.mul (hs (.x i))
  | iPsiCube => exact hpot
  | iPsiPsiSq => exact (hs .iPsi).mul hsq
  | iPsiSqPsiSq => exact ((hs .iPsiSq).mul hsq).sub contDiff_const
  | iPsiCubePsi => exact hpot.mul (hs .psi)
  | iPsiCubePsiSq => exact (hpot.mul hsq).sub (contDiff_const.mul (hs .psi))
  | iPsiCubeSq => exact hpot.mul hpot
  | one => exact hs .one
  | noise => exact hs .noise
  | x0 => exact hs .x0
  | x i => exact hs (.x i)
  | xMul q => exact hs (.xMul q)
  | psi => exact hs .psi
  | iPsi => exact hs .iPsi
  | psiX i => exact hs (.psiX i)
  | iPsiSq => exact hs .iPsiSq
  | iPsiPsi => exact hs .iPsiPsi
  | iPsiSqPsi => exact hs .iPsiSqPsi

/-- Polynomial growth of every actual global renormalised tree follows
from polynomial growth of the noise and the explicit finite formulas. -/
theorem renormalisedExtensionGlobalBasis_growth (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (hf : PolyBounded noise.zeta)
    (c : RenormalisationConstants) (τ : Symbol) :
    PolyBounded ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGlobalBasis c τ) := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hg := canonicalGlobalPiBasis_growth N (κ := κ) noise hf
  have hsq : PolyBounded (fun y => D.globalPsiSq y - C₁ c) :=
    (hg .psiSq).sub (const_growth _)
  have hcube : PolyBounded (fun y => D.globalPsiCube y - 3 * C₁ c * D.globalPsi y) :=
    (hg .psiCube).sub ((hg .psi).const_mul _)
  have hpot : PolyBounded (D.renormalisedExtensionPotential c) :=
    (hg .iPsiCube).sub ((hg .iPsi).const_mul _)
  change PolyBounded (D.renormalisedExtensionGlobalBasis c τ)
  cases τ with
  | psiSq => exact hsq
  | psiCube => exact hcube
  | psiSqX i => exact canonicalPolyBounded_mul hsq (hg (.x i))
  | iPsiCube => exact hpot
  | iPsiPsiSq => exact canonicalPolyBounded_mul (hg .iPsi) hsq
  | iPsiSqPsiSq => exact (canonicalPolyBounded_mul (hg .iPsiSq) hsq).sub (const_growth _)
  | iPsiCubePsi => exact canonicalPolyBounded_mul hpot (hg .psi)
  | iPsiCubePsiSq => exact (canonicalPolyBounded_mul hpot hsq).sub ((hg .psi).const_mul _)
  | iPsiCubeSq => exact canonicalPolyBounded_mul hpot hpot
  | one => exact hg .one
  | noise => exact hg .noise
  | x0 => exact hg .x0
  | x i => exact hg (.x i)
  | xMul q => exact hg (.xMul q)
  | psi => exact hg .psi
  | iPsi => exact hg .iPsi
  | psiX i => exact hg (.psiX i)
  | iPsiSq => exact hg .iPsiSq
  | iPsiPsi => exact hg .iPsiPsi
  | iPsiSqPsi => exact hg .iPsiSqPsi

end RegularityStructures.Phi43

end
