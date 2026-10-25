/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.Kernel1Estimate
public import Phi43.Potential.PairingGenericNear
public import Phi43.Potential.Convolution
public import RegularityStructures.Abstract.Singular.WindowAt.Basic

/-!
# The hypotheses on a model and the noise coordinate it realises

`NoiseModelHyp M γ CPi CGam o ξ` bundles what the pairing bounds need: window bounds of `M` with
near-pair `Γ`, qualitative growth, the symbol `o` of degree below `γ` realised by the continuous
function `ξ` of polynomial growth, bounded on the strip `-1 ≤ t ≤ 2`.  It is stable under the
difference-model construction (used for the two-model version).
-/

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Potential

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- Window model bounds and the realisation of the noise coordinate `o` by `ξ`. -/
structure NoiseModelHyp (M : Model 𝒯 parabolicSemigroup) (γ CPi CGam : ℝ) (o : ι)
    (ξ : ParabolicSpace → ℝ) : Prop where
  pi : M.PiBoundOn γ CPi hairerTimeWindow
  cpi : 0 ≤ CPi
  gam : M.GammaNearOn γ CGam hairerTimeWindow
  deg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j
  ho : 𝒯.deg o < γ
  cont : Continuous ξ
  poly : ∃ (B : ℝ) (n : ℕ), ∀ u, |ξ u| ≤ B * (1 + parabolicNorm u) ^ n
  reg : ∀ (x : ParabolicSpace) (t : ℝ), 0 < t → ∀ y,
    M.regPi x (Pi.single o 1) t y = parabolicSemigroup.apply t ξ y
  growth : ∀ z : ParabolicSpace, 0 ≤ z.1 → z.1 ≤ 1 → M.HasQualitativeGrowthAt γ z
  bdd : ∃ Bξ : ℝ, ∀ y : ParabolicSpace, -1 ≤ y.1 → y.1 ≤ 2 → |ξ y| ≤ Bξ

variable {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam : ℝ} {o : ι} {ξ : ParabolicSpace → ℝ}

/-- The pairing with the part `(1 - χ) K + χ (K - G^m)` of the kernel `K`. -/
theorem NoiseModelHyp.abs_conv_nonpot_le (H : NoiseModelHyp M γ CPi CGam o ξ) (N : ℕ)
    {z : ParabolicSpace} (hz0 : 0 ≤ z.1) (hz1 : z.1 ≤ 1) :
    |potConv ξ (potTail N) z + potConv ξ (potK1 N) z| ≤
      r4ModelConst 𝒯 γ * (max 1 CGam * CPi) *
        (potKernelConst (potTail N) + potK1Const N (𝒯.deg o)) := by
  obtain ⟨B, n, hB⟩ := H.poly
  obtain ⟨Bξ, hξb⟩ := H.bdd
  have h1 := abs_potConv_le_near M H.pi H.cpi H.gam H.deg H.ho H.cont hB H.reg H.growth
    (isUnitKernel_potTail N) hz0 hz1
  have h2 := abs_potConv_potK1_le M H.pi H.cpi H.gam H.deg H.ho H.cont hB H.reg H.growth hξb N
    hz0 hz1
  refine (abs_add_le _ _).trans ?_
  nlinarith

end RegularityStructures.Potential

end
