/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.ExcludedKappa
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Size
public import Phi43Statements.Defs.Phi43Dist
public import RegularityStructures.Probability.WhiteNoise
public import Phi43.Mollifier
public import Phi43.Constants
public import Phi43.Steps.GModelsConvergence

/-!
# Convergence of the G-models

The *G-models* are the renormalised canonical models of the regularised noises, renormalised with
the constants `C₁^ε`, `C₂^ε` of the statement (Definition 2.5), which are built from the massive
heat kernel `G`, shifted by a fixed pair `c = (c₁, c₂)`. Together with the massive potentials of
the noises they form the lifts (`IsModeratePhi43Lift`). For every horizon `T ≥ 1`:

1. the sizes `phi43Size` of the lifts are tight in `ε ∈ (0, 1]`;
2. the lifts are Cauchy in probability for the distance `phi43Dist` as `ε, ε' ↓ 0`, also for two
   different mollifiers;
3. almost surely, for every integer horizon, the lifts along the dyadic scales `ε = 2^{-n}` are
   Cauchy for `phi43Dist` and have bounded sizes.

No rate is asserted. The result combines the convergence of the BPHZ models
[Hai14, Theorem 10.22] with the comparison of the renormalisation constants and the convergence of
the potentials. In the proof of Theorem A, together with the persistence and stopped continuity of
classical solutions, it gives conditions (A1)–(A4). The shift `c = (a/3, 0)` accounts for the
mass `a`.

Here `κ ∈ (0, 1/16)` fixes the homogeneity `-5/2 - κ` of the noise symbol `Ξ` in the Φ⁴₃ regularity
structure `phi43RegularityStructure κ`, the cutoff of the fixed point is `γ = gamma κ = 1 + 3κ`, and
`N` fixes the truncated heat kernel `annKernel0C N` of the kernel decomposition [Hai14, Assumption
5.4].

The proof is `RegularityStructures.Phi43.phi43GModels_convergence`,
in the module `Phi43.Steps.GModelsConvergence`.

Source: [Hai14, Theorem 10.22]; the statement, Theorem A.
-/

public section

namespace RegularityStructures.Phi43

open scoped Topology

/-- **Convergence of the G-models.** Consider the lifts of the regularised noises,
renormalised with the constants of the statement shifted by a fixed `c`, and fix a horizon. (i)
The sizes `S_T` are tight on `(0, 1]`. (ii) The lifts are Cauchy in probability in `d_(T)`, across
mollifiers. (iii) Almost surely, for every integer horizon, the lifts along the dyadic scales
`2^{-n}` are Cauchy in `d_(T)` with bounded sizes. No rate is asserted. -/
theorem Statements.phi43GModels_convergence (κ : RegularityStructures.Phi43.Kappa)
    (hκE : κ.1 ∉ RegularityStructures.Phi43.Statements.excludedKappa) (N : ℕ) (hN : 5 ≤ N)
    (η : RegularityStructures.NegExponent)
    (hη : (η : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ))) (hκη : κ.1 < -(1 / 2 : ℝ) - η)
    (ρ ρ' : RegularityStructures.ParabolicSpace → ℝ)
    (hρ : RegularityStructures.Phi43.IsMollifier ρ) (hρ' : RegularityStructures.Phi43.IsMollifier ρ')
    (c : RegularityStructures.Phi43.RenormalisationConstants) :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure P] (W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ),
      RegularityStructures.IsWhiteNoise P W →
      ∀ (ξ ξ' : ℝ → Ω → RegularityStructures.SpaceTime → ℝ),
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε (ξ ε)) →
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ' ε (ξ' ε)) →
      ∀ (Z Z' : ℝ → Ω → RegularityStructures.Model
          (RegularityStructures.Phi43.phi43RegularityStructure κ)
          RegularityStructures.parabolicSemigroup)
        (ψ ψ' : ℝ → Ω → ℝ → C(RegularityStructures.Torus3, ℝ)),
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
          RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ (ξ ε ω)
            (RegularityStructures.Phi43.wickConstant ρ ε + c.1,
              RegularityStructures.Phi43.sunsetConstant ρ ε + c.2) (Z ε ω) (ψ ε ω)) →
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
          RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ (ξ' ε ω)
            (RegularityStructures.Phi43.wickConstant ρ' ε + c.1,
              RegularityStructures.Phi43.sunsetConstant ρ' ε + c.2) (Z' ε ω) (ψ' ε ω)) →
        (∀ T : ℝ, 1 ≤ T → ∀ ϑ : ℝ, 0 < ϑ → ∃ B : ℝ, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
          P {ω | ENNReal.ofReal B <
            RegularityStructures.Phi43.Statements.phi43Size κ η T (Z ε ω) (ψ ε ω)} ≤
              ENNReal.ofReal ϑ) ∧
        (∀ T : ℝ, 1 ≤ T → ∀ δ : ℝ, 0 < δ →
          Filter.Tendsto (fun e : ℝ × ℝ =>
              P {ω | ENNReal.ofReal δ < RegularityStructures.Phi43.Statements.phi43Dist κ η T
                (Z e.1 ω) (Z' e.2 ω) (ψ e.1 ω) (ψ' e.2 ω)})
            ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 0)) ∧
        ∀ᵐ ω ∂P, ∀ T : ℕ, 1 ≤ T →
          (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
            RegularityStructures.Phi43.Statements.phi43Dist κ η T
              (Z ((2 : ℝ) ^ n)⁻¹ ω) (Z ((2 : ℝ) ^ m)⁻¹ ω)
              (ψ ((2 : ℝ) ^ n)⁻¹ ω) (ψ ((2 : ℝ) ^ m)⁻¹ ω) ≤ ENNReal.ofReal δ) ∧
          ∃ B : ℝ, ∀ n : ℕ,
            RegularityStructures.Phi43.Statements.phi43Size κ η T
              (Z ((2 : ℝ) ^ n)⁻¹ ω) (ψ ((2 : ℝ) ^ n)⁻¹ ω) ≤ ENNReal.ofReal B :=
  by exact RegularityStructures.Phi43.phi43GModels_convergence κ hκE N hN η hη hκη ρ ρ' hρ hρ' c

end RegularityStructures.Phi43

end
