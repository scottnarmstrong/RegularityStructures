/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedBphzCauchyBounds
public import Phi43.BPHZ.ShiftedInputsAssembly
public import Phi43.BPHZ.BphzCauchyMoments
public import Phi43.Steps.RenormalisedCanonicalModel
public import RegularityStructures.Probability.ModelKolmogorov
public import Phi43.Steps.NoiseCauchy
public import Phi43Statements.Defs.ExcludedKappa
public import Phi43Statements.Defs.IsModeratePhi43ModelOf

/-!
# Convergence of the BPHZ models

The renormalised canonical models of the regularised noises, renormalised with Hairer's constants
[Hai14, (10.33), (10.41)], form a Cauchy family in `L^p`, with a rate `max(ε, ε')^θ`, also for two
different mollifiers [Hai14, Theorem 10.22]. The theorem `bphzModels_cauchy` has exactly the
statement `Statements.bphzModels_cauchy` of `Phi43Statements.Steps.BphzModelsCauchy`.

The proof specialises the shifted Cauchy bound `bphzModels_cauchy_shifted` to zero shifts
(`c = c' = 0`, `B = 0`), for which `shiftConst N ρ ε 0` is the pair of Hairer constants. It uses
the existence and uniqueness of the renormalised canonical model
(`renormalisedCanonicalModel_existsUnique`), the Kolmogorov criterion for the model norms
(`kolmogorov_modelNorm`), the convergence of the noise potentials (`phi43Noise_cauchy`), and the
moment bounds for the regularised trees, packaged as
`shiftedBphzInputs_of_bphzCauchyMoments bphzCauchyMoments_holds`.

Source: [Hai14, Theorem 10.22].
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- **Convergence of the BPHZ models**, Cauchy form [Hai14, Theorem 10.22]: uniform moments of the
model norms, and `E ‖Z ε; Z' ε'‖^p ≤ C max(ε, ε')^{θp}` for the models of two mollifiers. -/
theorem bphzModels_cauchy (κ : RegularityStructures.Phi43.Kappa)
    (hκE : κ.1 ∉ RegularityStructures.Phi43.Statements.excludedKappa)
    (N : ℕ) (hN : 5 ≤ N) (ρ ρ' : RegularityStructures.ParabolicSpace → ℝ)
    (hρ : RegularityStructures.Phi43.IsMollifier ρ) (hρ' : RegularityStructures.Phi43.IsMollifier ρ')
    (S : Set RegularityStructures.ParabolicSpace) (hS : IsCompact S) (p : ℕ) (hp : 1 ≤ p) :
    ∃ θ C : ℝ, 0 < θ ∧ 0 ≤ C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure P] (W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ),
      RegularityStructures.IsWhiteNoise P W →
      ∀ (ξ ξ' : ℝ → Ω → RegularityStructures.SpaceTime → ℝ),
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε (ξ ε)) →
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ' ε (ξ' ε)) →
      ∀ (Z Z' : ℝ → Ω → RegularityStructures.Model
          (RegularityStructures.Phi43.phi43RegularityStructure κ)
          RegularityStructures.parabolicSemigroup),
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
          RegularityStructures.Phi43.Statements.IsModeratePhi43ModelOf N κ (ξ ε ω)
            (RegularityStructures.Phi43.hairerWickConstant N ρ ε,
              RegularityStructures.Phi43.hairerSunsetConstant N ρ ε) (Z ε ω)) →
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
          RegularityStructures.Phi43.Statements.IsModeratePhi43ModelOf N κ (ξ' ε ω)
            (RegularityStructures.Phi43.hairerWickConstant N ρ' ε,
              RegularityStructures.Phi43.hairerSunsetConstant N ρ' ε) (Z' ε ω)) →
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ε' ∈ Set.Ioc (0 : ℝ) 1,
        AEMeasurable (fun ω => (Z ε ω).normOn (RegularityStructures.Phi43.gamma κ) S) P ∧
        AEMeasurable
          (fun ω => (Z ε ω).diffNormOn (Z' ε' ω) (RegularityStructures.Phi43.gamma κ) S) P ∧
        ∫⁻ ω, (Z ε ω).normOn (RegularityStructures.Phi43.gamma κ) S ^ p ∂P ≤ ENNReal.ofReal C ∧
        ∫⁻ ω, (Z ε ω).diffNormOn (Z' ε' ω) (RegularityStructures.Phi43.gamma κ) S ^ p ∂P ≤
          ENNReal.ofReal (C * max ε ε' ^ (θ * p)) :=
  by
  obtain ⟨θ, C, hθ, hC, h⟩ := bphzModels_cauchy_shifted.{u_1}
    (fun N κ noise Cg q hg C => renormalisedCanonicalModel_existsUnique N κ noise Cg q hg C)
    (fun {ι} i1 i2 => @kolmogorov_modelNorm ι i1 i2) phi43Noise_cauchy
    (shiftedBphzInputs_of_bphzCauchyMoments bphzCauchyMoments_holds) κ hκE N hN ρ ρ' hρ hρ' S hS p hp 0
    le_rfl
  refine ⟨θ, C, hθ, hC, ?_⟩
  intro Ω _ P _ W hW ξ ξ' hξ hξ' Z Z' hZ hZ' ε hε ε' hε'
  have hsc : ∀ (σ : ParabolicSpace → ℝ) (e : ℝ),
      shiftConst N σ e 0 = (hairerWickConstant N σ e, hairerSunsetConstant N σ e) :=
    fun _ _ => add_zero _
  obtain ⟨h1, h2, h3, h4⟩ := h P W hW ξ ξ' hξ hξ' (fun _ => 0) (fun _ => 0)
    (fun _ _ => by simp) (fun _ _ => by simp) Z Z' (by simpa only [hsc] using hZ)
    (by simpa only [hsc] using hZ') ε hε ε' hε'
  refine ⟨h1, h2, h3, h4.trans_eq ?_⟩
  rw [sub_self, norm_zero, add_zero, ← Real.rpow_natCast,
    ← Real.rpow_mul (le_max_of_le_left hε.1.le)]

end RegularityStructures.Phi43

end
