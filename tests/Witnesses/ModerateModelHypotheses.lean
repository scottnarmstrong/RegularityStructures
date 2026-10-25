/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Steps.RenormalisedCanonicalModel
public import Phi43Statements.Steps.NoiseCauchy
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.IsRenormalisedCanonicalModel
public import Phi43Statements.ClassicalWellPosed

/-!
# Satisfiability of the hypotheses on moderate canonical models

* **Section A**: the weighted growth clause of `IsModerateRenormalisedCanonicalModel` is inhabited
  (constant weight), the predicate is exactly `IsRenormalisedCanonicalModel` together with the
  growth clause, and a global unweighted `Π` bound gives the clause.
* **Section B** applies `Statements.renormalisedCanonicalModel_existsUnique` and
  `Statements.phi43Noise_cauchy`: the moderate-lift hypotheses of
  `Statements.phi43ClassicalSolution_stoppedContinuity`, `Statements.bphzModels_cauchy` and
  `Statements.phi43GModels_convergence` are inhabited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace RegularityStructures.Phi43.ModerateWitnesses

/-! ## A. The weighted growth clause -/

/-- The weight `ρ = 1` is moderate with `p = 0`. -/
theorem moderateWeight_inhabited :
    ∃ (ρ : RegularityStructures.ParabolicSpace → ℝ) (p : ℝ),
      RegularityStructures.RegularisingSemigroup.IsModerateWeight
        RegularityStructures.parabolicSemigroup ρ p :=
  ⟨_, _, RegularityStructures.parabolicSemigroup.isModerateWeight_one⟩

/-- `IsModerateRenormalisedCanonicalModel` is `IsRenormalisedCanonicalModel` plus the weighted
growth clause. -/
theorem isModerateRenormalisedCanonicalModel_iff (N : ℕ) (κ : RegularityStructures.Phi43.Kappa)
    (noise : RegularityStructures.Phi43.CanonicalNoise)
    (C : RegularityStructures.Phi43.RenormalisationConstants)
    (Z : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
      RegularityStructures.parabolicSemigroup) :
    Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z ↔
      Statements.IsRenormalisedCanonicalModel N κ noise C Z ∧
        ∃ (ρ : RegularityStructures.ParabolicSpace → ℝ) (p B : ℝ),
          RegularityStructures.RegularisingSemigroup.IsModerateWeight
              RegularityStructures.parabolicSemigroup ρ p ∧
            0 ≤ B ∧ Z.PiBoundGrowth (RegularityStructures.Phi43.gamma κ) B ρ :=
  ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩, fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

/-- A global unweighted `Π` bound gives the growth clause with `ρ = 1`. -/
theorem growthClause_of_piBoundOn_univ {κ : RegularityStructures.Phi43.Kappa}
    (Z : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
      RegularityStructures.parabolicSemigroup) {B : ℝ} (hB : 0 ≤ B)
    (h : Z.PiBoundOn (RegularityStructures.Phi43.gamma κ) B Set.univ) :
    ∃ (ρ : RegularityStructures.ParabolicSpace → ℝ) (p B : ℝ),
      RegularityStructures.RegularisingSemigroup.IsModerateWeight
          RegularityStructures.parabolicSemigroup ρ p ∧
        0 ≤ B ∧ Z.PiBoundGrowth (RegularityStructures.Phi43.gamma κ) B ρ :=
  ⟨_, _, B, RegularityStructures.parabolicSemigroup.isModerateWeight_one, hB,
    h.piBoundGrowth⟩

/-- The zero noise. -/
def zeroNoise : RegularityStructures.Phi43.CanonicalNoise where
  zeta _ := 0
  smooth := contDiff_const
  periodic _ _ := rfl

/-- The zero noise satisfies the growth premise of
`Statements.renormalisedCanonicalModel_existsUnique` with `Cg = 0`, `q = 0`. -/
theorem zeroNoise_growth : ∀ k : ℕ, k ≤ 4 → ∀ z : RegularityStructures.ParabolicSpace,
    ‖iteratedFDeriv ℝ k zeroNoise.zeta z‖ ≤ 0 * (1 + RegularityStructures.parabolicNorm z) ^ 0 := by
  intro k _ z
  simp [zeroNoise, iteratedFDeriv_fun_zero]

theorem isSmoothOnSpaceTime_zero :
    RegularityStructures.IsSmoothOnSpaceTime (fun _ => 0) := by
  unfold RegularityStructures.IsSmoothOnSpaceTime
  exact contDiff_const

theorem hasPhi43NoiseGrowth_zero :
    RegularityStructures.Phi43.Statements.HasPhi43NoiseGrowth (fun _ => 0) :=
  ⟨0, 0, fun k _ z => by simp⟩

theorem isMassivePotential_zero :
    RegularityStructures.IsMassivePotential (fun _ => 0) (fun _ => 0) :=
  ⟨fun t x => by simp, fun t x => by simp⟩

/-! ## B. Moderate lifts -/

/-- The periodic lift of a smooth noise on `ℝ × T³`. -/
def liftNoise (f : RegularityStructures.SpaceTime → ℝ)
    (hf : RegularityStructures.IsSmoothOnSpaceTime f) : RegularityStructures.Phi43.CanonicalNoise where
  zeta z := f (z.1, RegularityStructures.torusProj z.2)
  smooth := hf
  periodic n z := by
    congr 2
    funext i
    simp [RegularityStructures.torusProj]

/-- `Statements.renormalisedCanonicalModel_existsUnique` gives a moderate model of every smooth
noise with growth, for any constants. -/
theorem exists_moderatePhi43ModelOf (N : ℕ) (κ : RegularityStructures.Phi43.Kappa)
    (f : RegularityStructures.SpaceTime → ℝ) (hf : RegularityStructures.IsSmoothOnSpaceTime f)
    (hg : RegularityStructures.Phi43.Statements.HasPhi43NoiseGrowth f)
    (C : RegularityStructures.Phi43.RenormalisationConstants) :
    ∃ Z, RegularityStructures.Phi43.Statements.IsModeratePhi43ModelOf N κ f C Z := by
  obtain ⟨Cg, q, hgq⟩ := hg
  obtain ⟨⟨Z, hZ⟩, -⟩ :=
    RegularityStructures.Phi43.Statements.renormalisedCanonicalModel_existsUnique N κ
      (liftNoise f hf) Cg q hgq C
  exact ⟨Z, liftNoise f hf, fun _ => rfl, hZ⟩

/-- The almost-sure lift hypotheses of `Statements.bphzModels_cauchy` and
`Statements.phi43GModels_convergence` hold, by the first two parts of `Statements.phi43Noise_cauchy`. -/
theorem ae_exists_moderatePhi43Lift (N : ℕ) (κ : RegularityStructures.Phi43.Kappa)
    (ρ : RegularityStructures.ParabolicSpace → ℝ) (hρ : RegularityStructures.Phi43.IsMollifier ρ)
    (η : RegularityStructures.NegExponent) (hη : (η : ℝ) < -(1 / 2 : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ)
    (hW : RegularityStructures.IsWhiteNoise P W) (ξ : ℝ → Ω → RegularityStructures.SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε (ξ ε))
    (C : RegularityStructures.Phi43.RenormalisationConstants) :
    ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
      ∃ Z ψ, RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ (ξ ε ω) C Z ψ := by
  intro ε hε
  obtain ⟨hpot, hgrowth, -⟩ := RegularityStructures.Phi43.Statements.phi43Noise_cauchy.{_, 0} η hη
  filter_upwards [(hgrowth ρ hρ P W hW ξ hξ ε hε).2] with ω hω
  obtain ⟨Z, hZ⟩ := exists_moderatePhi43ModelOf N κ (ξ ε ω) ((hξ ε hε).1 ω) hω C
  obtain ⟨ψ, hψ, -, -⟩ := hpot (ξ ε ω) ((hξ ε hε).1 ω) hω
  exact ⟨Z, ψ, hω, hZ, hψ⟩

/-- The hypotheses of `Statements.phi43ClassicalSolution_stoppedContinuity` are jointly inhabited. -/
theorem stoppedContinuity_hypotheses_inhabited (N : ℕ) (κ : RegularityStructures.Phi43.Kappa)
    (u₀ : C(RegularityStructures.Torus3, ℝ)) (hu₀ : RegularityStructures.IsSmoothOnTorus u₀) :
    ∃ (Z : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
        RegularityStructures.parabolicSemigroup) (u : ℝ → C(RegularityStructures.Torus3, ℝ)),
      RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ (fun _ => 0) (0, 0) Z (fun _ => 0) ∧
      RegularityStructures.Phi43.IsClassicalSolution (3 * (0 : ℝ × ℝ).1 - 9 * (0 : ℝ × ℝ).2)
        (fun _ => 0) u₀ u := by
  obtain ⟨Z, hZ⟩ := exists_moderatePhi43ModelOf N κ (fun _ => 0) isSmoothOnSpaceTime_zero
    hasPhi43NoiseGrowth_zero (0, 0)
  obtain ⟨⟨u, hu⟩, -⟩ := RegularityStructures.Phi43.Statements.classicalSolution_exists_unique
    (3 * (0 : ℝ × ℝ).1 - 9 * (0 : ℝ × ℝ).2) isSmoothOnSpaceTime_zero hu₀
  exact ⟨Z, u, ⟨hasPhi43NoiseGrowth_zero, hZ, isMassivePotential_zero⟩, hu⟩

/-- The model hypotheses of `Statements.bphzModels_cauchy` and `Statements.phi43GModels_convergence`
are inhabited for every family of constants. -/
theorem moderateLift_family_inhabited (N : ℕ) (κ : RegularityStructures.Phi43.Kappa)
    (ρ : RegularityStructures.ParabolicSpace → ℝ) (hρ : RegularityStructures.Phi43.IsMollifier ρ)
    (η : RegularityStructures.NegExponent) (hη : (η : ℝ) < -(1 / 2 : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ)
    (hW : RegularityStructures.IsWhiteNoise P W) (ξ : ℝ → Ω → RegularityStructures.SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε (ξ ε))
    (C : ℝ → RegularityStructures.Phi43.RenormalisationConstants) :
    ∃ (Z : ℝ → Ω → RegularityStructures.Model
        (RegularityStructures.Phi43.phi43RegularityStructure κ)
        RegularityStructures.parabolicSemigroup)
      (ψ : ℝ → Ω → ℝ → C(RegularityStructures.Torus3, ℝ)),
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
        RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ (ξ ε ω) (C ε) (Z ε ω) (ψ ε ω) := by
  classical
  obtain ⟨Z₀, -⟩ := exists_moderatePhi43ModelOf N κ (fun _ => 0) isSmoothOnSpaceTime_zero
    hasPhi43NoiseGrowth_zero (0, 0)
  refine ⟨fun ε ω => if h : ∃ Z ψ,
        RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ (ξ ε ω) (C ε) Z ψ
      then h.choose else Z₀,
    fun ε ω => if h : ∃ Z ψ,
        RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ (ξ ε ω) (C ε) Z ψ
      then h.choose_spec.choose else fun _ => 0, fun ε hε => ?_⟩
  filter_upwards [ae_exists_moderatePhi43Lift N κ ρ hρ η hη P W hW ξ hξ (C ε) ε hε] with ω hω
  simp only [hω, ↓reduceDIte]
  exact hω.choose_spec.choose_spec


end RegularityStructures.Phi43.ModerateWitnesses

end
