/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GModelsMoments
public import Phi43.BPHZ.GModelsConstantShift
public import Phi43.BPHZ.GModelsNoiseDist
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Dist
public import Phi43Statements.Defs.Phi43Size
public import RegularityStructures.BPHZ.CauchyTransfer

/-!
# Tightness and Cauchy property in probability of the `G`-models

* `tendsto_measure_lt_of_shifted_momentBound`: Markov for a first moment bounded by
  `C * (max ε ε' ^ θ + d ε ε')` with `d → 0`.
* `gModels_tight` and `gModels_cauchy`: the tightness and Cauchy-in-probability clauses of the
  convergence of the G-models, from the first moments of the `G`-models
  (`gModels_bphzCauchy_moments`) and of the noise (`phi43Noise_cauchy`).

The argument goes through the shifted BPHZ models and uses no Lipschitz bound for the action of the
renormalisation constants on models.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

universe u

namespace RegularityStructures

/-- Convergence in probability from a first-moment bound with a rate-`θ` term and a vanishing
term `d`. -/
theorem tendsto_measure_lt_of_shifted_momentBound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : ℝ → ℝ → Ω → ℝ≥0∞} {d : ℝ → ℝ → ℝ} {θ C : ℝ} (hθ : 0 < θ)
    (hm : ∀ ε ε' : ℝ, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 → AEMeasurable (D ε ε') P)
    (hb : ∀ ε ε' : ℝ, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∫⁻ ω, D ε ε' ω ∂P ≤ ENNReal.ofReal (C * (max ε ε' ^ θ + d ε ε')))
    (hd : Tendsto (fun e : ℝ × ℝ => d e.1 e.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun e : ℝ × ℝ => P {ω | ENNReal.ofReal δ < D e.1 e.2 ω})
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hmax : Tendsto (fun e : ℝ × ℝ => max e.1 e.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun e : ℝ × ℝ => e.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.comp tendsto_fst
    have h2 : Tendsto (fun e : ℝ × ℝ => e.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.comp tendsto_snd
    simpa using h1.max h2
  have hrp : Tendsto (fun e : ℝ × ℝ => max e.1 e.2 ^ θ) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto.comp hmax
    rw [Real.zero_rpow hθ.ne'] at this
    exact this
  have hup : Tendsto (fun e : ℝ × ℝ => C / δ * (max e.1 e.2 ^ θ + d e.1 e.2))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ((hrp.add hd).const_mul (C / δ))
  have hup' := (ENNReal.tendsto_ofReal hup)
  rw [ENNReal.ofReal_zero] at hup'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup' (Eventually.of_forall
    fun _ => bot_le) ?_
  have hev : ∀ᶠ e : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ), 0 < e.1 ∧ e.1 ≤ 1 ∧ 0 < e.2 ∧
      e.2 ≤ 1 := by
    have a : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 < x ∧ x ≤ 1 := by
      filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with x hx hx1
      exact ⟨hx, hx1.2⟩
    exact (a.prod_inl _).and (a.prod_inr _) |>.mono fun e he => ⟨he.1.1, he.1.2, he.2.1, he.2.2⟩
  filter_upwards [hev] with e ⟨h0, h1, h0', h1'⟩
  have hM := mul_meas_ge_le_lintegral₀ (hm _ _ h0 h1 h0' h1') (ENNReal.ofReal δ)
  have hδ' : ENNReal.ofReal δ ≠ 0 := (ENNReal.ofReal_pos.2 hδ).ne'
  have hsub : P {ω | ENNReal.ofReal δ < D e.1 e.2 ω} ≤ P {ω | ENNReal.ofReal δ ≤ D e.1 e.2 ω} :=
    measure_mono fun ω (hω : ENNReal.ofReal δ < D e.1 e.2 ω) => le_of_lt hω
  refine hsub.trans ?_
  have hle : ENNReal.ofReal δ * P {ω | ENNReal.ofReal δ ≤ D e.1 e.2 ω} ≤
      ENNReal.ofReal (C * (max e.1 e.2 ^ θ + d e.1 e.2)) := hM.trans (hb _ _ h0 h1 h0' h1')
  have h2 : P {ω | ENNReal.ofReal δ ≤ D e.1 e.2 ω} ≤
      ENNReal.ofReal (C * (max e.1 e.2 ^ θ + d e.1 e.2)) / ENNReal.ofReal δ :=
    (ENNReal.le_div_iff_mul_le (Or.inl hδ') (Or.inl ENNReal.ofReal_ne_top)).2
      (by rw [mul_comm]; exact hle)
  refine h2.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_div_of_pos hδ]
  congr 1
  ring

end RegularityStructures

namespace RegularityStructures.Phi43

/-- **Tightness of the sizes** of the `G`-models. -/
theorem gModels_tight (hG1 : RenormalisedCanonicalModelStatement) (hG5 : KolmogorovModelNormStatement.{u, 0})
    (hG7 : NoiseCauchyStatement.{u}) (hG8 : ConstantsComparisonStatement)
    (hin : ∀ (N : ℕ) (κ : RegularityStructures.Phi43.Kappa),
      RegularityStructures.Phi43.ShiftedBphzInputs.{u} N κ)
    {κ : RegularityStructures.Phi43.Kappa}
    (hκE : κ.1 ∉ RegularityStructures.Phi43.Statements.excludedKappa) {N : ℕ} (hN : 5 ≤ N)
    {η : RegularityStructures.NegExponent}
    (hη : (η : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    {ρ : RegularityStructures.ParabolicSpace → ℝ}
    (hρ : RegularityStructures.Phi43.IsMollifier ρ)
    (c : RegularityStructures.Phi43.RenormalisationConstants)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ)
    (hW : RegularityStructures.IsWhiteNoise P W)
    (ξ : ℝ → Ω → RegularityStructures.SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε (ξ ε))
    (Z : ℝ → Ω → RegularityStructures.Model
      (RegularityStructures.Phi43.phi43RegularityStructure κ)
      RegularityStructures.parabolicSemigroup)
    (ψ : ℝ → Ω → ℝ → C(RegularityStructures.Torus3, ℝ))
    (hlift : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
      RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ (ξ ε ω)
        (RegularityStructures.Phi43.wickConstant ρ ε + c.1,
          RegularityStructures.Phi43.sunsetConstant ρ ε + c.2) (Z ε ω) (ψ ε ω)) :
    ∀ T : ℝ, 1 ≤ T → ∀ ϑ : ℝ, 0 < ϑ → ∃ B : ℝ, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      P {ω | ENNReal.ofReal B <
        RegularityStructures.Phi43.Statements.phi43Size κ η T (Z ε ω) (ψ ε ω)} ≤
          ENNReal.ofReal ϑ := by
  obtain ⟨Bc, hBc, -, -, -⟩ := gModels_constants hG8 N hρ hρ c
  have hψ : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P, RegularityStructures.IsMassivePotential (ξ ε ω) (ψ ε ω) :=
    fun ε hε => (hlift ε hε).mono fun ω hω => hω.2.2
  intro T hT ϑ hϑ
  obtain ⟨_, C₁, _, _, hA, -⟩ := gModels_bphzCauchy_moments hG1 hG5 hG7 hin κ hκE N hN ρ ρ hρ hρ c hBc hBc
    (Statements.phi43Box (T + 1)) (isCompact_phi43Box _) P W hW ξ ξ hξ hξ Z Z ψ ψ hlift hlift
  obtain ⟨_, C₂, _, _, hN7, -⟩ := gModels_noiseCauchy_moments hG7 η hη.2 ρ ρ hρ hρ T hT P W hW ξ ξ
    hξ hξ ψ ψ hψ hψ
  obtain ⟨B, hB⟩ := RegularityStructures.exists_measure_lt_add_le_of_transfer
    (A := fun ε ω => (Z ε ω).normOn (RegularityStructures.Phi43.gamma κ) (Statements.phi43Box (T + 1)))
    (Nz := fun ε ω => Statements.phi43NoiseSize η T (ψ ε ω))
    (X := fun ε ω => (Z ε ω).normOn (RegularityStructures.Phi43.gamma κ) (Statements.phi43Box (T + 1)))
    (fun ε h0 h1 => (hA ε h0 h1).1) (fun ε h0 h1 => (hA ε h0 h1).2)
    (fun ε h0 h1 => (hN7 ε h0 h1).1) (fun ε h0 h1 => (hN7 ε h0 h1).2)
    ⟨0, fun B _ => ⟨B, fun _ _ _ => Filter.Eventually.of_forall fun _ h => h⟩⟩ hϑ
  exact ⟨B, fun ε hε => hB ε hε.1 hε.2⟩

/-- **Cauchy in probability** of the `G`-models across mollifiers. -/
theorem gModels_cauchy (hG1 : RenormalisedCanonicalModelStatement) (hG5 : KolmogorovModelNormStatement.{u, 0})
    (hG7 : NoiseCauchyStatement.{u}) (hG8 : ConstantsComparisonStatement)
    (hin : ∀ (N : ℕ) (κ : RegularityStructures.Phi43.Kappa),
      RegularityStructures.Phi43.ShiftedBphzInputs.{u} N κ)
    {κ : RegularityStructures.Phi43.Kappa}
    (hκE : κ.1 ∉ RegularityStructures.Phi43.Statements.excludedKappa) {N : ℕ} (hN : 5 ≤ N)
    {η : RegularityStructures.NegExponent}
    (hη : (η : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    {ρ ρ' : RegularityStructures.ParabolicSpace → ℝ}
    (hρ : RegularityStructures.Phi43.IsMollifier ρ)
    (hρ' : RegularityStructures.Phi43.IsMollifier ρ')
    (c : RegularityStructures.Phi43.RenormalisationConstants)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ)
    (hW : RegularityStructures.IsWhiteNoise P W)
    (ξ ξ' : ℝ → Ω → RegularityStructures.SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε (ξ ε))
    (hξ' : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ' ε (ξ' ε))
    (Z Z' : ℝ → Ω → RegularityStructures.Model
      (RegularityStructures.Phi43.phi43RegularityStructure κ)
      RegularityStructures.parabolicSemigroup)
    (ψ ψ' : ℝ → Ω → ℝ → C(RegularityStructures.Torus3, ℝ))
    (hlift : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
      RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ (ξ ε ω)
        (RegularityStructures.Phi43.wickConstant ρ ε + c.1,
          RegularityStructures.Phi43.sunsetConstant ρ ε + c.2) (Z ε ω) (ψ ε ω))
    (hlift' : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
      RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ (ξ' ε ω)
        (RegularityStructures.Phi43.wickConstant ρ' ε + c.1,
          RegularityStructures.Phi43.sunsetConstant ρ' ε + c.2) (Z' ε ω) (ψ' ε ω)) :
    ∀ T : ℝ, 1 ≤ T → ∀ δ : ℝ, 0 < δ →
      Filter.Tendsto (fun e : ℝ × ℝ =>
          P {ω | ENNReal.ofReal δ < RegularityStructures.Phi43.Statements.phi43Dist κ η T
            (Z e.1 ω) (Z' e.2 ω) (ψ e.1 ω) (ψ' e.2 ω)})
        ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  obtain ⟨Bc, hBc, hBc', hd, -⟩ := gModels_constants hG8 N hρ hρ' c
  have hψ : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P, RegularityStructures.IsMassivePotential (ξ ε ω) (ψ ε ω) :=
    fun ε hε => (hlift ε hε).mono fun ω hω => hω.2.2
  have hψ' : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P, RegularityStructures.IsMassivePotential (ξ' ε ω) (ψ' ε ω) :=
    fun ε hε => (hlift' ε hε).mono fun ω hω => hω.2.2
  intro T hT δ hδ
  obtain ⟨θ₁, C₁, hθ₁, hC₁, hA, hE⟩ := gModels_bphzCauchy_moments hG1 hG5 hG7 hin κ hκE N hN ρ ρ' hρ hρ' c
    hBc hBc' (Statements.phi43Box (T + 1)) (isCompact_phi43Box _) P W hW ξ ξ' hξ hξ' Z Z' ψ ψ' hlift hlift'
  obtain ⟨_, _, _, _, hA', -⟩ := gModels_bphzCauchy_moments hG1 hG5 hG7 hin κ hκE N hN ρ' ρ hρ' hρ c
    hBc' hBc (Statements.phi43Box (T + 1)) (isCompact_phi43Box _) P W hW ξ' ξ hξ' hξ Z' Z ψ' ψ hlift' hlift
  obtain ⟨θ₂, C₂, hθ₂, hC₂, -, hNd⟩ := gModels_noiseCauchy_moments hG7 η hη.2 ρ ρ' hρ hρ' T hT P W hW ξ ξ'
    hξ hξ' ψ ψ' hψ hψ'
  have hD : ∀ δ : ℝ, 0 < δ → Tendsto (fun e : ℝ × ℝ =>
      P {ω | ENNReal.ofReal δ < (Z e.1 ω).diffNormOn (Z' e.2 ω)
        (RegularityStructures.Phi43.gamma κ) (Statements.phi43Box (T + 1))})
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := fun δ hδ =>
    RegularityStructures.tendsto_measure_lt_of_shifted_momentBound hθ₁
      (D := fun ε ε' ω => (Z ε ω).diffNormOn (Z' ε' ω) (RegularityStructures.Phi43.gamma κ)
        (Statements.phi43Box (T + 1)))
      (d := fun ε ε' => ‖RegularityStructures.Phi43.gModelsShift N ρ c ε -
        RegularityStructures.Phi43.gModelsShift N ρ' c ε'‖) (C := C₁)
      (fun ε ε' h0 h1 h0' h1' => (hE ε ⟨h0, h1⟩ ε' ⟨h0', h1'⟩).1)
      (fun ε ε' h0 h1 h0' h1' => (hE ε ⟨h0, h1⟩ ε' ⟨h0', h1'⟩).2) hd hδ
  refine RegularityStructures.tendsto_measure_lt_add_of_transfer
    (A₁ := fun ε ω => (Z ε ω).normOn (RegularityStructures.Phi43.gamma κ) (Statements.phi43Box (T + 1)))
    (A₂ := fun ε ω => (Z' ε ω).normOn (RegularityStructures.Phi43.gamma κ) (Statements.phi43Box (T + 1)))
    (Nd := fun ε ε' ω => Statements.phi43NoiseDist η T (ψ ε ω) (ψ' ε' ω))
    (X := fun ε ε' ω => (Z ε ω).diffNormOn (Z' ε' ω) (RegularityStructures.Phi43.gamma κ)
      (Statements.phi43Box (T + 1)))
    (E := fun ε ε' ω => (Z ε ω).diffNormOn (Z' ε' ω) (RegularityStructures.Phi43.gamma κ)
      (Statements.phi43Box (T + 1)))
    (d := fun _ _ => 0)
    (fun ϑ hϑ => RegularityStructures.exists_measure_lt_le_of_sizeMoment hA hϑ)
    (fun ϑ hϑ => RegularityStructures.exists_measure_lt_le_of_sizeMoment hA' hϑ)
    hD (fun δ hδ => RegularityStructures.tendsto_measure_lt_of_momentBound hθ₂ hC₂ hNd hδ)
    tendsto_const_nhds ?_ hδ
  exact ⟨0, fun B _ => ⟨1, fun ε ε' _ _ _ _ => Filter.Eventually.of_forall fun ω _ _ => by
    simp⟩⟩

end RegularityStructures.Phi43

end
