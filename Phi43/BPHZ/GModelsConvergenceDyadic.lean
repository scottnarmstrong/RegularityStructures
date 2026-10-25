/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GModelsTightCauchy
public import Phi43.BPHZ.GModelsConstantShift
public import Phi43.BPHZ.GModelsNoiseDist
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Dist
public import Phi43Statements.Defs.Phi43Size
public import RegularityStructures.BPHZ.ModelNormTriangle

/-!
# The dyadic almost-sure clause, from a power rate for the constant shifts

`gModels_dyadic_of_shiftRate` is the dyadic clause of the convergence of the `G`-models.  The
first moment of the model difference from the Cauchy bound for the shifted BPHZ models has the
factor `max ε ε' ^ θ + ‖s ε - s ε'‖`; with a power rate for `s ε` towards a limit `L` this is a
`MomentBound` of exponent `min θ θ'`, and the dyadic Borel–Cantelli argument applies.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

universe u

namespace RegularityStructures.Phi43

/-- A power rate towards a limit turns the shifted first moment into a `MomentBound`. -/
theorem momentBound_of_shiftRate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : ℝ → ℝ → Ω → ℝ≥0∞} {s : ℝ → RenormalisationConstants} {L : RenormalisationConstants}
    {C₀ θ θ' C₁ : ℝ} (hθ' : 0 < θ') (hC₁ : 0 ≤ C₁)
    (hrate : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ‖s ε - L‖ ≤ C₀ * ε ^ θ')
    (hE : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ε' ∈ Set.Ioc (0 : ℝ) 1,
      AEMeasurable (D ε ε') P ∧
        ∫⁻ ω, D ε ε' ω ∂P ≤ ENNReal.ofReal (C₁ * (max ε ε' ^ θ + ‖s ε - s ε'‖))) :
    MomentBound P D (min θ θ') (C₁ * (1 + 2 * C₀)) := by
  intro ε ε' h0 h1 h0' h1'
  obtain ⟨hm, hb⟩ := hE ε ⟨h0, h1⟩ ε' ⟨h0', h1'⟩
  refine ⟨hm, hb.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hC₀ : 0 ≤ C₀ := by
    have := hrate 1 ⟨one_pos, le_rfl⟩
    rw [Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hm0 : 0 < max ε ε' := lt_max_of_lt_left h0
  have hm1 : max ε ε' ≤ 1 := max_le h1 h1'
  set m := max ε ε' with hmdef
  have e1 : m ^ θ ≤ m ^ min θ θ' := Real.rpow_le_rpow_of_exponent_ge hm0 hm1 (min_le_left _ _)
  have e2 : m ^ θ' ≤ m ^ min θ θ' := Real.rpow_le_rpow_of_exponent_ge hm0 hm1 (min_le_right _ _)
  have a1 : ε ^ θ' ≤ m ^ θ' := Real.rpow_le_rpow h0.le (le_max_left _ _) hθ'.le
  have a2 : ε' ^ θ' ≤ m ^ θ' := Real.rpow_le_rpow h0'.le (le_max_right _ _) hθ'.le
  have hd : ‖s ε - s ε'‖ ≤ 2 * C₀ * m ^ min θ θ' := by
    have h := norm_sub_le_norm_sub_add_norm_sub (s ε) L (s ε')
    rw [norm_sub_rev L (s ε')] at h
    have := add_le_add (hrate ε ⟨h0, h1⟩) (hrate ε' ⟨h0', h1'⟩)
    nlinarith [mul_le_mul_of_nonneg_left a1 hC₀, mul_le_mul_of_nonneg_left a2 hC₀,
      mul_le_mul_of_nonneg_left e2 hC₀]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add e1 hd) hC₁]

/-- **Dyadic almost-sure clause of the convergence of the G-models, from a power rate of the
shifts.** -/
theorem gModels_dyadic_of_shiftRate (hG1 : RenormalisedCanonicalModelStatement) (hG5 : KolmogorovModelNormStatement.{u, 0})
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
    (hrate : ∃ L : RegularityStructures.Phi43.RenormalisationConstants, ∃ C θ' : ℝ, 0 < θ' ∧
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        ‖RegularityStructures.Phi43.gModelsShift N ρ c ε - L‖ ≤ C * ε ^ θ')
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
      Statements.IsModeratePhi43Lift N κ (ξ ε ω) (RegularityStructures.Phi43.wickConstant ρ ε + c.1,
        RegularityStructures.Phi43.sunsetConstant ρ ε + c.2) (Z ε ω) (ψ ε ω))
    (T : ℝ) (hT : 1 ≤ T) :
    ∀ᵐ ω ∂P,
      (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
        Statements.phi43Dist κ η T (Z ((2⁻¹ : ℝ) ^ n) ω) (Z ((2⁻¹ : ℝ) ^ m) ω)
          (ψ ((2⁻¹ : ℝ) ^ n) ω) (ψ ((2⁻¹ : ℝ) ^ m) ω) ≤ ENNReal.ofReal δ) ∧
      ∃ B : ℝ, ∀ n : ℕ, Statements.phi43Size κ η T (Z ((2⁻¹ : ℝ) ^ n) ω) (ψ ((2⁻¹ : ℝ) ^ n) ω) ≤
        ENNReal.ofReal B := by
  obtain ⟨L, C₀, θ', hθ', hr⟩ := hrate
  obtain ⟨Bc, hBc, -, -, -⟩ := gModels_constants hG8 N hρ hρ c
  have hψ : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P, RegularityStructures.IsMassivePotential (ξ ε ω) (ψ ε ω) :=
    fun ε hε => (hlift ε hε).mono fun ω hω => hω.2.2
  obtain ⟨θ₁, C₁, hθ₁, hC₁, hA, hE⟩ := gModels_bphzCauchy_moments hG1 hG5 hG7 hin κ hκE N hN ρ ρ hρ hρ c
    hBc hBc (Statements.phi43Box (T + 1)) (isCompact_phi43Box _) P W hW ξ ξ hξ hξ Z Z ψ ψ hlift hlift
  obtain ⟨θ₂, C₂, hθ₂, hC₂, hN7, hNd⟩ := gModels_noiseCauchy_moments hG7 η hη.2 ρ ρ hρ hρ T hT P W hW ξ ξ
    hξ hξ ψ ψ hψ hψ
  have hMB := momentBound_of_shiftRate (hθ' := hθ') (hC₁ := hC₁) hr hE
  have hC₀ : 0 ≤ C₀ := by
    have := hr 1 ⟨one_pos, le_rfl⟩
    rw [Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hCm : 0 ≤ C₁ * (1 + 2 * C₀) := by positivity
  have hDm := hMB.add hNd hCm hC₂
  have hSm := hA.add hN7 hC₁ hC₂
  refine RegularityStructures.ae_dyadic_of_momentBound (P := P)
    (D := fun ε ε' ω => (Z ε ω).diffNormOn (Z ε' ω) (RegularityStructures.Phi43.gamma κ)
      (Statements.phi43Box (T + 1)) + Statements.phi43NoiseDist η T (ψ ε ω) (ψ ε' ω))
    (S := fun ε ω => (Z ε ω).normOn (RegularityStructures.Phi43.gamma κ) (Statements.phi43Box (T + 1)) +
      Statements.phi43NoiseSize η T (ψ ε ω))
    (lt_min (lt_min hθ₁ hθ') hθ₂) (add_nonneg hCm hC₂) hDm hSm
    (Filter.Eventually.of_forall fun ω n m => by
      rw [Model.diffNormOn_comm, phi43NoiseDist_comm])
    (Filter.Eventually.of_forall fun ω n => by
      simp [Model.diffNormOn_self, phi43NoiseDist_self])
    (Filter.Eventually.of_forall fun ω n k m => by
      refine (add_le_add Model.diffNormOn_triangle (phi43NoiseDist_triangle η T _ (ψ _ ω) _)).trans
        (le_of_eq (add_add_add_comm _ _ _ _)))
    (Filter.Eventually.of_forall fun ω n => by
      refine (add_le_add Model.normOn_le_add_diffNormOn (phi43NoiseSize_le_add_dist η T _ _)).trans
        (le_of_eq (add_add_add_comm _ _ _ _)))

end RegularityStructures.Phi43

end
