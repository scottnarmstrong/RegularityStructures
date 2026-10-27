/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43Statements.Defs.IsGlobalPhi43Flow
public import RegularityStructures.Probability.WhiteNoiseExists
public import Phi43.RegularisedNoise.SmoothVersion.ExistsUnique
public import Phi43.ClassicalSolution.WellPosed
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Non-vacuity of the hypotheses of the global statements

The hypotheses of each statement of `GlobalPhi43Statements` are jointly satisfiable. This uses the
existence results of Theorem A's setting (white noise `exists_whiteNoise`, regularised noises
`regularisedNoise_exists_unique`, classical solutions `classicalSolution_exists_unique`) and a
normalised bump as mollifier.

* `globalDynamics_hypotheses`: a complete probability space with a white noise, and an admissible `η`. The
  white-noise space is completed (`isWhiteNoise_completion`).
* `regularisedBound_hypotheses`: in addition a mollifier, regularised noises for every
  `ε ∈ (0, 1]` and classical solutions from every smooth datum, and an admissible `η'`.
* `exponentCompatibility_hypotheses`: the compatibility statement assumes only a mass and an
  admissible noise space, as the global dynamics does; its exponent range contains pairs `η < η'' < -1/2`.

No `sorry`: every declaration here uses only the standard axioms.
-/

public section

open MeasureTheory Set
open RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.NonVacuity

/-- Completing a probability space keeps a white noise a white noise. -/
theorem isWhiteNoise_completion {α : Type*} [MeasurableSpace α] (P : Measure α)
    (W : (SpaceTime → ℝ) → α → ℝ) (hW : IsWhiteNoise P W) : IsWhiteNoise P.completion W := by
  refine ⟨fun h hh => (hW.1 h hh).nullMeasurable.measurable', fun n h hh => ?_⟩
  obtain ⟨-, hG, hm, hc⟩ := hW.2 n h hh
  let X : α → Fin n → ℝ := fun ω i => W (h i) ω
  have hX : Measurable X := measurable_pi_iff.2 fun i => hW.1 (h i) (hh i)
  let XQ : NullMeasurableSpace α P → Fin n → ℝ := X
  have hXQ : Measurable XQ := (hX.nullMeasurable (μ := P)).measurable'
  have hmap : P.completion.map XQ = P.map X := by
    ext A hA
    rw [Measure.map_apply hXQ hA, Measure.map_apply hX hA]
    rfl
  have hint : ∀ g : (Fin n → ℝ) → ℝ, Continuous g →
      ∫ ω, g (XQ ω) ∂P.completion = ∫ ω, g (X ω) ∂P := by
    intro g hg
    rw [← integral_map hXQ.aemeasurable hg.aestronglyMeasurable, hmap,
      integral_map hX.aemeasurable hg.aestronglyMeasurable]
  refine ⟨hXQ.aemeasurable, ?_, fun i => ?_, fun i j => ?_⟩
  · change ProbabilityTheory.IsGaussian (P.completion.map XQ)
    rw [hmap]
    exact hG
  · rw [← hm i]
    exact hint (fun v => v i) (continuous_apply i)
  · rw [← hc i j]
    exact hint (fun v => v i * v j) ((continuous_apply i).mul (continuous_apply j))

/-- A normalised smooth bump is a mollifier. -/
theorem exists_mollifier : ∃ ρ : ℝ × (Fin 3 → ℝ) → ℝ, IsMollifier ρ := by
  let f : ContDiffBump (0 : ℝ × (Fin 3 → ℝ)) := ⟨1, 2, by norm_num, by norm_num⟩
  exact ⟨f.normed volume, ⟨f.contDiff_normed, f.hasCompactSupport_normed, f.integral_normed⟩⟩

/-- An admissible exponent. -/
noncomputable def etaAdmissible : NegExponent := ⟨-(3 / 5), by norm_num⟩

theorem etaAdmissible_mem : (etaAdmissible : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)) := by
  simp only [etaAdmissible, mem_Ioo]
  norm_num

/-- **Global dynamics**: its hypotheses (a complete probability space carrying a space-time white noise,
an admissible exponent) are jointly satisfiable. -/
theorem globalDynamics_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ),
      IsProbabilityMeasure P ∧ P.IsComplete ∧ IsWhiteNoise P W ∧
      ∃ η : NegExponent, (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)) := by
  obtain ⟨Ω, _, P, W, hP, hW⟩ := exists_whiteNoise
  refine ⟨NullMeasurableSpace Ω P, inferInstance, P.completion, W,
    ⟨show P univ = 1 from measure_univ⟩, inferInstance,
    isWhiteNoise_completion P W hW, etaAdmissible, etaAdmissible_mem⟩

/-- **Uniform moment bound for the regularised equations**: its hypotheses are jointly satisfiable, on a complete probability space
with a white noise: a mollifier, regularised noises for every `ε ∈ (0, 1]`, classical solutions from
every smooth datum, and an admissible `η'`, for every mass `a`. -/
theorem regularisedBound_hypotheses (a : ℝ) :
    ∃ (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (_ : IsMollifier ρ) (η' : ℝ)
      (_ : η' ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
      (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ)
      (ξ : ℝ → Ω → SpaceTime → ℝ) (uε : ℝ → C(Torus3, ℝ) → Ω → ℝ → C(Torus3, ℝ)),
      IsProbabilityMeasure P ∧ P.IsComplete ∧ IsWhiteNoise P W ∧
      (∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)) ∧
      ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ x : C(Torus3, ℝ), IsSmoothOnTorus x → ∀ ω, IsClassicalSolution
        (a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε) (ξ ε ω) x (uε ε x ω) := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_mollifier
  obtain ⟨Ω₁, m₁, P₁, W, hP₁, hW₁⟩ := exists_whiteNoise
  let P : Measure (NullMeasurableSpace Ω₁ P₁) := P₁.completion
  have hP : IsProbabilityMeasure P := ⟨show P₁ univ = 1 from measure_univ⟩
  have hW : IsWhiteNoise P W := isWhiteNoise_completion P₁ W hW₁
  let ξ : ℝ → NullMeasurableSpace Ω₁ P₁ → SpaceTime → ℝ := fun ε =>
    if h : ε ∈ Ioc (0 : ℝ) 1 then (regularisedNoise_exists_unique P W hW ρ hρ h).1.choose
    else fun _ _ => 0
  have hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε) := fun ε hε => by
    simp only [ξ, hε, ↓reduceDIte]
    exact (regularisedNoise_exists_unique P W hW ρ hρ hε).1.choose_spec
  let c : ℝ → ℝ := fun ε => a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε
  let uε : ℝ → C(Torus3, ℝ) → NullMeasurableSpace Ω₁ P₁ → ℝ → C(Torus3, ℝ) := fun ε x ω =>
    if h : ε ∈ Ioc (0 : ℝ) 1 ∧ IsSmoothOnTorus x then
      (classicalSolution_exists_unique (c ε) ((hξ ε h.1).1 ω) h.2).1.choose
    else fun _ => x
  refine ⟨ρ, hρ, -(3 / 5), by norm_num, NullMeasurableSpace Ω₁ P₁, inferInstance, P, W, ξ, uε,
    hP, inferInstance, hW, hξ, fun ε hε x hx ω => ?_⟩
  have h : ε ∈ Ioc (0 : ℝ) 1 ∧ IsSmoothOnTorus x := ⟨hε, hx⟩
  simp only [uε, h, and_self, ↓reduceDIte]
  exact (classicalSolution_exists_unique (c ε) ((hξ ε h.1).1 ω) h.2).1.choose_spec

/-- **Compatibility across Hölder exponents**: its hypotheses are a mass and an admissible noise
space, as for the global dynamics,
and its exponent range contains pairs `η < η'' < -1/2`. All are jointly satisfiable. -/
theorem exponentCompatibility_hypotheses :
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ),
      IsProbabilityMeasure P ∧ P.IsComplete ∧ IsWhiteNoise P W) ∧
    ∃ η η'' : NegExponent, (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)) ∧ (η : ℝ) < η'' ∧
      (η'' : ℝ) < -(1 / 2 : ℝ) := by
  obtain ⟨Ω, m, P, W, hP, hc, hW, -⟩ := globalDynamics_hypotheses
  refine ⟨⟨Ω, m, P, W, hP, hc, hW⟩, etaAdmissible, ⟨-(11 / 20), by norm_num⟩, etaAdmissible_mem, ?_, ?_⟩ <;>
    simp only [etaAdmissible] <;> norm_num

end GlobalPhi43.NonVacuity

end
