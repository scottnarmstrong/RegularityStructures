/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiXiSmearUnfolded
public import Phi43.BPHZ.SemigroupTestAllMoments
public import Phi43.Stochastic.WhiteNoiseL2
public import Phi43.BPHZ.NoiseTreeFubini
public import Phi43.RegularisedNoise.Properties

/-!
# Second moment of the tested difference of two regularised noises (semigroup test)

For regularised noises `ξ` (mollifier `ρ`, scale `ε`), `ξ'` (mollifier `ρ'`, scale `ε'`) of the same
white noise, `θ ≥ 0` with `2θ ≤ 1`, `t ∈ (0, 1]`, `lam = t^(1/4)` and every `x`,

`E|∫ (ξ - ξ') q^♯_t(x, ·)|² ≤ C (max ε ε')^(2θ) lam^(-(5 + 2θ))`

(`regularisedNoise_sub_semigroupPeriodised_second_moment_le`).  The tested difference is the first
chaos variable `W (ψ ⋆ ρ_ε^♯ - ψ ⋆ ρ'_ε'^♯)`; its second moment is at most
`2 ‖ψ ⋆ ρ_ε^♯ - ψ‖² + 2 ‖ψ ⋆ ρ'_ε'^♯ - ψ‖²`, bounded by `noiseSmearedTest_semigroupPeriodised_sub_sq_integral_le`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem integrable_mul_periodise_comp {K ψ : SpaceTime → ℝ} {B : ℝ} (hψm : Measurable ψ)
    (hψ1 : Integrable ψ) (hK : Measurable K) (hKb : ∀ z, |K z| ≤ B) (u : SpaceTime) :
    Integrable (fun w => ψ w * K (w - u)) := by
  refine (hψ1.abs.mul_const B).mono'
    (hψm.mul (hK.comp (measurable_id.sub_const u))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hKb _) (abs_nonneg _)

/-- **Second moment of the tested difference of two regularised noises, semigroup test.** -/
theorem regularisedNoise_sub_semigroupPeriodised_second_moment_le {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : 2 * θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, (ξ ω w - ξ' ω w) * semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (-(5 + 2 * θ)) := by
  have ha0 : 0 ≤ 2 * θ := by linarith
  obtain ⟨C0, hC0, h0⟩ := noiseSmearedTest_semigroupPeriodised_sub_sq_integral_le hρ ha0 hθ1
  obtain ⟨C1, hC1, h1⟩ := noiseSmearedTest_semigroupPeriodised_sub_sq_integral_le hρ' ha0 hθ1
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  refine ⟨2 * (C0 + C1), by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' t ht ht1 x
  have := hW.isProbabilityMeasure
  set ψ := semigroupPeriodised t x with hψ
  have h := hB ht ht1 x
  have hψm : Measurable ψ := h.measurable
  have hψ1 : Integrable ψ := h.integrable
  have hψ2i : Integrable (fun w => ψ w ^ 2) := integrable_semigroupPeriodised_sq ht ht1 x
  have hψ2 : MemLp ψ 2 := (memLp_two_iff_integrable_sq hψm.aestronglyMeasurable).2 hψ2i
  obtain ⟨B1, hB1⟩ := bounded_periodise ρ hρ hε.1
  obtain ⟨B2, hB2⟩ := bounded_periodise ρ' hρ' hε'.1
  set K : SpaceTime → ℝ := fun z => periodise ρ ε z - periodise ρ' ε' z with hK
  have hKm : Measurable K := (measurable_periodise ρ hρ).sub (measurable_periodise ρ' hρ')
  have hKi : Integrable K :=
    (integrable_periodise ρ hρ hε.1).sub (integrable_periodise ρ' hρ' hε'.1)
  have hKb : ∀ z, |K z| ≤ B1 + B2 := fun z => (abs_sub _ _).trans (add_le_add (hB1 z) (hB2 z))
  have hΞ : Measurable fun q : Ω × SpaceTime => ξ q.1 q.2 - ξ' q.1 q.2 :=
    (regularisedNoise_measurable_uncurry P W ρ ε ξ hξ).sub
      (regularisedNoise_measurable_uncurry P W ρ' ε' ξ' hξ')
  have hΞW : ∀ w, (fun ω => ξ ω w - ξ' ω w) =ᵐ[P] W (fun u => K (w - u)) := by
    intro w
    filter_upwards [(hξ.2 w).2, (hξ'.2 w).2, whiteNoise_pairing_sub_ae hW
      (memLp_mollifierAt ρ hρ hε.1 w) (memLp_mollifierAt ρ' hρ' hε'.1 w)] with ω h1 h2 h3
    show ξ ω w - ξ' ω w = W (fun u => K (w - u)) ω
    rw [h1, h2, h3]
    rfl
  obtain ⟨hg, hae⟩ := noise_pairing_ae_eq_whiteNoise_of_jointVersion hW hKm hKi hKb hψm hψ1 hψ2
    hΞ hΞW
  have hgeq : ∀ u, ∫ w, ψ w * K (w - u) =
      noiseSmearedTest ρ ε ψ u - noiseSmearedTest ρ' ε' ψ u := by
    intro u
    unfold noiseSmearedTest
    rw [← integral_sub
      (integrable_mul_periodise_comp hψm hψ1 (measurable_periodise ρ hρ) hB1 u)
      (integrable_mul_periodise_comp hψm hψ1 (measurable_periodise ρ' hρ') hB2 u)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hK]
    ring
  obtain ⟨hS0, -⟩ := noiseSmearedTest_sq_integral_le hρ hε hψm hψ2
  obtain ⟨hS1, -⟩ := noiseSmearedTest_sq_integral_le hρ' hε' hψm hψ2
  have hd0 : Integrable (fun u => (noiseSmearedTest ρ ε ψ u - ψ u) ^ 2) :=
    (hS0.sub hψ2).integrable_sq
  have hd1 : Integrable (fun u => (noiseSmearedTest ρ' ε' ψ u - ψ u) ^ 2) :=
    (hS1.sub hψ2).integrable_sq
  have hg2 : ∫ ω, |∫ w, (ξ ω w - ξ' ω w) * ψ w| ^ 2 ∂P = ∫ u, (∫ w, ψ w * K (w - u)) ^ 2 := by
    rw [← whiteNoise_pairing_abs_sq_integral hW hg]
    · refine integral_congr_ae ?_
      filter_upwards [hae] with ω hω
      have : ∫ w, (ξ ω w - ξ' ω w) * ψ w = ∫ w, ψ w * (ξ ω w - ξ' ω w) :=
        integral_congr_ae (Filter.Eventually.of_forall fun w => mul_comm _ _)
      rw [this, hω]
  have hmax0 : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hlam : 0 ≤ (t ^ (1 / 4 : ℝ)) ^ (-(5 + 2 * θ)) :=
    Real.rpow_nonneg (Real.rpow_nonneg ht.le _) _
  have hεm : ε ^ (2 * θ) ≤ (max ε ε') ^ (2 * θ) :=
    Real.rpow_le_rpow hε.1.le (le_max_left _ _) ha0
  have hε'm : ε' ^ (2 * θ) ≤ (max ε ε') ^ (2 * θ) :=
    Real.rpow_le_rpow hε'.1.le (le_max_right _ _) ha0
  have e0 := h0 ε hε ht ht1 x
  have e1 := h1 ε' hε' ht ht1 x
  rw [hg2]
  calc ∫ u, (∫ w, ψ w * K (w - u)) ^ 2
      = ∫ u, (noiseSmearedTest ρ ε ψ u - noiseSmearedTest ρ' ε' ψ u) ^ 2 := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        dsimp only
        rw [hgeq u]
    _ ≤ ∫ u, (2 * (noiseSmearedTest ρ ε ψ u - ψ u) ^ 2 +
          2 * (noiseSmearedTest ρ' ε' ψ u - ψ u) ^ 2) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _)
          ((hd0.const_mul 2).add (hd1.const_mul 2)) (Filter.Eventually.of_forall fun u => ?_)
        nlinarith [sq_nonneg (noiseSmearedTest ρ ε ψ u + noiseSmearedTest ρ' ε' ψ u - 2 * ψ u)]
    _ = 2 * (∫ u, (noiseSmearedTest ρ ε ψ u - ψ u) ^ 2) +
          2 * (∫ u, (noiseSmearedTest ρ' ε' ψ u - ψ u) ^ 2) := by
        rw [integral_add (hd0.const_mul 2) (hd1.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 * (C0 * ε ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (-(5 + 2 * θ))) +
          2 * (C1 * ε' ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (-(5 + 2 * θ))) :=
        add_le_add (mul_le_mul_of_nonneg_left e0 two_pos.le)
          (mul_le_mul_of_nonneg_left e1 two_pos.le)
    _ ≤ 2 * (C0 * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (-(5 + 2 * θ))) +
          2 * (C1 * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (-(5 + 2 * θ))) := by
        have a0 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεm hC0) hlam
        have a1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε'm hC1) hlam
        linarith
    _ = _ := by ring

end RegularityStructures.Phi43

end
