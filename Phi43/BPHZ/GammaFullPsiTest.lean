/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaFullKernelLint
public import Phi43.BPHZ.GammaMomentGradDiffLq
public import Phi43.BPHZ.GammaMomentGradLq
import Mathlib.Tactic

/-!
# Uniform second moments of a single translated kernel test of `Ψ`

For a measurable kernel `K` supported in `|t| ≤ 1` with `|K| ≤ B s⁻ᵃ` and the Gaussian field
`Ψ = hairerPsiField N ξ`, the second moment of the test `∫ K(z - w) Ψ(w) dw` is at most `C B²`
uniformly in `z`, `ε ∈ (0, 1]` and the probability space (`gammaFull_psiTest_second_le`), and the
test of `Ψ^ε - Ψ^ε'` has second moment at most `C B² (ε ∨ ε')^(2θ)`
(`gammaFull_psiTest_sub_second_le`).  The covariance of `Ψ` is bounded by `s⁻¹`, and the time
support makes the exponent `1` (resp. `1 + 2θ`) admissible by `gammaFull_lintBound_kernel_shift_sq_of_le`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem gfp_flip_le {Rr : SpaceTime → ℝ} {C e : ℝ} (he : 0 ≤ e) (hC : 0 ≤ C)
    (h : ∀ x, 0 < torusParabolicSize x → |Rr x| ≤ C * torusParabolicSize x ^ (-e))
    {u v : SpaceTime} (hv : 0 < torusParabolicSize (v - u)) :
    |Rr (u - v)| ≤ (C * 2 ^ e) * torusParabolicSize (v - u) ^ (-e) := by
  have hpos : 0 < torusParabolicSize (u - v) := torusParabolicSize_pos_of_sub_pos hv
  have h1 := h (u - v) hpos
  have hn : -(u - v) = v - u := neg_sub u v
  have h2 := torusParabolicSize_rpow_neg_le_flip he (u := u - v) (by rw [hn]; exact hv)
  rw [hn] at h2
  calc |Rr (u - v)| ≤ C * torusParabolicSize (u - v) ^ (-e) := h1
    _ ≤ C * (2 ^ e * torusParabolicSize (v - u) ^ (-e)) := mul_le_mul_of_nonneg_left h2 hC
    _ = _ := by ring

/-- **Uniform second moment of a single kernel test of `Ψ`.** -/
theorem gammaFull_psiTest_second_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {a p : ℝ} (ha : 0 < a) (ha5 : a < 5) (hp5 : p < 5) (hap : 5 < a + p)
    (h2a : 2 * a + p < 10) (hp1 : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {K : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable K →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u → |K u| ≤ B * torusParabolicSize u ^ (-a)) →
      (∀ z : SpaceTime, Integrable fun w => K (z - w)) → ∀ z : SpaceTime,
      ∫ ω, (∫ w, K (z - w) * hairerPsiField N ξ ω w) ^ 2 ∂P ≤ C * B ^ 2 := by
  obtain ⟨CL, hCL, hL⟩ := gammaFull_lintBound_kernel_shift_sq_of_le (p₀ := 1) ha ha5 hp5 hap h2a
    one_pos hp1
  obtain ⟨BQ, hBQ, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  refine ⟨2 * BQ * CL, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ K B hB hKm hKs hKb hKi z
  have := hW.isProbabilityMeasure
  have hcov := hairerPsiField_integral_mul N hρ hε.1 hW hξ
  have hf : Measurable fun w : SpaceTime => K (z - w) :=
    hKm.comp (measurable_const.sub measurable_id)
  have key := gammaMoment_second_le_of_lintBound (P := P) (Y := hairerPsiField N ξ)
    (measurable_hairerPsiField_uncurry N hξ)
    (fun u => hairerPsiField_memLp N hρ hε.1 hW hξ u) (M₀ := hairerCovariance N ρ ε 0)
    (fun u => by rw [hcov u u, sub_self])
    (R := hairerCovariance N ρ ε) hcov (p := 1) (A := 2 * BQ) (by positivity)
    (fun u v h => by
      have := abs_cov_flip_le hBQ (hQ hε.1 hε.2) h
      exact this)
    hf (hKi z) (M := CL * B ^ 2) (by positivity) (hL hB hKm hKs hKb z)
  have e : ∀ ω, |∫ w, hairerPsiField N ξ ω w * K (z - w)| ^ 2 =
      (∫ w, K (z - w) * hairerPsiField N ξ ω w) ^ 2 := fun ω => by
    simp only [sq_abs, mul_comm]
  simp only [e] at key
  refine key.trans (le_of_eq ?_)
  ring

/-- **Uniform two-scale second moment of a single kernel test of `Ψ`.** -/
theorem gammaFull_psiTest_sub_second_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ a p : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (ha : 0 < a) (ha5 : a < 5) (hp5 : p < 5) (hap : 5 < a + p) (h2a : 2 * a + p < 10)
    (hp1 : 1 + 2 * θ ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {K : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable K →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u → |K u| ≤ B * torusParabolicSize u ^ (-a)) →
      (∀ z : SpaceTime, Integrable fun w => K (z - w)) → ∀ z : SpaceTime,
      ∫ ω, ((∫ w, K (z - w) * hairerPsiField N ξ ω w) -
        ∫ w, K (z - w) * hairerPsiField N ξ' ω w) ^ 2 ∂P ≤ C * B ^ 2 * (max ε ε') ^ (2 * θ) := by
  obtain ⟨CL, hCL, hL⟩ := gammaFull_lintBound_kernel_shift_sq_of_le (p₀ := 1 + 2 * θ) ha ha5 hp5
    hap h2a (by linarith) hp1
  obtain ⟨CQ, hCQ, hQ⟩ := hairerKernelDiffCovarianceTwo_abs_le N ρ ρ' hρ hρ' hθ hθ1
  have he : (0 : ℝ) ≤ 1 + 2 * θ := by linarith
  have h2e : (0 : ℝ) ≤ 2 ^ (1 + 2 * θ) := Real.rpow_nonneg (by norm_num) _
  refine ⟨CQ * 2 ^ (1 + 2 * θ) * CL, mul_nonneg (mul_nonneg hCQ h2e) hCL, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' K B hB hKm hKs hKb hKi z
  have := hW.isProbabilityMeasure
  have hMx : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hcov := hairerPsiField_sub_integral_mulTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ'
  have hf : Measurable fun w : SpaceTime => K (z - w) :=
    hKm.comp (measurable_const.sub measurable_id)
  have hcont : ∀ (ξ₀ : Ω → SpaceTime → ℝ), IsRegularisedNoise P W ρ ε ξ₀ ∨
      IsRegularisedNoise P W ρ' ε' ξ₀ → ∀ ω, Continuous (hairerPsiField N ξ₀ ω) := by
    intro ξ₀ h ω
    rcases h with h | h <;> exact continuous_hairerPsiField N h.1 ω
  have key := gammaMoment_second_le_of_lintBound (P := P)
    (Y := fun ω u => hairerPsiField N ξ ω u - hairerPsiField N ξ' ω u)
    ((measurable_hairerPsiField_uncurry N hξ).sub (measurable_hairerPsiField_uncurry N hξ'))
    (fun u => (hairerPsiField_memLp N hρ hε.1 hW hξ u).sub
      (hairerPsiField_memLp N hρ' hε'.1 hW hξ' u))
    (M₀ := hairerKernelDiffCovarianceTwo N ρ ε ρ' ε' 0)
    (fun u => by rw [hcov u u, sub_self]) (R := hairerKernelDiffCovarianceTwo N ρ ε ρ' ε') hcov
    (p := 1 + 2 * θ) (A := CQ * (max ε ε') ^ (2 * θ) * 2 ^ (1 + 2 * θ))
    (mul_nonneg (mul_nonneg hCQ hMx) h2e)
    (fun u v hv => gfp_flip_le (Rr := hairerKernelDiffCovarianceTwo N ρ ε ρ' ε')
      (C := CQ * (max ε ε') ^ (2 * θ)) he (mul_nonneg hCQ hMx) (fun z hz => by
        have h0 := hQ hε.1 hε.2 hε'.1 hε'.2 z hz
        rw [show -1 - 2 * θ = -(1 + 2 * θ) by ring] at h0
        exact h0) hv)
    hf (hKi z) (M := CL * B ^ 2) (by positivity) (hL hB hKm hKs hKb z)
  have hI : ∀ ξ₀ : Ω → SpaceTime → ℝ, (IsRegularisedNoise P W ρ ε ξ₀ ∨
      IsRegularisedNoise P W ρ' ε' ξ₀) → ∀ ω, Integrable (fun w => K (z - w) *
        hairerPsiField N ξ₀ ω w) := by
    intro ξ₀ h ω
    obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := z.1 - 1) (b := z.1 + 1)).prod
      (isCompact_univ (X := Torus3)) |>.exists_bound_of_continuousOn
        (hcont ξ₀ h ω).continuousOn
    refine ((hKi z).abs.mul_const C0).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · exact (hf.mul (hcont ξ₀ h ω).measurable).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      by_cases hw : 1 < |(z - w).1|
      · rw [hKs _ hw]
        simp
      · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hmem : w ∈ Set.Icc (z.1 - 1) (z.1 + 1) ×ˢ (Set.univ : Set Torus3) := by
          refine ⟨?_, Set.mem_univ _⟩
          have h2 := abs_le.1 (not_lt.1 hw)
          simp only [Set.mem_Icc, Prod.fst_sub] at h2 ⊢
          constructor <;> linarith [h2.1, h2.2]
        simpa using hC0 _ hmem
  have e : ∀ ω, |∫ w, (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) * K (z - w)| ^ 2 =
      ((∫ w, K (z - w) * hairerPsiField N ξ ω w) -
        ∫ w, K (z - w) * hairerPsiField N ξ' ω w) ^ 2 := fun ω => by
    have hint : ∫ w, (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) * K (z - w) =
        (∫ w, K (z - w) * hairerPsiField N ξ ω w) -
          ∫ w, K (z - w) * hairerPsiField N ξ' ω w := by
      rw [← integral_sub (hI ξ (Or.inl hξ) ω) (hI ξ' (Or.inr hξ') ω)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only
      ring
    rw [sq_abs, hint]
  simp only [e] at key
  refine key.trans (le_of_eq ?_)
  ring

end RegularityStructures.Phi43

end
