/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentWick
public import Phi43.BPHZ.GammaMomentCrossCov
public import Phi43.BPHZ.SemigroupTestAllMomentsSetup
import Mathlib.Tactic

/-!
# Second moments of the two-scale differences of `v₂` and `v₃`

For regularised noises `ξ` (mollifier `ρ`, scale `ε`) and `ξ'` (mollifier `ρ'`, scale `ε'`) of the
same white noise, and `d = s(y - x) ≤ 1`:

* `gammaWickSq_sub_second_moment_le`: `E (v₂^ε - v₂^ε')² ≤ C (ε ∨ ε')^(2θ) d^(2 - 2θ - δ)`;
* `gammaWickCube_sub_second_moment_le`: `E (v₃^ε - v₃^ε')² ≤ C (ε ∨ ε')^(2θ) d^(1 - 2θ - δ)`.

This is the `(ε ∨ ε')^θ` gain of [Hai14, (10.3)] with the loss `d^(-θ)` of the degree.  The
proofs repeat those of `GammaMomentWick` with the covariances
`2 (a² - b² - c² + d²)` and `6 (a³ - b³ - c³ + d³)` of the differences of Wick powers.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The integrand `f * F` is integrable for an integrable `f` supported in a compact set and
continuous `F`. -/
theorem integrable_mul_of_compact_support {g F : SpaceTime → ℝ} (hg : Integrable g)
    {S : Set SpaceTime} (hS : IsCompact S) (hgS : ∀ w, g w ≠ 0 → w ∈ S) (hF : Continuous F) :
    Integrable (fun w => g w * F w) := by
  obtain ⟨c, hc⟩ := hS.exists_bound_of_continuousOn hF.continuousOn
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hb : Integrable (fun w => g w * S.indicator F w) := by
    refine hg.mul_bdd (c := max c 0) ((hF.measurable.indicator hSm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ S
    · rw [Set.indicator_of_mem hw]
      exact (hc w hw).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hw]
      simp
  refine hb.congr (Filter.Eventually.of_forall fun w => ?_)
  show g w * S.indicator F w = g w * F w
  by_cases hw : w ∈ S
  · rw [Set.indicator_of_mem hw]
  · have : g w = 0 := by
      by_contra h
      exact hw (hgS w h)
    simp [this]

private theorem rpow_mul_self_two {r γ : ℝ} (hr : 0 ≤ r) (hγ : 0 ≤ γ) :
    r ^ γ * r ^ γ = r ^ (2 * γ) := by
  rcases hγ.lt_or_eq with h | h
  · rw [← Real.rpow_add' hr (by linarith)]
    congr 1
    ring
  · subst h
    simp

/-- Flipping a bound of the form `|R x| ≤ C s(x)^(-e)`. -/
private theorem abs_flip_le {Rr : SpaceTime → ℝ} {C e : ℝ} (he : 0 ≤ e) (hC : 0 ≤ C)
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

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The kernel integral `v₂` is the integral of the product of the kernel and the Wick square. -/
theorem integrable_gammaWickSq_integrand {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ} (N : ℕ)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (x y : SpaceTime) (ω : Ω) :
    Integrable (fun w => hairerI2Psi2Kernel N x y w * hairerPsiWickSquare N ρ ε ξ ω w) := by
  obtain ⟨S, hSc, hS⟩ := hairerI2Psi2Kernel_slab_support N x y.1 0
  exact integrable_mul_of_compact_support (integrable_hairerI2Psi2Kernel N x y) hSc
    (fun w hw => hS y (by simp) w hw)
    (((continuous_hairerPsiField N hξ.1 ω).pow 2).sub continuous_const)

/-- The kernel integral `v₃` is the integral of the product of the kernel and the Wick cube. -/
theorem integrable_gammaWickCube_integrand {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ} (N : ℕ)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (x y : SpaceTime) (ω : Ω) :
    Integrable (fun w => hairerI2Psi2Kernel N x y w * hairerPsiWickCube N ρ ε ξ ω w) := by
  obtain ⟨S, hSc, hS⟩ := hairerI2Psi2Kernel_slab_support N x y.1 0
  exact integrable_mul_of_compact_support (integrable_hairerI2Psi2Kernel N x y) hSc
    (fun w hw => hS y (by simp) w hw)
    (((continuous_hairerPsiField N hξ.1 ω).pow 3).sub
      (continuous_const.mul (continuous_hairerPsiField N hξ.1 ω)))

/-- The difference of kernel integrals is the kernel integral of the difference. -/
private theorem gammaWickSq_sub_eq {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (x y : SpaceTime) (ω : Ω) :
    ∫ w, (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w) *
        hairerI2Psi2Kernel N x y w = gammaWickSq N ρ ε ξ x y ω - gammaWickSq N ρ' ε' ξ' x y ω := by
  unfold gammaWickSq
  rw [← integral_sub (integrable_gammaWickSq_integrand N hξ x y ω)
    (integrable_gammaWickSq_integrand N hξ' x y ω)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  ring

/-- The difference of kernel integrals is the kernel integral of the difference. -/
private theorem gammaWickCube_sub_eq {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (x y : SpaceTime) (ω : Ω) :
    ∫ w, (hairerPsiWickCube N ρ ε ξ ω w - hairerPsiWickCube N ρ' ε' ξ' ω w) *
        hairerI2Psi2Kernel N x y w = gammaWickCube N ρ ε ξ x y ω - gammaWickCube N ρ' ε' ξ' x y ω := by
  unfold gammaWickCube
  rw [← integral_sub (integrable_gammaWickCube_integrand N hξ x y ω)
    (integrable_gammaWickCube_integrand N hξ' x y ω)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  ring

/-- **Two-scale second moment of `v₂`.**  For `θ ∈ (0, 1]`, `δ > 0` with `2θ + δ ≤ 2`:
`E (v₂^ε - v₂^ε')² ≤ C (ε ∨ ε')^(2θ) s(y - x)^(2 - 2θ - δ)` for `s(y - x) ≤ 1`. -/
theorem gammaWickSq_sub_second_moment_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hδ : 0 < δ) (hθδ : 2 * θ + δ ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫ ω, (gammaWickSq N ρ ε ξ x y ω - gammaWickSq N ρ' ε' ξ' x y ω) ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * torusParabolicSize (y - x) ^ (2 - 2 * θ - δ) := by
  obtain ⟨BK, hBK, hK⟩ := i2Psi2KernelHyp_hairerKernelTorus N
  obtain ⟨CD, hCD, hD⟩ := i2Psi2LintBound_diag_sq (γ := 1 - θ - δ / 2) (γ' := 1 - θ - δ / 2)
    (e := 2 + 2 * θ) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)
  obtain ⟨CQ, hCQ, hQ⟩ := hairerCrossTwo_sq_sub_abs_le N ρ ρ' hρ hρ' hθ hθ1
  have he : (0 : ℝ) ≤ 2 + 2 * θ := by linarith
  have h2e : (0 : ℝ) ≤ 2 ^ (2 + 2 * θ) := Real.rpow_nonneg (by norm_num) _
  refine ⟨(2 * (CQ * 2 ^ (2 + 2 * θ))) * (CD * BK ^ 2), by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y hd
  have := hW.isProbabilityMeasure
  have hxy : |y.1 - x.1| ≤ 1 := gammaMoment_abs_time_le_one hd rfl
  have hMx : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hcov := hairerPsiWickSquare_sub_integral_mulTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ'
  have hlint := hD hK x y y hxy hxy
  have hγ0 : 0 ≤ 1 - θ - δ / 2 := by linarith
  have key := gammaMoment_second_le_of_lintBound (P := P)
    (Y := fun ω u => hairerPsiWickSquare N ρ ε ξ ω u - hairerPsiWickSquare N ρ' ε' ξ' ω u)
    ((measurable_hairerPsiWickSquare_uncurry N hξ).sub
      (measurable_hairerPsiWickSquare_uncurry N hξ'))
    (fun u => hairerPsiWickSquare_sub_memLpTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ' u)
    (M₀ := 2 * (hairerCrossCovarianceTwo N ρ ε ρ ε 0 ^ 2 - hairerCrossCovarianceTwo N ρ ε ρ' ε' 0 ^ 2 -
      hairerCrossCovarianceTwo N ρ' ε' ρ ε 0 ^ 2 + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' 0 ^ 2))
    (fun u => by rw [hcov u u, sub_self])
    (R := fun z => 2 * (hairerCrossCovarianceTwo N ρ ε ρ ε z ^ 2 - hairerCrossCovarianceTwo N ρ ε ρ' ε' z ^ 2 -
      hairerCrossCovarianceTwo N ρ' ε' ρ ε z ^ 2 + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z ^ 2)) hcov
    (p := 2 + 2 * θ) (A := 2 * (CQ * (max ε ε') ^ (2 * θ) * 2 ^ (2 + 2 * θ)))
    (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hCQ hMx) h2e))
    (fun u v hv => by
      have h := abs_flip_le (Rr := fun z => hairerCrossCovarianceTwo N ρ ε ρ ε z ^ 2 -
        hairerCrossCovarianceTwo N ρ ε ρ' ε' z ^ 2 - hairerCrossCovarianceTwo N ρ' ε' ρ ε z ^ 2 +
        hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z ^ 2) (C := CQ * (max ε ε') ^ (2 * θ)) he
        (mul_nonneg hCQ hMx) (fun z hz => by
          have h0 := hQ hε.1 hε.2 hε'.1 hε'.2 z hz
          rw [show -2 - 2 * θ = -(2 + 2 * θ) by ring] at h0
          exact h0) hv
      rw [abs_mul, abs_two]
      calc 2 * _ ≤ 2 * ((CQ * (max ε ε') ^ (2 * θ) * 2 ^ (2 + 2 * θ)) *
            torusParabolicSize (v - u) ^ (-(2 + 2 * θ))) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ = _ := by ring)
    (measurable_hairerI2Psi2Kernel N x y) (integrable_hairerI2Psi2Kernel N x y)
    (M := CD * BK ^ 2 * torusParabolicSize (y - x) ^ (1 - θ - δ / 2) *
      torusParabolicSize (y - x) ^ (1 - θ - δ / 2))
    (mul_nonneg (mul_nonneg (mul_nonneg hCD (sq_nonneg _)) (Real.rpow_nonneg
      (torusParabolicSize_nonneg _) _)) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)) hlint
  have e : ∀ ω, |∫ w, (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w) *
      hairerI2Psi2Kernel N x y w| ^ 2 =
      (gammaWickSq N ρ ε ξ x y ω - gammaWickSq N ρ' ε' ξ' x y ω) ^ 2 := fun ω => by
    rw [sq_abs, gammaWickSq_sub_eq N hξ hξ' x y ω]
  simp only [e] at key
  refine key.trans (le_of_eq ?_)
  have e1 : CD * BK ^ 2 * torusParabolicSize (y - x) ^ (1 - θ - δ / 2) *
      torusParabolicSize (y - x) ^ (1 - θ - δ / 2) =
      CD * BK ^ 2 * torusParabolicSize (y - x) ^ (2 - 2 * θ - δ) := by
    rw [mul_assoc (CD * BK ^ 2), rpow_mul_self_two (torusParabolicSize_nonneg _) hγ0]
    congr 2
    ring
  rw [e1]
  ring

/-- **Two-scale second moment of `v₃`.**  For `θ, δ > 0` with `2θ + δ ≤ 1`:
`E (v₃^ε - v₃^ε')² ≤ C (ε ∨ ε')^(2θ) s(y - x)^(1 - 2θ - δ)` for `s(y - x) ≤ 1`. -/
theorem gammaWickCube_sub_second_moment_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hθδ : 2 * θ + δ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫ ω, (gammaWickCube N ρ ε ξ x y ω - gammaWickCube N ρ' ε' ξ' x y ω) ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * torusParabolicSize (y - x) ^ (1 - 2 * θ - δ) := by
  obtain ⟨BK, hBK, hK⟩ := i2Psi2KernelHyp_hairerKernelTorus N
  obtain ⟨CD, hCD, hD⟩ := i2Psi2LintBound_diag_sq (γ := (1 - 2 * θ - δ) / 2)
    (γ' := (1 - 2 * θ - δ) / 2) (e := 3 + 2 * θ) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨CQ, hCQ, hQ⟩ := hairerCrossTwo_cube_sub_abs_le N ρ ρ' hρ hρ' hθ (θ := θ) (by linarith)
  have he : (0 : ℝ) ≤ 3 + 2 * θ := by linarith
  have h2e : (0 : ℝ) ≤ 2 ^ (3 + 2 * θ) := Real.rpow_nonneg (by norm_num) _
  refine ⟨(6 * (CQ * 2 ^ (3 + 2 * θ))) * (CD * BK ^ 2), by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y hd
  have := hW.isProbabilityMeasure
  have hxy : |y.1 - x.1| ≤ 1 := gammaMoment_abs_time_le_one hd rfl
  have hMx : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hcov := hairerPsiWickCube_sub_integral_mulTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ'
  have hlint := hD hK x y y hxy hxy
  have hγ0 : 0 ≤ (1 - 2 * θ - δ) / 2 := by linarith
  have key := gammaMoment_second_le_of_lintBound (P := P)
    (Y := fun ω u => hairerPsiWickCube N ρ ε ξ ω u - hairerPsiWickCube N ρ' ε' ξ' ω u)
    ((measurable_hairerPsiWickCube_uncurry N hξ).sub
      (measurable_hairerPsiWickCube_uncurry N hξ'))
    (fun u => hairerPsiWickCube_sub_memLpTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ' u)
    (M₀ := 6 * (hairerCrossCovarianceTwo N ρ ε ρ ε 0 ^ 3 - hairerCrossCovarianceTwo N ρ ε ρ' ε' 0 ^ 3 -
      hairerCrossCovarianceTwo N ρ' ε' ρ ε 0 ^ 3 + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' 0 ^ 3))
    (fun u => by rw [hcov u u, sub_self])
    (R := fun z => 6 * (hairerCrossCovarianceTwo N ρ ε ρ ε z ^ 3 - hairerCrossCovarianceTwo N ρ ε ρ' ε' z ^ 3 -
      hairerCrossCovarianceTwo N ρ' ε' ρ ε z ^ 3 + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z ^ 3)) hcov
    (p := 3 + 2 * θ) (A := 6 * (CQ * (max ε ε') ^ (2 * θ) * 2 ^ (3 + 2 * θ)))
    (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hCQ hMx) h2e))
    (fun u v hv => by
      have h := abs_flip_le (Rr := fun z => hairerCrossCovarianceTwo N ρ ε ρ ε z ^ 3 -
        hairerCrossCovarianceTwo N ρ ε ρ' ε' z ^ 3 - hairerCrossCovarianceTwo N ρ' ε' ρ ε z ^ 3 +
        hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z ^ 3) (C := CQ * (max ε ε') ^ (2 * θ)) he
        (mul_nonneg hCQ hMx) (fun z hz => by
          have h0 := hQ hε.1 hε.2 hε'.1 hε'.2 z hz
          rw [show -3 - 2 * θ = -(3 + 2 * θ) by ring] at h0
          exact h0) hv
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      calc 6 * _ ≤ 6 * ((CQ * (max ε ε') ^ (2 * θ) * 2 ^ (3 + 2 * θ)) *
            torusParabolicSize (v - u) ^ (-(3 + 2 * θ))) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ = _ := by ring)
    (measurable_hairerI2Psi2Kernel N x y) (integrable_hairerI2Psi2Kernel N x y)
    (M := CD * BK ^ 2 * torusParabolicSize (y - x) ^ ((1 - 2 * θ - δ) / 2) *
      torusParabolicSize (y - x) ^ ((1 - 2 * θ - δ) / 2))
    (mul_nonneg (mul_nonneg (mul_nonneg hCD (sq_nonneg _)) (Real.rpow_nonneg
      (torusParabolicSize_nonneg _) _)) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)) hlint
  have e : ∀ ω, |∫ w, (hairerPsiWickCube N ρ ε ξ ω w - hairerPsiWickCube N ρ' ε' ξ' ω w) *
      hairerI2Psi2Kernel N x y w| ^ 2 =
      (gammaWickCube N ρ ε ξ x y ω - gammaWickCube N ρ' ε' ξ' x y ω) ^ 2 := fun ω => by
    rw [sq_abs, gammaWickCube_sub_eq N hξ hξ' x y ω]
  simp only [e] at key
  refine key.trans (le_of_eq ?_)
  have e1 : CD * BK ^ 2 * torusParabolicSize (y - x) ^ ((1 - 2 * θ - δ) / 2) *
      torusParabolicSize (y - x) ^ ((1 - 2 * θ - δ) / 2) =
      CD * BK ^ 2 * torusParabolicSize (y - x) ^ (1 - 2 * θ - δ) := by
    rw [mul_assoc (CD * BK ^ 2), rpow_mul_self_two (torusParabolicSize_nonneg _) hγ0]
    congr 2
    ring
  rw [e1]
  ring

end RegularityStructures.Phi43

end
