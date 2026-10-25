/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaFullGrad
public import Phi43.BPHZ.GammaFullMinkowski
import Mathlib.Tactic

/-!
# Uniform `q`-th moments of `g_i` and `v₁`

For all `x, y` (no restriction on `s(y - x)`) and every `q ≥ 1`:

* `∫⁻ ‖g_i‖ₑ^q ≤ ofReal C ^ q` (`gammaGrad_lintegral_enorm_pow_le_uniform`);
* `∫⁻ ‖v₁(x; t, a)‖ₑ^q ≤ ofReal (C (1 + r))^q` whenever `|aᵢ| ≤ r`
  (`gammaPsiTaylor_lintegral_enorm_pow_le_uniform`), the growth being the linear Taylor term;

and for two regularised noises, with the extra factor `(ε ∨ ε')^θ`, `0 < θ ≤ 1/4`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Uniform `q`-th moment of `g_i`.** -/
theorem gammaGrad_lintegral_enorm_pow_le_uniform (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ (i : Fin 3) (x y : SpaceTime),
        ∫⁻ ω, ‖gammaGrad N ξ i x y ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal C ^ q := by
  obtain ⟨C₁, hC₁, h⟩ := gammaFull_grad_lintegral_le.{u} N hρ hq
  refine ⟨C₁ + C₁, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ i x y
  have := hW.isProbabilityMeasure
  have hm : ∀ z, Measurable fun ω => gammaFullGrad N ξ i z ω := fun z =>
    measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
      ((measurable_hairerKernelTorusGrad N i).comp (measurable_const.sub measurable_id))
  have e : ∀ ω, gammaGrad N ξ i x y ω = gammaFullGrad N ξ i y ω - gammaFullGrad N ξ i x ω :=
    fun ω => gammaGrad_eq_gammaFullGrad_sub (hξ.1 ω) i x y
  simp_rw [e]
  exact lintegral_enorm_pow_sub_le hq (hm y).aestronglyMeasurable (hm x).aestronglyMeasurable
    (h hW hε hξ i y) (h hW hε hξ i x) hC₁ hC₁

/-- **Uniform `q`-th moment of `v₁`**, with the linear growth of the Taylor term. -/
theorem gammaPsiTaylor_lintegral_enorm_pow_le_uniform (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ (x : SpaceTime) (t : ℝ) (a : Fin 3 → ℝ) (r : ℝ), 0 ≤ r → (∀ i, |a i| ≤ r) →
        ∫⁻ ω, ‖gammaPsiTaylor N ξ x t a ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (C * (1 + r)) ^ q := by
  obtain ⟨C₀, hC₀, h0⟩ := gammaFull_conv_lintegral_le.{u} N hρ hq
  obtain ⟨C₁, hC₁, h1⟩ := gammaFull_grad_lintegral_le.{u} N hρ hq
  refine ⟨2 * C₀ + 3 * C₁, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x t a r hr ha
  have := hW.isProbabilityMeasure
  have hm0 : ∀ z, Measurable fun ω => gammaFullConv N ξ z ω := fun z =>
    measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
      ((measurable_constantsComparison_hairerKernelTorus N).comp
        (measurable_const.sub measurable_id))
  have hm1 : ∀ i z, Measurable fun ω => gammaFullGrad N ξ i z ω := fun i z =>
    measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
      ((measurable_hairerKernelTorusGrad N i).comp (measurable_const.sub measurable_id))
  have e : ∀ ω, gammaPsiTaylor N ξ x t a ω = (gammaFullConv N ξ (x + (t, torusProj a)) ω -
      gammaFullConv N ξ x ω) - (a 0 * gammaFullGrad N ξ 0 x ω + a 1 * gammaFullGrad N ξ 1 x ω +
        a 2 * gammaFullGrad N ξ 2 x ω) := fun ω => by
    rw [gammaPsiTaylor_eq_gammaFullConv_sub (hξ.1 ω), Fin.sum_univ_three]
  have hg : ∀ i : Fin 3, ∫⁻ ω, ‖a i * gammaFullGrad N ξ i x ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (r * C₁) ^ q := fun i =>
    lintegral_enorm_pow_mono (lintegral_enorm_pow_const_mul_le (a i) (h1 hW hε hξ i x))
      (mul_le_mul_of_nonneg_right (ha i) hC₁)
  have hmg : ∀ i : Fin 3, Measurable fun ω => a i * gammaFullGrad N ξ i x ω := fun i =>
    (hm1 i x).const_mul _
  have hsum := lintegral_enorm_pow_add_le hq
    (((hmg 0).add (hmg 1)).aestronglyMeasurable) (hmg 2).aestronglyMeasurable
    (lintegral_enorm_pow_add_le hq (hmg 0).aestronglyMeasurable (hmg 1).aestronglyMeasurable
      (hg 0) (hg 1) (by positivity) (by positivity)) (hg 2) (by positivity) (by positivity)
  have hdiff := lintegral_enorm_pow_sub_le hq (hm0 (x + (t, torusProj a))).aestronglyMeasurable
    (hm0 x).aestronglyMeasurable (h0 hW hε hξ _) (h0 hW hε hξ x) hC₀ hC₀
  simp_rw [e]
  refine lintegral_enorm_pow_mono (lintegral_enorm_pow_sub_le hq
    (((hm0 _).sub (hm0 x)).aestronglyMeasurable)
    ((((hmg 0).add (hmg 1)).add (hmg 2)).aestronglyMeasurable) hdiff hsum (by positivity)
    (by positivity)) ?_
  nlinarith [mul_nonneg hr hC₁, mul_nonneg hr hC₀]

/-- **Uniform `q`-th moment of `g_i^ε - g_i^ε'`.** -/
theorem gammaGrad_sub_lintegral_enorm_pow_le_uniform (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ (i : Fin 3) (x y : SpaceTime),
        ∫⁻ ω, ‖gammaGrad N ξ i x y ω - gammaGrad N ξ' i x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ) ^ q := by
  obtain ⟨C₁, hC₁, h⟩ := gammaFull_grad_sub_lintegral_le.{u} N hρ hρ' hθ hθ1 hq
  refine ⟨C₁ + C₁, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' i x y
  have := hW.isProbabilityMeasure
  have hm : ∀ (ξ₀ : Ω → SpaceTime → ℝ), IsRegularisedNoise P W ρ ε ξ₀ ∨
      IsRegularisedNoise P W ρ' ε' ξ₀ → ∀ z, Measurable fun ω => gammaFullGrad N ξ₀ i z ω := by
    intro ξ₀ h z
    rcases h with h | h <;>
    exact measurable_integral_mul_field (measurable_hairerPsiField_uncurry N h)
      ((measurable_hairerKernelTorusGrad N i).comp (measurable_const.sub measurable_id))
  have e : ∀ ω, gammaGrad N ξ i x y ω - gammaGrad N ξ' i x y ω =
      ((gammaFullGrad N ξ i y ω - gammaFullGrad N ξ' i y ω) -
        (gammaFullGrad N ξ i x ω - gammaFullGrad N ξ' i x ω)) := fun ω => by
    rw [gammaGrad_eq_gammaFullGrad_sub (hξ.1 ω), gammaGrad_eq_gammaFullGrad_sub (hξ'.1 ω)]
    ring
  have hM : 0 ≤ C₁ * (max ε ε') ^ θ :=
    mul_nonneg hC₁ (Real.rpow_nonneg (le_max_of_le_left hε.1.le) _)
  simp_rw [e]
  have := lintegral_enorm_pow_sub_le (P := P)
    (f := fun ω => gammaFullGrad N ξ i y ω - gammaFullGrad N ξ' i y ω)
    (g := fun ω => gammaFullGrad N ξ i x ω - gammaFullGrad N ξ' i x ω) hq
    (((hm ξ (Or.inl hξ) y).sub (hm ξ' (Or.inr hξ') y)).aestronglyMeasurable)
    (((hm ξ (Or.inl hξ) x).sub (hm ξ' (Or.inr hξ') x)).aestronglyMeasurable)
    (h hW hε hε' hξ hξ' i y) (h hW hε hε' hξ hξ' i x) hM hM
  simpa only [← add_mul] using this

/-- **Uniform `q`-th moment of `v₁^ε - v₁^ε'`**, with the linear growth of the Taylor term. -/
theorem gammaPsiTaylor_sub_lintegral_enorm_pow_le_uniform (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ (x : SpaceTime) (t : ℝ) (a : Fin 3 → ℝ) (r : ℝ), 0 ≤ r → (∀ i, |a i| ≤ r) →
        ∫⁻ ω, ‖gammaPsiTaylor N ξ x t a ω - gammaPsiTaylor N ξ' x t a ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ * (1 + r)) ^ q := by
  obtain ⟨C₀, hC₀, h0⟩ := gammaFull_conv_sub_lintegral_le.{u} N hρ hρ' hθ hθ1 hq
  obtain ⟨C₁, hC₁, h1⟩ := gammaFull_grad_sub_lintegral_le.{u} N hρ hρ' hθ hθ1 hq
  refine ⟨2 * C₀ + 3 * C₁, by linarith, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x t a r hr ha
  have := hW.isProbabilityMeasure
  have hMx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hreg : ∀ ξ₀ : Ω → SpaceTime → ℝ, (IsRegularisedNoise P W ρ ε ξ₀ ∨
      IsRegularisedNoise P W ρ' ε' ξ₀) → Measurable fun q : Ω × SpaceTime =>
        hairerPsiField N ξ₀ q.1 q.2 := by
    intro ξ₀ h
    rcases h with h | h <;> exact measurable_hairerPsiField_uncurry N h
  have hm0 : ∀ ξ₀ : Ω → SpaceTime → ℝ, (IsRegularisedNoise P W ρ ε ξ₀ ∨
      IsRegularisedNoise P W ρ' ε' ξ₀) → ∀ z, Measurable fun ω => gammaFullConv N ξ₀ z ω :=
    fun ξ₀ h z => measurable_integral_mul_field (hreg ξ₀ h)
      ((measurable_constantsComparison_hairerKernelTorus N).comp
        (measurable_const.sub measurable_id))
  have hm1 : ∀ ξ₀ : Ω → SpaceTime → ℝ, (IsRegularisedNoise P W ρ ε ξ₀ ∨
      IsRegularisedNoise P W ρ' ε' ξ₀) → ∀ i z, Measurable fun ω => gammaFullGrad N ξ₀ i z ω :=
    fun ξ₀ h i z => measurable_integral_mul_field (hreg ξ₀ h)
      ((measurable_hairerKernelTorusGrad N i).comp (measurable_const.sub measurable_id))
  have hd0 : ∀ z, Measurable fun ω => gammaFullConv N ξ z ω - gammaFullConv N ξ' z ω :=
    fun z => (hm0 ξ (Or.inl hξ) z).sub (hm0 ξ' (Or.inr hξ') z)
  have hd1 : ∀ i z, Measurable fun ω => gammaFullGrad N ξ i z ω - gammaFullGrad N ξ' i z ω :=
    fun i z => (hm1 ξ (Or.inl hξ) i z).sub (hm1 ξ' (Or.inr hξ') i z)
  have e : ∀ ω, gammaPsiTaylor N ξ x t a ω - gammaPsiTaylor N ξ' x t a ω =
      ((gammaFullConv N ξ (x + (t, torusProj a)) ω - gammaFullConv N ξ' (x + (t, torusProj a)) ω) -
        (gammaFullConv N ξ x ω - gammaFullConv N ξ' x ω)) -
      (a 0 * (gammaFullGrad N ξ 0 x ω - gammaFullGrad N ξ' 0 x ω) +
        a 1 * (gammaFullGrad N ξ 1 x ω - gammaFullGrad N ξ' 1 x ω) +
        a 2 * (gammaFullGrad N ξ 2 x ω - gammaFullGrad N ξ' 2 x ω)) := fun ω => by
    rw [gammaPsiTaylor_eq_gammaFullConv_sub (hξ.1 ω), gammaPsiTaylor_eq_gammaFullConv_sub (hξ'.1 ω),
      Fin.sum_univ_three, Fin.sum_univ_three]
    ring
  have hg : ∀ i : Fin 3, ∫⁻ ω, ‖a i * (gammaFullGrad N ξ i x ω - gammaFullGrad N ξ' i x ω)‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (r * (C₁ * (max ε ε') ^ θ)) ^ q := fun i =>
    lintegral_enorm_pow_mono (lintegral_enorm_pow_const_mul_le (a i)
      (h1 hW hε hε' hξ hξ' i x)) (mul_le_mul_of_nonneg_right (ha i) (mul_nonneg hC₁ hMx))
  have hmg : ∀ i : Fin 3, Measurable fun ω =>
      a i * (gammaFullGrad N ξ i x ω - gammaFullGrad N ξ' i x ω) := fun i => (hd1 i x).const_mul _
  have hR : 0 ≤ r * (C₁ * (max ε ε') ^ θ) := mul_nonneg hr (mul_nonneg hC₁ hMx)
  have hsum := lintegral_enorm_pow_add_le hq
    (((hmg 0).add (hmg 1)).aestronglyMeasurable) (hmg 2).aestronglyMeasurable
    (lintegral_enorm_pow_add_le hq (hmg 0).aestronglyMeasurable (hmg 1).aestronglyMeasurable
      (hg 0) (hg 1) hR hR) (hg 2) (add_nonneg hR hR) hR
  have hdiff := lintegral_enorm_pow_sub_le hq (hd0 (x + (t, torusProj a))).aestronglyMeasurable
    (hd0 x).aestronglyMeasurable (h0 hW hε hε' hξ hξ' _) (h0 hW hε hε' hξ hξ' x)
    (mul_nonneg hC₀ hMx) (mul_nonneg hC₀ hMx)
  simp_rw [e]
  refine lintegral_enorm_pow_mono (lintegral_enorm_pow_sub_le hq
    ((hd0 _).sub (hd0 x)).aestronglyMeasurable
    ((((hmg 0).add (hmg 1)).add (hmg 2)).aestronglyMeasurable) hdiff hsum
    (add_nonneg (mul_nonneg hC₀ hMx) (mul_nonneg hC₀ hMx)) (add_nonneg (add_nonneg hR hR) hR)) ?_
  generalize (max ε ε') ^ θ = M at hMx ⊢
  nlinarith [mul_nonneg hC₀ hMx, mul_nonneg hC₁ hMx, mul_nonneg hr (mul_nonneg hC₁ hMx),
    mul_nonneg hr (mul_nonneg hC₀ hMx)]

end RegularityStructures.Phi43

end
