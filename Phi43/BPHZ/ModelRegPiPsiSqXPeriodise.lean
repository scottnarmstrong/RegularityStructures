/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiPsiSqXMoment
public import Phi43.BPHZ.ModelRegPiTreesHint

/-!
# Periodisation of the coordinate-weighted kernel, and almost sure integrability

* `integral_mul_comp_proj_eq_periodised`: for a measurable `κ̃ : ℝ⁴ → ℝ` and measurable `G` on
  `ℝ × T³` with `κ̃ (G ∘ proj)` integrable,
  `∫_{ℝ⁴} κ̃(y) G(proj y) dy = ∫_{ℝ × T³} (∑_k κ̃(u₀, torusRep u' + k)) G(u) du`
  (general form of `integral_semigroup_kernel_mul_comp_proj`).
* `integral_semigroup_kernel_coord_mul_comp_proj`: the case `κ̃(y) = Q_t(x, y) (yᵢ - xᵢ)`, whose
  periodisation is `semigroupPeriodisedX`.
* `kernel_coord_mul_field_integrable_ae_of_sq_bound`: almost sure integrability on `ℝ⁴` of
  `Q_t(x, y) (yᵢ - xᵢ) F(proj y)` for a random field with a uniform second moment bound.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

/-- **Periodisation of a measurable kernel against a lifted function.** -/
theorem integral_mul_comp_proj_eq_periodised {κ : ParabolicSpace → ℝ} (hκ : Measurable κ)
    {G : SpaceTime → ℝ} (hG : Measurable G)
    (hint : Integrable (fun y : ParabolicSpace => κ y * G (Phi43.spaceTimeProj y))) :
    Integrable (fun u : SpaceTime =>
      (∑' k : Fin 3 → ℤ, κ (u.1, torusRep u.2 + fun i => (k i : ℝ))) * G u) ∧
      ∫ y : ParabolicSpace, κ y * G (Phi43.spaceTimeProj y) =
        ∫ u : SpaceTime, (∑' k : Fin 3 → ℤ, κ (u.1, torusRep u.2 + fun i => (k i : ℝ))) * G u := by
  set H : ParabolicSpace → ℝ := fun y => κ y * G (Phi43.spaceTimeProj y) with hH
  have hHm : Measurable H := hκ.mul (hG.comp Phi43.continuous_spaceTimeProj.measurable)
  have hlift : ∀ q : SpaceTime, ∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ)) =
      (∑' k : Fin 3 → ℤ, κ (q.1, torusRep q.2 + fun i => (k i : ℝ))) * G q := by
    intro q
    rw [← tsum_mul_right]
    refine tsum_congr fun k => ?_
    simp only [hH, spaceTimeProj_semigroup_lift]
  have hHt : Measurable (fun q : SpaceTime =>
      ∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ))) :=
    Measurable.tsum fun k => hHm.comp
      (measurable_fst.prodMk ((measurable_torusRep.comp measurable_snd).add measurable_const))
  have hfin : ∫⁻ q : SpaceTime, ‖∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ))‖ₑ <
      ⊤ := by
    calc ∫⁻ q : SpaceTime, ‖∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ))‖ₑ
        ≤ ∫⁻ q : SpaceTime, ∑' k : Fin 3 → ℤ,
            ‖H (q.1, torusRep q.2 + fun i => (k i : ℝ))‖ₑ :=
          lintegral_mono fun q => enorm_tsum_le_tsum_enorm
      _ = ∫⁻ y : ParabolicSpace, ‖H y‖ₑ :=
          (Phi43.lintegral_eq_lintegral_spaceTime_tsum hHm.enorm).symm
      _ < ⊤ := hint.2
  have hIntT : Integrable (fun u : SpaceTime =>
      (∑' k : Fin 3 → ℤ, κ (u.1, torusRep u.2 + fun i => (k i : ℝ))) * G u) := by
    have h1 : Integrable (fun q : SpaceTime =>
        ∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ))) :=
      ⟨hHt.aestronglyMeasurable, hfin⟩
    exact h1.congr (Filter.Eventually.of_forall hlift)
  refine ⟨hIntT, ?_⟩
  have hint' : Integrable H (volume.prod volume : Measure (ℝ × (Fin 3 → ℝ))) := by
    rwa [← Measure.volume_eq_prod]
  have hIntT' : Integrable (fun q : SpaceTime =>
      (∑' k : Fin 3 → ℤ, κ (q.1, torusRep q.2 + fun i => (k i : ℝ))) * G q)
      (volume.prod volume : Measure (ℝ × Torus3)) := by
    rwa [← Measure.volume_eq_prod]
  rw [show (∫ y : ParabolicSpace, H y) = ∫ t' : ℝ, ∫ z : Fin 3 → ℝ, H (t', z) by
      rw [Measure.volume_eq_prod]; exact integral_prod _ hint',
    show (∫ u : SpaceTime, (∑' k : Fin 3 → ℤ, κ (u.1, torusRep u.2 + fun i => (k i : ℝ))) * G u) =
      ∫ t' : ℝ, ∫ u : Torus3,
        (∑' k : Fin 3 → ℤ, κ (t', torusRep u + fun i => (k i : ℝ))) * G (t', u) by
      rw [Measure.volume_eq_prod]; exact integral_prod _ hIntT']
  refine integral_congr_ae ?_
  filter_upwards [hint'.prod_right_ae] with t' ht'
  rw [Phi43.integral_eq_integral_torus_tsum (H := fun z => H (t', z)) ht']
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => hlift (t', u))

/-- **Periodisation of the coordinate-weighted semigroup test.** -/
theorem integral_semigroup_kernel_coord_mul_comp_proj (t : ℝ) (x : ParabolicSpace) (i : Fin 3)
    {G : SpaceTime → ℝ} (hG : Measurable G)
    (hint : Integrable (fun y : ParabolicSpace => parabolicSemigroup.kernel t x y *
      (G (Phi43.spaceTimeProj y) * (y.2 i - x.2 i)))) :
    Integrable (fun u : SpaceTime => semigroupPeriodisedX t x i u * G u) ∧
      ∫ y : ParabolicSpace, parabolicSemigroup.kernel t x y *
        (G (Phi43.spaceTimeProj y) * (y.2 i - x.2 i)) =
        ∫ u : SpaceTime, semigroupPeriodisedX t x i u * G u := by
  set κ : ParabolicSpace → ℝ := fun y => parabolicSemigroup.kernel t x y * (y.2 i - x.2 i)
    with hκ
  have hκm : Measurable κ :=
    (measurable_parabolicSemigroup_kernel t x).mul
      (((measurable_pi_apply i).comp measurable_snd).sub_const _)
  have e : ∀ y : ParabolicSpace, parabolicSemigroup.kernel t x y *
      (G (Phi43.spaceTimeProj y) * (y.2 i - x.2 i)) = κ y * G (Phi43.spaceTimeProj y) := by
    intro y
    simp only [hκ]
    ring
  simp only [e] at hint ⊢
  have := integral_mul_comp_proj_eq_periodised hκm hG hint
  exact this

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

theorem integrable_kernel_mul_coord {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) (i : Fin 3) :
    Integrable (fun y : ParabolicSpace => parabolicSemigroup.kernel t x y * (y.2 i - x.2 i)) := by
  have h := parabolicSemigroup.integrable_moment ht (r := 1) zero_le_one x
  refine h.mono' ((measurable_parabolicSemigroup_kernel t x).mul
    (((measurable_pi_apply i).comp measurable_snd).sub_const _)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hw : |y.2 i - x.2 i| ≤ parabolicNorm (y - x) := by
    have := RegularityStructures.abs_coord_le_parabolicNorm (y - x) i
    simpa using this
  show _ ≤ |parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ (1 : ℝ)
  rw [Real.rpow_one]
  exact mul_le_mul_of_nonneg_left hw (abs_nonneg _)

/-- **Almost sure integrability of the coordinate-weighted kernel times a field with a uniform
second moment bound.** -/
theorem kernel_coord_mul_field_integrable_ae_of_sq_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Ω → SpaceTime → ℝ}
    (hF : Measurable fun q : Ω × SpaceTime => F q.1 q.2)
    (hL2 : ∀ u, MemLp (fun ω => F ω u) 2 P) {V : ℝ} (hV : ∀ u, ∫ ω, F ω u ^ 2 ∂P ≤ V)
    {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) (i : Fin 3) :
    ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * (F ω (spaceTimeProj y) * (y.2 i - x.2 i))) := by
  have hK := integrable_kernel_mul_coord ht x i
  have hYj : AEStronglyMeasurable (Function.uncurry fun (ω : Ω) (y : ParabolicSpace) =>
      F ω (spaceTimeProj y)) (P.prod volume) :=
    (hF.comp (measurable_fst.prodMk
      (continuous_spaceTimeProj.measurable.comp measurable_snd))).aestronglyMeasurable
  have hYi : ∀ y : ParabolicSpace, Integrable (fun ω => F ω (spaceTimeProj y)) P :=
    fun y => (hL2 (spaceTimeProj y)).integrable one_le_two
  have hM : ∀ y : ParabolicSpace, ∫ ω, |F ω (spaceTimeProj y)| ∂P ≤ (V + 1) / 2 := by
    intro y
    have hsq : Integrable (fun ω => F ω (spaceTimeProj y) ^ 2) P :=
      (hL2 (spaceTimeProj y)).integrable_sq
    calc ∫ ω, |F ω (spaceTimeProj y)| ∂P
        ≤ ∫ ω, (F ω (spaceTimeProj y) ^ 2 + 1) / 2 ∂P := by
          refine integral_mono (hYi y).abs ((hsq.add (integrable_const 1)).div_const 2)
            fun ω => ?_
          nlinarith [sq_nonneg (|F ω (spaceTimeProj y)| - 1), sq_abs (F ω (spaceTimeProj y))]
      _ = (∫ ω, F ω (spaceTimeProj y) ^ 2 ∂P + 1) / 2 := by
          rw [integral_div, integral_add hsq (integrable_const 1)]
          simp
      _ ≤ (V + 1) / 2 := by linarith [hV (spaceTimeProj y)]
  have h := (integrable_uncurry_mul_of_bound hK hYj hYi hM).prod_right_ae
  filter_upwards [h] with ω hω
  refine hω.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.uncurry_apply_pair]
  ring

end RegularityStructures.Phi43

end
