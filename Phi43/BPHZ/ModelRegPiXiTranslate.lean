/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestSup
public import RegularityStructures.Abstract.QFamilyR4KernelIncrement
public import Phi43.BPHZ.CanonicalBridgeConvolution

/-!
# `L¹` translation modulus of the periodised semigroup kernel

For `t ∈ (0, 1]`, `lam = t^(1/4)`, `x ∈ ℝ⁴` and a translation `y ∈ ℝ⁴` with `‖y‖ ≤ lam`,

`∫_{ℝ × T³} |q^♯_t(x, u + proj y) - q^♯_t(x, u)| du ≤ K (lam⁻¹ ‖y‖)`

(`exists_integral_abs_semigroupPeriodised_add_sub_le`). The proof writes the increment of the
periodised kernel as the periodisation of the increment `Q_t(x, · + y) - Q_t(x, ·)` on `ℝ⁴`, unfolds
the torus integral and applies the weighted `L¹` increment bound for the parabolic kernel.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

private theorem eq_torusRep_torusProj_add_floor (a : Fin 3 → ℝ) :
    a = torusRep (torusProj a) + fun i => ((⌊a i⌋ : ℤ) : ℝ) := by
  funext i
  change a i = ((AddCircle.equivIco (1 : ℝ) 0 ((a i : ℝ) : UnitAddCircle) : ℝ)) + (⌊a i⌋ : ℤ)
  rw [AddCircle.coe_equivIco_mk_apply]
  simp only [div_one, mul_one]
  exact (Int.fract_add_floor _).symm

/-- The periodised kernel at a translated point is the periodisation of the translated kernel. -/
theorem semigroupPeriodised_add_spaceTimeProj (t : ℝ) (x y : ParabolicSpace) (u : SpaceTime) :
    semigroupPeriodised t x (u + Phi43.spaceTimeProj y) =
      ∑' k : Fin 3 → ℤ, parabolicSemigroup.kernel t x
        (u.1 + y.1, torusRep u.2 + y.2 + fun i => (k i : ℝ)) := by
  set a : Fin 3 → ℝ := torusRep u.2 + y.2 with ha
  have hproj : torusProj a = u.2 + torusProj y.2 := by
    rw [ha, PDE.torusProj_add, PDE.torusProj_torusRep]
  have hrep : torusRep (u.2 + torusProj y.2) = a + fun i => ((-⌊a i⌋ : ℤ) : ℝ) := by
    rw [← hproj]
    have h := eq_torusRep_torusProj_add_floor a
    funext i
    have := congrFun h i
    simp only [Pi.add_apply, Int.cast_neg] at this ⊢
    linarith
  unfold semigroupPeriodised
  have hterm : ∀ k : Fin 3 → ℤ, parabolicSemigroup.kernel t x
      ((u + Phi43.spaceTimeProj y).1, torusRep (u + Phi43.spaceTimeProj y).2 + fun i => (k i : ℝ)) =
      parabolicSemigroup.kernel t x
        (u.1 + y.1, a + fun i => (((k + fun i => -⌊a i⌋) i : ℤ) : ℝ)) := by
    intro k
    congr 1
    refine Prod.ext rfl ?_
    show torusRep (u.2 + torusProj y.2) + _ = _
    rw [hrep]
    funext i
    simp only [Pi.add_apply, Int.cast_add, Int.cast_neg]
    ring
  rw [tsum_congr hterm]
  exact (Equiv.addRight (fun i => -⌊a i⌋ : Fin 3 → ℤ)).tsum_eq
    (fun k : Fin 3 → ℤ => parabolicSemigroup.kernel t x
      (u.1 + y.1, a + fun i => (k i : ℝ)))

/-- The lattice sum of the semigroup kernel over a coset is absolutely summable. -/
theorem summable_abs_parabolicSemigroup_kernel_lattice {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (x : ParabolicSpace) (s : ℝ) (b : Fin 3 → ℝ) :
    Summable (fun k : Fin 3 → ℤ =>
      |parabolicSemigroup.kernel t x (s, b + fun i => (k i : ℝ))|) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_parabolicKernel_le_decay
  obtain ⟨L, hL0, hL⟩ := exists_lattice_sum_le
  set a : Fin 3 → ℝ := fun i => x.2 i - b i with ha
  set P : (Fin 3 → ℤ) → ℝ := fun k => ∏ i, ((1 + |a i + (k i : ℝ)|) ^ 2)⁻¹ with hP
  have hterm : ∀ k : Fin 3 → ℤ,
      |parabolicSemigroup.kernel t x (s, b + fun i => (k i : ℝ))| ≤
        C * t ^ (-(5 / 4 : ℝ)) * P (-k) := by
    intro k
    rw [parabolicSemigroup_kernel_eq]
    refine (hC ht ht1 _).trans (le_of_eq ?_)
    simp only [hP, ha, Prod.snd_sub, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Int.cast_neg]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show x.2 i - (b i + (k i : ℝ)) = x.2 i - b i + -(k i : ℝ) by ring]
  have hPs : Summable (fun k => P (-k)) :=
    ((Equiv.neg (Fin 3 → ℤ)).summable_iff (f := P)).2 (hL a).1
  exact Summable.of_nonneg_of_le (fun k => abs_nonneg _) hterm (hPs.mul_left _)

theorem summable_parabolicSemigroup_kernel_lattice {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (x : ParabolicSpace) (s : ℝ) (b : Fin 3 → ℝ) :
    Summable (fun k : Fin 3 → ℤ => parabolicSemigroup.kernel t x (s, b + fun i => (k i : ℝ))) :=
  Summable.of_norm (by simpa only [Real.norm_eq_abs] using
    summable_abs_parabolicSemigroup_kernel_lattice ht ht1 x s b)

local instance : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]
  have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
  infer_instance

local instance : (volume : Measure ParabolicSpace).IsNegInvariant := by
  rw [Measure.volume_eq_prod]
  have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
  have : (volume.prod volume : Measure ParabolicSpace).Regular := inferInstance
  infer_instance

private theorem integrable_kernel_translate_sub {t : ℝ} (ht : 0 < t) (x y : ParabolicSpace) :
    Integrable (fun w : ParabolicSpace => parabolicSemigroup.kernel t x (w + y) -
      parabolicSemigroup.kernel t x w) := by
  have h := integrable_parabolicKernel ht
  have h1 : Integrable (fun w : ParabolicSpace => parabolicKernel t (x - y - w)) :=
    h.comp_sub_left (x - y)
  have h2 : Integrable (fun w : ParabolicSpace => parabolicKernel t (x - w)) :=
    h.comp_sub_left x
  refine (h1.sub h2).congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [parabolicSemigroup_kernel_eq, Pi.sub_apply]
  rw [show x - (w + y) = x - y - w by abel]

private theorem integral_abs_kernel_translate_sub {t : ℝ} (x y : ParabolicSpace) :
    ∫ w : ParabolicSpace, |parabolicSemigroup.kernel t x (w + y) -
        parabolicSemigroup.kernel t x w| =
      ∫ z : ParabolicSpace, |parabolicKernel t (z + y) - parabolicKernel t z| := by
  have h := integral_sub_left_eq_self (μ := (volume : Measure ParabolicSpace))
    (fun z : ParabolicSpace => |parabolicKernel t z - parabolicKernel t (z + y)|) (x - y)
  have e1 : ∫ w : ParabolicSpace, |parabolicSemigroup.kernel t x (w + y) -
        parabolicSemigroup.kernel t x w| =
      ∫ w : ParabolicSpace, |parabolicKernel t (x - y - w) -
        parabolicKernel t (x - y - w + y)| := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [parabolicSemigroup_kernel_eq]
    rw [show x - (w + y) = x - y - w by abel, show x - y - w + y = x - w by abel]
  rw [e1, h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact abs_sub_comm _ _

/-- **`L¹` translation modulus of the periodised semigroup kernel.**  For `‖y‖ ≤ lam`,
`∫ |q^♯_t(x, u + proj y) - q^♯_t(x, u)| du ≤ K lam⁻¹ ‖y‖`. -/
theorem exists_integral_abs_semigroupPeriodised_add_sub_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ (x y : ParabolicSpace),
      parabolicNorm y ≤ t ^ (1 / 4 : ℝ) →
      ∫ u : SpaceTime, |semigroupPeriodised t x (u + Phi43.spaceTimeProj y) -
          semigroupPeriodised t x u| ≤ K * (t ^ (-(1 / 4 : ℝ)) * parabolicNorm y) := by
  obtain ⟨K, hK0, hK⟩ := exists_integral_abs_parabolicKernel_add_sub_le (r := 0) le_rfl
  refine ⟨K, hK0, fun {t} ht ht1 x y hy => ?_⟩
  set H : ParabolicSpace → ℝ := fun w => parabolicSemigroup.kernel t x (w + y) -
    parabolicSemigroup.kernel t x w with hH
  have hHm : Measurable H :=
    ((measurable_parabolicSemigroup_kernel t x).comp (measurable_id.add_const y)).sub
      (measurable_parabolicSemigroup_kernel t x)
  have hΔ : ∀ u : SpaceTime, semigroupPeriodised t x (u + Phi43.spaceTimeProj y) -
      semigroupPeriodised t x u = ∑' k : Fin 3 → ℤ,
        H (u.1, torusRep u.2 + fun i => (k i : ℝ)) := by
    intro u
    rw [semigroupPeriodised_add_spaceTimeProj]
    unfold semigroupPeriodised
    rw [← Summable.tsum_sub
      (summable_parabolicSemigroup_kernel_lattice ht ht1 x (u.1 + y.1) (torusRep u.2 + y.2))
      (summable_parabolicSemigroup_kernel_lattice ht ht1 x u.1 (torusRep u.2))]
    refine tsum_congr fun k => ?_
    have e : ((u.1, torusRep u.2 + fun i => (k i : ℝ)) + y : ParabolicSpace) =
        (u.1 + y.1, torusRep u.2 + y.2 + fun i => (k i : ℝ)) :=
      Prod.ext rfl (add_right_comm _ _ _)
    simp only [hH, e]
  have hmeas : AEStronglyMeasurable (fun u : SpaceTime =>
      |semigroupPeriodised t x (u + Phi43.spaceTimeProj y) - semigroupPeriodised t x u|) volume :=
    (((measurable_semigroupPeriodised t x).comp (measurable_id.add_const _)).sub
      (measurable_semigroupPeriodised t x)).norm.aestronglyMeasurable
  have hlint : ∫⁻ u : SpaceTime, ENNReal.ofReal |semigroupPeriodised t x (u + Phi43.spaceTimeProj y) -
      semigroupPeriodised t x u| ≤ ENNReal.ofReal (∫ w : ParabolicSpace, |H w|) := by
    calc ∫⁻ u : SpaceTime, ENNReal.ofReal |semigroupPeriodised t x (u + Phi43.spaceTimeProj y) -
          semigroupPeriodised t x u|
        = ∫⁻ u : SpaceTime, ‖∑' k : Fin 3 → ℤ, H (u.1, torusRep u.2 + fun i => (k i : ℝ))‖ₑ := by
          refine lintegral_congr fun u => ?_
          rw [hΔ u, Real.enorm_eq_ofReal_abs]
      _ ≤ ∫⁻ u : SpaceTime, ∑' k : Fin 3 → ℤ, ‖H (u.1, torusRep u.2 + fun i => (k i : ℝ))‖ₑ :=
          lintegral_mono fun u => enorm_tsum_le_tsum_enorm
      _ = ∫⁻ w : ParabolicSpace, ‖H w‖ₑ :=
          (Phi43.lintegral_eq_lintegral_spaceTime_tsum hHm.enorm).symm
      _ = ENNReal.ofReal (∫ w : ParabolicSpace, |H w|) := by
          rw [ofReal_integral_eq_lintegral_ofReal (integrable_kernel_translate_sub ht x y).abs
            (Filter.Eventually.of_forall fun w => abs_nonneg _)]
          refine lintegral_congr fun w => ?_
          rw [Real.enorm_eq_ofReal_abs]
  have hB : ∫ w : ParabolicSpace, |H w| ≤ K * (t ^ (-(1 / 4 : ℝ)) * parabolicNorm y) := by
    have := hK ht y hy
    simp only [Real.rpow_zero, mul_one, zero_div, Real.rpow_zero] at this
    rw [show ∫ w : ParabolicSpace, |H w| = ∫ z : ParabolicSpace,
        |parabolicKernel t (z + y) - parabolicKernel t z| from
      integral_abs_kernel_translate_sub x y]
    exact this
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => abs_nonneg _) hmeas]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint).trans ?_
  rw [ENNReal.toReal_ofReal (integral_nonneg fun w => abs_nonneg _)]
  exact hB

end RegularityStructures

end
