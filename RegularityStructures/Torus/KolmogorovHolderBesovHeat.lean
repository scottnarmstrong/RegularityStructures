/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernelIntegral
public import RegularityStructures.Torus.HeatKernelRegularity
public import RegularityStructures.Torus.HolderBesov
public import RegularityStructures.PDE.Semigroup
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Heat-kernel input for the Kolmogorov criterion

This file records the scale-uniform Gaussian estimate used by the spatial
Kolmogorov argument.  The periodisation and normalization are those of
`RegularityStructures.Torus.HeatKernelIntegral`; the resulting estimate is the
three-dimensional heat-kernel bound behind Hairer [Hai14, (2.1)--(2.3)].
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

def gaussianMajorantQuarter (n : ℤ) : ℝ :=
  gaussianOneDimMajorant (1 / 4 : ℝ) n

private theorem gaussianOneDimMajorant_mono_quarter {a : ℝ} (ha : (1 / 4 : ℝ) ≤ a)
    (n : ℤ) : gaussianOneDimMajorant a n ≤ gaussianMajorantQuarter n := by
  unfold gaussianMajorantQuarter gaussianOneDimMajorant
  by_cases hn : n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ)
  · simp only [hn, ↓reduceIte]
    have hexp : Real.exp (-(a / 4) * (n : ℝ) ^ 2) ≤
        Real.exp (-(1 / 4 / 4) * (n : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
      nlinarith
    simpa [add_comm] using add_le_add_left hexp 1
  · simp only [hn, ↓reduceIte, zero_add]
    apply Real.exp_le_exp.mpr
    have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
    nlinarith

private theorem summable_gaussian_vector_majorant_quarter :
    Summable (fun k : Fin 3 → ℤ => ∏ i, gaussianMajorantQuarter (k i)) := by
  exact summable_pi_fin3_prod
    (summable_gaussianOneDimMajorant (show (0 : ℝ) < 1 / 4 by norm_num))
    gaussianOneDimMajorant_nonneg

noncomputable def gaussianVectorMajorantConstant : ℝ :=
  ∑' k : Fin 3 → ℤ, ∏ i, gaussianMajorantQuarter (k i)

theorem gaussianVectorMajorantConstant_nonneg :
    0 ≤ gaussianVectorMajorantConstant := by
  unfold gaussianVectorMajorantConstant
  exact tsum_nonneg fun k => Finset.prod_nonneg fun i _ =>
    gaussianOneDimMajorant_nonneg (a := (1 / 4 : ℝ)) _

private theorem heatKernel_le_prefactor_mul_majorant {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (x : Torus3) :
    heatKernel t x ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
      gaussianVectorMajorantConstant := by
  have hta : (1 / 4 : ℝ) ≤ (4 * t)⁻¹ := by
    simpa [one_div] using
      (one_div_le_one_div_of_le (show (0 : ℝ) < 4 * t by positivity)
        (show 4 * t ≤ 4 by nlinarith))
  have hsum := summable_gaussian_vector_majorant ht
  have hsumq := summable_gaussian_vector_majorant_quarter
  refine (heatKernel_le_uniform_majorant ht x).trans ?_
  calc
    (∑' k : Fin 3 → ℤ,
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          ∏ i, gaussianOneDimMajorant ((4 * t)⁻¹) (k i)) ≤
        ∑' k : Fin 3 → ℤ,
          (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            ∏ i, gaussianMajorantQuarter (k i) := by
      refine hsum.tsum_le_tsum (fun k => ?_) (hsumq.mul_left _)
      have hk : ∀ i, gaussianOneDimMajorant ((4 * t)⁻¹) (k i) ≤
          gaussianMajorantQuarter (k i) := fun i =>
        gaussianOneDimMajorant_mono_quarter hta (k i)
      exact mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun i _ =>
          gaussianOneDimMajorant_nonneg (a := (4 * t)⁻¹) (k i))
          (fun i _ => hk i))
        (by positivity)
    _ = (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        gaussianVectorMajorantConstant := by
      exact hsumq.tsum_mul_left _

theorem heatKernel_le_scale_uniform {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (x : Torus3) :
    heatKernel t x ≤ (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
      gaussianVectorMajorantConstant * t ^ (-(3 : ℝ) / 2) := by
  have hC : 0 ≤ 4 * Real.pi := by positivity
  have htp : 0 ≤ t := ht.le
  have hfac : (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) =
      (4 * Real.pi) ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) := by
    rw [← Real.mul_rpow hC htp]
  calc
    heatKernel t x ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        gaussianVectorMajorantConstant := heatKernel_le_prefactor_mul_majorant ht ht1 x
    _ = (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
        gaussianVectorMajorantConstant * t ^ (-(3 : ℝ) / 2) := by
      rw [hfac]
      ring

theorem heatSemigroup_eq_torus_integral {s : ℝ} (hs : 0 < s)
    (f : C(Torus3, ℝ)) (x : Torus3) :
    heatSemigroup s f x = ∫ y : Torus3, heatKernel s y * f (x - y) := by
  let D : Set (Fin 3 → ℝ) := ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))
  let Doc : Set (Fin 3 → ℝ) :=
    {y | ∀ i : Fin 3, y i ∈ Set.Ioc (0 : ℝ) 1}
  have hDmeas : MeasurableSet D := by
    dsimp [D]
    rw [ZSpan.fundamentalDomain_pi_basisFun]
    exact (measurableSet_pi Set.countable_univ).2 <| Or.inl fun i _ => measurableSet_Ico
  have hDmem : ∀ y ∈ D, ∀ i, y i ∈ Set.Ico (0 : ℝ) 1 := by
    intro y hy i
    dsimp [D] at hy
    rw [ZSpan.fundamentalDomain_pi_basisFun] at hy
    exact (Set.mem_pi.mp hy) i (Set.mem_univ i)
  have hset : D =ᵐ[volume] Doc := by
    dsimp [D, Doc]
    filter_upwards [fundamentalDomain_ae_eq_pi_Ioc] with y hy
    simpa only [Set.mem_pi, Set.mem_univ, true_implies] using hy
  let F : (Fin 3 → ℝ) → ℝ := fun y =>
    gaussKernel s y * f (x - torusProj y)
  have hF : Integrable F := by
    dsimp [F]
    exact (integrable_gaussKernel hs).mul_bdd
      ((f.continuous.comp (continuous_const.sub
        (continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
          (continuous_apply i)))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => f.norm_coe_le_norm _)
  have hpart := (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 3)) volume).integral_eq_tsum'' F hF
  have hheat : ∀ y ∈ D,
      heatKernel s (torusProj y) =
        ∑' k : Fin 3 → ℤ, gaussKernel s (y + fun i => (k i : ℝ)) := by
    intro y hy
    rw [heatKernel, torusRep_torusProj_of_mem_Ico (hDmem y hy)]
  have hmeas : ∀ k : Fin 3 → ℤ,
      AEStronglyMeasurable (fun y : Fin 3 → ℝ =>
        F ((fun i => (k i : ℝ)) + y))
        (volume.restrict D) := by
    intro k
    have htorus : Continuous torusProj := by
      unfold torusProj
      fun_prop
    have hshift : Continuous (fun y : Fin 3 → ℝ => (fun i => (k i : ℝ)) + y) :=
      continuous_const.add continuous_id
    have hcont : Continuous (fun y : Fin 3 → ℝ =>
        F ((fun i => (k i : ℝ)) + y)) := by
      dsimp [F]
      exact (continuous_gaussKernel_fixed hs).comp hshift |>.mul <|
        f.continuous.comp (continuous_const.sub (htorus.comp hshift))
    exact hcont.aestronglyMeasurable.restrict
  have hgauss : ∑' k : Fin 3 → ℤ,
      ∫⁻ y : Fin 3 → ℝ in D,
        ‖gaussKernel s (y + fun i => (k i : ℝ))‖ₑ = 1 := by
    have hmeas' : ∀ k : Fin 3 → ℤ,
        AEMeasurable (fun y : Fin 3 → ℝ =>
          ENNReal.ofReal (gaussKernel s (y + fun i => (k i : ℝ))))
          (volume.restrict D) := by
      intro k
      exact (((continuous_gaussKernel_fixed hs).measurable.comp
        (measurable_id.add measurable_const)).ennreal_ofReal.aemeasurable.restrict)
    have hsum : (∑' k : Fin 3 → ℤ,
        ∫⁻ y : Fin 3 → ℝ in D,
          ENNReal.ofReal (gaussKernel s (y + fun i => (k i : ℝ)))) =
        ∫⁻ y : Fin 3 → ℝ in D,
          ∑' k : Fin 3 → ℤ, ENNReal.ofReal
            (gaussKernel s (y + fun i => (k i : ℝ))) := by
      rw [← lintegral_tsum hmeas']
    calc
      (∑' k : Fin 3 → ℤ,
          ∫⁻ y : Fin 3 → ℝ in D,
            ‖gaussKernel s (y + fun i => (k i : ℝ))‖ₑ) =
          ∑' k : Fin 3 → ℤ,
            ∫⁻ y : Fin 3 → ℝ in D,
              ENNReal.ofReal (gaussKernel s (y + fun i => (k i : ℝ))) := by
        apply tsum_congr
        intro k
        apply lintegral_congr_ae
        filter_upwards [] with y
        calc
          ‖gaussKernel s (y + fun i => (k i : ℝ))‖ₑ =
              ENNReal.ofReal ‖gaussKernel s (y + fun i => (k i : ℝ))‖ :=
            (ofReal_norm _).symm
          _ = ENNReal.ofReal (gaussKernel s (y + fun i => (k i : ℝ))) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (gaussKernel_nonneg hs _)]
      _ = ∫⁻ y : Fin 3 → ℝ in D,
          ∑' k : Fin 3 → ℤ, ENNReal.ofReal
            (gaussKernel s (y + fun i => (k i : ℝ))) := hsum
      _ = ∫⁻ y : Fin 3 → ℝ in D,
          ENNReal.ofReal (heatKernel s (torusProj y)) := by
        apply setLIntegral_congr_fun hDmeas
        intro y hy
        change (∑' k : Fin 3 → ℤ, ENNReal.ofReal
            (gaussKernel s (y + fun i => (k i : ℝ)))) =
          ENNReal.ofReal (heatKernel s (torusProj y))
        calc
          (∑' k : Fin 3 → ℤ, ENNReal.ofReal
              (gaussKernel s (y + fun i => (k i : ℝ)))) =
              ENNReal.ofReal (∑' k : Fin 3 → ℤ,
                gaussKernel s (y + fun i => (k i : ℝ))) :=
            (ENNReal.ofReal_tsum_of_nonneg
              (fun k => gaussKernel_nonneg hs _)
              (summable_gaussKernel_shift hs y (hDmem y hy))).symm
          _ = ENNReal.ofReal (heatKernel s (torusProj y)) := by rw [hheat y hy]
      _ = 1 := by
        have hrestrict : volume.restrict D = volume.restrict Doc :=
          Measure.restrict_congr_set hset
        change (∫⁻ y : Fin 3 → ℝ,
          ENNReal.ofReal (heatKernel s (torusProj y)) ∂volume.restrict D) = 1
        rw [hrestrict]
        rw [show (fun y : Fin 3 → ℝ =>
            ENNReal.ofReal (heatKernel s (torusProj y))) =
            (fun y : Fin 3 → ℝ =>
              ENNReal.ofReal (heatKernel s (fun i => (y i : UnitAddCircle)))) by
          rfl]
        rw [lintegral_heatKernel_preimage_eq_gauss hs]
        calc
          (∫⁻ y : Fin 3 → ℝ, ENNReal.ofReal (gaussKernel s y)) =
              ENNReal.ofReal (∫ y : Fin 3 → ℝ, gaussKernel s y) :=
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
              (integrable_gaussKernel hs)
              (Filter.Eventually.of_forall (fun y => gaussKernel_nonneg hs y))).symm
          _ = 1 := by rw [integral_gaussKernel hs]; simp
  have hnormsum : ∑' k : Fin 3 → ℤ,
      ∫⁻ y : Fin 3 → ℝ in D, ‖F (y + fun i => (k i : ℝ))‖ₑ ≠ ∞ := by
    have hle : ∑' k : Fin 3 → ℤ,
        ∫⁻ y : Fin 3 → ℝ in D, ‖F (y + fun i => (k i : ℝ))‖ₑ ≤
        ‖f‖ₑ * (∑' k : Fin 3 → ℤ,
          ∫⁻ y : Fin 3 → ℝ in D,
            ‖gaussKernel s (y + fun i => (k i : ℝ))‖ₑ) := by
      calc
        (∑' k : Fin 3 → ℤ,
            ∫⁻ y : Fin 3 → ℝ in D, ‖F (y + fun i => (k i : ℝ))‖ₑ) ≤
            ∑' k : Fin 3 → ℤ, ‖f‖ₑ *
              ∫⁻ y : Fin 3 → ℝ in D,
                ‖gaussKernel s (y + fun i => (k i : ℝ))‖ₑ := by
          refine ENNReal.tsum_le_tsum
            (f := fun k : Fin 3 → ℤ => ∫⁻ y : Fin 3 → ℝ in D,
              ‖F (y + fun i => (k i : ℝ))‖ₑ)
            (g := fun k : Fin 3 → ℤ => ‖f‖ₑ *
              ∫⁻ y : Fin 3 → ℝ in D,
                ‖gaussKernel s (y + fun i => (k i : ℝ))‖ₑ) (fun k => ?_)
          calc
            (∫⁻ y : Fin 3 → ℝ in D, ‖F (y + fun i => (k i : ℝ))‖ₑ) ≤
                ∫⁻ y : Fin 3 → ℝ in D,
                  ‖f‖ₑ * ‖gaussKernel s (y + fun i => (k i : ℝ))‖ₑ := by
              apply lintegral_mono
              intro y
              dsimp [F]
              rw [enorm_mul]
              calc
                ‖gaussKernel s (y + fun i => (k i : ℝ))‖ₑ *
                    ‖f (x - torusProj (y + fun i => (k i : ℝ)))‖ₑ ≤
                    ‖gaussKernel s (y + fun i => (k i : ℝ))‖ₑ * ‖f‖ₑ :=
                  mul_le_mul_of_nonneg_left
                    (enorm_le_iff_norm_le.2 (f.norm_coe_le_norm _)) (by positivity)
                _ = ‖f‖ₑ * ‖gaussKernel s (y + fun i => (k i : ℝ))‖ₑ := by ring
            _ = ‖f‖ₑ * ∫⁻ y : Fin 3 → ℝ in D,
                ‖gaussKernel s (y + fun i => (k i : ℝ))‖ₑ := by
              exact MeasureTheory.lintegral_const_mul' ‖f‖ₑ _ ENNReal.coe_ne_top
        _ = ‖f‖ₑ * (∑' k : Fin 3 → ℤ,
            ∫⁻ y : Fin 3 → ℝ in D,
              ‖gaussKernel s (y + fun i => (k i : ℝ))‖ₑ) := by
          rw [ENNReal.tsum_mul_left]
    have hle' : ∑' k : Fin 3 → ℤ,
        ∫⁻ y : Fin 3 → ℝ in D, ‖F (y + fun i => (k i : ℝ))‖ₑ ≤ ‖f‖ₑ := by
      simpa [hgauss] using hle
    exact ne_of_lt (hle'.trans_lt ENNReal.coe_lt_top)
  calc
    heatSemigroup s f x = ∫ y : Fin 3 → ℝ, F y := rfl
    _ = ∑' k : (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup,
        ∫ y : Fin 3 → ℝ in D, F (k + y) := hpart
    _ = ∑' k : Fin 3 → ℤ,
        ∫ y : Fin 3 → ℝ in D, F ((fun i => (k i : ℝ)) + y) := by
      rw [← integerLatticeAddEquiv.tsum_eq]
      apply tsum_congr
      intro k
      congr 2
      funext y
      have harg : (integerLatticeAddEquiv k : Fin 3 → ℝ) + y =
          (fun i => (k i : ℝ)) + y := by
        funext i
        simp [integerLatticeAddEquiv_apply]
      rw [harg]
    _ = ∫ y : Fin 3 → ℝ in D,
        ∑' k : Fin 3 → ℤ, F ((fun i => (k i : ℝ)) + y) := by
      have hnormsum' : ∑' k : Fin 3 → ℤ,
          ∫⁻ y : Fin 3 → ℝ in D, ‖F ((fun i => (k i : ℝ)) + y)‖ₑ ≠ ∞ := by
        simpa [add_comm] using hnormsum
      exact (integral_tsum hmeas hnormsum').symm
    _ = ∫ y : Fin 3 → ℝ in D,
        heatKernel s (torusProj y) * f (x - torusProj y) := by
      apply setIntegral_congr_fun hDmeas
      intro y hy
      dsimp [F]
      have htorus_add : ∀ k : Fin 3 → ℤ,
          torusProj ((fun i => (k i : ℝ)) + y) = torusProj y := by
        intro k
        ext i
        dsimp [torusProj]
        have hk : ((k i : ℝ) : UnitAddCircle) = 0 := by
          apply (QuotientAddGroup.eq_zero_iff _).2
          exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k i, by norm_num⟩
        rw [hk, zero_add]
      have hfun : (fun k : Fin 3 → ℤ =>
          gaussKernel s ((fun i => (k i : ℝ)) + y) *
            f (x - torusProj ((fun i => (k i : ℝ)) + y))) =
          (fun k : Fin 3 → ℤ => gaussKernel s ((fun i => (k i : ℝ)) + y) *
            (f (x - torusProj y))) := by
        funext k
        rw [htorus_add k]
      rw [hfun, tsum_mul_right]
      have hsum : (∑' k : Fin 3 → ℤ,
          gaussKernel s ((fun i => (k i : ℝ)) + y)) =
          heatKernel s (torusProj y) := by
        calc
          (∑' k : Fin 3 → ℤ,
              gaussKernel s ((fun i => (k i : ℝ)) + y)) =
              ∑' k : Fin 3 → ℤ,
                gaussKernel s (y + fun i => (k i : ℝ)) := by
                  apply tsum_congr
                  intro k
                  simp [add_comm]
          _ = heatKernel s (torusProj y) := (hheat y hy).symm
      rw [hsum]
    _ = ∫ y : Torus3, heatKernel s y * f (x - y) := by
      have hrestrict : volume.restrict D = volume.restrict Doc :=
        Measure.restrict_congr_set hset
      symm
      calc
        (∫ y : Torus3, heatKernel s y * f (x - y)) =
            ∫ y : Fin 3 → ℝ in Doc,
              heatKernel s (torusProj y) * f (x - torusProj y) := by
          have hcircle : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
            rw [AddCircle.volume_eq_smul_haarAddCircle]
            simp
          have htorus : (volume : Measure Torus3) =
              Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle) := by
            symm
            apply Measure.pi_eq
            intro s hs
            change (Measure.pi (fun _ : Fin 3 => (volume : Measure UnitAddCircle)))
                (Set.univ.pi s) = _
            rw [Measure.pi_pi]
            exact congrArg (fun m : Measure UnitAddCircle => ∏ i : Fin 3, m (s i)) hcircle
          rw [htorus]
          change (∫ y : UnitAddTorus (Fin 3), heatKernel s y * f (x - y)
              ∂Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle)) =
            ∫ y : Fin 3 → ℝ in {y | ∀ i, y i ∈ Set.Ioc (0 : ℝ) 1},
              heatKernel s (fun i => ((y i : ℝ) : UnitAddCircle)) *
                f (x - fun i => ((y i : ℝ) : UnitAddCircle))
          simpa only [MeasureSpace.volume, instMeasureSpaceUnitAddCircle,
            AddCircle.measureSpace, zero_add] using
            (UnitAddTorus.integral_preimage
              (fun y : Torus3 => heatKernel s y * f (x - y))
              (fun _ : Fin 3 => (0 : ℝ)))
        _ = ∫ y : Fin 3 → ℝ in D,
              heatKernel s (torusProj y) * f (x - torusProj y) := by
          rw [← hrestrict]

end RegularityStructures

end
