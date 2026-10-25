/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsPeriodiseL1
public import Phi43.Stochastic.MollifierL1
public import Phi43.Constants.Finite
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Mass of a periodised parabolic mollifier

The spatial periodisation preserves the total mass.  This is the cancellation identity used when
comparing two regularisation scales after convolving a singular covariance kernel.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

private theorem integrable_rescale_slice
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ}
    (hε : 0 < ε) (t : ℝ) :
    Integrable (fun y : Fin 3 → ℝ => rescale ρ ε (t, y)) := by
  let f : (Fin 3 → ℝ) → ℝ := fun y => rescale ρ ε (t, y)
  have hcont : Continuous f := by
    dsimp [f]
    exact (contDiff_rescale ρ hρ hε).continuous.comp
      (continuous_const.prodMk continuous_id)
  obtain ⟨R, hR, hbox⟩ := exists_mollifier_support_box ρ hρ
  let K : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-R * ε) (R * ε))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hcompact : HasCompactSupport f := by
    apply HasCompactSupport.intro hK
    intro y hy
    by_contra hne
    have harg : (ε ^ (-2 : ℤ) * t, ε⁻¹ • y) ∈ tsupport ρ := by
      by_contra hnot
      apply hne
      dsimp [f]
      unfold rescale
      rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
    have hsp := (hbox _ harg).2
    apply hy
    apply Set.mem_pi.mpr
    intro i hi
    have hi' : |ε⁻¹ * y i| ≤ R := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hsp i
    have hmul : ε * |ε⁻¹ * y i| ≤ ε * R :=
      mul_le_mul_of_nonneg_left hi' hε.le
    have hcancel : ε * |ε⁻¹ * y i| = |y i| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hε)]
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hε), one_mul]
    rw [hcancel] at hmul
    rw [mem_Icc]
    have habs : 0 ≤ |y i| := abs_nonneg _
    have hRE : 0 ≤ R * ε := mul_nonneg hR hε.le
    have hmul' : |y i| ≤ R * ε := by simpa [mul_comm] using hmul
    have hneg : -|y i| ≤ y i := neg_abs_le _
    constructor
    · linarith
    · exact (le_abs_self _).trans hmul'
  exact hcont.integrable_of_hasCompactSupport hcompact

theorem stochasticHeat_integral_periodise_eq_one
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ z : SpaceTime, periodise ρ ε z = 1 := by
  obtain ⟨s, hs⟩ := periodise_eq_finset_sum_uniform ρ hρ
  let D : Set (Fin 3 → ℝ) := ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))
  have hDmeas : MeasurableSet D := by
    dsimp [D]
    rw [ZSpan.fundamentalDomain_pi_basisFun]
    exact (measurableSet_pi Set.countable_univ).2 <| Or.inl fun i _ => measurableSet_Ico
  have hDmem : ∀ y ∈ D, ∀ i, y i ∈ Set.Ico (0 : ℝ) 1 := by
    intro y hy i
    dsimp [D] at hy
    rw [ZSpan.fundamentalDomain_pi_basisFun] at hy
    exact (Set.mem_pi.mp hy) i (Set.mem_univ i)
  have hset : D =ᵐ[volume] Set.pi Set.univ (fun _ : Fin 3 => Set.Ioc (0 : ℝ) 1) :=
    fundamentalDomain_ae_eq_pi_Ioc
  have hrestrict : volume.restrict D =
      volume.restrict (Set.pi Set.univ (fun _ : Fin 3 => Set.Ioc (0 : ℝ) 1)) :=
    MeasureTheory.Measure.restrict_congr_set hset
  have hslice : ∀ t : ℝ,
      ∫ x : Torus3, periodise ρ ε (t, x) =
        ∫ y : Fin 3 → ℝ, rescale ρ ε (t, y) := by
    intro t
    have hpre : ∫ x : Torus3, periodise ρ ε (t, x) =
        ∫ (x : Fin 3 → ℝ) in {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
          periodise ρ ε (t, fun i => (x i : UnitAddCircle)) := by
      simpa only [Set.mem_pi, Set.mem_univ, true_implies, zero_add,
        MeasureSpace.volume, instMeasureSpaceUnitAddCircle,
        AddCircle.measureSpace, AddCircle.haarAddCircle, ENNReal.ofReal_one,
        one_smul] using
        UnitAddTorus.integral_preimage
          (fun x : Torus3 => periodise ρ ε (t, x)) (fun _ : Fin 3 => (0 : ℝ))
    rw [hpre]
    rw [show {x : Fin 3 → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
        Set.pi Set.univ (fun _ : Fin 3 => Set.Ioc (0 : ℝ) 1) by
      ext x
      simp]
    rw [← hrestrict]
    change (∫ x : Fin 3 → ℝ in D,
      periodise ρ ε (t, torusProj x)) = ∫ y : Fin 3 → ℝ, rescale ρ ε (t, y)
    have hsum : ∀ y ∈ D,
        periodise ρ ε (t, torusProj y) =
          ∑ k ∈ s, rescale ρ ε (t, y + fun i => (k i : ℝ)) := by
      intro y hy
      have hrep : torusRep (torusProj y) = y := torusRep_torusProj_of_mem_Ico (hDmem y hy)
      have h := (hs hε hε1 (t, torusProj y)).1
      rw [hrep] at h
      exact h
    rw [setIntegral_congr_fun hDmeas hsum]
    rw [integral_finsetSum]
    · have htile : ∫ y : Fin 3 → ℝ, rescale ρ ε (t, y) =
          ∑' k : Fin 3 → ℤ,
            ∫ y : Fin 3 → ℝ in D,
              rescale ρ ε (t, y + (fun i => (k i : ℝ))) := by
        have h := (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 3)) volume).integral_eq_tsum''
          (fun y : Fin 3 → ℝ => rescale ρ ε (t, y)) (integrable_rescale_slice ρ hρ hε t)
        calc
          ∫ y : Fin 3 → ℝ, rescale ρ ε (t, y) =
              ∑' k : (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup,
                ∫ y : Fin 3 → ℝ in D,
                  rescale ρ ε (t, k + y) := h
          _ = ∑' k : Fin 3 → ℤ,
                ∫ y : Fin 3 → ℝ in D,
                  rescale ρ ε (t, y + (fun i => (k i : ℝ))) := by
            rw [← integerLatticeAddEquiv.tsum_eq]
            apply tsum_congr
            intro k
            congr 2
            funext y
            congr 2
            funext i
            simp [integerLatticeAddEquiv_apply, add_comm]
      have hsum_eq : (∑' k : Fin 3 → ℤ,
          ∫ y : Fin 3 → ℝ in D,
            rescale ρ ε (t, y + (fun i => (k i : ℝ)))) =
          ∑ k ∈ s, ∫ y : Fin 3 → ℝ in D,
            rescale ρ ε (t, y + (fun i => (k i : ℝ))) := by
        rw [tsum_eq_sum]
        intro k hk
        have hzero : ∀ᵐ y ∂volume.restrict D,
            rescale ρ ε (t, y + (fun i => (k i : ℝ))) = 0 := by
          filter_upwards [ae_restrict_mem hDmeas] with y hy
          have hrep := torusRep_torusProj_of_mem_Ico (hDmem y hy)
          have hz := (hs hε hε1 (t, torusProj y)).2 k hk
          rw [hrep] at hz
          simpa [add_comm] using hz
        rw [integral_congr_ae hzero]
        simp
      rw [← hsum_eq, ← htile]
    · intro k hk
      have hi := integrable_rescale_slice ρ hρ hε t
      have hp := measurePreserving_add_right (volume : Measure (Fin 3 → ℝ))
        (fun i => (k i : ℝ))
      have hshift := hp.integrable_comp_of_integrable hi
      exact hshift.integrableOn
  have hprod : ∫ z : SpaceTime, periodise ρ ε z =
      ∫ t : ℝ, ∫ x : Torus3, periodise ρ ε (t, x) := by
    have hP := integrable_periodise ρ hρ hε
    change ∫ z : ℝ × Torus3, periodise ρ ε z = _
    exact integral_prod _ hP
  rw [hprod]
  have hrescale_meas : AEStronglyMeasurable (rescale ρ ε) := by
    exact (contDiff_rescale ρ hρ hε).continuous.measurable.aestronglyMeasurable
  have hrescale : Integrable (rescale ρ ε) :=
    (integrable_norm_iff hrescale_meas).mp (integrable_abs_rescale ρ hρ hε)
  have hrescale_mass : ∫ z : ParabolicSpace, rescale ρ ε z = 1 := by
    have hpoint : (fun z : ParabolicSpace => rescale ρ ε z) =
        (fun z => ε ^ (-5 : ℤ) * ρ (parabolicDilate ε⁻¹ z)) := by
      funext z
      unfold rescale parabolicDilate
      congr 2
      norm_num
    rw [hpoint, integral_const_mul,
      integral_comp_parabolicDilate (fun z : ParabolicSpace => ρ z)
        (inv_pos.mpr hε), hρ.integral_eq_one]
    rw [inv_pow]
    field_simp
  calc
    ∫ t : ℝ, ∫ x : Torus3, periodise ρ ε (t, x) =
        ∫ t : ℝ, ∫ y : Fin 3 → ℝ, rescale ρ ε (t, y) := by
          apply integral_congr_ae
          filter_upwards [] with t
          exact hslice t
    _ = ∫ z : ParabolicSpace, rescale ρ ε z :=
      (integral_prod _ hrescale).symm
    _ = 1 := hrescale_mass

end RegularityStructures.Phi43

end
