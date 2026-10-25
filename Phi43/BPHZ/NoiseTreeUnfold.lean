/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsPeriodiseL1
public import Phi43.ClassicalSolution.Periodise

/-!
# Unfolding the periodised mollifier against a periodic weight

`lintegral_periodise_le` bounds the `L¹` norm of the periodisation by that of the Euclidean lift.
The same proof, with an extra measurable weight `F` on the torus, gives
`∫_{ℝ × T³} |ρ_ε^♯| F ≤ ∫_{ℝ × ℝ³} |ρ_ε| (F ∘ π)`.  This is what turns a translation estimate on the
torus into an estimate against the Euclidean mollifier.
-/

public section

open MeasureTheory Real Set Submodule
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem measurable_torusProj' : Measurable torusProj :=
  (continuous_pi fun i =>
    (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)).measurable

private theorem torusProj_add_int (x : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    torusProj (x + fun i => (k i : ℝ)) = torusProj x := by
  funext j
  simp [torusProj]

theorem noise_lintegral_periodise_slice_mul_le (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ) (F : Torus3 → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x : Torus3, ENNReal.ofReal |periodise ρ ε (t, x)| * F x) ≤
      ∫⁻ y : Fin 3 → ℝ, ENNReal.ofReal |rescale ρ ε (t, y)| * F (torusProj y) := by
  obtain ⟨s, hs⟩ := periodise_eq_finset_sum_uniform ρ hρ
  let D : Set (Fin 3 → ℝ) := ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))
  have hDmeas : MeasurableSet D := by
    dsimp [D]
    rw [ZSpan.fundamentalDomain_pi_basisFun]
    exact (measurableSet_pi Set.countable_univ).2 <| Or.inl fun i _ => measurableSet_Ico
  have hDmem : ∀ x ∈ D, ∀ i, x i ∈ Set.Ico (0 : ℝ) 1 := by
    intro x hx i
    dsimp [D] at hx
    rw [ZSpan.fundamentalDomain_pi_basisFun] at hx
    exact (Set.mem_pi.mp hx) i (Set.mem_univ i)
  have hset : D =ᵐ[volume] Set.pi Set.univ (fun _ : Fin 3 => Set.Ioc (0 : ℝ) 1) :=
    fundamentalDomain_ae_eq_pi_Ioc
  have hrestrict : volume.restrict D =
      volume.restrict (Set.pi Set.univ (fun _ : Fin 3 => Set.Ioc (0 : ℝ) 1)) :=
    MeasureTheory.Measure.restrict_congr_set hset
  have hpre0 :
      (∫⁻ x : Torus3, ENNReal.ofReal |periodise ρ ε (t, x)| * F x) =
        ∫⁻ (x : Fin 3 → ℝ) in {x | ∀ i : Fin 3, x i ∈ Set.Ioc (0 : ℝ) 1},
          ENNReal.ofReal |periodise ρ ε (t, fun i => (x i : UnitAddCircle))| *
            F (fun i => (x i : UnitAddCircle)) := by
    simpa only [Set.mem_pi, Set.mem_univ, true_implies, zero_add,
      MeasureSpace.volume, instMeasureSpaceUnitAddCircle,
      AddCircle.measureSpace, AddCircle.haarAddCircle, ENNReal.ofReal_one, one_smul] using
      UnitAddTorus.lintegral_preimage
        (fun x : Torus3 => (ENNReal.ofReal |periodise ρ ε (t, x)| * F x))
        (fun _ : Fin 3 => (0 : ℝ))
  have hpre :
      (∫⁻ x : Torus3, ENNReal.ofReal |periodise ρ ε (t, x)| * F x) =
        ∫⁻ (x : Fin 3 → ℝ) in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioc (0 : ℝ) 1),
          ENNReal.ofReal |periodise ρ ε (t, fun i => (x i : UnitAddCircle))| *
            F (fun i => (x i : UnitAddCircle)) := by
    rw [hpre0]
    congr 2
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [hpre, ← hrestrict]
  have hpoint : ∀ x ∈ D,
      ENNReal.ofReal |periodise ρ ε (t, torusProj x)| * F (torusProj x) ≤
        ∑ k ∈ s, ENNReal.ofReal (abs
          (rescale ρ ε (t, x + fun i => (k i : ℝ)))) *
            F (torusProj (x + fun i => (k i : ℝ))) := by
    intro x hx
    have hrep : torusRep (torusProj x) = x := torusRep_torusProj_of_mem_Ico (hDmem x hx)
    have hsum := (hs hε hε1 (t, torusProj x)).1
    rw [hrep] at hsum
    rw [hsum]
    simp_rw [torusProj_add_int]
    rw [← Finset.sum_mul]
    refine mul_le_mul_left ?_ _
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k hk => abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.norm_eq_abs] using
      (norm_sum_le s (fun k => rescale ρ ε (t, x + fun i => (k i : ℝ))))
  have hmeas : ∀ k : Fin 3 → ℤ,
      Measurable (fun x : Fin 3 → ℝ => ENNReal.ofReal (abs
        (rescale ρ ε (t, x + fun i => (k i : ℝ)))) *
          F (torusProj (x + fun i => (k i : ℝ)))) := by
    intro k
    have hc : Continuous (fun x : Fin 3 → ℝ =>
        rescale ρ ε (t, x + fun i => (k i : ℝ))) := by
      unfold rescale
      apply Continuous.const_mul
      exact hρ.contDiff.continuous.comp (by fun_prop)
    exact hc.norm.measurable.ennreal_ofReal.mul
      (hF.comp (measurable_torusProj'.comp (measurable_id.add_const _)))
  calc
    ∫⁻ x in D, ENNReal.ofReal |periodise ρ ε (t, torusProj x)| * F (torusProj x) ≤
        ∫⁻ x in D, ∑ k ∈ s, ENNReal.ofReal (abs
          (rescale ρ ε (t, x + fun i => (k i : ℝ)))) *
            F (torusProj (x + fun i => (k i : ℝ))) :=
      setLIntegral_mono' hDmeas (fun x hx => hpoint x hx)
    _ = ∑ k ∈ s, ∫⁻ x in D, ENNReal.ofReal (abs
          (rescale ρ ε (t, x + fun i => (k i : ℝ)))) *
            F (torusProj (x + fun i => (k i : ℝ))) := by
      rw [lintegral_finsetSum]
      intro k hk
      exact hmeas k
    _ = ∫⁻ y : Fin 3 → ℝ, ENNReal.ofReal (abs (rescale ρ ε (t, y))) * F (torusProj y) := by
      let f : (Fin 3 → ℝ) → ENNReal := fun y =>
        ENNReal.ofReal (abs (rescale ρ ε (t, y))) * F (torusProj y)
      have htile :
          ∫⁻ y : Fin 3 → ℝ, f y =
            ∑' k : Fin 3 → ℤ, ∫⁻ y in D,
              f (y + fun i => (k i : ℝ)) := by
        rw [ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 3)) volume |>.lintegral_eq_tsum'']
        rw [← integerLatticeAddEquiv.tsum_eq]
        apply tsum_congr
        intro k
        congr 2
        funext y
        congr 1
        funext i
        change (integerLatticeAddEquiv k).1 i + y i = y i + (k i : ℝ)
        rw [integerLatticeAddEquiv_apply]
        ring
      calc
        ∑ k ∈ s, ∫⁻ x in D, f (x + fun i => (k i : ℝ)) =
            ∑' k : Fin 3 → ℤ, ∫⁻ x in D, f (x + fun i => (k i : ℝ)) := by
          symm
          rw [tsum_eq_sum]
          intro k hk
          calc
            (∫⁻ x in D, f (x + fun i => (k i : ℝ))) = ∫⁻ x in D, 0 := by
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem hDmeas] with x hx
              have hrep : torusRep (torusProj x) = x :=
                torusRep_torusProj_of_mem_Ico (hDmem x hx)
              have hzero := (hs hε hε1 (t, torusProj x)).2 k hk
              rw [hrep] at hzero
              simp only [f, hzero, abs_zero, ENNReal.ofReal_zero, zero_mul]
            _ = 0 := by simp
        _ = ∫⁻ y : Fin 3 → ℝ, f y := htile.symm

/-- Weighted unfolding of the periodised mollifier. -/
theorem noise_lintegral_periodise_mul_le (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (F : SpaceTime → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z : SpaceTime, ENNReal.ofReal |periodise ρ ε z| * F z ≤
      ∫⁻ y : ParabolicSpace, ENNReal.ofReal |rescale ρ ε y| * F (y.1, torusProj y.2) := by
  have hP : Measurable (fun z : SpaceTime => ENNReal.ofReal |periodise ρ ε z| * F z) :=
    (measurable_periodise ρ hρ).norm.ennreal_ofReal.mul hF
  have hres : Measurable (rescale ρ ε) := by
    unfold rescale
    apply measurable_const.mul
    apply hρ.contDiff.continuous.measurable.comp
    exact (measurable_const.mul measurable_fst).prodMk
      (measurable_snd.const_smul ε⁻¹)
  have hR : Measurable (fun y : ParabolicSpace =>
      ENNReal.ofReal |rescale ρ ε y| * F (y.1, torusProj y.2)) :=
    hres.norm.ennreal_ofReal.mul
      (hF.comp (measurable_fst.prodMk (measurable_torusProj'.comp measurable_snd)))
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.volume_eq_prod]
  rw [lintegral_prod _ hP.aemeasurable, lintegral_prod _ hR.aemeasurable]
  exact lintegral_mono fun t =>
    noise_lintegral_periodise_slice_mul_le ρ hρ hε hε1 t (fun x => F (t, x))
      (hF.comp (measurable_const.prodMk measurable_id))

end RegularityStructures.Phi43

end
