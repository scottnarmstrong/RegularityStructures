/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.WindowedKernel
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The finite-window change of variables

The window torus is normalized to unit period.  The map `windowPoint` therefore pulls normalized
Haar measure back to the physical space-time measure on the window, divided by its time length.
This is the measure identity used to transport the multivariate Fourier `L²` series.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

theorem integral_windowPoint {a b : ℝ} (hab : a < b) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpaceTime → E) (hf : Integrable f (volume : Measure SpaceTime))
    (hfp : Integrable
      (fun x : ℝ × (Fin 3 → ℝ) => f
        (a + (b - a) * x.1, torusProj x.2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (Measure.pi (fun _ : Fin 3 => volume.restrict (Ioc (0 : ℝ) 1))))) :
    ∫ y : UnitAddTorus (Fin 4), f (windowPoint a b y) =
      (b - a)⁻¹ • ∫ z in windowInterval a b, f z := by
  have hpre :
      (∫ (x : Fin 4 → ℝ) in {x : Fin 4 → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) (0 + 1)},
          f (windowPoint a b (fun i => (x i : UnitAddCircle)))) =
        ∫ y : UnitAddTorus (Fin 4), f (windowPoint a b y) := by
    simpa [volume, AddCircle.haarAddCircle] using
      (UnitAddTorus.integral_preimage
        (fun y : UnitAddTorus (Fin 4) => f (windowPoint a b y)) (fun _ => 0)).symm
  rw [← hpre]
  change
    (∫ x : Fin 4 → ℝ,
        f (windowPoint a b (fun i => (x i : UnitAddCircle))) ∂
          (volume : Measure (Fin 4 → ℝ)).restrict
            {x : Fin 4 → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) (0 + 1)}) = _
  rw [show (volume : Measure (Fin 4 → ℝ)) = Measure.pi (fun _ : Fin 4 => volume) by rfl]
  have hset : {x : Fin 4 → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) (0 + 1)} =
      Set.univ.pi (fun _ : Fin 4 => Ioc (0 : ℝ) 1) := by
    ext x
    simp
  rw [hset]
  change
    (∫ x : Fin 4 → ℝ,
        f (windowPoint a b (fun i => (x i : UnitAddCircle))) ∂
          (Measure.pi (fun _ : Fin 4 => volume)).restrict
            (Set.univ.pi (fun _ : Fin 4 => Ioc (0 : ℝ) 1))) = _
  rw [Measure.restrict_pi_pi (μ := fun _ : Fin 4 => volume)
    (fun _ : Fin 4 => Ioc (0 : ℝ) 1)]
  rw [← ((measurePreserving_piFinSuccAbove
    (fun _ : Fin 4 => volume.restrict (Ioc (0 : ℝ) 1)) 0).symm).integral_comp']
  simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  simp_rw [Fin.insertNthEquiv]
  simp_rw [Fin.insertNth_zero]
  simp only [Equiv.coe_fn_mk, windowPoint, Fin.cons_zero, Fin.cons_succ, cast_eq]
  have hsp (t : ℝ) :
      (∫ x : Fin 3 → ℝ, f (t, fun i => (x i : UnitAddCircle)) ∂
        Measure.pi (fun _ : Fin 3 => volume.restrict (Ioc (0 : ℝ) 1))) =
        ∫ y : UnitAddTorus (Fin 3), f (t, y) := by
    have hpre := UnitAddTorus.integral_preimage
      (fun y : UnitAddTorus (Fin 3) => f (t, y)) (fun _ => 0)
    rw [← Measure.restrict_pi_pi (μ := fun _ : Fin 3 => volume)
      (fun _ : Fin 3 => Ioc (0 : ℝ) 1)]
    change
      (∫ x : Fin 3 → ℝ in Set.univ.pi (fun _ : Fin 3 => Ioc (0 : ℝ) 1),
        f (t, fun i => (x i : UnitAddCircle))) = _
    have hset : {x : Fin 3 → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) (0 + 1)} =
        Set.univ.pi (fun _ : Fin 3 => Ioc (0 : ℝ) 1) := by
      ext x
      simp
    rw [← hset]
    simpa [volume, AddCircle.haarAddCircle] using hpre.symm
  have hfirst : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), t ∈ Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  have hpair : ∀ᵐ x ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod
      (Measure.pi (fun _ : Fin 3 => volume.restrict (Ioc (0 : ℝ) 1)))),
      x.1 ∈ Ioc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_preimage measurable_fst measurableSet_Ioc)).2
    filter_upwards [hfirst] with t ht
    exact ae_of_all _ (fun _ => ht)
  have heq :
      (fun x : ℝ × (Fin 3 → ℝ) =>
        f (a + (b - a) * ↑((AddCircle.equivIoc (1 : ℝ) 0) (↑x.1) : ℝ),
          fun i => (x.2 i : UnitAddCircle))) =ᵐ[
            (volume.restrict (Ioc (0 : ℝ) 1)).prod
              (Measure.pi (fun _ : Fin 3 => volume.restrict (Ioc (0 : ℝ) 1)))]
        (fun x => f (a + (b - a) * x.1, torusProj x.2)) := by
    filter_upwards [hpair] with x hx
    have htime : (AddCircle.equivIoc (1 : ℝ) 0 (↑x.1) : ℝ) = x.1 :=
      AddCircle.equivIoc_coe_of_mem (by simpa only [zero_add] using hx)
    rw [htime]
    rfl
  rw [integral_congr_ae heq, integral_prod _ hfp]
  change
    (∫ x : ℝ in Ioc (0 : ℝ) 1,
      ∫ y : Fin 3 → ℝ,
        f (a + (b - a) * x, fun i => (y i : UnitAddCircle)) ∂
          Measure.pi (fun _ : Fin 3 => volume.restrict (Ioc (0 : ℝ) 1))) = _
  simp_rw [hsp]
  let g : ℝ → E := fun t => ∫ y : UnitAddTorus (Fin 3), f (t, y)
  have hRhs :
      (∫ z in windowInterval a b, f z) = ∫ t in Ioc a b, g t := by
    have hfi : Integrable ((windowInterval a b).indicator f)
        (volume : Measure SpaceTime) :=
      hf.integrableOn.integrable_indicator (measurableSet_Ioc.prod MeasurableSet.univ)
    calc
      (∫ z in windowInterval a b, f z) =
          ∫ z, (windowInterval a b).indicator f z := by
            symm
            exact integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)
      _ = ∫ t : ℝ, ∫ y : UnitAddTorus (Fin 3),
          (windowInterval a b).indicator f (t, y) :=
        integral_prod _ hfi
      _ = ∫ t : ℝ, ∫ y : UnitAddTorus (Fin 3),
          (Ioc a b).indicator (fun s => f (s, y)) t := by
        refine integral_congr_ae ?_
        filter_upwards [] with t
        refine integral_congr_ae ?_
        filter_upwards [] with y
        by_cases ht : t ∈ Ioc a b
        · simp [windowInterval, ht]
        · simp [windowInterval, ht]
      _ = ∫ t in Ioc a b, g t := by
        simpa [g] using (integral_integral_indicator (μ := (volume : Measure ℝ))
          (ν := (volume : Measure (UnitAddTorus (Fin 3))))
          (f := fun t y => f (t, y)) (s := Ioc a b) measurableSet_Ioc)
  rw [hRhs]
  let L : ℝ := b - a
  have hL : 0 < L := sub_pos.mpr hab
  have htime :
      (∫ t in Ioc (0 : ℝ) 1, g (a + (b - a) * t)) =
        (b - a)⁻¹ • ∫ t in Ioc a b, g t := by
    calc
      (∫ t in Ioc (0 : ℝ) 1, g (a + (b - a) * t)) =
          ∫ t in (0 : ℝ)..1, g (a + (b - a) * t) := by
            rw [intervalIntegral.integral_of_le (by norm_num)]
      _ = (b - a)⁻¹ • ((b - a) •
          ∫ t in (0 : ℝ)..1, g (a + (b - a) * t)) := by
            rw [inv_smul_smul₀ (ne_of_gt hL)]
      _ = (b - a)⁻¹ • ∫ t in a + (b - a) * 0..a + (b - a) * 1, g t := by
            rw [intervalIntegral.smul_integral_comp_add_mul]
      _ = (b - a)⁻¹ • ∫ t in a..b, g t := by
            congr 2 <;> simp
      _ = (b - a)⁻¹ • ∫ t in Ioc a b, g t := by
            rw [intervalIntegral.integral_of_le hab.le]
  exact htime

end RegularityStructures.Phi43

end
