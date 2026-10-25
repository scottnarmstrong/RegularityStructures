/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.FourierDecayChain
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Coordinate slices of the torus Fourier coefficient

The multivariate Fourier coefficient is first rewritten as an iterated integral in one coordinate.
This is the measure-theoretic part of the finite-window decay estimate; the one-dimensional
integration-by-parts estimate is supplied separately by `FourierDecayChain`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace RegularityStructures.Phi43

def coordinateInsert {n : ℕ} (i : Fin (n + 1)) (t : UnitAddCircle)
    (x : Fin n → UnitAddCircle) : Fin (n + 1) → UnitAddCircle :=
  Fin.insertNth i t x

theorem mFourierCoeff_eq_coordinateIntegral {n : ℕ} (i : Fin (n + 1))
    (f : UnitAddTorus (Fin (n + 1)) → ℂ) (k : Fin (n + 1) → ℤ) (hf : Continuous f) :
    UnitAddTorus.mFourierCoeff f k =
      ∫ x : UnitAddTorus (Fin n), ∫ t : UnitAddCircle,
        UnitAddTorus.mFourier (-k) (coordinateInsert i t x) •
          f (coordinateInsert i t x) := by
  let e : (UnitAddCircle × (Fin n → UnitAddCircle)) ≃ᵐ
      (Fin (n + 1) → UnitAddCircle) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) i).symm
  let F : UnitAddCircle × (Fin n → UnitAddCircle) → ℂ := fun p =>
    UnitAddTorus.mFourier (-k) (e p) • f (e p)
  have hFmeas : Measurable F := by
    exact ((UnitAddTorus.mFourier (-k)).measurable.comp e.measurable).mul
      (hf.measurable.comp e.measurable)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hFbound : ∀ p, ‖F p‖ ≤ C := by
    intro p
    change ‖UnitAddTorus.mFourier (-k) (e p) • f (e p)‖ ≤ C
    rw [norm_smul]
    have hmode : ‖UnitAddTorus.mFourier (-k) (e p)‖ = 1 := by
      simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
        fourier_apply, Circle.norm_coe, Finset.prod_const_one]
    rw [hmode, one_mul]
    exact hC _ (Set.mem_univ _)
  have hcircle : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  have htorus : (volume : Measure (Fin (n + 1) → UnitAddCircle)) =
      Measure.pi (fun _ : Fin (n + 1) => AddCircle.haarAddCircle) := by
    change Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle)) = _
    rw [hcircle]
  have hint : Integrable (fun p : UnitAddCircle × (Fin n → UnitAddCircle) =>
      F p)
      ((volume : Measure UnitAddCircle).prod
        (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle)))) := by
    have hbound := IntegrableOn.of_bound (μ :=
        (volume : Measure UnitAddCircle).prod
          (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (s := Set.univ) (by simp [hcircle]) hFmeas.aestronglyMeasurable C
      (ae_of_all _ hFbound)
    exact integrableOn_univ.mp hbound
  calc
    UnitAddTorus.mFourierCoeff f k =
        ∫ y : Fin (n + 1) → UnitAddCircle,
          UnitAddTorus.mFourier (-k) y • f y := by
            change (∫ y : Fin (n + 1) → UnitAddCircle,
              UnitAddTorus.mFourier (-k) y • f y ∂
                Measure.pi (fun _ : Fin (n + 1) => AddCircle.haarAddCircle)) = _
            rw [← htorus]
    _ = ∫ p : UnitAddCircle × (Fin n → UnitAddCircle),
        UnitAddTorus.mFourier (-k) (e p) • f (e p) := by
      change (∫ y : Fin (n + 1) → UnitAddCircle,
          UnitAddTorus.mFourier (-k) y • f y ∂
            Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle))) =
        ∫ p : UnitAddCircle × (Fin n → UnitAddCircle),
          UnitAddTorus.mFourier (-k) (e p) • f (e p) ∂
            (volume : Measure UnitAddCircle).prod
              (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle)))
      rw [← (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle)) i).symm.integral_comp']
      
    _ = ∫ x : Fin n → UnitAddCircle, ∫ t : UnitAddCircle,
        UnitAddTorus.mFourier (-k) (coordinateInsert i t x) •
          f (coordinateInsert i t x) := by
      change (∫ p : UnitAddCircle × (Fin n → UnitAddCircle),
        UnitAddTorus.mFourier (-k) (e p) • f (e p) ∂
          (volume : Measure UnitAddCircle).prod
            (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle)))) = _
      change (∫ p : UnitAddCircle × (Fin n → UnitAddCircle), F p ∂
          ((volume : Measure UnitAddCircle).prod
            (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))) = _
      rw [← integral_prod_swap]
      have hiter := integral_prod
        (fun z : (Fin n → UnitAddCircle) × UnitAddCircle =>
          F z.swap) hint.swap
      simpa [F, e, coordinateInsert, MeasurableEquiv.piFinSuccAbove,
        Fin.insertNthEquiv, Function.comp_def, volume, AddCircle.haarAddCircle] using hiter

end RegularityStructures.Phi43

end
