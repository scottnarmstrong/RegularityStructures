/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.ExpPoly
public import RegularityStructures.PDE.Semigroup
public import RegularityStructures.Torus.HolderBesov
public import RegularityStructures.Torus.HeatKernel
public import RegularityStructures.PDE.HeatOpBridge

/-!
# Time slices of the forcing and the Duhamel integrand `F_t(r)`

For a continuous forcing `f : ℝ × T³ → ℝ` with polynomial growth in time (`PotForcing`), the slices
`f_r = f(r, ·) ∈ C(T³)` depend continuously on `r` (`continuous_potSlice`), and
`potF t r = e^{-(t - r)} P_{t-r} f_r ∈ C(T³)` is continuous in `r` and dominated by
`e^{-(t-r)} B (1 + |r|)^n`, hence integrable on `(-∞, t]` (`integrableOn_potF`).  The massive potential
is `ψ(t) = ∫_{r ≤ t} F_t(r) dr` (see `Phi43.Potential.SlicePotential`).
-/

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures.Potential

open RegularityStructures

/-- A continuous forcing on `ℝ × T³` of polynomial growth in time. -/
structure PotForcing (f : SpaceTime → ℝ) : Prop where
  cont : Continuous f
  bound : ∃ (B : ℝ) (n : ℕ), 0 ≤ B ∧ ∀ (r : ℝ) (y : Torus3), |f (r, y)| ≤ B * (1 + |r|) ^ n

/-- The time slice `f(r, ·)` as a continuous function on `T³`. -/
@[expose] def potSlice {f : SpaceTime → ℝ} (hf : Continuous f) (r : ℝ) : C(Torus3, ℝ) :=
  ⟨fun y => f (r, y), hf.comp (Continuous.prodMk continuous_const continuous_id)⟩

theorem potSlice_apply {f : SpaceTime → ℝ} (hf : Continuous f) (r : ℝ) (y : Torus3) :
    potSlice hf r y = f (r, y) := rfl

theorem continuous_potSlice {f : SpaceTime → ℝ} (hf : Continuous f) :
    Continuous (potSlice hf) := by
  have : potSlice hf = ContinuousMap.curry ⟨f, hf⟩ := rfl
  rw [this]
  exact (ContinuousMap.curry ⟨f, hf⟩).continuous

theorem norm_potSlice_le {f : SpaceTime → ℝ} {B : ℝ} {n : ℕ} (hB : 0 ≤ B)
    (h : ∀ (r : ℝ) (y : Torus3), |f (r, y)| ≤ B * (1 + |r|) ^ n) (hf : Continuous f) (r : ℝ) :
    ‖potSlice hf r‖ ≤ B * (1 + |r|) ^ n :=
  (ContinuousMap.norm_le _ (by positivity)).2 fun y => by
    simpa [potSlice_apply, Real.norm_eq_abs] using h r y

/-- The Duhamel integrand `F_t(r) = e^{-(t-r)} P_{t-r} f_r`. -/
@[expose] noncomputable def potF {f : SpaceTime → ℝ} (hf : Continuous f) (t r : ℝ) :
    C(Torus3, ℝ) :=
  Real.exp (-(t - r)) • PDE.heatOp (t - r) (potSlice hf r)

theorem continuous_potF {f : SpaceTime → ℝ} (hf : Continuous f) (t : ℝ) :
    Continuous (potF hf t) := by
  unfold potF
  have h1 : Continuous fun r : ℝ => PDE.heatOp (t - r) (potSlice hf r) :=
    PDE.continuous_heatOp.comp ((continuous_const.sub continuous_id).prodMk (continuous_potSlice hf))
  exact (Real.continuous_exp.comp (continuous_const.sub continuous_id).neg).smul h1

theorem norm_potF_le {f : SpaceTime → ℝ} {B : ℝ} {n : ℕ} (hB : 0 ≤ B)
    (h : ∀ (r : ℝ) (y : Torus3), |f (r, y)| ≤ B * (1 + |r|) ^ n) (hf : Continuous f) (t r : ℝ) :
    ‖potF hf t r‖ ≤ Real.exp (-(t - r)) * (B * (1 + |r|) ^ n) := by
  unfold potF
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_left
    ((PDE.norm_heatOp_le _ _).trans (norm_potSlice_le hB h hf r)) (Real.exp_pos _).le

theorem integrableOn_potF {f : SpaceTime → ℝ} (hF : PotForcing f) (t : ℝ) :
    IntegrableOn (potF hF.cont t) (Iic t) := by
  obtain ⟨B, n, hB, h⟩ := hF.bound
  have hi : IntegrableOn (fun r : ℝ => Real.exp (-(t - r)) * (B * (1 + |r|) ^ n)) (Iic t) := by
    have : IntegrableOn (fun r : ℝ => B * (Real.exp (-(t - r)) * (1 + |r|) ^ n)) (Iic t) :=
      (integrableOn_exp_mul_pow_Iic t n).const_mul B
    refine this.congr_fun (fun r _ => ?_) measurableSet_Iic
    ring
  exact hi.mono' (continuous_potF hF.cont t).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Iic fun r _ => norm_potF_le hB h hF.cont t r)

end RegularityStructures.Potential

end
