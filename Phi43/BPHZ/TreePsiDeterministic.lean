/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Constants.Finite
public import Phi43.ClassicalSolution.PeriodiseRegularity
public import Phi43.ClassicalSolution.Periodise
public import RegularityStructures.Probability.SpaceTimeMeasure

/-!
# Deterministic Fubini identities for the tree `Ψ`

For an integrable kernel `k` and the mollifier family `M x v = mollifierAt ρ ε x v`, put
`h v = ∫ x, k x * M x v`.  This file proves that `h` is integrable and bounded, hence square
integrable, and the two deterministic identities used by the stochastic Fubini theorem:
`∫∫ k x k y ∫ M x v M y v = ∫ h²` and `∫ k x ∫ M x v h v = ∫ h²`.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The kernel `v ↦ ∫ x, k x * mollifierAt ρ ε x v`, i.e. `k` pushed through the mollifier. -/
noncomputable def treePsiConv (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (k : SpaceTime → ℝ)
    (v : SpaceTime) : ℝ :=
  ∫ x, k x * mollifierAt ρ ε x v

end RegularityStructures.Phi43

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {k : SpaceTime → ℝ}

private theorem mollifierAt_meas (hρ : IsMollifier ρ) :
    Measurable (fun q : SpaceTime × SpaceTime => mollifierAt ρ ε q.1 q.2) :=
  (measurable_periodise ρ hρ).comp (measurable_fst.sub measurable_snd)

private theorem mollifierAt_bdd (hρ : IsMollifier ρ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x v, |mollifierAt ρ ε x v| ≤ B := by
  obtain ⟨C, hC⟩ := bounded_periodise ρ hρ hε
  exact ⟨max C 0, le_max_right _ _, fun x v => (hC (x - v)).trans (le_max_left _ _)⟩

private theorem mollifierAt_integrable (hρ : IsMollifier ρ) (hε : 0 < ε) (x : SpaceTime) :
    Integrable (mollifierAt ρ ε x) :=
  integrable_comp_sub_left_spaceTime (integrable_periodise ρ hρ hε) x

/-- The integrand `k x * M x v` is integrable on `ℝ×T³ × ℝ×T³`. -/
theorem treePsi_integrable_kernel_mul (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hk : Integrable k) :
    Integrable (fun q : SpaceTime × SpaceTime => k q.1 * mollifierAt ρ ε q.1 q.2)
      ((volume : Measure SpaceTime).prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun q : SpaceTime × SpaceTime => k q.1 * mollifierAt ρ ε q.1 q.2)
      ((volume : Measure SpaceTime).prod volume) :=
    hk.aestronglyMeasurable.comp_fst.mul (mollifierAt_meas hρ).aestronglyMeasurable
  refine (integrable_prod_iff hmeas).2 ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
  · exact (mollifierAt_integrable hρ hε x).const_mul (k x)
  · have hL : ∀ x, ∫ v, ‖k x * mollifierAt ρ ε x v‖ = |k x| * ∫ v, |periodise ρ ε v| := by
      intro x
      simp only [norm_mul, Real.norm_eq_abs]
      rw [integral_const_mul]
      congr 1
      exact integral_comp_sub_left_spaceTime (fun v => |periodise ρ ε v|) x
    simp_rw [hL]
    exact hk.norm.mul_const _

/-- The function `h v = ∫ k x * M x v dx`. -/
theorem treePsi_integrable_conv (hρ : IsMollifier ρ) (hε : 0 < ε) (hk : Integrable k) :
    Integrable (treePsiConv ρ ε k) := by
  have := (treePsi_integrable_kernel_mul hρ hε hk).swap.integral_prod_left
  exact this

/-- `h` is bounded. -/
theorem treePsi_conv_abs_le (hρ : IsMollifier ρ) (hε : 0 < ε) (hk : Integrable k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, |treePsiConv ρ ε k v| ≤ C := by
  obtain ⟨B, hB, hMB⟩ := mollifierAt_bdd hρ hε
  refine ⟨B * ∫ x, |k x|, mul_nonneg hB (integral_nonneg fun _ => abs_nonneg _), fun v => ?_⟩
  have h1 : Integrable (fun x => k x * mollifierAt ρ ε x v) := by
    have hMv : AEStronglyMeasurable (fun x => mollifierAt ρ ε x v) :=
      ((mollifierAt_meas hρ).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    refine Integrable.mono' (hk.norm.mul_const B) (hk.aestronglyMeasurable.mul hMv)
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hMB x v) (abs_nonneg _) |>.trans_eq (by ring)
  unfold treePsiConv
  calc |∫ x, k x * mollifierAt ρ ε x v| ≤ ∫ x, |k x * mollifierAt ρ ε x v| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun x => k x * mollifierAt ρ ε x v)
    _ ≤ ∫ x, B * |k x| := by
        refine integral_mono h1.abs (hk.norm.const_mul B) fun x => ?_
        rw [abs_mul]
        calc |k x| * |mollifierAt ρ ε x v| ≤ |k x| * B :=
              mul_le_mul_of_nonneg_left (hMB x v) (abs_nonneg _)
          _ = B * |k x| := by ring
    _ = B * ∫ x, |k x| := integral_const_mul _ _

/-- `h` is square integrable. -/
theorem treePsi_memLp_conv (hρ : IsMollifier ρ) (hε : 0 < ε) (hk : Integrable k) :
    MemLp (treePsiConv ρ ε k) 2 := by
  obtain ⟨C, hC, hbd⟩ := treePsi_conv_abs_le hρ hε hk
  have hi := treePsi_integrable_conv hρ hε hk
  refine (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).2 ?_
  refine Integrable.mono' (hi.norm.const_mul C) (hi.aestronglyMeasurable.pow 2)
    (Filter.Eventually.of_forall fun v => ?_)
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  calc treePsiConv ρ ε k v ^ 2
      = |treePsiConv ρ ε k v| * |treePsiConv ρ ε k v| := by
        rw [← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]
    _ ≤ C * |treePsiConv ρ ε k v| :=
        mul_le_mul_of_nonneg_right (hbd v) (abs_nonneg _)

/-- Slices of the integrand `k x * M x v` in `x` are integrable. -/
private theorem slice_integrable (hρ : IsMollifier ρ) (hε : 0 < ε) (hk : Integrable k)
    (v : SpaceTime) : Integrable (fun x => k x * mollifierAt ρ ε x v) := by
  obtain ⟨B, hB, hMB⟩ := mollifierAt_bdd hρ hε
  have hMv : AEStronglyMeasurable (fun x => mollifierAt ρ ε x v) :=
    ((mollifierAt_meas hρ).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  refine Integrable.mono' (hk.norm.mul_const B) (hk.aestronglyMeasurable.mul hMv)
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hMB x v) (abs_nonneg _) |>.trans_eq (by ring)

/-- Cross identity: `∫ k x ∫ M x v h v = ∫ h²`. -/
theorem treePsi_det_cross (hρ : IsMollifier ρ) (hε : 0 < ε) (hk : Integrable k) :
    ∫ x, k x * (∫ v, mollifierAt ρ ε x v * treePsiConv ρ ε k v) =
      ∫ v, treePsiConv ρ ε k v ^ 2 := by
  obtain ⟨C, hC, hbd⟩ := treePsi_conv_abs_le hρ hε hk
  have hint := treePsi_integrable_conv hρ hε hk
  have hF := treePsi_integrable_kernel_mul hρ hε hk
  have hFh : Integrable (fun q : SpaceTime × SpaceTime =>
      k q.1 * mollifierAt ρ ε q.1 q.2 * treePsiConv ρ ε k q.2)
      ((volume : Measure SpaceTime).prod volume) := by
    refine Integrable.mono' (hF.norm.mul_const C)
      (hF.aestronglyMeasurable.mul hint.aestronglyMeasurable.comp_snd)
      (Filter.Eventually.of_forall fun q => ?_)
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbd q.2) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc ∫ x, k x * (∫ v, mollifierAt ρ ε x v * treePsiConv ρ ε k v)
      = ∫ x, ∫ v, k x * mollifierAt ρ ε x v * treePsiConv ρ ε k v := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun v => by ring)
    _ = ∫ v, ∫ x, k x * mollifierAt ρ ε x v * treePsiConv ρ ε k v := integral_integral_swap hFh
    _ = ∫ v, treePsiConv ρ ε k v ^ 2 := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp only
        rw [integral_mul_const, sq]
        rfl


private theorem prod_mul_sq (g : SpaceTime → ℝ) :
    ∫ p : SpaceTime × SpaceTime, g p.1 * g p.2 = (∫ x, g x) ^ 2 := by
  rw [sq]
  exact integral_prod_mul g g

/-- The triple integrand `F(x, v) F(y, v)` is integrable. -/
private theorem triple_integrable (hρ : IsMollifier ρ) (hε : 0 < ε) (hk : Integrable k) :
    Integrable (fun q : (SpaceTime × SpaceTime) × SpaceTime =>
      (k q.1.1 * mollifierAt ρ ε q.1.1 q.2) * (k q.1.2 * mollifierAt ρ ε q.1.2 q.2))
      (((volume : Measure SpaceTime).prod volume).prod volume) := by
  obtain ⟨B, hB, hMB⟩ := mollifierAt_bdd hρ hε
  have hF := treePsi_integrable_kernel_mul hρ hε hk
  have hkm := hk.aestronglyMeasurable
  have hMm := mollifierAt_meas (ε := ε) hρ
  have hmeas : AEStronglyMeasurable (fun q : (SpaceTime × SpaceTime) × SpaceTime =>
      (k q.1.1 * mollifierAt ρ ε q.1.1 q.2) * (k q.1.2 * mollifierAt ρ ε q.1.2 q.2))
      (((volume : Measure SpaceTime).prod volume).prod volume) := by
    have h1 : AEStronglyMeasurable (fun q : (SpaceTime × SpaceTime) × SpaceTime => k q.1.1)
        (((volume : Measure SpaceTime).prod volume).prod volume) :=
      hkm.comp_fst.comp_fst
    have h2 : AEStronglyMeasurable (fun q : (SpaceTime × SpaceTime) × SpaceTime => k q.1.2)
        (((volume : Measure SpaceTime).prod volume).prod volume) :=
      hkm.comp_snd.comp_fst
    have h3 : Measurable (fun q : (SpaceTime × SpaceTime) × SpaceTime =>
        mollifierAt ρ ε q.1.1 q.2) :=
      hMm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h4 : Measurable (fun q : (SpaceTime × SpaceTime) × SpaceTime =>
        mollifierAt ρ ε q.1.2 q.2) :=
      hMm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact (h1.mul h3.aestronglyMeasurable).mul (h2.mul h4.aestronglyMeasurable)
  have hslice : ∀ v, Integrable (fun x => k x * mollifierAt ρ ε x v) :=
    slice_integrable hρ hε hk
  have hnorm : ∀ v, ∫ p : SpaceTime × SpaceTime,
      ‖(k p.1 * mollifierAt ρ ε p.1 v) * (k p.2 * mollifierAt ρ ε p.2 v)‖ =
      (∫ x, |k x * mollifierAt ρ ε x v|) ^ 2 := by
    intro v
    have := prod_mul_sq (fun x => |k x * mollifierAt ρ ε x v|)
    simpa only [norm_mul, Real.norm_eq_abs, abs_mul] using this
  rw [integrable_prod_iff' hmeas]
  refine ⟨Filter.Eventually.of_forall fun v => (hslice v).mul_prod (hslice v), ?_⟩
  have ha : Integrable (fun v => ∫ x, |k x * mollifierAt ρ ε x v|) := by
    have := hF.swap.integral_norm_prod_left
    simpa [Real.norm_eq_abs] using this
  have hbd : ∀ v, ∫ x, |k x * mollifierAt ρ ε x v| ≤ B * ∫ x, |k x| := by
    intro v
    rw [← integral_const_mul]
    refine integral_mono (hslice v).abs (hk.norm.const_mul B) fun x => ?_
    rw [abs_mul]
    calc |k x| * |mollifierAt ρ ε x v| ≤ |k x| * B :=
          mul_le_mul_of_nonneg_left (hMB x v) (abs_nonneg _)
      _ = B * |k x| := by ring
  have hinner : AEStronglyMeasurable (fun v => ∫ p : SpaceTime × SpaceTime,
      ‖(k p.1 * mollifierAt ρ ε p.1 v) * (k p.2 * mollifierAt ρ ε p.2 v)‖)
      (volume : Measure SpaceTime) := hmeas.prod_swap.norm.integral_prod_right'
  refine Integrable.mono' (ha.const_mul (B * ∫ x, |k x|)) hinner
    (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.norm_of_nonneg (integral_nonneg fun p => norm_nonneg _)]
  refine (hnorm v).le.trans ?_
  rw [sq]
  have h0 : 0 ≤ ∫ x, |k x * mollifierAt ρ ε x v| := integral_nonneg fun _ => abs_nonneg _
  calc (∫ x, |k x * mollifierAt ρ ε x v|) * ∫ x, |k x * mollifierAt ρ ε x v|
      ≤ (B * ∫ x, |k x|) * ∫ x, |k x * mollifierAt ρ ε x v| :=
        mul_le_mul_of_nonneg_right (hbd v) h0
    _ = _ := rfl

/-- Double identity: `∫∫ k x k y ∫ M x v M y v = ∫ h²`. -/
theorem treePsi_det_double (hρ : IsMollifier ρ) (hε : 0 < ε) (hk : Integrable k) :
    ∫ x, ∫ y, k x * k y * (∫ v, mollifierAt ρ ε x v * mollifierAt ρ ε y v) =
      ∫ v, treePsiConv ρ ε k v ^ 2 := by
  have hT := triple_integrable hρ hε hk
  have hslice := slice_integrable hρ hε hk
  calc ∫ x, ∫ y, k x * k y * (∫ v, mollifierAt ρ ε x v * mollifierAt ρ ε y v)
      = ∫ x, ∫ y, ∫ v, (k x * mollifierAt ρ ε x v) * (k y * mollifierAt ρ ε y v) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun v => by ring)
    _ = ∫ p : SpaceTime × SpaceTime, ∫ v, (k p.1 * mollifierAt ρ ε p.1 v) *
          (k p.2 * mollifierAt ρ ε p.2 v) := by
        exact (integral_prod (fun p : SpaceTime × SpaceTime => ∫ v,
          (k p.1 * mollifierAt ρ ε p.1 v) * (k p.2 * mollifierAt ρ ε p.2 v))
          hT.integral_prod_left).symm
    _ = ∫ v, ∫ p : SpaceTime × SpaceTime, (k p.1 * mollifierAt ρ ε p.1 v) *
          (k p.2 * mollifierAt ρ ε p.2 v) := integral_integral_swap hT
    _ = ∫ v, treePsiConv ρ ε k v ^ 2 := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        exact prod_mul_sq (fun x => k x * mollifierAt ρ ε x v)

end RegularityStructures.Phi43

end
