/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.QFamilyR4Convolution
public import RegularityStructures.Abstract.QFamilyR4Feller
public import RegularityStructures.Abstract.QFamilyBesovPairing
public import RegularityStructures.Analysis.Parabolic.GeneratorScaling

/-!
# Pairings with rescaled test functions on `ℝ⁴`

For the parabolic semigroup on `ℝ⁴`: support properties of `φ^c_z`, existence of the pairing of a
Besov-type `Q`-family with `φ^c_z` for `φ ∈ B^4` (`tendsto_integral_rescaledTestFunction`), the
uniform bound by `r4PairingConst`, and the identity
`∫_v φ^c_0(v) D_t(x + v) dv = ∫_w q_t(x − w) ⟨D, φ^c_w⟩ dw`
(`integral_rescaledTestFunction_mul_eq`).

Source: [Hai14, Theorem 3.10, (3.3)].
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The constant of the uniform bound `|∫ D_s φ^c_w| ≤ C r4PairingConst α c` for `φ ∈ B^4`:
`16 + 4/(α + 4) · 16 (a + 3b) c^{-4}` (`a, b` the coefficients of the generator). -/
def r4PairingConst (α c : ℝ) : ℝ :=
  16 + 4 / (α + 4) * (16 * (generatorTimeCoeff + 3 * generatorSpaceCoeff) * c ^ (-(4 : ℝ)))

end RegularityStructures

end

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures

attribute [local instance] isAddHaarMeasure_volume_parabolicSpace

theorem parabolicSemigroup_order : parabolicSemigroup.order = 4 :=
  rfl

theorem isSupported_rescaledTestFunction {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4)
    {c : ℝ} (hc : 0 < c) (z : ParabolicSpace) :
    parabolicSemigroup.IsSupported (rescaledTestFunction φ c z) z c :=
  ⟨measurable_rescaledTestFunction hφ c z, integrable_rescaledTestFunction hφ hc z,
    fun _ hy => rescaledTestFunction_eq_zero hφ.2.1 hc hy⟩

theorem isSupported_parabolicGenerator_rescaledTestFunction {φ : ParabolicSpace → ℝ}
    (hφ : φ ∈ testFunctionClass 4) {c : ℝ} (hc : 0 < c) (z : ParabolicSpace) :
    parabolicSemigroup.IsSupported (parabolicGenerator (rescaledTestFunction φ c z)) z c :=
  ⟨measurable_parabolicGenerator_rescaledTestFunction hφ c z,
    integrable_parabolicGenerator_rescaledTestFunction hφ hc z,
    fun _ hy => parabolicGenerator_rescaledTestFunction_eq_zero hφ hc hy⟩

variable {D : ℝ → ParabolicSpace → ℝ}

/-- Existence of the pairing of a Besov-type `Q`-family with `φ^c_z`, `φ ∈ B^4`, any `c > 0`. -/
theorem tendsto_integral_rescaledTestFunction (hD : D ∈ parabolicSemigroup.distributions)
    (hDm : ∀ u, 0 < u → Measurable (D u)) {α C : ℝ} (hα : -4 < α)
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |D u y| ≤ C * u ^ (α / 4)) {φ : ParabolicSpace → ℝ}
    (hφ : φ ∈ testFunctionClass 4) {c : ℝ} (hc : 0 < c) (z : ParabolicSpace) :
    Tendsto (fun s => ∫ y, D s y * rescaledTestFunction φ c z y) (𝓝[>] 0)
      (𝓝 (parabolicSemigroup.pairing D (rescaledTestFunction φ c z))) :=
  RegularisingSemigroup.tendsto_integral_pairing_of_besov parabolicSemigroup_isSymmetric
    parabolicSemigroup_isMetricScale parabolicSemigroup_isJointMeasurable hD hDm hα hb hc
    (isSupported_rescaledTestFunction hφ hc z)
    (isSupported_parabolicGenerator_rescaledTestFunction hφ hc z)
    (isGeneratorPair_rescaledTestFunction hφ hc z)

/-- Uniform bound `|∫ D_s φ^c_z| ≤ C r4PairingConst α c` for `0 < s ≤ 1`. -/
theorem abs_integral_rescaledTestFunction_le (hD : D ∈ parabolicSemigroup.distributions)
    (hDm : ∀ u, 0 < u → Measurable (D u)) {α C : ℝ} (hα : -4 < α)
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |D u y| ≤ C * u ^ (α / 4)) {φ : ParabolicSpace → ℝ}
    (hφ : φ ∈ testFunctionClass 4) {c : ℝ} (hc : 0 < c) (z : ParabolicSpace) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    |∫ y, D s y * rescaledTestFunction φ c z y| ≤ C * r4PairingConst α c := by
  have h := RegularisingSemigroup.abs_integral_le_of_besov parabolicSemigroup_isSymmetric
    parabolicSemigroup_isMetricScale parabolicSemigroup_isJointMeasurable hD hDm hα hb hc
    (isSupported_rescaledTestFunction hφ hc z)
    (isSupported_parabolicGenerator_rescaledTestFunction hφ hc z)
    (isGeneratorPair_rescaledTestFunction hφ hc z) hs
  rw [parabolicSemigroup_order] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_
    (RegularisingSemigroup.nonneg_of_besov (K := parabolicSemigroup) hb z))
  have hq : 0 ≤ 4 / (α + 4) := div_nonneg (by norm_num) (by linarith)
  exact add_le_add (integral_abs_rescaledTestFunction_le hφ hc z)
    (mul_le_mul_of_nonneg_left (integral_abs_parabolicGenerator_rescaledTestFunction_le hφ hc z)
      hq)

/-- **Convolution identity** (Fubini and translation invariance): for `s, t > 0` and a bounded
measurable `D_s`,
`∫_w q_t(x − w) (∫_y D_s(y) ρ(y − w) dy) dw = ∫_v ρ(v) D_{t+s}(x + v) dv`. -/
theorem integral_kernel_mul_integral_eq (hD : D ∈ parabolicSemigroup.distributions) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hDm : Measurable (D s)) {B : ℝ} (hB : ∀ y, |D s y| ≤ B)
    {ρ : ParabolicSpace → ℝ} (hρm : Measurable ρ) (hρ : Integrable ρ) (x : ParabolicSpace) :
    ∫ w, parabolicKernel t (x - w) * ∫ y, D s y * ρ (y - w) =
      ∫ v, ρ v * D (t + s) (x + v) := by
  have hq : Integrable (parabolicKernel t) := integrable_parabolicKernel ht
  have h1 : ∀ w, ∫ y, D s y * ρ (y - w) = ∫ v, D s (v + w) * ρ v := fun w => by
    have := integral_sub_right_eq_self (μ := volume) (fun v => D s (v + w) * ρ v) w
    simp only [sub_add_cancel] at this
    exact this
  have hmeas : Measurable (Function.uncurry fun (w v : ParabolicSpace) =>
      parabolicKernel t (x - w) * (D s (v + w) * ρ v)) :=
    ((measurable_parabolicKernel t).comp (measurable_const.sub measurable_fst)).mul
      ((hDm.comp (measurable_snd.add measurable_fst)).mul (hρm.comp measurable_snd))
  have hint : Integrable (Function.uncurry fun (w v : ParabolicSpace) =>
      parabolicKernel t (x - w) * (D s (v + w) * ρ v)) (volume.prod volume) := by
    refine Integrable.mono' ((hq.comp_sub_left x).norm.mul_prod (hρ.norm.const_mul B))
      hmeas.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    obtain ⟨w, v⟩ := p
    simp only [Function.uncurry_apply_pair]
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [Real.norm_eq_abs]
    exact hB _
  calc ∫ w, parabolicKernel t (x - w) * ∫ y, D s y * ρ (y - w)
      = ∫ w, ∫ v, parabolicKernel t (x - w) * (D s (v + w) * ρ v) := by
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        simp only [h1, integral_const_mul]
    _ = ∫ v, ∫ w, parabolicKernel t (x - w) * (D s (v + w) * ρ v) :=
        integral_integral_swap hint
    _ = ∫ v, ρ v * D (t + s) (x + v) := by
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        have e : ∫ w, parabolicKernel t (x - w) * (D s (v + w) * ρ v) =
            ρ v * ∫ y, parabolicKernel t (x + v - y) * D s y := by
          rw [← integral_const_mul]
          have := integral_add_left_eq_self (μ := volume)
            (fun y => ρ v * (parabolicKernel t (x + v - y) * D s y)) v
          rw [← this]
          refine integral_congr_ae (Eventually.of_forall fun w => ?_)
          ring_nf
        beta_reduce
        rw [e]
        congr 1
        exact parabolicSemigroup.apply_eq hD ht hs (x + v)

theorem rescaledTestFunction_zero_sub (φ : ParabolicSpace → ℝ) (c : ℝ) (y w : ParabolicSpace) :
    rescaledTestFunction φ c 0 (y - w) = rescaledTestFunction φ c w y := by
  simp only [rescaledTestFunction, sub_zero]

/-- **The mollification of `D_t` is the `Q_t`-average of the pairings**: for `t > 0` and `c > 0`,
`∫_v φ^c_0(v) D_t(x + v) dv = ∫_w q_t(x − w) ⟨D, φ^c_w⟩ dw`. -/
theorem integral_rescaledTestFunction_mul_eq (hD : D ∈ parabolicSemigroup.distributions)
    (hDm : ∀ u, 0 < u → Measurable (D u)) {α C : ℝ} (hα : -4 < α)
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |D u y| ≤ C * u ^ (α / 4)) {φ : ParabolicSpace → ℝ}
    (hφ : φ ∈ testFunctionClass 4) {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t)
    (x : ParabolicSpace) :
    ∫ v, rescaledTestFunction φ c 0 v * D t (x + v) =
      ∫ w, parabolicKernel t (x - w) *
        parabolicSemigroup.pairing D (rescaledTestFunction φ c w) := by
  set ρ := rescaledTestFunction φ c 0 with hρdef
  have hρm : Measurable ρ := measurable_rescaledTestFunction hφ c 0
  have hρi : Integrable ρ := integrable_rescaledTestFunction hφ hc 0
  have hDb : ∀ u, 0 < u → ∃ B, ∀ y, |D u y| ≤ B := fun u hu =>
    parabolicSemigroup.exists_bound_of_besov hD hb hu
  obtain ⟨Bt, hBt⟩ := hDb t ht
  have hq : Integrable (parabolicKernel t) := integrable_parabolicKernel ht
  have hR : Tendsto (fun s => ∫ v, ρ v * D (t + s) (x + v)) (𝓝[>] 0)
      (𝓝 (∫ v, ρ v * D t (x + v))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun v => |ρ v| * (parabolicSemigroup.momentConst 0 * Bt)) ?_ ?_
      (hρi.abs.mul_const _) (Eventually.of_forall fun v => ?_)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hρm.mul ((hDm _ (add_pos ht hs)).comp (measurable_const.add measurable_id)))
        |>.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with s hs
      refine Eventually.of_forall fun v => ?_
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [add_comm t s, ← parabolicSemigroup.apply_eq hD hs ht (x + v)]
      exact parabolicSemigroup.abs_apply_le_of_bound hs hBt _
    · exact (RegularisingSemigroup.tendsto_add_nhdsGT parabolicSemigroup_isConservative
        parabolicSemigroup_isStrongFeller hD hDm hDb ht (x + v)).const_mul (ρ v)
  have hL : Tendsto (fun s => ∫ w, parabolicKernel t (x - w) * ∫ y, D s y * ρ (y - w))
      (𝓝[>] 0) (𝓝 (∫ w, parabolicKernel t (x - w) *
        parabolicSemigroup.pairing D (rescaledTestFunction φ c w))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun w => |parabolicKernel t (x - w)| * (C * r4PairingConst α c)) ?_ ?_
      ((hq.comp_sub_left x).abs.mul_const _) (Eventually.of_forall fun w => ?_)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hm : StronglyMeasurable (Function.uncurry fun (w y : ParabolicSpace) =>
          D s y * ρ (y - w)) :=
        (((hDm s hs).comp measurable_snd).mul
          (hρm.comp (measurable_snd.sub measurable_fst))).stronglyMeasurable
      exact (((measurable_parabolicKernel t).comp (measurable_const.sub measurable_id)).mul
        hm.integral_prod_right.measurable).aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT one_pos] with s hs
      refine Eventually.of_forall fun w => ?_
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      simp only [hρdef, rescaledTestFunction_zero_sub]
      exact abs_integral_rescaledTestFunction_le hD hDm hα hb hφ hc w hs
    · simp only [hρdef, rescaledTestFunction_zero_sub]
      exact (tendsto_integral_rescaledTestFunction hD hDm hα hb hφ hc w).const_mul _
  have heq : (fun s => ∫ w, parabolicKernel t (x - w) * ∫ y, D s y * ρ (y - w)) =ᶠ[𝓝[>] 0]
      fun s => ∫ v, ρ v * D (t + s) (x + v) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    obtain ⟨Bs, hBs⟩ := hDb s hs
    exact integral_kernel_mul_integral_eq hD hs ht (hDm s hs) hBs hρm hρi x
  exact tendsto_nhds_unique hR (hL.congr' heq)

end RegularityStructures

end
