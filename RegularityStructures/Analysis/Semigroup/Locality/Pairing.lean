/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Main

/-!
# The test-function bound for a distribution that is of local order only on a ball

Generalisation of `abs_pairing_le` / `abs_pairing_le_of_growth` to a `Q`-distribution `Λ` that
satisfies the local-order bound
`|Λ_u(y)| ≤ C ∑_{a ∈ A} u^{a/ℓ} d(y, x₀)^{γ - a}` only for `d(y, x₀) ≤ R`, and a crude bound
`|Λ_u(y)| ≤ C' u^{β/ℓ} (1 + d(y, x₀))^q` for all `y` (`0 < u ≤ 1`).

For `λ ≤ min(1, R)` the test function is supported in `{d(·, x₀) ≤ λ} ⊆ {d(·, x₀) ≤ R}`, so the
crude bound enters only through the finiteness of `∫ |Q_v(y, z)| |Λ_s(z)| dz` (`LocalBall`),
which is needed for the existence of the pairing. The resulting estimate

`|⟨Λ, φ⟩| ≤ C · pairingConst A · (B₀ + B₁) · λ^γ`

has *no* contribution from `C'`: the constants depend only on `K`, `A`, `C`, and the outside of
the ball is not seen at all (this is stronger than the form
`C c_A λ^γ + C' c_k (λ/R)^k`, which follows from it since `C' c_k (λ/R)^k ≥ 0`).

* `LocalBall.of_local`: `LocalBall Λ x₀ γ A C λ` from the two bounds;
* `exists_tendsto_abs_le_of_local`, `tendsto_integral_pairing_of_local`,
  `abs_pairing_le_of_local`: the pairing bound.

Source: [Hai14] = arXiv:1303.5113v4, Theorem 3.10, (3.3).
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}

/-- The finiteness of `∫ |Q_v(y, z)| |Λ_s(z)| dz` from the crude bound alone. -/
theorem kernel_int_of_crude (hd : K.IsMetricScale) {Λ : ℝ → E → ℝ} {x₀ : E} {q C' β : ℝ}
    (hC' : 0 ≤ C') (hq : 0 ≤ q)
    (hcrude : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y,
      |Λ u y| ≤ C' * u ^ (β / K.order) * (1 + K.scaleDist y x₀) ^ q)
    {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) {lam : ℝ} (hlam : 0 ≤ lam) (h₀ : ℝ) :
    ∃ W : ℝ, ∀ v ∈ Set.Ioc (0 : ℝ) h₀, ∀ y, K.scaleDist y x₀ ≤ lam →
      ∫ z, |K.kernel v y z| * |Λ s z| ∂μ ≤ W := by
  set c : ℝ := C' * s ^ (β / K.order) * 2 ^ q with hc
  have hc0 : 0 ≤ c :=
    mul_nonneg (mul_nonneg hC' (Real.rpow_nonneg hs.1.le _)) (Real.rpow_nonneg (by norm_num) _)
  refine ⟨c * ((1 + lam) ^ q * K.momentConst 0) + c * (K.momentConst q * h₀ ^ (q / K.order)), ?_⟩
  intro v hv y hy
  have hv0 : 0 < v := hv.1
  have hb : 1 ≤ 1 + lam := by linarith
  have hf : Integrable (fun z => |K.kernel v y z|) μ := (K.integrable_kernel hv0 y).abs
  have hg : Integrable (fun z => |K.kernel v y z| * K.scaleDist z y ^ q) μ :=
    K.integrable_moment hv0 hq y
  have hD : Integrable (fun z => c * ((1 + lam) ^ q * |K.kernel v y z|) +
      c * (|K.kernel v y z| * K.scaleDist z y ^ q)) μ :=
    ((hf.const_mul _).const_mul _).add (hg.const_mul _)
  have hle := integral_mono_of_nonneg (f := fun z => |K.kernel v y z| * |Λ s z|)
    (Filter.Eventually.of_forall fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _)) hD (Filter.Eventually.of_forall fun z => ?_)
  · refine hle.trans ?_
    rw [integral_add ((hf.const_mul _).const_mul _) (hg.const_mul _), integral_const_mul,
      integral_const_mul, integral_const_mul]
    have e1 : ∫ z, |K.kernel v y z| * K.scaleDist z y ^ q ∂μ ≤
        K.momentConst q * h₀ ^ (q / K.order) :=
      (K.moment_le hv0 hq y).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hv0.le hv.2 (div_nonneg hq K.order_pos.le))
        (K.momentConst_nonneg _))
    have e2 : ∫ z, |K.kernel v y z| ∂μ ≤ K.momentConst 0 := K.integral_abs_kernel_le hv0 y
    have hb0 : 0 ≤ (1 + lam) ^ q := Real.rpow_nonneg (by linarith) _
    have h5 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e2 hb0) hc0
    have h6 := mul_le_mul_of_nonneg_left e1 hc0
    linarith
  · dsimp only
    have hDw : K.scaleDist z x₀ ≤ K.scaleDist z y + (1 + lam) - 1 := by
      have := hd.triangle z y x₀
      linarith
    have h1 := rpow_mul_rpow_le (K.scaleDist_nonneg z x₀) (K.scaleDist_nonneg z y) hb hq
      le_rfl hDw
    simp only [Real.rpow_zero, mul_one, add_zero] at h1
    calc |K.kernel v y z| * |Λ s z|
        ≤ |K.kernel v y z| * (C' * s ^ (β / K.order) * (1 + K.scaleDist z x₀) ^ q) :=
          mul_le_mul_of_nonneg_left (hcrude s hs z) (abs_nonneg _)
      _ ≤ |K.kernel v y z| * (C' * s ^ (β / K.order) *
          (2 ^ q * ((1 + lam) ^ q + K.scaleDist z y ^ q))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1
            (mul_nonneg hC' (Real.rpow_nonneg hs.1.le _))) (abs_nonneg _)
      _ = _ := by rw [hc]; ring

/-- `LocalBall` from the local-order bound on `{d(·, x₀) ≤ R}` and a crude polynomial bound
everywhere, for `lam ≤ R`. The `LocalBall` constant is `C`, with no growth factor. -/
theorem LocalBall.of_local (hd : K.IsMetricScale) {Λ : ℝ → E → ℝ} {x₀ : E} {γ q C' β R : ℝ}
    {A : Finset ℝ} {C : ℝ} (hΛ : Λ ∈ K.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hq : 0 ≤ q) (hA : ∀ a ∈ A, a ≤ γ)
    (hloc : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y, K.scaleDist y x₀ ≤ R →
      |Λ u y| ≤ C * ∑ a ∈ A, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a))
    (hcrude : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y,
      |Λ u y| ≤ C' * u ^ (β / K.order) * (1 + K.scaleDist y x₀) ^ q)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlamR : lam ≤ R) :
    K.LocalBall Λ x₀ γ A C lam where
  mem := hΛ
  meas := hΛm
  nonneg := hC
  le := hA
  kernel_int := fun _ hs h₀ => kernel_int_of_crude hd hC' hq hcrude hs hlam h₀
  ball u hu y hy := by
    refine (hloc u hu y (hy.trans hlamR)).trans ?_
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a ha =>
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (K.scaleDist_nonneg _ _) hy
        (sub_nonneg.2 (hA a ha))) (Real.rpow_nonneg hu.1.le _)) hC

/-- Existence of the pairing and the test-function bound for a distribution that is of local
order `γ` only on `{d(·, x₀) ≤ R}` and polynomially bounded elsewhere: for `φ, ψ = Lφ` supported
in the ball of radius `lam ≤ min(1, R)`,
`|⟨Λ, φ⟩| ≤ C · pairingConst A · (B₀ + B₁) · lam^γ`. -/
theorem exists_tendsto_abs_le_of_local [SFinite μ] (hK : K.IsSymmetric) (hd : K.IsMetricScale)
    (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {x₀ : E} {γ q C' β R : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, -K.order < a ∧ a ≤ γ) {C : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (hq : 0 ≤ q)
    (hloc : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y, K.scaleDist y x₀ ≤ R →
      |Λ u y| ≤ C * ∑ a ∈ A, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a))
    (hcrude : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y,
      |Λ u y| ≤ C' * u ^ (β / K.order) * (1 + K.scaleDist y x₀) ^ q)
    {φ ψ : E → ℝ} {lam B₀ B₁ : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hlamR : lam ≤ R)
    (hφm : Measurable φ) (hψm : Measurable ψ)
    (hφi : Integrable φ μ) (hψi : Integrable ψ μ)
    (hφs : ∀ y, lam < K.scaleDist y x₀ → φ y = 0) (hψs : ∀ y, lam < K.scaleDist y x₀ → ψ y = 0)
    (hφ1 : ∫ y, |φ y| ∂μ ≤ B₀) (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * lam ^ (-K.order))
    (hgen : K.IsGeneratorPair φ ψ) :
    ∃ L : ℝ, Tendsto (fun s => ∫ y, Λ s y * φ y ∂μ) (𝓝[>] 0) (𝓝 L) ∧
      |L| ≤ C * K.pairingConst A * (B₀ + B₁) * lam ^ γ :=
  (LocalBall.of_local hd hΛ hΛm hC hC' hq (fun a ha => (hA a ha).2) hloc hcrude hlam.le
    hlamR).exists_tendsto_abs_le hK hJ (fun a ha => (hA a ha).1) hlam hlam1
    ⟨hφm, hφi, hφs⟩ ⟨hψm, hψi, hψs⟩ hφ1 hψ1 hgen

/-- The pairing exists for a distribution of local order only on a ball. -/
theorem tendsto_integral_pairing_of_local [SFinite μ] (hK : K.IsSymmetric) (hd : K.IsMetricScale)
    (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {x₀ : E} {γ q C' β R : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, -K.order < a ∧ a ≤ γ) {C : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (hq : 0 ≤ q)
    (hloc : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y, K.scaleDist y x₀ ≤ R →
      |Λ u y| ≤ C * ∑ a ∈ A, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a))
    (hcrude : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y,
      |Λ u y| ≤ C' * u ^ (β / K.order) * (1 + K.scaleDist y x₀) ^ q)
    {φ ψ : E → ℝ} {lam B₀ B₁ : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hlamR : lam ≤ R)
    (hφm : Measurable φ) (hψm : Measurable ψ)
    (hφi : Integrable φ μ) (hψi : Integrable ψ μ)
    (hφs : ∀ y, lam < K.scaleDist y x₀ → φ y = 0) (hψs : ∀ y, lam < K.scaleDist y x₀ → ψ y = 0)
    (hφ1 : ∫ y, |φ y| ∂μ ≤ B₀) (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * lam ^ (-K.order))
    (hgen : K.IsGeneratorPair φ ψ) :
    Tendsto (fun s => ∫ y, Λ s y * φ y ∂μ) (𝓝[>] 0) (𝓝 (K.pairing Λ φ)) := by
  obtain ⟨L, hL, -⟩ := exists_tendsto_abs_le_of_local hK hd hJ hΛ hΛm hA hC hC' hq hloc hcrude
    hlam hlam1 hlamR hφm hψm hφi hψi hφs hψs hφ1 hψ1 hgen
  rwa [K.pairing_eq_of_tendsto hL]

/-- **Test-function bound for local data on a ball**:
`|⟨Λ, φ⟩| ≤ C · pairingConst A · (B₀ + B₁) · lam^γ` for `lam ≤ min(1, R)`
([Hai14, Theorem 3.10, (3.3)]). The constant depends only on `K` (through `ℓ`), `A` and `C`. -/
theorem abs_pairing_le_of_local [SFinite μ] (hK : K.IsSymmetric) (hd : K.IsMetricScale)
    (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {x₀ : E} {γ q C' β R : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, -K.order < a ∧ a ≤ γ) {C : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (hq : 0 ≤ q)
    (hloc : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y, K.scaleDist y x₀ ≤ R →
      |Λ u y| ≤ C * ∑ a ∈ A, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a))
    (hcrude : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y,
      |Λ u y| ≤ C' * u ^ (β / K.order) * (1 + K.scaleDist y x₀) ^ q)
    {φ ψ : E → ℝ} {lam B₀ B₁ : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hlamR : lam ≤ R)
    (hφm : Measurable φ) (hψm : Measurable ψ)
    (hφi : Integrable φ μ) (hψi : Integrable ψ μ)
    (hφs : ∀ y, lam < K.scaleDist y x₀ → φ y = 0) (hψs : ∀ y, lam < K.scaleDist y x₀ → ψ y = 0)
    (hφ1 : ∫ y, |φ y| ∂μ ≤ B₀) (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * lam ^ (-K.order))
    (hgen : K.IsGeneratorPair φ ψ) :
    |K.pairing Λ φ| ≤ C * K.pairingConst A * (B₀ + B₁) * lam ^ γ := by
  obtain ⟨L, hL, hb⟩ := exists_tendsto_abs_le_of_local hK hd hJ hΛ hΛm hA hC hC' hq hloc hcrude
    hlam hlam1 hlamR hφm hψm hφi hψi hφs hψs hφ1 hψ1 hgen
  rwa [K.pairing_eq_of_tendsto hL]

end RegularityStructures.RegularisingSemigroup

end
