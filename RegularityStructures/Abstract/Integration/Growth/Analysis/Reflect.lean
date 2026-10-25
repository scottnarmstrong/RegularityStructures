/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.PairingGrowth
public import RegularityStructures.Analysis.Heat.Schauder.TaylorPairing
public import RegularityStructures.Analysis.Heat.Schauder.Reflect

/-!
# Pairing against a reflected test function, local order with polynomial growth

Growth versions of the bounds for the pairing of a distribution of local order with a reflected
test function. For `Λ` with
`IsLocalOrderGrowth Λ x γ A C q` and test functions supported in the ball of radius `R` about `x`,
the factor `(1 + d)^q` is at most `(1 + R)^q`; this is the only change in the estimates
(`LocalBall.of_growth`).

* `LocalBall.exists_tendsto_abs_le_of_time`: ball version of
  `LocalData.exists_tendsto_abs_le_of_time`;
* `tendsto_and_abs_pairing_reflect_le_centre_ball`, `..._growth`: pairing with `h (c - ·)`;
* `abs_pairing_reflect_le_of_localOrderGrowth`: pairing with `h (x - ·)`, `h` supported in the
  ball of radius `lam ≤ 1`.

Source: [Hai14] = arXiv:1303.5113v4, Theorem 3.10, Lemmas 5.18, 5.19.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}

theorem LocalBall.exists_tendsto_abs_le_of_time [SFinite μ] (hK : K.IsSymmetric)
    (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ}
    {A : Finset ℝ} {C R : ℝ} (hΛ : K.LocalBall Λ x₀ γ A C R) (hA : ∀ a ∈ A, -K.order < a)
    {φ ψ : E → ℝ} {B₀ B₁ T : ℝ} (hR : 0 < R) (hB₁ : 0 ≤ B₁) (hφ : K.IsSupported φ x₀ R)
    (hψ : K.IsSupported ψ x₀ R) (hφ1 : ∫ y, |φ y| ∂μ ≤ B₀)
    (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * R ^ (-K.order)) (hgen : K.IsGeneratorPair φ ψ)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    ∃ L : ℝ, Tendsto (fun s => ∫ y, Λ s y * φ y ∂μ) (𝓝[>] 0) (𝓝 L) ∧
      |L| ≤ C * (∑ a ∈ A, T ^ (a / K.order) * R ^ (γ - a)) * B₀ +
        K.incrBound A γ R (C * (B₁ * R ^ (-K.order))) T := by
  obtain ⟨L, hL⟩ := hΛ.exists_tendsto_integral hK hJ hA hR hB₁ hφ hψ hgen hψ1
  refine ⟨L, hL, ?_⟩
  have hTm : T ∈ Set.Ioc (0 : ℝ) 1 := ⟨hT, hT1⟩
  have h1 := hΛ.abs_integral_mul_le hTm hφ
  have hS : 0 ≤ C * ∑ a ∈ A, T ^ (a / K.order) * R ^ (γ - a) :=
    mul_nonneg hΛ.nonneg (Finset.sum_nonneg fun a _ =>
      mul_nonneg (Real.rpow_nonneg hT.le _) (Real.rpow_nonneg hR.le _))
  have hb : ∀ s ∈ Set.Ioo 0 T, |∫ y, Λ s y * φ y ∂μ| ≤
      C * (∑ a ∈ A, T ^ (a / K.order) * R ^ (γ - a)) * B₀ +
        K.incrBound A γ R (C * (B₁ * R ^ (-K.order))) T := by
    intro s hs
    have h2 := hΛ.abs_integral_sub_le hK hJ hA hR hB₁ hφ hψ hgen hψ1 hs.1 hs.2 hT1
    calc _ = |(∫ y, Λ T y * φ y ∂μ) - ((∫ y, Λ T y * φ y ∂μ) - ∫ y, Λ s y * φ y ∂μ)| := by
          congr 1; ring
      _ ≤ |∫ y, Λ T y * φ y ∂μ| + |(∫ y, Λ T y * φ y ∂μ) - ∫ y, Λ s y * φ y ∂μ| :=
          abs_sub _ _
      _ ≤ _ := add_le_add (h1.trans (mul_le_mul_of_nonneg_left hφ1 hS)) h2
  exact le_of_tendsto hL.abs (Filter.mem_of_superset (Ioo_mem_nhdsGT hT) hb)

theorem LocalBall.mono_const {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C C' lam : ℝ}
    (h : K.LocalBall Λ x₀ γ A C lam) (hCC : C ≤ C') (hlam : 0 ≤ lam) :
    K.LocalBall Λ x₀ γ A C' lam where
  mem := h.mem
  meas := h.meas
  nonneg := h.nonneg.trans hCC
  le := h.le
  ball u hu y hy := by
    refine (h.ball u hu y hy).trans (mul_le_mul_of_nonneg_right hCC ?_)
    exact Finset.sum_nonneg fun a _ => mul_nonneg (Real.rpow_nonneg hu.1.le _)
      (Real.rpow_nonneg hlam _)
  kernel_int := h.kernel_int

/-- `LocalBall` of radius `lam ≤ Rm` for a distribution of local order with growth `q`, with the
constant `C (1 + Rm)^q`. -/
theorem LocalBall.of_growth_le (hd : K.IsMetricScale) {Λ : ℝ → E → ℝ} {x₀ : E} {γ q : ℝ}
    {A : Finset ℝ} {C : ℝ} (hΛ : Λ ∈ K.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hA : ∀ a ∈ A, a ≤ γ)
    (hloc : K.IsLocalOrderGrowth Λ x₀ γ A C q) {lam Rm : ℝ} (hlam : 0 ≤ lam) (hR : lam ≤ Rm) :
    K.LocalBall Λ x₀ γ A (C * (1 + Rm) ^ q) lam :=
  (LocalBall.of_growth hd hΛ hΛm hC hq hA hloc hlam).mono_const
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) hq) hC) hlam

end RegularityStructures.RegularisingSemigroup

namespace RegularityStructures

theorem tendsto_and_abs_pairing_reflect_le_centre_ball {Λ : ℝ → ParabolicSpace → ℝ}
    {x c : ParabolicSpace} {γ C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ)
    {h : ParabolicSpace → ℝ} (hh : ContDiff ℝ ∞ h) {lam B₀ B₁ : ℝ} (hlam : 0 < lam)
    (hlam2 : lam ≤ 2) (hball : parabolicSemigroup.LocalBall Λ x γ A C (lam + parabolicNorm (c - x))) (hs : ∀ w, lam < parabolicNorm w → h w = 0)
    (h0 : ∫ w, |h w| ≤ B₀) (h1 : ∫ w, |parabolicGenerator h w| ≤ B₁ * lam ^ (-(4 : ℝ))) :
    Filter.Tendsto (fun s => ∫ y, Λ s y * h (c - y)) (nhdsWithin 0 (Ioi 0))
        (nhds (parabolicSemigroup.pairing Λ (fun z => h (c - z)))) ∧
      |parabolicSemigroup.pairing Λ (fun z => h (c - z))| ≤
        C * (∑ a ∈ A, pairingWeight a * (lam ^ a * (lam + parabolicNorm (c - x)) ^ (γ - a))) *
          (B₀ + B₁) := by
  set d := parabolicNorm (c - x) with hd
  have hd0 : 0 ≤ d := parabolicNorm_nonneg _
  set R := lam + d with hR
  have hR0 : 0 < R := by linarith
  have hB₀ : 0 ≤ B₀ := (integral_nonneg fun _ => abs_nonneg _).trans h0
  have hB₁ : 0 ≤ B₁ := by
    have h2 : 0 ≤ B₁ * lam ^ (-(4 : ℝ)) := (integral_nonneg fun _ => abs_nonneg _).trans h1
    exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hlam _)).1 h2
  have hφ : ContDiff ℝ ∞ (fun y => h (c - y)) := hh.comp (contDiff_const.sub contDiff_id)
  have hcs : ∀ g : ParabolicSpace → ℝ, (∀ w, lam < parabolicNorm w → g w = 0) →
      ∀ y, R < parabolicNorm (y - x) → g (c - y) = 0 := by
    intro g hg y hy
    refine hg _ ?_
    have h3 : parabolicNorm (y - x) ≤ parabolicNorm (y - c) + parabolicNorm (c - x) := by
      simpa using parabolicNorm_add_le (y - c) (c - x)
    rw [parabolicNorm_sub_comm]
    linarith
  have hcsup : HasCompactSupport (fun y => h (c - y)) :=
    hasCompactSupport_of_eq_zero hR0 x (hcs h hs)
  have hLcont : Continuous (parabolicGenerator (fun y => h (c - y))) :=
    continuous_parabolicGenerator hφ
  have hLeq : parabolicGenerator (fun y => h (c - y)) =
      fun y => parabolicGenerator h (c - y) := funext (parabolicGenerator_sub_left hh c)
  have hLs : ∀ y, R < parabolicNorm (y - x) →
      parabolicGenerator (fun y => h (c - y)) y = 0 := by
    intro y hy
    rw [hLeq]
    exact hcs (parabolicGenerator h) (fun w hw => parabolicGenerator_eq_zero_of_lt hs hw) y hy
  have hLsup : HasCompactSupport (parabolicGenerator (fun y => h (c - y))) :=
    hasCompactSupport_of_eq_zero hR0 x hLs
  have hgen := parabolicSemigroup_isGeneratorPair hφ hcsup
  have hA' : ∀ a ∈ A, -parabolicSemigroup.order < a := fun a ha => by
    simpa [parabolicSemigroup] using (hA a ha).1
  set B₁' := B₁ * lam ^ (-(4 : ℝ)) * R ^ (4 : ℝ) with hB₁'
  have hB₁'0 : 0 ≤ B₁' := by
    exact mul_nonneg (mul_nonneg hB₁ (Real.rpow_nonneg hlam.le (-(4 : ℝ))))
      (Real.rpow_nonneg hR0.le (4 : ℝ))
  have hRR : R ^ (4 : ℝ) * R ^ (-(4 : ℝ)) = 1 := by
    rw [← Real.rpow_add hR0]; simp
  set T : ℝ := (lam / 2) ^ (4 : ℝ) with hT
  have hT0 : 0 < T := Real.rpow_pos_of_pos (by positivity) _
  have hT1 : T ≤ 1 := Real.rpow_le_one (by positivity) (by linarith) (by norm_num)
  have hC : 0 ≤ C := hball.nonneg
  obtain ⟨L, hL, key⟩ := RegularisingSemigroup.LocalBall.exists_tendsto_abs_le_of_time
    (K := parabolicSemigroup) parabolicSemigroup_isSymmetric
    parabolicSemigroup_isJointMeasurable hball hA'
    (φ := fun y => h (c - y)) (ψ := parabolicGenerator (fun y => h (c - y))) (R := R)
    (B₀ := B₀) (B₁ := B₁') (T := T) hR0 hB₁'0
    ⟨hφ.continuous.measurable, hφ.continuous.integrable_of_hasCompactSupport hcsup,
      hcs h hs⟩
    ⟨hLcont.measurable, hLcont.integrable_of_hasCompactSupport hLsup, hLs⟩
    (by rw [integral_abs_sub_left]; exact h0)
    (by
      rw [hLeq]
      have := integral_abs_sub_left (parabolicGenerator h) c
      simp only [parabolicSemigroup]
      rw [this]
      refine h1.trans (le_of_eq ?_)
      rw [hB₁', mul_assoc (B₁ * lam ^ (-(4 : ℝ))), hRR, mul_one])
    hgen hT0 hT1
  have hpair : parabolicSemigroup.pairing Λ (fun z => h (c - z)) = L :=
    parabolicSemigroup.pairing_eq_of_tendsto hL
  rw [hpair]
  refine ⟨hL, key.trans ?_⟩
  have hord : parabolicSemigroup.order = 4 := rfl
  simp only [hord, RegularisingSemigroup.incrBound]
  have hβ : C * (B₁' * R ^ (-(4 : ℝ))) = C * (B₁ * lam ^ (-(4 : ℝ))) := by
    rw [hB₁', mul_assoc (B₁ * lam ^ (-(4 : ℝ))), hRR, mul_one]
  rw [hβ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    Finset.sum_mul]
  refine Finset.sum_le_sum fun a ha => ?_
  have hlt : -4 < a := (hA a ha).1
  have h1' : T ^ (a / 4) = (lam / 2) ^ a := timeTerm_eq hlam
  have h2' := incrTerm_eq hlam hlt
  have hrw : C * (B₁ * lam ^ (-(4 : ℝ))) * (T ^ (a / 4 + 1) / (a / 4 + 1) * R ^ (γ - a)) =
      C * B₁ * ((lam / 2) ^ a * R ^ (γ - a) * ((1 / 16) * (4 / (a + 4)))) := by
    have : C * (B₁ * lam ^ (-(4 : ℝ))) * (T ^ (a / 4 + 1) / (a / 4 + 1) * R ^ (γ - a)) =
        C * B₁ * ((T ^ (a / 4 + 1) / (a / 4 + 1) * lam ^ (-(4 : ℝ))) * R ^ (γ - a)) := by ring
    rw [this, hT, h2']
    ring
  have hpw : pairingWeight a * (lam ^ a * R ^ (γ - a)) = (1 + 4 / (a + 4)) *
      ((lam / 2) ^ a * R ^ (γ - a)) := by
    rw [pairingWeight, Real.div_rpow hlam.le (by norm_num), Real.rpow_neg (by norm_num)]
    have : (2 : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) a).ne'
    field_simp
  rw [hrw, hpw, h1']
  have hP : 0 ≤ (lam / 2) ^ a * R ^ (γ - a) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hR0.le _)
  have hv : 0 ≤ 4 / (a + 4) := div_nonneg (by norm_num) (by linarith)
  have := alg_term_le hC hP hB₀ hB₁ hv
  refine le_trans (le_of_eq ?_) this
  ring

/-- Pairing with a reflected function supported in the ball of radius `lam ≤ 1` about `x`, for `Λ`
of local order `γ` at `x` with growth `q`. -/
theorem abs_pairing_reflect_le_of_localOrderGrowth {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {x : ParabolicSpace} {γ C q : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hloc : parabolicSemigroup.IsLocalOrderGrowth Λ x γ A C q)
    {h : ParabolicSpace → ℝ} (hh : ContDiff ℝ ∞ h) {lam B₀ B₁ : ℝ} (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hs : ∀ w, lam < parabolicNorm w → h w = 0)
    (h0 : ∫ w, |h w| ≤ B₀) (h1 : ∫ w, |parabolicGenerator h w| ≤ B₁ * lam ^ (-(4 : ℝ))) :
    |parabolicSemigroup.pairing Λ (fun y => h (x - y))| ≤
      2 ^ q * C * parabolicSemigroup.pairingConst A * (B₀ + B₁) * lam ^ γ := by
  have hφ : ContDiff ℝ ∞ (fun y => h (x - y)) := hh.comp (contDiff_const.sub contDiff_id)
  have hcs : ∀ g : ParabolicSpace → ℝ, (∀ w, lam < parabolicNorm w → g w = 0) →
      ∀ y, lam < parabolicNorm (y - x) → g (x - y) = 0 := fun g hg y hy => by
    refine hg _ ?_
    rwa [parabolicNorm_sub_comm]
  have hcsup : HasCompactSupport (fun y => h (x - y)) :=
    hasCompactSupport_of_eq_zero hlam x (hcs h hs)
  have hLcont : Continuous (parabolicGenerator (fun y => h (x - y))) :=
    continuous_parabolicGenerator hφ
  have hLeq : parabolicGenerator (fun y => h (x - y)) =
      fun y => parabolicGenerator h (x - y) := funext (parabolicGenerator_sub_left hh x)
  have hLs : ∀ y, lam < parabolicNorm (y - x) → parabolicGenerator (fun y => h (x - y)) y = 0 := by
    intro y hy
    rw [hLeq]
    exact parabolicGenerator_eq_zero_of_lt hs (by rwa [parabolicNorm_sub_comm])
  have hLsup : HasCompactSupport (parabolicGenerator (fun y => h (x - y))) :=
    hasCompactSupport_of_eq_zero hlam x hLs
  have hgen := parabolicSemigroup_isGeneratorPair hφ hcsup
  have hA' : ∀ a ∈ A, -parabolicSemigroup.order < a ∧ a ≤ γ := fun a ha => by
    refine ⟨?_, (hA a ha).2⟩
    simpa [parabolicSemigroup] using (hA a ha).1
  exact parabolicSemigroup.abs_pairing_le_of_growth parabolicSemigroup_isSymmetric
    parabolicSemigroup_isMetricScale parabolicSemigroup_isJointMeasurable hΛ hΛm hA' hC hq hloc
    (φ := fun y => h (x - y)) (ψ := parabolicGenerator (fun y => h (x - y))) (lam := lam)
    (B₀ := B₀) (B₁ := B₁) hlam hlam1 hφ.continuous.measurable hLcont.measurable
    (hφ.continuous.integrable_of_hasCompactSupport hcsup)
    (hLcont.integrable_of_hasCompactSupport hLsup) (fun y hy => hcs h hs y hy) hLs
    (by rw [integral_abs_sub_left]; exact h0)
    (by
      rw [hLeq]
      have := integral_abs_sub_left (parabolicGenerator h) x
      simp only [parabolicSemigroup]
      rw [this]; exact h1)
    hgen

end RegularityStructures

end
