/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiLatticeKernel
public import Phi43.BPHZ.PositivePiMomentIPsiBound
import Mathlib.Tactic

/-!
# Pathwise reduction of `∫_{ℝ⁴} Q_t(x, y) v₁(x, y) Φ(y) dy` to `ℝ × T³`

For `Ψ` continuous and `u` with finite weight sum,
`∑_n Q_n(u) ∫ T_n(u, w) Ψ(w) dw = g(u) ∫ k(u, w) Ψ(w) dw`
(`tsum_latticeQ_mul_integral`), and for an integrable `ℝ⁴`-integrand
`Q(y) (v₁(x, y) Φ(proj y))` the integral over `ℝ⁴` equals
`∫_{ℝ×T³} ((∫ k(u, w) Ψ(w) dw) Φ(u)) g(u) du` (`integral_semigroup_mul_iPsi_field_eq`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- Interchange of the lattice sum with the `w`-integral. -/
theorem tsum_latticeQ_mul_integral {N : ℕ} {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ (x' : SpaceTime) (t' : ℝ) (a : Fin 3 → ℝ),
      ∫ w, |hairerTaylorKernel N x' t' a w| ≤ L * (1 + ∑ i, |a i|))
    {Ψ : SpaceTime → ℝ} (hΨ : Continuous Ψ) (t : ℝ) (x : ParabolicSpace) {u : SpaceTime}
    (hu : latticeWeightSum t x u < ⊤) :
    ∑' n : Fin 3 → ℤ, parabolicSemigroup.kernel t x (latticeLift u n) *
        ∫ w, hairerTaylorKernelAt N x (latticeLift u n) w * Ψ w =
      (∫ w, latticeK N t x u w * Ψ w) * latticeG t x u := by
  set T : ℝ := |u.1| + |x.1| + 1 with hT
  set Kc : Set SpaceTime := Set.Icc (-T) T ×ˢ (Set.univ : Set Torus3) with hKc
  have hKcc : IsCompact Kc := isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hKcc.exists_bound_of_continuousOn hΨ.continuousOn
  set M : ℝ := max C 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hΨM : ∀ w ∈ Kc, |Ψ w| ≤ M := fun w hw => by
    have := hC w hw
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hsupp : ∀ n w, hairerTaylorKernelAt N x (latticeLift u n) w ≠ 0 → w ∈ Kc := by
    intro n w hw
    refine ⟨?_, Set.mem_univ _⟩
    have htime := hairerTaylorKernel_ne_zero_time N hw
    have e : (spaceTimeProj x).1 + ((latticeLift u n).1 - x.1) - w.1 = u.1 - w.1 := by
      simp [spaceTimeProj, latticeLift]
    rw [e] at htime
    have h1 := le_abs_self u.1
    have h2 := neg_abs_le u.1
    have h3 := le_abs_self x.1
    have h4 := neg_abs_le x.1
    rcases htime with h | h
    · have h' := abs_le.1 h
      have := abs_nonneg x.1
      constructor <;> linarith
    · change |x.1 - w.1| ≤ 1 at h
      have h' := abs_le.1 h
      have := abs_nonneg u.1
      constructor <;> linarith
  have hTi : ∀ n, Integrable (hairerTaylorKernelAt N x (latticeLift u n)) := fun n =>
    integrable_hairerTaylorKernel N _ _ _
  have hTΨ : ∀ n, Integrable fun w => hairerTaylorKernelAt N x (latticeLift u n) w * Ψ w := by
    intro n
    refine Integrable.mono' ((hTi n).abs.mul_const M)
      (((measurable_uncurry_hairerTaylorKernelAt N x).comp
        (f := fun w : SpaceTime => (latticeLift u n, w))
        (measurable_const.prodMk measurable_id)).mul hΨ.measurable).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hw : hairerTaylorKernelAt N x (latticeLift u n) w = 0
    · simp [hw]
    · exact mul_le_mul_of_nonneg_left (hΨM w (hsupp n w hw)) (abs_nonneg _)
  obtain ⟨hsum, hG⟩ := summable_latticeWeight hu
  set F : (Fin 3 → ℤ) → SpaceTime → ℝ := fun n w => parabolicSemigroup.kernel t x
    (latticeLift u n) * (hairerTaylorKernelAt N x (latticeLift u n) w * Ψ w) with hF
  have hFi : ∀ n, Integrable (F n) := fun n => (hTΨ n).const_mul _
  have hbd : ∀ n, ∫ w, ‖F n w‖ ≤ M * L * (|parabolicSemigroup.kernel t x (latticeLift u n)| *
      (1 + parabolicNorm (latticeLift u n - x))) := by
    intro n
    set y := latticeLift u n with hy
    have h1 : ∫ w, ‖F n w‖ = |parabolicSemigroup.kernel t x y| *
        ∫ w, |hairerTaylorKernelAt N x y w * Ψ w| := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      show ‖F n w‖ = |parabolicSemigroup.kernel t x y| * |hairerTaylorKernelAt N x y w * Ψ w|
      rw [Real.norm_eq_abs, abs_mul]
    have h2 : ∫ w, |hairerTaylorKernelAt N x y w * Ψ w| ≤ ∫ w, |hairerTaylorKernelAt N x y w| * M := by
      refine integral_mono (hTΨ n).abs ((hTi n).abs.mul_const M) fun w => ?_
      rw [abs_mul]
      by_cases hw : hairerTaylorKernelAt N x y w = 0
      · simp [hw]
      · exact mul_le_mul_of_nonneg_left (hΨM w (hsupp n w hw)) (abs_nonneg _)
    have h3 : ∫ w, |hairerTaylorKernelAt N x y w| ≤ L * (1 + parabolicNorm (y - x)) := by
      refine (hL _ _ _).trans (mul_le_mul_of_nonneg_left ?_ hL0)
      have hs := sum_abs_le_parabolicNorm (y - x)
      simp only [Prod.snd_sub] at hs
      linarith
    rw [h1]
    calc |parabolicSemigroup.kernel t x y| * ∫ w, |hairerTaylorKernelAt N x y w * Ψ w|
        ≤ |parabolicSemigroup.kernel t x y| * ∫ w, |hairerTaylorKernelAt N x y w| * M :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = |parabolicSemigroup.kernel t x y| * ((∫ w, |hairerTaylorKernelAt N x y w|) * M) := by
          rw [integral_mul_const]
      _ ≤ |parabolicSemigroup.kernel t x y| * ((L * (1 + parabolicNorm (y - x))) * M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hM0) (abs_nonneg _)
      _ = _ := by ring
  have hsumN : Summable fun n => ∫ w, ‖F n w‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hbd
      (hsum.mul_left (M * L))
  have hint := integral_tsum_of_summable_integral_norm hFi hsumN
  have hFn : ∀ n, ∫ w, F n w = parabolicSemigroup.kernel t x (latticeLift u n) *
      ∫ w, hairerTaylorKernelAt N x (latticeLift u n) w * Ψ w := fun n => integral_const_mul _ _
  have hFw : ∀ w, ∑' n, F n w = latticeNum N t x u w * Ψ w := by
    intro w
    unfold latticeNum
    rw [← tsum_mul_right]
    exact tsum_congr fun n => by simp only [hF]; ring
  simp only [hFn] at hint
  rw [hint]
  simp_rw [hFw]
  by_cases hG0 : latticeG t x u = 0
  · have h0 : ∀ w, latticeNum N t x u w = 0 := latticeNum_eq_zero_of_latticeG_eq_zero hu hG0
    simp [h0, hG0]
  · have : ∀ w, latticeNum N t x u w * Ψ w = latticeG t x u * (latticeK N t x u w * Ψ w) := by
      intro w
      simp only [latticeK]
      field_simp
    simp_rw [this]
    rw [integral_const_mul]
    ring

/-- **Reduction of the `ℝ⁴`-integral of a recentred-product field to `ℝ × T³`.** -/
theorem integral_semigroup_mul_iPsi_field_eq {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
    {N : ℕ} {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ (x' : SpaceTime) (t' : ℝ) (a : Fin 3 → ℝ),
      ∫ w, |hairerTaylorKernel N x' t' a w| ≤ L * (1 + ∑ i, |a i|))
    (hξ : IsSmoothOnSpaceTime (ξ ω)) {Φ : SpaceTime → ℝ} (hΦ : Measurable Φ) {t : ℝ} (ht : 0 < t)
    (x : ParabolicSpace)
    (hint : Integrable fun y : ParabolicSpace => parabolicSemigroup.kernel t x y *
      (hairerIPsiRecentred N ξ ω x y * Φ (spaceTimeProj y))) :
    ∫ y, parabolicSemigroup.kernel t x y *
        (hairerIPsiRecentred N ξ ω x y * Φ (spaceTimeProj y)) =
      ∫ u, ((∫ w, latticeK N t x u w * hairerPsiField N ξ ω w) * Φ u + 0) * latticeG t x u := by
  have hv : Measurable fun y : ParabolicSpace => hairerIPsiRecentred N ξ ω x y :=
    (continuous_hairerIPsiRecentred_right N ω hξ x).measurable
  have hm : Measurable fun y : ParabolicSpace => parabolicSemigroup.kernel t x y *
      (hairerIPsiRecentred N ξ ω x y * Φ (spaceTimeProj y)) :=
    (measurable_parabolicSemigroup_kernel t x).mul
      (hv.mul (hΦ.comp continuous_spaceTimeProj.measurable))
  rw [(integrable_and_integral_tsum_latticeLift hm hint).2]
  have hΨc : Continuous (hairerPsiField N ξ ω) :=
    continuous_hairerKernelTorus_convolution N (IsSmoothOnSpaceTime.continuous hξ)
  refine integral_congr_ae ?_
  filter_upwards [ae_latticeWeightSum_lt_top ht x] with u hu
  have h1 := tsum_latticeQ_mul_integral hL0 hL hΨc t x hu
  have e : ∀ n : Fin 3 → ℤ, parabolicSemigroup.kernel t x (latticeLift u n) *
      (hairerIPsiRecentred N ξ ω x (latticeLift u n) * Φ (spaceTimeProj (latticeLift u n))) =
      (parabolicSemigroup.kernel t x (latticeLift u n) *
        ∫ w, hairerTaylorKernelAt N x (latticeLift u n) w * hairerPsiField N ξ ω w) * Φ u := by
    intro n
    rw [hairerIPsiRecentred_eq_integral_taylorKernelAt N hξ, spaceTimeProj_latticeLift]
    ring
  simp_rw [e]
  rw [tsum_mul_right, h1]
  ring

end RegularityStructures.Phi43

end
