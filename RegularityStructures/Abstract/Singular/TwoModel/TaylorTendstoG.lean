/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Growth.Analysis.Linear
public import RegularityStructures.Analysis.Heat.Schauder.DerivativeScaling
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Convergence of the regularised pairings with the Taylor kernels, with growth

Growth version of `tendsto_integral_taylorKernel`: for `Λ` with `IsLocalOrderGrowth`, the integrals
`∫ Λ_s K^σ_{n;xy}` converge as `s ↓ 0` to `pairing Λ K^σ_{n;xy}`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace RegularityStructures

theorem tendsto_integral_taylorKernel_growth {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    {x y : ParabolicSpace} {γ C qg : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ)
    (hC : 0 ≤ C) (hqg : 0 ≤ qg) (hloc : parabolicSemigroup.IsLocalOrderGrowth Λ x γ A C qg) (σ : ℝ) (n : ℕ) :
    Filter.Tendsto (fun s => ∫ z, Λ s z * taylorKernel h n σ x y z) (nhdsWithin 0 (Ioi 0))
      (nhds (parabolicSemigroup.pairing Λ (taylorKernel h n σ x y))) := by
  classical
  set d : ℝ := parabolicNorm (y - x) with hd
  set q : ℝ := (2 : ℝ)⁻¹ ^ n with hq
  have hd0 : 0 ≤ d := parabolicNorm_nonneg _
  have hq0 : 0 < q := by positivity
  set g := scaledShell h n with hg
  have hgs : ContDiff ℝ ∞ g := contDiff_scaledShell h0 n
  set c : (Fin 4 →₀ ℕ) → ℝ := fun k =>
    evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k with hc
  set φ₁ : ParabolicSpace → ℝ := fun w => g (y - w) with hφ₁
  set φk : (Fin 4 →₀ ℕ) → ParabolicSpace → ℝ := fun k w => lineIter (multiDirs k) g (x - w)
    with hφk
  have hker : taylorKernel h n σ x y = fun w => φ₁ w - ∑ k ∈ taylorIdx σ, c k * φk k w := by
    funext w
    rfl
  obtain ⟨T1, -⟩ := tendsto_and_abs_pairing_scaledShell_centre_le_growth hΛ hΛm h0 hs hA hC hqg hloc n
    (y := y)
  have hTk : ∀ k : Fin 4 →₀ ℕ, _ := fun k =>
    tendsto_and_abs_pairing_word_scaledShell_le_growth hΛ hΛm h0 hs hA hC hqg hloc
      ((Finsupp.toMultiset k).toList) n
  have hint₁ : ∀ s ∈ Ioc (0 : ℝ) 1, Integrable fun z => Λ s z * φ₁ z := by
    intro s hs'
    have hc1 : Continuous φ₁ := hgs.continuous.comp (continuous_const.sub continuous_id)
    have hcs : HasCompactSupport φ₁ := by
      refine hasCompactSupport_of_eq_zero (c := q) hq0 y fun w hw => ?_
      refine scaledShell_eq_zero hs ?_
      rwa [parabolicNorm_sub_comm]
    exact integrable_mul_of_growth hΛ hΛm hC hqg (fun a ha => (hA a ha).2) hloc hs'
      (lam := q + d) (add_nonneg hq0.le hd0) ⟨hc1.measurable,
      hc1.integrable_of_hasCompactSupport hcs, fun w hw => by
        have h3 : parabolicNorm (w - x) ≤ parabolicNorm (w - y) + parabolicNorm (y - x) := by
          simpa using parabolicNorm_add_le (w - y) (y - x)
        have : q < parabolicNorm (w - y) := by
          change q + d < parabolicNorm (w - x) at hw
          linarith
        refine scaledShell_eq_zero hs ?_
        rwa [parabolicNorm_sub_comm]⟩
  have hintk : ∀ k : Fin 4 →₀ ℕ, ∀ s ∈ Ioc (0 : ℝ) 1, Integrable fun z => Λ s z * φk k z := by
    intro k s hs'
    have hFk : ContDiff ℝ ∞ (lineIter (multiDirs k) g) := contDiff_lineIter hgs _
    have hc1 : Continuous (φk k) := hFk.continuous.comp (continuous_const.sub continuous_id)
    have hz : ∀ w, q < parabolicNorm w → lineIter (multiDirs k) g w = 0 := fun w hw =>
      lineIter_eq_zero_of_isOpen (U := {w | (2 : ℝ)⁻¹ ^ n < parabolicNorm w})
        (isOpen_lt continuous_const continuous_parabolicNorm) _ _
        (fun w hw => scaledShell_eq_zero hs hw) w hw
    have hcs : HasCompactSupport (φk k) := by
      refine hasCompactSupport_of_eq_zero (c := q) hq0 x fun w hw => ?_
      refine hz _ ?_
      rwa [parabolicNorm_sub_comm]
    exact integrable_mul_of_growth hΛ hΛm hC hqg (fun a ha => (hA a ha).2) hloc hs'
      (lam := q) hq0.le ⟨hc1.measurable,
      hc1.integrable_of_hasCompactSupport hcs, fun w hw => by
        refine hz _ ?_
        have : q < parabolicNorm (w - x) := hw
        rwa [parabolicNorm_sub_comm]⟩
  have hlim : Filter.Tendsto (fun s => ∫ z, Λ s z * (φ₁ z - ∑ k ∈ taylorIdx σ, c k * φk k z))
      (nhdsWithin 0 (Ioi 0))
      (nhds (parabolicSemigroup.pairing Λ φ₁ -
        ∑ k ∈ taylorIdx σ, c k * parabolicSemigroup.pairing Λ (φk k))) := by
    refine (T1.sub (tendsto_finsetSum _ fun k _ => (hTk k).1.const_mul (c k))).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with s hs'
    have hs2 : s ∈ Ioc (0 : ℝ) 1 := ⟨hs'.1, hs'.2.le⟩
    simp only [mul_sub, Finset.mul_sum]
    rw [integral_sub (hint₁ s hs2) (integrable_finsetSum _ fun k _ => ?_)]
    · congr 1
      rw [integral_finsetSum _ fun k _ => ?_]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [hφk, multiDirs_eq_map]; ring
      · simpa only [mul_left_comm] using (hintk k s hs2).const_mul (c k)
    · simpa only [mul_left_comm] using (hintk k s hs2).const_mul (c k)
  rw [pairing_taylorKernel_eq_growth hΛ hΛm h0 hs hA hC hqg hloc σ n (x := x) (y := y), hker]
  exact hlim

end RegularityStructures

end
