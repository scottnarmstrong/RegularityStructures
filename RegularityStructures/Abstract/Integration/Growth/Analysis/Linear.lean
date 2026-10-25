/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Growth.Analysis.Small
public import RegularityStructures.Abstract.Integration.Growth.Analysis.Split
public import RegularityStructures.Analysis.Heat.Schauder.DerivativeScaling
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Splitting of the pairings with the Taylor kernels, local order with polynomial growth

Growth versions, for `Λ` with `IsLocalOrderGrowth`, of the splitting of the pairings with the
Taylor kernels of [Hai14, (5.14)] for distributions of local order: the
limits `s ↓ 0` of `∫ Λ_s φ` exist for the shells used in Hairer's proof and the pairing with
`K^α_{n;xy}` splits into the pairings with `K_n(y - ·)` and `D^k K_n(x - ·)`.
Source: [Hai14] = arXiv:1303.5113v4, (5.14), proof of Lemma 5.19.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace RegularityStructures

theorem integrable_mul_of_growth {Λ : ℝ → ParabolicSpace → ℝ}
    {x₀ : ParabolicSpace} {γ C q : ℝ} {A : Finset ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hA : ∀ a ∈ A, a ≤ γ)
    (hloc : parabolicSemigroup.IsLocalOrderGrowth Λ x₀ γ A C q) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1)
    {φ : ParabolicSpace → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hφ : parabolicSemigroup.IsSupported φ x₀ lam) : Integrable fun z => Λ s z * φ z :=
  (RegularisingSemigroup.LocalBall.of_growth parabolicSemigroup_isMetricScale hΛ hΛm hC hq hA
    hloc hlam).integrable_mul hs hφ

theorem integrable_mul_of_hasCompactSupport_growth {Λ : ℝ → ParabolicSpace → ℝ}
    {x₀ : ParabolicSpace} {γ C q : ℝ} {A : Finset ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hA : ∀ a ∈ A, a ≤ γ)
    (hloc : parabolicSemigroup.IsLocalOrderGrowth Λ x₀ γ A C q) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1)
    {φ : ParabolicSpace → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable fun z => Λ s z * φ z := by
  have hbdd : BddAbove ((fun z => parabolicNorm (z - x₀)) '' tsupport φ) :=
    (hc.isCompact.image (continuous_parabolicNorm.comp (continuous_id.sub continuous_const))).bddAbove
  obtain ⟨R, hR⟩ := hbdd
  have hR0 : 0 ≤ max R 0 := le_max_right _ _
  refine (RegularisingSemigroup.LocalBall.of_growth parabolicSemigroup_isMetricScale hΛ hΛm hC hq hA
    hloc hR0).integrable_mul hs ⟨hφ.measurable, hφ.integrable_of_hasCompactSupport hc,
    fun z hz => ?_⟩
  by_contra hne
  have : z ∈ tsupport φ := subset_tsupport φ hne
  have := hR ⟨z, this, rfl⟩
  have hz' : max R 0 < parabolicNorm (z - x₀) := hz
  have := le_max_left R 0
  linarith

theorem tendsto_dShell_centre_growth {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    {x y : ParabolicSpace} {γ C q : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hloc : parabolicSemigroup.IsLocalOrderGrowth Λ x γ A C q) (k : Fin 4 →₀ ℕ) (n : ℕ) :
    Tendsto (fun s => ∫ z, Λ s z * lineIter (multiDirs k) (scaledShell h n) (y - z))
      (nhdsWithin 0 (Ioi 0))
      (nhds (parabolicSemigroup.pairing Λ
        (fun z => lineIter (multiDirs k) (scaledShell h n) (y - z)))) := by
  have hh' : ContDiff ℝ ∞ (lineIter (multiDirs k) h) := contDiff_lineIter h0 _
  have hs' : ∀ z, 1 < parabolicNorm z → lineIter (multiDirs k) h z = 0 := fun z hz =>
    lineIter_eq_zero_of_lt hs _ hz
  obtain ⟨T, -⟩ := tendsto_and_abs_pairing_scaledShell_centre_le_growth hΛ hΛm hh' hs' hA hC hq hloc n
    (y := y)
  have hT : Tendsto (fun s => ∫ z, Λ s z * lineIter (multiDirs k) (scaledShell h n) (y - z))
      (nhdsWithin 0 (Ioi 0))
      (nhds (((2 : ℝ) ^ n) ^ multiDeg k * parabolicSemigroup.pairing Λ
        (fun z => scaledShell (lineIter (multiDirs k) h) n (y - z)))) := by
    refine (T.const_mul (((2 : ℝ) ^ n) ^ multiDeg k)).congr fun s => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [lineIter_multiDirs_scaledShell h0]
    ring
  convert hT using 2
  have e : (fun z => lineIter (multiDirs k) (scaledShell h n) (y - z)) =
      fun z => ((2 : ℝ) ^ n) ^ multiDeg k * scaledShell (lineIter (multiDirs k) h) n (y - z) := by
    funext z; rw [lineIter_multiDirs_scaledShell h0]
  rw [parabolicSemigroup.pairing_eq_of_tendsto hT]

theorem pairing_taylorKernel_eq_growth {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    {x y : ParabolicSpace} {γ C qg : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ)
    (hC : 0 ≤ C) (hqg : 0 ≤ qg) (hloc : parabolicSemigroup.IsLocalOrderGrowth Λ x γ A C qg) (σ : ℝ) (n : ℕ) :
    parabolicSemigroup.pairing Λ (taylorKernel h n σ x y) =
      parabolicSemigroup.pairing Λ (fun w => scaledShell h n (y - w)) -
        ∑ k ∈ taylorIdx σ, (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) *
          parabolicSemigroup.pairing Λ (fun w => lineIter (multiDirs k) (scaledShell h n) (x - w))
    := by
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
  rw [parabolicSemigroup.pairing_eq_of_tendsto (Λ := Λ) (φ := taylorKernel h n σ x y)
    (by rw [hker]; exact hlim)]

end RegularityStructures

end
