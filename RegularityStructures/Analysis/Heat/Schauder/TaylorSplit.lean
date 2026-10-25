/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorEstimate
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernelBound
public import RegularityStructures.Analysis.Heat.Schauder.TaylorSmall

/-!
# Small scales: the two pieces of `K^α_{n;xy}` separately

For `‖y - x‖_𝔰 > 2^{-n}` the shifted shell `scaledShell h n (y - ·)` and the derivative shells
`D^k scaledShell h n (x - ·)` are paired with `Λ` separately: each is adapted to the scale `2^{-n}`,
centred at `y` resp. `x`.

* `tendsto_and_abs_pairing_word_scaledShell_le`: `|⟨Λ, D^ℓ K_n (x - ·)⟩| ≤ C Pw (∫|D^ℓ h| + ∫|L D^ℓ h|)
  2^{(|ℓ|_𝔰 - γ - 2) n}`, `Pw = ∑_a κ_a`.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem tendsto_and_abs_pairing_word_scaledShell_le {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    {x : ParabolicSpace} {γ C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ) (hC : 0 ≤ C)
    (hloc : parabolicSemigroup.IsLocalOrder Λ x γ A C) (ℓ : List (Fin 4)) (n : ℕ) :
    Filter.Tendsto (fun s => ∫ z, Λ s z * lineIter (ℓ.map coordDir) (scaledShell h n) (x - z))
        (nhdsWithin 0 (Ioi 0))
        (nhds (parabolicSemigroup.pairing Λ
          (fun z => lineIter (ℓ.map coordDir) (scaledShell h n) (x - z)))) ∧
    |parabolicSemigroup.pairing Λ (fun z => lineIter (ℓ.map coordDir) (scaledShell h n) (x - z))| ≤
      C * (∑ a ∈ A, pairingWeight a) *
        ((∫ w, |lineIter (ℓ.map coordDir) h w|) +
          ∫ w, |lineIter (ℓ.map coordDir) (parabolicGenerator h) w|) *
        (2 : ℝ) ^ (((indexWeight ℓ : ℝ) - γ - 2) * n) := by
  have hN : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hlam : (0 : ℝ) < 2⁻¹ ^ n := by positivity
  have hlam2 : (2 : ℝ)⁻¹ ^ n ≤ 2 :=
    (pow_le_one₀ (by norm_num) (by norm_num)).trans (by norm_num)
  have hg := contDiff_scaledShell h0 n
  have hF : ContDiff ℝ ∞ (lineIter (ℓ.map coordDir) (scaledShell h n)) := contDiff_lineIter hg _
  have hsupp : ∀ w, (2 : ℝ)⁻¹ ^ n < parabolicNorm w →
      lineIter (ℓ.map coordDir) (scaledShell h n) w = 0 := fun w hw =>
    lineIter_eq_zero_of_isOpen (U := {w | (2 : ℝ)⁻¹ ^ n < parabolicNorm w})
      (isOpen_lt continuous_const continuous_parabolicNorm) _ _
      (fun w hw => scaledShell_eq_zero hs hw) w hw
  have hrp : ((2 : ℝ)⁻¹ ^ n) ^ (-(4 : ℝ)) = ((2 : ℝ) ^ n) ^ 4 := by
    rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hlam.le, Real.rpow_natCast]
    simp [inv_pow]
  set I : ℝ := ∫ w, |lineIter (ℓ.map coordDir) h w| with hI
  set I' : ℝ := ∫ w, |lineIter (ℓ.map coordDir) (parabolicGenerator h) w| with hI'
  have key := tendsto_and_abs_pairing_reflect_le_centre hΛ hΛm hA hC hloc hF hlam hlam2 hsupp
    (c := x)
    (B₀ := ((2 : ℝ) ^ n) ^ indexWeight ℓ * ((((2 : ℝ) ^ n)⁻¹ ^ 2) * I))
    (B₁ := ((2 : ℝ) ^ n) ^ indexWeight ℓ * ((((2 : ℝ) ^ n)⁻¹ ^ 2) * I'))
    (integral_abs_word_scaledShell h0 ℓ n).le
    (by
      rw [integral_abs_gen_word_scaledShell h0 ℓ n, hrp]
      refine le_of_eq ?_
      rw [hI']
      field_simp)
  refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
  rw [sub_self, parabolicNorm_zero, add_zero]
  have hsum : ∑ a ∈ A, pairingWeight a * (((2 : ℝ)⁻¹ ^ n) ^ a * ((2 : ℝ)⁻¹ ^ n) ^ (γ - a)) =
      (∑ a ∈ A, pairingWeight a) * ((2 : ℝ)⁻¹ ^ n) ^ γ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Real.rpow_add hlam]; congr 2; ring
  rw [hsum, two_rpow_deg_eq]
  ring

theorem abs_pairing_taylorKernel_small_le {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    {x y : ParabolicSpace} {γ C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ) (hC : 0 ≤ C)
    (hloc : parabolicSemigroup.IsLocalOrder Λ x γ A C) (σ : ℝ) (n : ℕ) :
    |parabolicSemigroup.pairing Λ (taylorKernel h n σ x y)| ≤
      ((∫ w, |h w|) + ∫ w, |parabolicGenerator h w|) * C *
        (∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2) * n) *
          ((2 : ℝ)⁻¹ ^ n + parabolicNorm (y - x)) ^ (γ - a))) +
      ∑ k ∈ taylorIdx σ, parabolicNorm (y - x) ^ multiDeg k *
        (C * (∑ a ∈ A, pairingWeight a) *
          ((∫ w, |lineIter (multiDirs k) h w|) +
            ∫ w, |lineIter (multiDirs k) (parabolicGenerator h) w|) *
          (2 : ℝ) ^ (((multiDeg k : ℝ) - γ - 2) * n)) := by
  classical
  set d : ℝ := parabolicNorm (y - x) with hd
  set q : ℝ := (2 : ℝ)⁻¹ ^ n with hq
  have hd0 : 0 ≤ d := parabolicNorm_nonneg _
  have hq0 : 0 < q := by positivity
  set g := scaledShell h n with hg
  have hgs : ContDiff ℝ ∞ g := contDiff_scaledShell h0 n
  have hLD : parabolicSemigroup.LocalData Λ x γ A C :=
    ⟨hΛ, hΛm, hC, fun a ha => (hA a ha).2, hloc⟩
  -- the pieces
  set c : (Fin 4 →₀ ℕ) → ℝ := fun k => coeffT (parabolicCoords (y - x)) k with hc
  set φ₁ : ParabolicSpace → ℝ := fun w => g (y - w) with hφ₁
  set φk : (Fin 4 →₀ ℕ) → ParabolicSpace → ℝ := fun k w => lineIter (multiDirs k) g (x - w) with hφk
  have hker : taylorKernel h n σ x y = fun w => φ₁ w - ∑ k ∈ taylorIdx σ, c k * φk k w := by
    funext w
    simp only [taylorKernel, hφ₁, hφk, hc, evalParabolic_monomial_div]
    rfl
  -- pieces: tendsto and bounds
  obtain ⟨T1, B1⟩ := tendsto_and_abs_pairing_scaledShell_centre_le hΛ hΛm h0 hs hA hC hloc n
    (y := y)
  have hTk : ∀ k : Fin 4 →₀ ℕ, _ := fun k => tendsto_and_abs_pairing_word_scaledShell_le hΛ hΛm h0 hs hA hC
    hloc ((Finsupp.toMultiset k).toList) n
  -- integrability of the slices
  have hint₁ : ∀ s ∈ Ioc (0 : ℝ) 1, Integrable fun z => Λ s z * φ₁ z := by
    intro s hs'
    have hc1 : Continuous φ₁ := hgs.continuous.comp (continuous_const.sub continuous_id)
    have hcs : HasCompactSupport φ₁ := by
      refine hasCompactSupport_of_eq_zero (c := q) hq0 y fun w hw => ?_
      refine scaledShell_eq_zero hs ?_
      rwa [parabolicNorm_sub_comm]
    exact hLD.integrable_mul hs' (lam := q + d) ⟨hc1.measurable, hc1.integrable_of_hasCompactSupport hcs,
      fun w hw => by
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
    exact hLD.integrable_mul hs' (lam := q) ⟨hc1.measurable,
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
  rw [hker, parabolicSemigroup.pairing_eq_of_tendsto hlim]
  refine (abs_sub _ _).trans (add_le_add B1 ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  have hz : ∀ i, |parabolicCoords (y - x) i| ≤ d ^ parabolicWeight i := fun i =>
    abs_parabolicCoords_le i
  have hk' := (hTk k).2
  rw [indexWeight_toList] at hk'
  refine mul_le_mul (abs_coeffT_le hz k) ?_ (abs_nonneg _) (pow_nonneg hd0 _)
  simp only [hφk, multiDirs_eq_map]
  exact hk'

end RegularityStructures

end
