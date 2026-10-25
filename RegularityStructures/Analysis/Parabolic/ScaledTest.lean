/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.TestFunction
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Test functions given by scaled derivative bounds

A smooth `g`, vanishing outside the parabolic ball `B(z, R)` (`0 < R ≤ 1`), whose scaled
profile `v ↦ g (z + S^R v)` has derivatives bounded by `A`, is a multiple
`(A R⁵) • φ^R_z` of a rescaled test function with `φ ∈ B^4`
(`exists_eq_smul_rescaledTestFunction`). We also give the calculus of such scaled bounds
(products, affine dilations, rescaled test functions in scaled coordinates) and a finite-sum
rule for the pairing `⟨Λ, ·⟩`.

Source: [Hai14] = arXiv:1303.5113v4, (2.13), Proposition 7.2.
-/

public section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace RegularityStructures

private theorem dilate_add_aux (c : ℝ) (z w : ParabolicSpace) :
    parabolicDilate c (z + w) = parabolicDilate c z + parabolicDilate c w := by
  simp only [parabolicDilate, Prod.fst_add, Prod.snd_add, smul_add, mul_add]
  rfl

theorem norm_parabolicDilateCLM_le_one {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    ‖parabolicDilateCLM c‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  have hc2 : c ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  rw [parabolicDilateCLM_apply, Prod.norm_def, one_mul]
  simp only [parabolicDilate]
  refine max_le ?_ ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg c)]
    exact (mul_le_of_le_one_left (abs_nonneg _) hc2).trans (by
      rw [← Real.norm_eq_abs]; exact le_max_left _ _)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
    exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans (le_max_right _ _)

/-- Scaled derivative bounds are stable under products, with constant `2 ^ r A B`. -/
theorem norm_iteratedFDeriv_mul_le_of_le {f g : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {r : ℕ} {A B : ℝ}
    (hfA : ∀ k ≤ r, ∀ v, ‖iteratedFDeriv ℝ k f v‖ ≤ A)
    (hgB : ∀ k ≤ r, ∀ v, ‖iteratedFDeriv ℝ k g v‖ ≤ B) {k : ℕ} (hk : k ≤ r)
    (v : ParabolicSpace) : ‖iteratedFDeriv ℝ k (f * g) v‖ ≤ 2 ^ r * A * B := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hfA 0 (Nat.zero_le _) v)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hgB 0 (Nat.zero_le _) v)
  have hfg : f * g = fun y => f y * g y := rfl
  rw [hfg]
  refine (_root_.norm_iteratedFDeriv_mul_le (N := k) (hf.of_le (by exact_mod_cast le_top)) (hg.of_le
    (by exact_mod_cast le_top)) v (by exact_mod_cast le_refl k)).trans ?_
  have : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f v‖ *
      ‖iteratedFDeriv ℝ (k - i) g v‖ ≤ k.choose i * (A * B) := by
    intro i hi
    have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hfA i (hi'.trans hk) v)
      (hgB _ ((Nat.sub_le _ _).trans hk) v) (norm_nonneg _) hA) (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum this).trans ?_
  rw [← Finset.sum_mul]
  have h2 : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [h2, mul_assoc]
  have : (2 : ℝ) ^ k ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hk
  nlinarith [mul_nonneg hA hB]

/-- Affine parabolic dilations by `0 ≤ c ≤ 1` preserve scaled derivative bounds. -/
theorem norm_iteratedFDeriv_comp_parabolicDilate_le {h : ParabolicSpace → ℝ}
    (hh : ContDiff ℝ ∞ h) {r : ℕ} {A : ℝ}
    (hA : ∀ k ≤ r, ∀ u, ‖iteratedFDeriv ℝ k h u‖ ≤ A) {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1)
    (a : ParabolicSpace) {k : ℕ} (hk : k ≤ r) (v : ParabolicSpace) :
    ‖iteratedFDeriv ℝ k (fun v => h (a + parabolicDilate c v)) v‖ ≤ A := by
  have hh' : ContDiff ℝ ∞ (fun u => h (a + u)) := hh.comp (contDiff_const.add contDiff_id)
  have e : (fun v => h (a + parabolicDilate c v)) =
      (fun u => h (a + u)) ∘ (parabolicDilateCLM c) := by
    funext v; simp
  rw [e]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (n := k) _ (hh'.of_le (by exact_mod_cast le_top)) v
    (by exact_mod_cast le_refl k)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hn := norm_parabolicDilateCLM_le_one h0 h1
  have hp : ∏ _i : Fin k, ‖parabolicDilateCLM c‖ ≤ 1 := by
    rw [Finset.prod_const]; exact pow_le_one₀ (norm_nonneg _) hn
  have hd : ‖iteratedFDeriv ℝ k (fun u => h (a + u)) (parabolicDilateCLM c v)‖ ≤ A := by
    rw [iteratedFDeriv_comp_add_left]
    exact hA k hk _
  calc _ ≤ ‖iteratedFDeriv ℝ k (fun u => h (a + u)) (parabolicDilateCLM c v)‖ * 1 := by
        gcongr
    _ ≤ A := by rw [mul_one]; exact hd

/-- The rescaled test function in scaled coordinates `v ↦ φ^λ_x (z + S^R v)`. -/
theorem norm_iteratedFDeriv_rescaledTestFunction_scaled_le {φ : ParabolicSpace → ℝ} {r : ℕ}
    (hφ : φ ∈ testFunctionClass r) {lam R : ℝ} (hR : 0 < R) (hRl : R ≤ lam)
    (x z : ParabolicSpace) {k : ℕ} (hk : k ≤ r) (v : ParabolicSpace) :
    ‖iteratedFDeriv ℝ k (fun v => rescaledTestFunction φ lam x (z + parabolicDilate R v)) v‖ ≤
      (lam ^ 5)⁻¹ := by
  have hl : 0 < lam := hR.trans_le hRl
  have e : (fun v => rescaledTestFunction φ lam x (z + parabolicDilate R v)) = fun v =>
      (lam ^ 5)⁻¹ • φ (parabolicDilate lam⁻¹ (z - x) + parabolicDilate (R / lam) v) := by
    funext v
    simp only [rescaledTestFunction, smul_eq_mul]
    congr 2
    rw [show z + parabolicDilate R v - x = (z - x) + parabolicDilate R v by abel,
      dilate_add_aux, div_eq_inv_mul, parabolicDilate_mul]
  have hF : ContDiff ℝ ∞ (fun v => φ (parabolicDilate lam⁻¹ (z - x) + parabolicDilate (R / lam) v)) :=
    hφ.1.comp (contDiff_const.add (parabolicDilateCLM (R / lam)).contDiff)
  rw [e, show (fun v => (lam ^ 5)⁻¹ • φ (parabolicDilate lam⁻¹ (z - x) +
      parabolicDilate (R / lam) v)) = (lam ^ 5)⁻¹ • (fun v => φ (parabolicDilate lam⁻¹ (z - x) +
      parabolicDilate (R / lam) v)) from rfl, iteratedFDeriv_const_smul_apply
    ((hF.of_le (by exact_mod_cast le_top) : ContDiff ℝ k _).contDiffAt), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := norm_iteratedFDeriv_comp_parabolicDilate_le hφ.1 (A := 1) hφ.2.2
    (div_nonneg hR.le hl.le) ((div_le_one hl).2 hRl) (parabolicDilate lam⁻¹ (z - x)) hk v
  calc _ ≤ (lam ^ 5)⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

/-- A smooth function supported in `B(z, R)` (`0 < R ≤ 1`) with scaled derivative bounds `A` is a
multiple `(A R⁵) φ^R_z` of a rescaled test function with `φ ∈ B^4`. -/
theorem exists_eq_smul_rescaledTestFunction {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    {z : ParabolicSpace} {R A : ℝ} (hR : 0 < R) (_hR1 : R ≤ 1) (hA : 0 < A)
    (hsupp : ∀ w, R < parabolicNorm (w - z) → g w = 0)
    (hder : ∀ k ≤ 4, ∀ v, ‖iteratedFDeriv ℝ k (fun v => g (z + parabolicDilate R v)) v‖ ≤ A) :
    ∃ φ ∈ testFunctionClass 4, g = (A * R ^ 5) • rescaledTestFunction φ R z := by
  have hc : ContDiff ℝ ∞ (fun v => g (z + parabolicDilate R v)) :=
    hg.comp (contDiff_const.add (parabolicDilateCLM R).contDiff)
  refine ⟨fun v => A⁻¹ * g (z + parabolicDilate R v), ⟨contDiff_const.mul hc, ?_, ?_⟩, ?_⟩
  · intro v hv
    have : R < parabolicNorm (z + parabolicDilate R v - z) := by
      rw [add_sub_cancel_left, parabolicNorm_parabolicDilate hR.le]
      nlinarith
    simp [hsupp _ this]
  · intro k hk v
    have := iteratedFDeriv_const_smul_apply (a := A⁻¹)
      ((hc.of_le (by exact_mod_cast le_top) : ContDiff ℝ k _).contDiffAt (x := v))
    rw [show (fun v => A⁻¹ * g (z + parabolicDilate R v)) =
      A⁻¹ • (fun v => g (z + parabolicDilate R v)) from rfl, this, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hA)]
    calc _ ≤ A⁻¹ * A := by gcongr; exact hder k hk v
      _ = 1 := inv_mul_cancel₀ hA.ne'
  · funext w
    simp only [rescaledTestFunction, Pi.smul_apply, smul_eq_mul]
    rw [← parabolicDilate_mul, mul_inv_cancel₀ hR.ne', parabolicDilate_one,
      add_sub_cancel]
    field_simp

/-- A finite sum of test functions: if each integral converges (and is integrable for small
`s > 0`) then so does the integral against the sum, and the pairing is additive. -/
theorem RegularisingSemigroup.pairing_finset_sum {E : Type*} [MeasurableSpace E] {μ : Measure E}
    (K : RegularisingSemigroup E μ) {ι : Type*} {Λ : ℝ → E → ℝ} (g : ι → E → ℝ)
    (S : Finset ι) {L : ι → ℝ}
    (hi : ∀ j ∈ S, ∀ᶠ s in 𝓝[>] (0 : ℝ), Integrable (fun y => Λ s y * g j y) μ)
    (h : ∀ j ∈ S, Tendsto (fun s => ∫ y, Λ s y * g j y ∂μ) (𝓝[>] 0) (𝓝 (L j))) :
    Tendsto (fun s => ∫ y, Λ s y * (∑ j ∈ S, g j) y ∂μ) (𝓝[>] 0) (𝓝 (∑ j ∈ S, L j)) ∧
      K.pairing Λ (∑ j ∈ S, g j) = ∑ j ∈ S, K.pairing Λ (g j) := by
  have ht : Tendsto (fun s => ∫ y, Λ s y * (∑ j ∈ S, g j) y ∂μ) (𝓝[>] 0)
      (𝓝 (∑ j ∈ S, L j)) := by
    have := tendsto_finsetSum S h
    refine this.congr' ?_
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ j ∈ S, Integrable (fun y => Λ s y * g j y) μ :=
      (Filter.eventually_all_finset S).2 hi
    filter_upwards [hev] with s hs
    simp only [Finset.sum_apply, Finset.mul_sum]
    rw [integral_finsetSum _ hs]
  refine ⟨ht, ?_⟩
  rw [K.pairing_eq_of_tendsto ht]
  exact Finset.sum_congr rfl fun j hj => (K.pairing_eq_of_tendsto (h j hj)).symm

end RegularityStructures

end
