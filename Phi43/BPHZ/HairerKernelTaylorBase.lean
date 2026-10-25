/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.HairerKernelIncrement
public import RegularityStructures.Analysis.Heat.Schauder.DerivativeScaling
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Taylor remainder of a smooth profile supported in the unit parabolic ball

For `g` smooth with `g = 0` outside `{‖z‖_𝔰 ≤ 1}` we prove, with the spatial gradient only
(`D_i g = lineIter [spaceDir i] g`), that for every `θ ∈ [0, 1]`
`|g (w + k) - g w - ∑ᵢ D_i g w kᵢ| ≤ L ‖k‖_𝔰 ^ (1 + θ)`.
A time increment `τ` costs `|τ| ≤ ‖k‖_𝔰²`, i.e. it counts as order `2`.
-/

public section

open scoped ContDiff

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem ktay_hasCompactSupport {g : ParabolicSpace → ℝ}
    (hs : ∀ z, 1 < parabolicNorm z → g z = 0) : HasCompactSupport g :=
  HasCompactSupport.intro (isCompact_parabolicNorm_le 1) fun z hz => hs z (not_le.1 hz)

/-- A smooth profile supported in the unit parabolic ball is bounded. -/
theorem hairerKernelTaylor_exists_abs_le {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : ∀ z, 1 < parabolicNorm z → g z = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, |g z| ≤ B := by
  obtain ⟨B, hB⟩ := hg.continuous.abs.bounded_above_of_compact_support
    (ktay_hasCompactSupport hs).norm
  refine ⟨max B 0, le_max_right B 0, fun z => ?_⟩
  have hz := (hB z).trans (le_max_left B 0)
  simpa only [Real.norm_eq_abs, abs_abs] using hz

private theorem ktay_norm_snd_le (κ : Fin 3 → ℝ) : ‖((0 : ℝ), κ)‖ ≤ ∑ i, |κ i| := by
  rw [Prod.norm_def, max_le_iff]
  have h0 : 0 ≤ ∑ i, |κ i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨by simpa using h0, ?_⟩
  rw [pi_norm_le_iff_of_nonneg h0]
  intro i
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |κ j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

private theorem ktay_sum_abs_le (k : ParabolicSpace) : ∑ i, |k.2 i| ≤ parabolicNorm k := by
  unfold parabolicNorm
  linarith [Real.sqrt_nonneg |k.1|]

private theorem ktay_abs_fst_le (k : ParabolicSpace) : |k.1| ≤ parabolicNorm k ^ 2 := by
  have h0 := Real.sqrt_nonneg |k.1|
  have h1 : √|k.1| ≤ parabolicNorm k := by
    unfold parabolicNorm
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg (k.2 i)]
  calc |k.1| = √|k.1| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
    _ ≤ parabolicNorm k ^ 2 := pow_le_pow_left₀ h0 h1 2

/-- Euclidean Lipschitz bound. -/
private theorem ktay_euclid_lip {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : ∀ z, 1 < parabolicNorm z → g z = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w k : ParabolicSpace, |g (w + k) - g w| ≤ K * ‖k‖ := by
  obtain ⟨K, hK⟩ := hg.lipschitzWith_of_hasCompactSupport (ktay_hasCompactSupport hs) (by simp)
  refine ⟨K, K.2, fun w k => ?_⟩
  have h1 := hK.dist_le_mul (w + k) w
  rwa [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at h1

/-- The Lipschitz bound of a smooth profile in the parabolic size. -/
theorem hairerKernelTaylor_abs_sub_le {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : ∀ z, 1 < parabolicNorm z → g z = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ w k : ParabolicSpace, |g (w + k) - g w| ≤ L * parabolicNorm k := by
  obtain ⟨K, hK0, hK⟩ := ktay_euclid_lip hg hs
  obtain ⟨B, hB0, hB⟩ := hairerKernelTaylor_exists_abs_le hg hs
  refine ⟨max K (2 * B), le_trans hK0 (le_max_left _ _), fun w k => ?_⟩
  have hk0 := parabolicNorm_nonneg k
  by_cases hk : parabolicNorm k ≤ 1
  · have h2 : ‖k‖ ≤ parabolicNorm k := by
      have hs0 := Real.sqrt_nonneg |k.1|
      have hsum := ktay_sum_abs_le k
      have hs1 : √|k.1| ≤ 1 := by
        unfold parabolicNorm at hk
        linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg (k.2 i)]
      rw [Prod.norm_def, max_le_iff]
      refine ⟨?_, ?_⟩
      · rw [Real.norm_eq_abs]
        have h1 : |k.1| = √|k.1| * √|k.1| := (Real.mul_self_sqrt (abs_nonneg _)).symm
        have h3 : √|k.1| * √|k.1| ≤ √|k.1| * 1 := mul_le_mul_of_nonneg_left hs1 hs0
        unfold parabolicNorm
        linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg (k.2 i)]
      · rw [pi_norm_le_iff_of_nonneg hk0]
        intro i
        rw [Real.norm_eq_abs]
        have := Finset.single_le_sum (f := fun j => |k.2 j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i)
        unfold parabolicNorm
        linarith [Real.sqrt_nonneg |k.1|]
    calc |g (w + k) - g w| ≤ K * ‖k‖ := hK w k
      _ ≤ K * parabolicNorm k := mul_le_mul_of_nonneg_left h2 hK0
      _ ≤ max K (2 * B) * parabolicNorm k :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hk0
  · have hk1 : 1 ≤ parabolicNorm k := (not_le.1 hk).le
    have h1 : |g (w + k) - g w| ≤ 2 * B := by
      have := abs_sub (g (w + k)) (g w)
      linarith [hB (w + k), hB w]
    calc |g (w + k) - g w| ≤ 2 * B := h1
      _ ≤ 2 * B * parabolicNorm k := le_mul_of_one_le_right (by positivity) hk1
      _ ≤ max K (2 * B) * parabolicNorm k :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hk0

/-- Second-order Taylor bound in an arbitrary direction. -/
private theorem ktay_second_order {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : ∀ z, 1 < parabolicNorm z → g z = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ w v : ParabolicSpace,
      |g (w + v) - g w - fderiv ℝ g w v| ≤ L * ‖v‖ ^ 2 := by
  have hc := ktay_hasCompactSupport hs
  have hd : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (m := ∞) (by simp)
  obtain ⟨K, hK⟩ := hd.lipschitzWith_of_hasCompactSupport (hc.fderiv ℝ) (by simp)
  refine ⟨K, K.2, fun w v => ?_⟩
  set φ : ℝ → ℝ := fun r => g (w + r • v) - r * fderiv ℝ g w v with hφ
  have hline : ∀ r : ℝ, HasDerivAt (fun r : ℝ => w + r • v) v r := fun r => by
    simpa only [one_smul, id_eq] using! ((hasDerivAt_id r).smul_const v).const_add w
  have hder : ∀ r : ℝ, HasDerivAt φ (fderiv ℝ g (w + r • v) v - fderiv ℝ g w v) r := by
    intro r
    have h1 := ((hg.differentiable (by simp)) (w + r • v)).hasFDerivAt.comp_hasDerivAt r
      (hline r)
    have h2 : HasDerivAt (fun r : ℝ => r * fderiv ℝ g w v) (fderiv ℝ g w v) r := by
      simpa using (hasDerivAt_id r).mul_const (fderiv ℝ g w v)
    exact h1.sub h2
  have hbd : ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ g (w + r • v) v - fderiv ℝ g w v‖ ≤
      K * ‖v‖ ^ 2 := by
    intro r hr
    have h1 : ‖fderiv ℝ g (w + r • v) - fderiv ℝ g w‖ ≤ K * ‖r • v‖ := by
      have := hK.dist_le_mul (w + r • v) w
      rwa [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at this
    have h2 : ‖r • v‖ ≤ ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hr.2
    calc ‖fderiv ℝ g (w + r • v) v - fderiv ℝ g w v‖
        = ‖(fderiv ℝ g (w + r • v) - fderiv ℝ g w) v‖ := by rw [sub_apply]
      _ ≤ ‖fderiv ℝ g (w + r • v) - fderiv ℝ g w‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖v‖ * ‖v‖ := by
        have := mul_le_mul_of_nonneg_left h2 K.2
        exact mul_le_mul (h1.trans this) le_rfl (norm_nonneg _) (by positivity)
      _ = K * ‖v‖ ^ 2 := by ring
  have key := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := φ) (f' := fun r => fderiv ℝ g (w + r • v) v - fderiv ℝ g w v)
    (fun r _ => (hder r).hasDerivWithinAt) hbd (Set.left_mem_Icc.2 zero_le_one)
    (Set.right_mem_Icc.2 zero_le_one)
  have e : φ 1 - φ 0 = g (w + v) - g w - fderiv ℝ g w v := by
    simp only [hφ, one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero]
    ring
  rw [e] at key
  simpa only [Real.norm_eq_abs, sub_zero, norm_one, mul_one] using key

private theorem ktay_sum_lineIter {g : ParabolicSpace → ℝ} (w : ParabolicSpace)
    (κ : Fin 3 → ℝ) :
    ∑ i : Fin 3, lineIter [spaceDir i] g w * κ i = fderiv ℝ g w ((0 : ℝ), κ) := by
  have e : (((0 : ℝ), κ) : ParabolicSpace) = ∑ i : Fin 3, κ i • spaceDir i := by
    refine Prod.ext (by simp [spaceDir, Prod.fst_sum]) ?_
    funext j
    simp [spaceDir, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

/-- **Taylor remainder of a profile**: with the spatial gradient only, for `θ ∈ [0, 1]`. -/
theorem hairerKernelTaylor_remainder_abs_le {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : ∀ z, 1 < parabolicNorm z → g z = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ 1 → ∀ w k : ParabolicSpace,
      |g (w + k) - g w - ∑ i : Fin 3, lineIter [spaceDir i] g w * k.2 i| ≤
        L * parabolicNorm k ^ (1 + θ) := by
  obtain ⟨K, hK0, hK⟩ := ktay_euclid_lip hg hs
  obtain ⟨L2, hL20, hL2⟩ := ktay_second_order hg hs
  obtain ⟨B, hB0, hB⟩ := hairerKernelTaylor_exists_abs_le hg hs
  have hbi : ∀ i : Fin 3, ∃ Bi : ℝ, 0 ≤ Bi ∧ ∀ z, |lineIter [spaceDir i] g z| ≤ Bi := fun i =>
    hairerKernelTaylor_exists_abs_le (contDiff_lineIter hg [spaceDir i])
      (fun z hz => lineIter_eq_zero_of_lt hs _ hz)
  choose Bi hBi0 hBi using hbi
  have hB1 : 0 ≤ ∑ i, Bi i := Finset.sum_nonneg fun i _ => hBi0 i
  have hB1d : ∀ (i : Fin 3) z, |lineIter [spaceDir i] g z| ≤ ∑ i, Bi i := fun i z =>
    (hBi i z).trans (Finset.single_le_sum (f := Bi) (fun j _ => hBi0 j) (Finset.mem_univ i))
  set B1 : ℝ := ∑ i, Bi i with hB1def
  refine ⟨K + L2 + 2 * B + B1, by positivity, fun {θ} hθ0 hθ1 w k => ?_⟩
  have hk0 := parabolicNorm_nonneg k
  rw [ktay_sum_lineIter]
  set s := parabolicNorm k with hsdef
  by_cases hk : s ≤ 1
  · have h1 : |g (w + k) - g (w + ((0 : ℝ), k.2))| ≤ K * s ^ 2 := by
      have e : w + k = (w + ((0 : ℝ), k.2)) + (k.1, 0) := by
        ext <;> simp [add_assoc]
      rw [e]
      refine (hK _ _).trans (mul_le_mul_of_nonneg_left ?_ hK0)
      calc ‖((k.1, (0 : Fin 3 → ℝ)) : ParabolicSpace)‖ = |k.1| := by
            simp [Prod.norm_def]
        _ ≤ s ^ 2 := ktay_abs_fst_le k
    have h2 := hL2 w ((0 : ℝ), k.2)
    have hn : ‖((0 : ℝ), k.2)‖ ≤ s := (ktay_norm_snd_le k.2).trans (ktay_sum_abs_le k)
    have hn2 : ‖((0 : ℝ), k.2)‖ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    have h3 : |g (w + k) - g w - fderiv ℝ g w ((0 : ℝ), k.2)| ≤ (K + L2) * s ^ 2 := by
      have e : g (w + k) - g w - fderiv ℝ g w ((0 : ℝ), k.2) =
          (g (w + k) - g (w + ((0 : ℝ), k.2))) +
            (g (w + ((0 : ℝ), k.2)) - g w - fderiv ℝ g w ((0 : ℝ), k.2)) := by ring
      rw [e]
      have := abs_add_le (g (w + k) - g (w + ((0 : ℝ), k.2)))
        (g (w + ((0 : ℝ), k.2)) - g w - fderiv ℝ g w ((0 : ℝ), k.2))
      nlinarith [mul_le_mul_of_nonneg_left hn2 hL20]
    have h4 : s ^ 2 ≤ s ^ (1 + θ) := by
      have : s ^ (2 : ℝ) ≤ s ^ (1 + θ) :=
        Real.rpow_le_rpow_of_exponent_ge' hk0 hk (by linarith) (by linarith)
      simpa using this
    have h5 : 0 ≤ s ^ (1 + θ) := Real.rpow_nonneg hk0 _
    calc _ ≤ (K + L2) * s ^ 2 := h3
      _ ≤ (K + L2) * s ^ (1 + θ) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ (K + L2 + 2 * B + B1) * s ^ (1 + θ) := by
        apply mul_le_mul_of_nonneg_right _ h5
        linarith
  · have hk1 : 1 ≤ s := (not_le.1 hk).le
    have h1 : |g (w + k) - g w| ≤ 2 * B := by
      have := abs_sub (g (w + k)) (g w)
      linarith [hB (w + k), hB w]
    have h2 : |fderiv ℝ g w ((0 : ℝ), k.2)| ≤ B1 * s := by
      rw [← ktay_sum_lineIter]
      calc |∑ i : Fin 3, lineIter [spaceDir i] g w * k.2 i|
          ≤ ∑ i : Fin 3, |lineIter [spaceDir i] g w * k.2 i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin 3, B1 * |k.2 i| := Finset.sum_le_sum fun i _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hB1d i w) (abs_nonneg _)
        _ = B1 * ∑ i, |k.2 i| := by rw [Finset.mul_sum]
        _ ≤ B1 * s := mul_le_mul_of_nonneg_left (ktay_sum_abs_le k) hB1
    have h3 : s ≤ s ^ (1 + θ) := by
      have : s ^ (1 : ℝ) ≤ s ^ (1 + θ) :=
        Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
      simpa using this
    have h5 : 0 ≤ s ^ (1 + θ) := Real.rpow_nonneg hk0 _
    have h6 : |g (w + k) - g w - fderiv ℝ g w ((0 : ℝ), k.2)| ≤ 2 * B + B1 * s := by
      have := abs_sub (g (w + k) - g w) (fderiv ℝ g w ((0 : ℝ), k.2))
      linarith
    calc _ ≤ 2 * B + B1 * s := h6
      _ ≤ (2 * B + B1) * s := by nlinarith
      _ ≤ (2 * B + B1) * s ^ (1 + θ) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ (K + L2 + 2 * B + B1) * s ^ (1 + θ) := by
        apply mul_le_mul_of_nonneg_right _ h5
        linarith

end RegularityStructures.Phi43

end
