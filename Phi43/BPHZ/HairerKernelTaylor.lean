/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.HairerKernelTaylorShell
public import Phi43.Structure.CanonicalKernelHairer
import Mathlib.Tactic

/-!
# Second-order bounds for the Euclidean Hairer kernel

For `K = hairerKernel N` and its spatial gradient `G = hairerKernelGrad N` we prove, shell by shell,
for `z ≠ 0` (parabolic sizes):

* `hairerKernelGrad_abs_le`: `|Gᵢ z| ≲ ‖z‖⁻⁴`;
* `hairerKernelGrad_sub_abs_le_of_le`: `|Gᵢ (z + h) - Gᵢ z| ≲ ‖h‖ ‖z‖⁻⁵` for `‖h‖ ≤ 9/10 ‖z‖`;
* `hairerKernel_taylor_abs_le_of_le`: for `θ ∈ [0, 1]` and `‖h‖ ≤ 9/10 ‖z‖`,
  `|K (z + h) - K z - ∑ᵢ Gᵢ z hᵢ| ≲ ‖h‖^(1+θ) ‖z‖^(-(4+θ))`,
  with the constant uniform in `θ`; the time increment of `h` counts as order `2`.

The constants depend on `N` only. The ratio `9/10` (rather than `1/2`) is what the periodisation
needs.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem ktaylor_pow_eq (n k : ℕ) :
    ((2 : ℝ) ^ n) ^ (k : ℝ) = ((2 : ℝ) ^ n) ^ k := Real.rpow_natCast _ k

private theorem ktaylor_setup (N : ℕ) {z h : ParabolicSpace} (hz : 0 < parabolicNorm z)
    (hh : parabolicNorm h ≤ 9 / 10 * parabolicNorm z) :
    ∃ m : ℕ, (∀ j < m, parabolicNorm z / 10 ≤ (2 : ℝ)⁻¹ ^ j) ∧
      ((∀ n, m ≤ n → annShellC N n z = 0 ∧ annShellC N n (z + h) = 0 ∧
        ∀ i : Fin 3, lineIter [spaceDir i] (annShellC N n) z = 0 ∧
          lineIter [spaceDir i] (annShellC N n) (z + h) = 0)) := by
  set r : ℝ := parabolicNorm z / 10 with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨m, hm1, hm2⟩ := hairerKernelTaylor_exists_index hr0
  have hzh : r ≤ parabolicNorm (z + h) := by
    have := parabolicNorm_add_le (z + h) (-h)
    rw [add_neg_cancel_right, parabolicNorm_neg] at this
    rw [hr]; linarith
  refine ⟨m, hm2, fun n hn => ?_⟩
  have hpow : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ m :=
    pow_le_pow_of_le_one (by positivity) (by norm_num) hn
  have h1 : (2 : ℝ)⁻¹ ^ n < parabolicNorm z := hpow.trans_lt (hm1.trans (by rw [hr]; linarith))
  have h2 : (2 : ℝ)⁻¹ ^ n < parabolicNorm (z + h) := hpow.trans_lt (lt_of_lt_of_le hm1 hzh)
  exact ⟨annShellC_eq_zero h1, annShellC_eq_zero h2, fun i =>
    ⟨lineIter_spaceDir_annShellC_eq_zero N n i h1, lineIter_spaceDir_annShellC_eq_zero N n i h2⟩⟩

private theorem ktaylor_sum_le {β s : ℝ} (hβ : 4 ≤ β) (hβ5 : β ≤ 5) (hs : 0 < s) {m : ℕ}
    (hm : ∀ j < m, s / 10 ≤ (2 : ℝ)⁻¹ ^ j) :
    ∑ n ∈ Finset.range m, ((2 : ℝ) ^ n) ^ β ≤ 2 * 10 ^ 5 * s ^ (-β) := by
  have h1 := hairerKernelTaylor_geom_sum_le hβ (by positivity : 0 < s / 10) hm
  have h10 : (10 : ℝ) ^ β ≤ 10 ^ 5 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 10) hβ5
    simpa using this
  have e : ((s / 10) ^ β)⁻¹ = 10 ^ β * s ^ (-β) := by
    rw [Real.div_rpow hs.le (by norm_num), inv_div, Real.rpow_neg hs.le, div_eq_mul_inv]
  have hsb : 0 ≤ s ^ (-β) := Real.rpow_nonneg hs.le _
  calc _ ≤ 2 * ((s / 10) ^ β)⁻¹ := h1
    _ = 2 * (10 ^ β * s ^ (-β)) := by rw [e]
    _ ≤ 2 * (10 ^ 5 * s ^ (-β)) := by gcongr
    _ = 2 * 10 ^ 5 * s ^ (-β) := by ring

/-- **Taylor remainder of the Hairer kernel** (ratio `9/10`). -/
theorem hairerKernel_taylor_abs_le_of_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ 1 → ∀ {z h : ParabolicSpace},
      0 < parabolicNorm z → parabolicNorm h ≤ 9 / 10 * parabolicNorm z →
        |hairerKernel N (z + h) - hairerKernel N z -
            ∑ i : Fin 3, hairerKernelGrad N i z * h.2 i| ≤
          C * parabolicNorm h ^ (1 + θ) * parabolicNorm z ^ (-(4 + θ)) := by
  obtain ⟨L, hL, hshell⟩ := annShellC_taylor_abs_le N
  refine ⟨2 * 10 ^ 5 * L, by positivity, fun {θ} hθ0 hθ1 z h hz hh => ?_⟩
  obtain ⟨m, hm, hvan⟩ := ktaylor_setup N hz hh
  have e1 : hairerKernel N (z + h) = ∑ n ∈ Finset.range m, annShellC N n (z + h) := by
    unfold hairerKernel
    exact tsum_eq_sum fun n hn => (hvan n (not_lt.1 (by simpa using hn))).2.1
  have e2 : hairerKernel N z = ∑ n ∈ Finset.range m, annShellC N n z := by
    unfold hairerKernel
    exact tsum_eq_sum fun n hn => (hvan n (not_lt.1 (by simpa using hn))).1
  have e3 : ∀ i : Fin 3, hairerKernelGrad N i z =
      ∑ n ∈ Finset.range m, lineIter [spaceDir i] (annShellC N n) z := fun i => by
    unfold hairerKernelGrad
    exact tsum_eq_sum fun n hn => (hvan n (not_lt.1 (by simpa using hn))).2.2 i |>.1
  have hdiff : hairerKernel N (z + h) - hairerKernel N z -
      ∑ i : Fin 3, hairerKernelGrad N i z * h.2 i =
      ∑ n ∈ Finset.range m, (annShellC N n (z + h) - annShellC N n z -
        ∑ i : Fin 3, lineIter [spaceDir i] (annShellC N n) z * h.2 i) := by
    simp only [e1, e2, e3, Finset.sum_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  rw [hdiff]
  have hβ : 4 ≤ 4 + θ := by linarith
  have hsum := ktaylor_sum_le hβ (by linarith) hz hm
  have hh0 := Real.rpow_nonneg (parabolicNorm_nonneg h) (1 + θ)
  calc |∑ n ∈ Finset.range m, (annShellC N n (z + h) - annShellC N n z -
          ∑ i : Fin 3, lineIter [spaceDir i] (annShellC N n) z * h.2 i)|
      ≤ ∑ n ∈ Finset.range m, |annShellC N n (z + h) - annShellC N n z -
          ∑ i : Fin 3, lineIter [spaceDir i] (annShellC N n) z * h.2 i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range m, L * parabolicNorm h ^ (1 + θ) * ((2 : ℝ) ^ n) ^ (4 + θ) :=
        Finset.sum_le_sum fun n _ => by
          have := hshell hθ0 hθ1 n z h
          linarith [this, show L * ((2 : ℝ) ^ n) ^ (4 + θ) * parabolicNorm h ^ (1 + θ) =
            L * parabolicNorm h ^ (1 + θ) * ((2 : ℝ) ^ n) ^ (4 + θ) by ring]
    _ = L * parabolicNorm h ^ (1 + θ) * ∑ n ∈ Finset.range m, ((2 : ℝ) ^ n) ^ (4 + θ) := by
        rw [Finset.mul_sum]
    _ ≤ L * parabolicNorm h ^ (1 + θ) * (2 * 10 ^ 5 * parabolicNorm z ^ (-(4 + θ))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * 10 ^ 5 * L * parabolicNorm h ^ (1 + θ) * parabolicNorm z ^ (-(4 + θ)) := by ring

/-- **Bound of the spatial gradient of the Hairer kernel**: `|∂ᵢK z| ≤ C ‖z‖⁻⁴`. -/
theorem hairerKernelGrad_abs_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 3) {z : ParabolicSpace}, 0 < parabolicNorm z →
      |hairerKernelGrad N i z| ≤ C * parabolicNorm z ^ (-(4 : ℝ)) := by
  obtain ⟨B, hB, hshell⟩ := annShellC_lineIter_abs_le N
  refine ⟨2 * 10 ^ 5 * B, by positivity, fun i z hz => ?_⟩
  obtain ⟨m, hm, hvan⟩ := ktaylor_setup N (h := 0) hz (by simp [parabolicNorm_zero]; positivity)
  have e3 : hairerKernelGrad N i z =
      ∑ n ∈ Finset.range m, lineIter [spaceDir i] (annShellC N n) z := by
    unfold hairerKernelGrad
    exact tsum_eq_sum fun n hn => (hvan n (not_lt.1 (by simpa using hn))).2.2 i |>.1
  have hsum := ktaylor_sum_le (β := 4) le_rfl (by norm_num) hz hm
  calc |hairerKernelGrad N i z|
      ≤ ∑ n ∈ Finset.range m, |lineIter [spaceDir i] (annShellC N n) z| := by
        rw [e3]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range m, B * ((2 : ℝ) ^ n) ^ (4 : ℝ) :=
        Finset.sum_le_sum fun n _ => by
          have := hshell i n z
          rwa [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ktaylor_pow_eq]
    _ = B * ∑ n ∈ Finset.range m, ((2 : ℝ) ^ n) ^ (4 : ℝ) := by rw [Finset.mul_sum]
    _ ≤ B * (2 * 10 ^ 5 * parabolicNorm z ^ (-(4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum hB
    _ = 2 * 10 ^ 5 * B * parabolicNorm z ^ (-(4 : ℝ)) := by ring

/-- **Increment of the spatial gradient** (ratio `9/10`). -/
theorem hairerKernelGrad_sub_abs_le_of_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 3) {z h : ParabolicSpace}, 0 < parabolicNorm z →
      parabolicNorm h ≤ 9 / 10 * parabolicNorm z →
        |hairerKernelGrad N i (z + h) - hairerKernelGrad N i z| ≤
          C * parabolicNorm h * parabolicNorm z ^ (-(5 : ℝ)) := by
  obtain ⟨L, hL, hshell⟩ := annShellC_lineIter_sub_abs_le N
  refine ⟨2 * 10 ^ 5 * L, by positivity, fun i z h hz hh => ?_⟩
  obtain ⟨m, hm, hvan⟩ := ktaylor_setup N hz hh
  have e3 : hairerKernelGrad N i z =
      ∑ n ∈ Finset.range m, lineIter [spaceDir i] (annShellC N n) z := by
    unfold hairerKernelGrad
    exact tsum_eq_sum fun n hn => (hvan n (not_lt.1 (by simpa using hn))).2.2 i |>.1
  have e4 : hairerKernelGrad N i (z + h) =
      ∑ n ∈ Finset.range m, lineIter [spaceDir i] (annShellC N n) (z + h) := by
    unfold hairerKernelGrad
    exact tsum_eq_sum fun n hn => (hvan n (not_lt.1 (by simpa using hn))).2.2 i |>.2
  have hsum := ktaylor_sum_le (β := 5) (by norm_num) le_rfl hz hm
  have hh0 := parabolicNorm_nonneg h
  calc |hairerKernelGrad N i (z + h) - hairerKernelGrad N i z|
      ≤ ∑ n ∈ Finset.range m, |lineIter [spaceDir i] (annShellC N n) (z + h) -
          lineIter [spaceDir i] (annShellC N n) z| := by
        rw [e3, e4, ← Finset.sum_sub_distrib]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range m, L * parabolicNorm h * ((2 : ℝ) ^ n) ^ (5 : ℝ) :=
        Finset.sum_le_sum fun n _ => by
          have := hshell i n z h
          rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, ktaylor_pow_eq]
          linarith [this, show L * ((2 : ℝ) ^ n) ^ 5 * parabolicNorm h =
            L * parabolicNorm h * ((2 : ℝ) ^ n) ^ 5 by ring]
    _ = L * parabolicNorm h * ∑ n ∈ Finset.range m, ((2 : ℝ) ^ n) ^ (5 : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ L * parabolicNorm h * (2 * 10 ^ 5 * parabolicNorm z ^ (-(5 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * 10 ^ 5 * L * parabolicNorm h * parabolicNorm z ^ (-(5 : ℝ)) := by ring

end RegularityStructures.Phi43

end
