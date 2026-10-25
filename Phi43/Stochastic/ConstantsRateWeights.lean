/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsCovariance
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Power weights on `ℝ × T³`: dyadic integral bounds

The parabolic size on `ℝ × T³` satisfies two volume bounds,
`vol {size ≤ r} ≤ 16 r⁵` and `vol {size ≤ r} ≤ 2 r²`.  A dyadic decomposition turns them into
bounds for the integrals of `size⁻ˢ` over the exterior `{size > ρ}` (for `s` above the relevant
dimension) and over the pointed interior `{0 < size ≤ R}` (for `s` below it).
All bounds are in `ℝ≥0∞`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem constantsRate_volume_ball_le_two {r : ℝ} (hr : 0 ≤ r) :
    volume {z : SpaceTime | torusParabolicSize z ≤ r} ≤ ENNReal.ofReal (2 * r ^ 2) := by
  let S : Set SpaceTime := {z | torusParabolicSize z ≤ r}
  let T : Set SpaceTime := Icc (-(r ^ 2)) (r ^ 2) ×ˢ (Set.univ : Set Torus3)
  have hST : S ⊆ T := by
    intro z hz
    change torusParabolicSize z ≤ r at hz
    have htime : √|z.1| ≤ r := by
      unfold torusParabolicSize at hz
      linarith [torusSpatialNorm_nonneg z.2]
    have hsquare : (√|z.1|) ^ 2 = |z.1| := Real.sq_sqrt (abs_nonneg _)
    have hsq : |z.1| ≤ r ^ 2 := by
      nlinarith [hsquare, Real.sqrt_nonneg |z.1|]
    exact ⟨abs_le.mp hsq, Set.mem_univ _⟩
  have hT : volume T = ENNReal.ofReal (2 * r ^ 2) := by
    dsimp [T]
    change ((volume : Measure ℝ).prod (volume : Measure Torus3))
      (Icc (-(r ^ 2)) (r ^ 2) ×ˢ (Set.univ : Set Torus3)) = _
    have hIcc : volume (Icc (-(r ^ 2)) (r ^ 2)) = ENNReal.ofReal (2 * r ^ 2) := by
      rw [Real.volume_Icc]
      congr 1
      ring
    rw [Measure.prod_prod, hIcc]
    rw [show (Set.univ : Set Torus3) = Set.pi Set.univ (fun _ => Set.univ) by
      ext x
      simp]
    rw [volume_pi_pi]
    simp
  exact (measure_mono hST).trans hT.le

theorem constantsRate_volume_ball_le_five_rpow {r : ℝ} (hr : 0 ≤ r) :
    volume {z : SpaceTime | torusParabolicSize z ≤ r} ≤
      ENNReal.ofReal (16 * r ^ (5 : ℝ)) := by
  have h := volume_torusParabolicBall_le_global hr
  rwa [show r ^ (5 : ℝ) = r ^ 5 by exact_mod_cast Real.rpow_natCast r 5]

theorem constantsRate_volume_ball_le_two_rpow {r : ℝ} (hr : 0 ≤ r) :
    volume {z : SpaceTime | torusParabolicSize z ≤ r} ≤
      ENNReal.ofReal (2 * r ^ (2 : ℝ)) := by
  have h := constantsRate_volume_ball_le_two hr
  rwa [show r ^ (2 : ℝ) = r ^ 2 by exact_mod_cast Real.rpow_natCast r 2]

private theorem two_pow_rpow (j : ℕ) (x : ℝ) : ((2 : ℝ) ^ j) ^ x = ((2 : ℝ) ^ x) ^ j := by
  conv_lhs => rw [← Real.rpow_natCast]
  conv_rhs => rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]

private theorem tail_term (j : ℕ) {d c s ρ : ℝ} (hρ : 0 < ρ) :
    (2 ^ j * ρ) ^ (-s) * (c * (2 ^ (j + 1) * ρ) ^ d) =
      c * 2 ^ d * ρ ^ (d - s) * (2 ^ (d - s)) ^ j := by
  have hu : (0 : ℝ) < 2 ^ j := by positivity
  have h2 : (2 : ℝ) ^ (j + 1) * ρ = 2 * 2 ^ j * ρ := by ring
  rw [h2, Real.mul_rpow hu.le hρ.le, Real.mul_rpow (by positivity) hρ.le,
    Real.mul_rpow (by norm_num) hu.le, ← two_pow_rpow, Real.rpow_sub hu, Real.rpow_sub hρ,
    Real.rpow_neg hu.le, Real.rpow_neg hρ.le]
  field_simp

private theorem head_term (j : ℕ) {d c s R : ℝ} (hR : 0 < R) :
    (R / 2 ^ (j + 1)) ^ (-s) * (c * (R / 2 ^ j) ^ d) =
      c * 2 ^ s * R ^ (d - s) * (2 ^ (s - d)) ^ j := by
  have hu : (0 : ℝ) < 2 ^ j := by positivity
  have h2 : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
  rw [h2, Real.div_rpow hR.le (by positivity), Real.div_rpow hR.le hu.le,
    Real.mul_rpow (by norm_num) hu.le, ← two_pow_rpow, Real.rpow_sub hu, Real.rpow_sub hR,
    Real.rpow_neg hR.le, Real.rpow_neg (by positivity), Real.rpow_neg hu.le]
  have hs2 : ((2 : ℝ) ^ (j : ℕ)) ^ (s : ℝ) ≠ 0 := by positivity
  have hd2 : ((2 : ℝ) ^ (j : ℕ)) ^ (d : ℝ) ≠ 0 := by positivity
  have hRs : R ^ s ≠ 0 := by positivity
  have h2s : (2 : ℝ) ^ s ≠ 0 := by positivity
  field_simp

/-- The exterior `{size > ρ}`: dyadic bound. -/
theorem constantsRate_lintegral_size_tail_le {d c s ρ : ℝ} (hd : 0 < d) (hc : 0 ≤ c)
    (hs : d < s) (hρ : 0 < ρ)
    (hvol : ∀ r : ℝ, 0 ≤ r →
      volume {z : SpaceTime | torusParabolicSize z ≤ r} ≤ ENNReal.ofReal (c * r ^ d)) :
    ∫⁻ z in {z : SpaceTime | ρ < torusParabolicSize z},
        ENNReal.ofReal (torusParabolicSize z ^ (-s)) ≤
      ENNReal.ofReal (c * 2 ^ d / (1 - 2 ^ (d - s)) * ρ ^ (d - s)) := by
  have hq0 : (0 : ℝ) ≤ 2 ^ (d - s) := by positivity
  have hq1 : (2 : ℝ) ^ (d - s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let T : ℕ → Set SpaceTime := fun j =>
    {z | 2 ^ j * ρ ≤ torusParabolicSize z ∧ torusParabolicSize z < 2 ^ (j + 1) * ρ}
  have hTm : ∀ j, MeasurableSet (T j) := fun j =>
    (measurableSet_le measurable_const measurable_torusParabolicSize).inter
      (measurableSet_lt measurable_torusParabolicSize measurable_const)
  have hcover : {z : SpaceTime | ρ < torusParabolicSize z} ⊆ ⋃ j, T j := by
    intro z hz
    have hz' : ρ < torusParabolicSize z := hz
    have hx : 1 ≤ torusParabolicSize z / ρ := by
      rw [le_div_iff₀ hρ]
      linarith
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
    refine mem_iUnion.mpr ⟨n, ?_, ?_⟩
    · rwa [le_div_iff₀ hρ] at hn1
    · rw [div_lt_iff₀ hρ] at hn2
      exact hn2
  have hterm : ∀ j : ℕ, ∫⁻ z in T j, ENNReal.ofReal (torusParabolicSize z ^ (-s)) ≤
      ENNReal.ofReal (c * 2 ^ d * ρ ^ (d - s) * (2 ^ (d - s)) ^ j) := by
    intro j
    have hjρ : 0 < (2 : ℝ) ^ j * ρ := by positivity
    calc
      ∫⁻ z in T j, ENNReal.ofReal (torusParabolicSize z ^ (-s)) ≤
          ∫⁻ _ in T j, ENNReal.ofReal ((2 ^ j * ρ) ^ (-s)) := by
        apply setLIntegral_mono' (hTm j)
        intro z hz
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_nonpos hjρ hz.1 (by linarith)
      _ = ENNReal.ofReal ((2 ^ j * ρ) ^ (-s)) * volume (T j) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal ((2 ^ j * ρ) ^ (-s)) *
          ENNReal.ofReal (c * (2 ^ (j + 1) * ρ) ^ d) := by
        apply mul_le_mul_right
        refine (measure_mono ?_).trans (hvol _ (by positivity))
        intro z hz
        exact hz.2.le
      _ = ENNReal.ofReal (c * 2 ^ d * ρ ^ (d - s) * (2 ^ (d - s)) ^ j) := by
        rw [← ENNReal.ofReal_mul (by positivity), tail_term j hρ]
  calc
    ∫⁻ z in {z : SpaceTime | ρ < torusParabolicSize z},
        ENNReal.ofReal (torusParabolicSize z ^ (-s)) ≤
        ∫⁻ z in ⋃ j, T j, ENNReal.ofReal (torusParabolicSize z ^ (-s)) :=
      lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ z in T j, ENNReal.ofReal (torusParabolicSize z ^ (-s)) :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (c * 2 ^ d * ρ ^ (d - s) * (2 ^ (d - s)) ^ j) :=
      ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j : ℕ, c * 2 ^ d * ρ ^ (d - s) * (2 ^ (d - s)) ^ j) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)]
      exact (summable_geometric_of_lt_one hq0 hq1).mul_left _
    _ = ENNReal.ofReal (c * 2 ^ d / (1 - 2 ^ (d - s)) * ρ ^ (d - s)) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      congr 1
      have : (1 - (2 : ℝ) ^ (d - s)) ≠ 0 := by linarith
      field_simp

/-- The pointed interior `{0 < size ≤ R}`: dyadic bound. -/
theorem constantsRate_lintegral_size_head_le {d c s R : ℝ} (hc : 0 ≤ c)
    (hs0 : 0 < s) (hs : s < d) (hR : 0 < R)
    (hvol : ∀ r : ℝ, 0 ≤ r →
      volume {z : SpaceTime | torusParabolicSize z ≤ r} ≤ ENNReal.ofReal (c * r ^ d)) :
    ∫⁻ z in {z : SpaceTime | 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ R},
        ENNReal.ofReal (torusParabolicSize z ^ (-s)) ≤
      ENNReal.ofReal (c * 2 ^ s / (1 - 2 ^ (s - d)) * R ^ (d - s)) := by
  have hq0 : (0 : ℝ) ≤ 2 ^ (s - d) := by positivity
  have hq1 : (2 : ℝ) ^ (s - d) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let H : ℕ → Set SpaceTime := fun j =>
    {z | R / 2 ^ (j + 1) < torusParabolicSize z ∧ torusParabolicSize z ≤ R / 2 ^ j}
  have hHm : ∀ j, MeasurableSet (H j) := fun j =>
    (measurableSet_lt measurable_const measurable_torusParabolicSize).inter
      (measurableSet_le measurable_torusParabolicSize measurable_const)
  have hcover : {z : SpaceTime | 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ R} ⊆
      ⋃ j, H j := by
    intro z hz
    obtain ⟨hz0, hzR⟩ := hz
    have hx : 1 ≤ R / torusParabolicSize z := by
      rw [le_div_iff₀ hz0]
      linarith
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
    refine mem_iUnion.mpr ⟨n, ?_, ?_⟩
    · rw [div_lt_iff₀ hz0] at hn2
      rw [div_lt_iff₀ (by positivity)]
      linarith
    · rw [le_div_iff₀ hz0] at hn1
      rw [le_div_iff₀ (by positivity)]
      linarith
  have hterm : ∀ j : ℕ, ∫⁻ z in H j, ENNReal.ofReal (torusParabolicSize z ^ (-s)) ≤
      ENNReal.ofReal (c * 2 ^ s * R ^ (d - s) * (2 ^ (s - d)) ^ j) := by
    intro j
    have hjR : 0 < R / (2 : ℝ) ^ (j + 1) := by positivity
    calc
      ∫⁻ z in H j, ENNReal.ofReal (torusParabolicSize z ^ (-s)) ≤
          ∫⁻ _ in H j, ENNReal.ofReal ((R / 2 ^ (j + 1)) ^ (-s)) := by
        apply setLIntegral_mono' (hHm j)
        intro z hz
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_nonpos hjR hz.1.le (by linarith)
      _ = ENNReal.ofReal ((R / 2 ^ (j + 1)) ^ (-s)) * volume (H j) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal ((R / 2 ^ (j + 1)) ^ (-s)) *
          ENNReal.ofReal (c * (R / 2 ^ j) ^ d) := by
        apply mul_le_mul_right
        refine (measure_mono ?_).trans (hvol _ (by positivity))
        intro z hz
        exact hz.2
      _ = ENNReal.ofReal (c * 2 ^ s * R ^ (d - s) * (2 ^ (s - d)) ^ j) := by
        rw [← ENNReal.ofReal_mul (by positivity), head_term j hR]
  calc
    ∫⁻ z in {z : SpaceTime | 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ R},
        ENNReal.ofReal (torusParabolicSize z ^ (-s)) ≤
        ∫⁻ z in ⋃ j, H j, ENNReal.ofReal (torusParabolicSize z ^ (-s)) :=
      lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ z in H j, ENNReal.ofReal (torusParabolicSize z ^ (-s)) :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (c * 2 ^ s * R ^ (d - s) * (2 ^ (s - d)) ^ j) :=
      ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j : ℕ, c * 2 ^ s * R ^ (d - s) * (2 ^ (s - d)) ^ j) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)]
      exact (summable_geometric_of_lt_one hq0 hq1).mul_left _
    _ = ENNReal.ofReal (c * 2 ^ s / (1 - 2 ^ (s - d)) * R ^ (d - s)) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      congr 1
      have : (1 - (2 : ℝ) ^ (s - d)) ≠ 0 := by linarith
      field_simp

end RegularityStructures.Phi43

end
