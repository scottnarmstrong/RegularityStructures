/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsGlobal
public import RegularityStructures.Torus.KernelBoundsLargeTime
public import RegularityStructures.Torus.KernelBoundsGaussian
public import RegularityStructures.Torus.KernelBoundsGeometry

/-!
# Auxiliary size bounds for the massive heat kernel

A fourth-order global bound `G z ≲ size(z)⁻⁴`, the smallness `G(τ, x) ≲ √τ |x|⁻⁴` of the kernel at
small positive times away from the singularity, and the comparison of `size z⁴` with `e^{τ}` for
times `τ` near `z.1`.
-/

@[expose] public noncomputable section

open Real Set

namespace RegularityStructures.Phi43

open RegularityStructures

theorem constantsRate_massive_le_inv_four :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : SpaceTime, 0 < torusParabolicSize z →
      massiveHeatKernel z ≤ C * torusParabolicSize z ^ (-(4 : ℝ)) := by
  obtain ⟨C₀, hC₀, hG⟩ := massiveHeatKernel_global_singular_bound
  obtain ⟨C₁, hC₁⟩ := massiveHeatKernel_exponential_bound
  refine ⟨2 * C₀ + 384 * max C₁ 0, by positivity, ?_⟩
  intro z hz
  set σ : ℝ := torusParabolicSize z with hσ
  have h3 := hG z hz
  have hpow : σ ^ (-(3 : ℝ)) = σ * σ ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_one_add' hz.le (by norm_num)]
    norm_num
  have hn0 : 0 ≤ σ ^ (-(4 : ℝ)) := Real.rpow_nonneg hz.le _
  have hsp : torusSpatialNorm z.2 ≤ 7 / 8 := torusSpatialNorm_le_seven_eighth z.2
  by_cases h0 : z.1 ≤ 0
  · have : massiveHeatKernel z = 0 := by
      simp [massiveHeatKernel, not_lt.mpr h0]
    rw [this]
    positivity
  have hzpos : 0 < z.1 := lt_of_not_ge h0
  have hσdef : σ = √|z.1| + torusSpatialNorm z.2 := rfl
  have habs : |z.1| = z.1 := abs_of_pos hzpos
  by_cases h1 : z.1 < 1
  · have hσ2 : σ ≤ 2 := by
      have ht : √|z.1| ≤ 1 := by
        rw [habs]
        calc
          √z.1 ≤ √1 := Real.sqrt_le_sqrt h1.le
          _ = 1 := Real.sqrt_one
      linarith
    calc
      massiveHeatKernel z ≤ C₀ * σ ^ (-(3 : ℝ)) := h3
      _ = C₀ * (σ * σ ^ (-(4 : ℝ))) := by rw [hpow]
      _ ≤ C₀ * (2 * σ ^ (-(4 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hC₀
        exact mul_le_mul_of_nonneg_right hσ2 hn0
      _ ≤ _ := by
        nlinarith [mul_nonneg hn0 (by positivity : (0 : ℝ) ≤ 384 * max C₁ 0)]
  · have h1' : 1 ≤ z.1 := not_lt.mp h1
    have hexp := hC₁ z h1'
    have hσle : σ ≤ 2 * z.1 := by
      have ht : √|z.1| ≤ z.1 := by
        rw [habs]
        exact Real.sqrt_le_self_iff.mpr (Or.inr h1')
      linarith
    have hσ4 : σ ^ 4 ≤ 16 * z.1 ^ 4 := by
      calc
        σ ^ 4 ≤ (2 * z.1) ^ 4 := pow_le_pow_left₀ hz.le hσle 4
        _ = 16 * z.1 ^ 4 := by ring
    have hfac := Real.pow_div_factorial_le_exp z.1 hzpos.le 4
    have hfac' : z.1 ^ 4 ≤ 24 * exp z.1 := by
      have : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
      rw [this, div_le_iff₀ (by norm_num)] at hfac
      linarith
    have hexpσ : exp (-z.1) ≤ 384 * σ ^ (-(4 : ℝ)) := by
      have hσ4pos : 0 < σ ^ 4 := by positivity
      have hnr : σ ^ (-(4 : ℝ)) = (σ ^ 4)⁻¹ := by
        rw [Real.rpow_neg hz.le]
        congr 1
        exact_mod_cast Real.rpow_natCast σ 4
      rw [hnr, ← div_eq_mul_inv, le_div_iff₀ hσ4pos]
      have he : exp (-z.1) * exp z.1 = 1 := by rw [← Real.exp_add]; simp
      calc
        exp (-z.1) * σ ^ 4 ≤ exp (-z.1) * (16 * z.1 ^ 4) :=
          mul_le_mul_of_nonneg_left hσ4 (exp_nonneg _)
        _ ≤ exp (-z.1) * (16 * (24 * exp z.1)) := by
          apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
          linarith
        _ = 384 := by
          have : exp (-z.1) * (16 * (24 * exp z.1)) = 384 * (exp (-z.1) * exp z.1) := by ring
          rw [this, he]
          ring
    calc
      massiveHeatKernel z ≤ C₁ * exp (-z.1) := hexp
      _ ≤ max C₁ 0 * exp (-z.1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_nonneg _)
      _ ≤ max C₁ 0 * (384 * σ ^ (-(4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hexpσ (le_max_right _ _)
      _ ≤ _ := by
        nlinarith [mul_nonneg hn0 hC₀, mul_nonneg hn0 (le_max_right C₁ 0)]

theorem constantsRate_massive_early :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (x : Torus3), 0 < τ → τ ≤ 1 → 0 < torusSpatialNorm x →
      massiveHeatKernel (τ, x) ≤ C * √τ * torusSpatialNorm x ^ (-(4 : ℝ)) := by
  refine ⟨(4 * π) ^ (-(3 : ℝ) / 2) * 32 * heatKernelMajorant,
    mul_nonneg (mul_nonneg (by positivity) (by norm_num)) nonneg_heatKernelMajorant, ?_⟩
  intro τ x hτ hτ1 hν
  set ν : ℝ := torusSpatialNorm x with hνdef
  have hG : massiveHeatKernel (τ, x) ≤ heatKernel τ x := by
    simp only [massiveHeatKernel, hτ, ite_true]
    have h1 : exp (-τ) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    calc
      exp (-τ) * heatKernel τ x ≤ 1 * heatKernel τ x :=
        mul_le_mul_of_nonneg_right h1 (heatKernel_nonneg hτ x)
      _ = heatKernel τ x := one_mul _
  refine hG.trans ((heatKernel_le_spatial_gaussian hτ hτ1 x).trans ?_)
  rw [← torusSpatialNorm_sq, ← hνdef]
  set u : ℝ := ν ^ 2 / (4 * τ) with hu
  have hu0 : 0 ≤ u := by positivity
  have hexp : exp (-ν ^ 2 / (4 * τ)) = exp (-u) := by
    congr 1
    rw [hu]
    ring
  have hu2 : u ^ 2 * exp (-u) ≤ 2 := by
    have h := Real.quadratic_le_exp_of_nonneg hu0
    have he : exp u * exp (-u) = 1 := by rw [← Real.exp_add]; simp
    have : u ^ 2 / 2 ≤ exp u := by nlinarith
    calc
      u ^ 2 * exp (-u) = 2 * (u ^ 2 / 2 * exp (-u)) := by ring
      _ ≤ 2 * (exp u * exp (-u)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right this (exp_nonneg _)
      _ = 2 := by rw [he]; ring
  have hν4 : ν ^ 4 = 16 * τ ^ 2 * u ^ 2 := by
    rw [hu]
    field_simp
    ring
  have hτ32 : τ ^ (-(3 : ℝ) / 2) = √τ * (τ ^ 2)⁻¹ := by
    rw [Real.sqrt_eq_rpow, show -(3 : ℝ) / 2 = 1 / 2 + (-(2 : ℝ)) by ring,
      Real.rpow_add hτ, Real.rpow_neg hτ.le]
    congr 2
    exact_mod_cast Real.rpow_natCast τ 2
  have hν4r : ν ^ (-(4 : ℝ)) = (ν ^ 4)⁻¹ := by
    rw [Real.rpow_neg hν.le]
    congr 1
    exact_mod_cast Real.rpow_natCast ν 4
  have hpref : (4 * π * τ) ^ (-(3 : ℝ) / 2) = (4 * π) ^ (-(3 : ℝ) / 2) * τ ^ (-(3 : ℝ) / 2) :=
    Real.mul_rpow (by positivity) hτ.le
  rw [hexp, hpref, hτ32, hν4r]
  have hν40 : 0 < ν ^ 4 := by positivity
  have hτ20 : 0 < τ ^ 2 := by positivity
  have hkey : exp (-u) * (τ ^ 2)⁻¹ ≤ 32 * (ν ^ 4)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, mul_one_div, div_le_div_iff₀ hτ20 hν40]
    rw [hν4]
    nlinarith [hu2, sq_nonneg τ, mul_nonneg (sq_nonneg τ) (sub_nonneg.mpr hu2)]
  have hA : 0 ≤ (4 * π) ^ (-(3 : ℝ) / 2) := by positivity
  have hK := nonneg_heatKernelMajorant
  calc
    (4 * π) ^ (-(3 : ℝ) / 2) * (√τ * (τ ^ 2)⁻¹) * exp (-u) * heatKernelMajorant =
        (4 * π) ^ (-(3 : ℝ) / 2) * √τ * (exp (-u) * (τ ^ 2)⁻¹) * heatKernelMajorant := by ring
    _ ≤ (4 * π) ^ (-(3 : ℝ) / 2) * √τ * (32 * (ν ^ 4)⁻¹) * heatKernelMajorant := by
      gcongr
    _ = (4 * π) ^ (-(3 : ℝ) / 2) * 32 * heatKernelMajorant * √τ * (ν ^ 4)⁻¹ := by ring

theorem constantsRate_exp_mul_size_pow_four :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : SpaceTime) (τ : ℝ), 1 / 2 ≤ τ → |z.1 - τ| ≤ 1 →
      exp (-τ) * torusParabolicSize z ^ 4 ≤ C := by
  refine ⟨15000, by norm_num, ?_⟩
  intro z τ hτ hzτ
  have hτ0 : 0 < τ := by linarith
  have hsp : torusSpatialNorm z.2 ≤ 7 / 8 := torusSpatialNorm_le_seven_eighth z.2
  have habs : |z.1| ≤ τ + 1 := by
    have := abs_le.mp hzτ
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]
  have hsq : √|z.1| ≤ τ + 1 := by
    calc
      √|z.1| ≤ √(τ + 1) := Real.sqrt_le_sqrt habs
      _ ≤ τ + 1 := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hσ : torusParabolicSize z ≤ 5 * τ := by
    unfold torusParabolicSize
    linarith
  have hσ0 : 0 ≤ torusParabolicSize z := torusParabolicSize_nonneg z
  have hσ4 : torusParabolicSize z ^ 4 ≤ 625 * τ ^ 4 := by
    calc
      torusParabolicSize z ^ 4 ≤ (5 * τ) ^ 4 := pow_le_pow_left₀ hσ0 hσ 4
      _ = 625 * τ ^ 4 := by ring
  have hfac := Real.pow_div_factorial_le_exp τ hτ0.le 4
  have hfac' : τ ^ 4 ≤ 24 * exp τ := by
    have : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [this, div_le_iff₀ (by norm_num)] at hfac
    linarith
  have he : exp (-τ) * exp τ = 1 := by rw [← Real.exp_add]; simp
  calc
    exp (-τ) * torusParabolicSize z ^ 4 ≤ exp (-τ) * (625 * τ ^ 4) :=
      mul_le_mul_of_nonneg_left hσ4 (exp_nonneg _)
    _ ≤ exp (-τ) * (625 * (24 * exp τ)) := by
      apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
      linarith
    _ = 15000 := by
      have : exp (-τ) * (625 * (24 * exp τ)) = 15000 * (exp (-τ) * exp τ) := by ring
      rw [this, he]
      ring

end RegularityStructures.Phi43

end
