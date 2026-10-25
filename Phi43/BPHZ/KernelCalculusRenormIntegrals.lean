/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.KernelCalculusBasic

/-!
# Integrals of the majorants for the renormalised convolution

Each of the four majorants in `abs_mul_sub_le_majorant` is integrable, with integral at most a
constant multiple of `ρ^(5-a₁-a₂)`, where `ρ = s(z)`.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.16, p. 156.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

private theorem rpow_mul_rpow_div {ρ k : ℝ} (hρ : 0 < ρ) (hk : 0 < k) (α β γ : ℝ)
    (h : α + β = γ) : ρ ^ α * (ρ / k) ^ β = k ^ (-β) * ρ ^ γ := by
  rw [Real.div_rpow hρ.le hk.le, Real.rpow_neg hk.le, ← h, Real.rpow_add hρ]
  field_simp

private theorem rpow_div_mul_rpow_div {ρ k m : ℝ} (hρ : 0 < ρ) (hk : 0 < k) (hm : 0 < m)
    (α β γ : ℝ) (h : α + β = γ) :
    (ρ / k) ^ α * (ρ / m) ^ β = k ^ (-α) * m ^ (-β) * ρ ^ γ := by
  rw [Real.div_rpow hρ.le hk.le, Real.div_rpow hρ.le hm.le, Real.rpow_neg hk.le,
    Real.rpow_neg hm.le, ← h, Real.rpow_add hρ]
  field_simp

theorem integral_renorm_majorant_near {a₁ a₂ : ℝ} (ha₁ : 5 < a₁) (ha₁' : a₁ < 6) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ B : ℝ}, 0 < ρ → 0 ≤ B →
      Integrable (fun x => B * (2 * ρ ^ (-a₂ - 1)) * singularLocalWeight (a₁ - 1) (ρ / 4) x) ∧
      ∫ x, B * (2 * ρ ^ (-a₂ - 1)) * singularLocalWeight (a₁ - 1) (ρ / 4) x ≤
        B * K * ρ ^ (5 - a₁ - a₂) := by
  have hp : 0 < a₁ - 1 := by linarith
  have hp5 : a₁ - 1 < 5 := by linarith
  have h5 : 0 < 5 - (a₁ - 1) := by linarith
  refine ⟨2 * (80 / (5 - (a₁ - 1)) * 4 ^ (-(5 - (a₁ - 1)))), by positivity, ?_⟩
  intro ρ B hρ hB
  have iL := integrable_singularLocalWeight hp hp5 (by positivity : 0 < ρ / 4)
  refine ⟨iL.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hb := integral_singularLocalWeight_le hp hp5 (by positivity : 0 < ρ / 4)
  have hc : 0 ≤ B * (2 * ρ ^ (-a₂ - 1)) := by
    have := Real.rpow_nonneg hρ.le (-a₂ - 1)
    positivity
  have key := rpow_mul_rpow_div hρ (by norm_num : (0 : ℝ) < 4) (-a₂ - 1) (5 - (a₁ - 1))
    (5 - a₁ - a₂) (by ring)
  calc
    B * (2 * ρ ^ (-a₂ - 1)) * ∫ x, singularLocalWeight (a₁ - 1) (ρ / 4) x ≤
        B * (2 * ρ ^ (-a₂ - 1)) * (80 / (5 - (a₁ - 1)) * (ρ / 4) ^ (5 - (a₁ - 1))) :=
      mul_le_mul_of_nonneg_left hb hc
    _ = B * 2 * (80 / (5 - (a₁ - 1))) * (ρ ^ (-a₂ - 1) * (ρ / 4) ^ (5 - (a₁ - 1))) := by ring
    _ = _ := by rw [key]; ring

theorem integral_renorm_majorant_tail {a₁ : ℝ} (ha₁ : 5 < a₁) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ c : ℝ}, 0 < ρ → 0 ≤ c →
      Integrable (fun x => c * singularTailWeight a₁ (ρ / 4) x) ∧
      ∫ x, c * singularTailWeight a₁ (ρ / 4) x ≤ c * K * ρ ^ (5 - a₁) := by
  have h5 : 0 < a₁ - 5 := by linarith
  have h0 : 0 < a₁ := by linarith
  refine ⟨16 * a₁ / (a₁ - 5) * 4 ^ (-(5 - a₁)), by positivity, ?_⟩
  intro ρ c hρ hc
  have iL := integrable_singularTailWeight ha₁ (by positivity : 0 < ρ / 4)
  refine ⟨iL.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hb := integral_singularTailWeight_le ha₁ (by positivity : 0 < ρ / 4)
  have key : (ρ / 4) ^ (5 - a₁) = 4 ^ (-(5 - a₁)) * ρ ^ (5 - a₁) := by
    rw [Real.div_rpow hρ.le (by norm_num), Real.rpow_neg (by norm_num)]
    field_simp
  calc
    c * ∫ x, singularTailWeight a₁ (ρ / 4) x ≤ c * (16 * a₁ / (a₁ - 5) * (ρ / 4) ^ (5 - a₁)) :=
      mul_le_mul_of_nonneg_left hb hc
    _ = _ := by rw [key]; ring

theorem integral_renorm_majorant_far {a₁ a₂ : ℝ} (ha₂ : 0 ≤ a₂) (ha₂5 : a₂ < 5) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : SpaceTime) {ρ B : ℝ}, 0 < ρ → 0 ≤ B →
      Integrable (fun x => B * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) *
        singularLocalWeight ((5 + a₂) / 2) (ρ / 8) (z - x)) ∧
      ∫ x, B * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) *
        singularLocalWeight ((5 + a₂) / 2) (ρ / 8) (z - x) ≤
        B * K * ρ ^ (5 - a₁ - a₂) := by
  have hp : 0 < (5 + a₂) / 2 := by linarith
  have hp5 : (5 + a₂) / 2 < 5 := by linarith
  have h5 : 0 < 5 - (5 + a₂) / 2 := by linarith
  refine ⟨4 ^ (-(-a₁)) * 8 ^ (-(5 - a₂)) * (80 / (5 - (5 + a₂) / 2)), by positivity, ?_⟩
  intro z ρ B hρ hB
  have hρ8 : 0 < ρ / 8 := by positivity
  have iL := integrable_singularLocalWeight hp hp5 hρ8
  have iL' := integrable_comp_sub_left_spaceTime iL z
  refine ⟨iL'.const_mul _, ?_⟩
  rw [integral_const_mul, integral_comp_sub_left_spaceTime (singularLocalWeight ((5 + a₂) / 2)
    (ρ / 8)) z]
  have hb := integral_singularLocalWeight_le hp hp5 hρ8
  have hc : 0 ≤ B * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) := by
    have h1 : 0 ≤ (ρ / 4) ^ (-a₁) := Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ (ρ / 8) ^ ((5 - a₂) / 2) := Real.rpow_nonneg hρ8.le _
    exact mul_nonneg hB (mul_nonneg h1 h2)
  have e1 : (ρ / 8) ^ ((5 - a₂) / 2) * (ρ / 8) ^ (5 - (5 + a₂) / 2) = (ρ / 8) ^ (5 - a₂) := by
    rw [← Real.rpow_add hρ8]; ring_nf
  have key := rpow_div_mul_rpow_div hρ (by norm_num : (0 : ℝ) < 4) (by norm_num : (0 : ℝ) < 8)
    (-a₁) (5 - a₂) (5 - a₁ - a₂) (by ring)
  calc
    B * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) *
        ∫ x, singularLocalWeight ((5 + a₂) / 2) (ρ / 8) x ≤
      B * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) *
        (80 / (5 - (5 + a₂) / 2) * (ρ / 8) ^ (5 - (5 + a₂) / 2)) :=
      mul_le_mul_of_nonneg_left hb hc
    _ = B * (80 / (5 - (5 + a₂) / 2)) * ((ρ / 4) ^ (-a₁) *
        ((ρ / 8) ^ ((5 - a₂) / 2) * (ρ / 8) ^ (5 - (5 + a₂) / 2))) := by ring
    _ = _ := by rw [e1, key]; ring

end RegularityStructures

end
