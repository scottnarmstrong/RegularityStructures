/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateMassiveInc
public import Phi43.Stochastic.ConstantsRateLift

/-!
# Increments of the massive heat kernel on `ℝ × T³`

`|G(z - h) - G(z)| ≲ size(h) size(z)⁻⁴` for `64 size(h) ≤ size(z)` and `size(h) ≤ 1/16`.  The
increment is split into a spatial increment at the shifted time and a time increment at the
original point; the cases of positive and non-positive times, and of small and large times, are
treated separately.
-/

@[expose] public noncomputable section

open Real Set

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem abs_shift_sq_le (h : SpaceTime) : |h.1| ≤ torusParabolicSize h ^ 2 := by
  have h1 : √|h.1| ≤ torusParabolicSize h := by
    unfold torusParabolicSize
    linarith [torusSpatialNorm_nonneg h.2]
  calc
    |h.1| = √|h.1| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
    _ ≤ torusParabolicSize h ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2

private theorem sum_abs_centered_le (h : SpaceTime) :
    ∑ j, |torusCenteredRep h.2 j| ≤ 2 * torusParabolicSize h := by
  have := constantsRate_parabolicNorm_centered_le h
  unfold parabolicNorm at this
  linarith [Real.sqrt_nonneg |h.1|]

private theorem sqrt_abs_le_of_sub (t s : ℝ) : √|t| ≤ √|t - s| + √|s| := by
  have := sqrt_abs_add_le (t - s) s
  rwa [sub_add_cancel] at this

private theorem sqrt_abs_shift_le (h : SpaceTime) : √|h.1| ≤ torusParabolicSize h := by
  unfold torusParabolicSize
  linarith [torusSpatialNorm_nonneg h.2]

theorem constantsRate_massive_space_part :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z h : SpaceTime, 0 < torusParabolicSize z →
      64 * torusParabolicSize h ≤ torusParabolicSize z → torusParabolicSize h ≤ 1 / 16 →
      |massiveHeatKernel (z.1 - h.1, z.2 - h.2) - massiveHeatKernel (z.1 - h.1, z.2)| ≤
        B * torusParabolicSize h * torusParabolicSize z ^ (-(4 : ℝ)) := by
  obtain ⟨C₁, hC₁, hsmall⟩ := constantsRate_massive_space_small
  obtain ⟨C₂, hC₂, hlarge⟩ := constantsRate_massive_space_large
  obtain ⟨C₆, hC₆, hexp⟩ := constantsRate_exp_mul_size_pow_four
  refine ⟨2 * C₁ * (64 / 63) ^ 4 + 2 * C₂ * C₆, by positivity, ?_⟩
  intro z h hσ hzh hr1
  set r : ℝ := torusParabolicSize h with hr
  set σ : ℝ := torusParabolicSize z with hσdef
  have hr0 : 0 ≤ r := torusParabolicSize_nonneg h
  have hσ4 : 0 ≤ σ ^ (-(4 : ℝ)) := Real.rpow_nonneg hσ.le _
  have hsum := sum_abs_centered_le h
  have hs2 := abs_shift_sq_le h
  by_cases ht' : 0 < z.1 - h.1
  swap
  · have h1 : massiveHeatKernel (z.1 - h.1, z.2 - h.2) = 0 := by
      simp [massiveHeatKernel, ht']
    have h2 : massiveHeatKernel (z.1 - h.1, z.2) = 0 := by
      simp [massiveHeatKernel, ht']
    rw [h1, h2]
    simp only [sub_self, abs_zero]
    positivity
  set t' : ℝ := z.1 - h.1 with ht'def
  by_cases ht1 : t' ≤ 1
  · -- small time
    have hq : (63 / 64) * σ ≤ √t' + torusSpatialNorm z.2 := by
      have hsq : √|z.1| ≤ √t' + r := by
        have h1 := sqrt_abs_le_of_sub z.1 h.1
        have h2 : √|h.1| ≤ r := sqrt_abs_shift_le h
        have h3 : |z.1 - h.1| = t' := abs_of_pos ht'
        rw [h3] at h1
        linarith
      have : σ = √|z.1| + torusSpatialNorm z.2 := rfl
      linarith
    have hA : ∑ j, |torusCenteredRep h.2 j| ≤ (√t' + torusSpatialNorm z.2) / 8 := by
      linarith
    have h1 := hsmall t' z.2 h.2 ht' ht1 hA
    have hq0 : 0 < (63 / 64) * σ := by positivity
    have hpow : (√t' + torusSpatialNorm z.2) ^ (-(4 : ℝ)) ≤ ((63 / 64) * σ) ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hq0 hq (by norm_num)
    have hmul : ((63 / 64) * σ) ^ (-(4 : ℝ)) = (64 / 63) ^ 4 * σ ^ (-(4 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num) hσ.le, Real.rpow_neg (by norm_num),
        show ((63 / 64 : ℝ) ^ (4 : ℝ)) = (63 / 64 : ℝ) ^ (4 : ℕ) by
          exact_mod_cast Real.rpow_natCast (63 / 64 : ℝ) 4]
      norm_num
    have hsum0 : 0 ≤ ∑ j, |torusCenteredRep h.2 j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    calc
      _ ≤ C₁ * (∑ j, |torusCenteredRep h.2 j|) *
          (√t' + torusSpatialNorm z.2) ^ (-(4 : ℝ)) := h1
      _ ≤ C₁ * (2 * r) * (((63 / 64) * σ) ^ (-(4 : ℝ))) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hsum hC₁
        · exact hpow
        · exact Real.rpow_nonneg (add_nonneg (Real.sqrt_nonneg _) (torusSpatialNorm_nonneg _)) _
        · positivity
      _ = 2 * C₁ * (64 / 63) ^ 4 * r * σ ^ (-(4 : ℝ)) := by rw [hmul]; ring
      _ ≤ _ := by
        have : 0 ≤ 2 * C₂ * C₆ * r * σ ^ (-(4 : ℝ)) := by positivity
        linarith
  · -- large time
    have ht1' : 1 < t' := lt_of_not_ge ht1
    have h1 := hlarge t' z.2 h.2 (by linarith)
    have hz1 : |z.1 - t'| ≤ 1 := by
      have : z.1 - t' = h.1 := by rw [ht'def]; ring
      rw [this]
      have : |h.1| ≤ 1 := by nlinarith [hs2, hr1, hr0]
      exact this
    have h6 := hexp z t' (by linarith) hz1
    have hexp' : exp (-t') ≤ C₆ * σ ^ (-(4 : ℝ)) := by
      have hσ4pos : 0 < σ ^ 4 := by positivity
      have hnr : σ ^ (-(4 : ℝ)) = (σ ^ 4)⁻¹ := by
        rw [Real.rpow_neg hσ.le]
        congr 1
        exact_mod_cast Real.rpow_natCast σ 4
      rw [hnr, ← div_eq_mul_inv, le_div_iff₀ hσ4pos]
      linarith
    have hsum0 : 0 ≤ ∑ j, |torusCenteredRep h.2 j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    calc
      _ ≤ C₂ * exp (-t') * ∑ j, |torusCenteredRep h.2 j| := h1
      _ ≤ C₂ * (C₆ * σ ^ (-(4 : ℝ))) * (2 * r) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hexp' hC₂
        · exact hsum
        · exact hsum0
        · positivity
      _ = 2 * C₂ * C₆ * r * σ ^ (-(4 : ℝ)) := by ring
      _ ≤ _ := by
        have : 0 ≤ 2 * C₁ * (64 / 63) ^ 4 * r * σ ^ (-(4 : ℝ)) := by positivity
        linarith

private theorem massive_eq_zero_of_nonpos (τ : ℝ) (x : Torus3) (h : τ ≤ 0) :
    massiveHeatKernel (τ, x) = 0 := by
  simp [massiveHeatKernel, not_lt.mpr h]

private theorem rpow_neg_four_eq (x : ℝ) (hx : 0 ≤ x) : x ^ (-(4 : ℝ)) = (x ^ 4)⁻¹ := by
  rw [Real.rpow_neg hx]
  congr 1
  exact_mod_cast Real.rpow_natCast x 4

private theorem rpow_neg_five_eq (x : ℝ) (hx : 0 ≤ x) : x ^ (-(5 : ℝ)) = (x ^ 5)⁻¹ := by
  rw [Real.rpow_neg hx]
  congr 1
  exact_mod_cast Real.rpow_natCast x 5

private theorem term_quarter_bound {r σ : ℝ} (hσ : 0 < σ) (hr0 : 0 ≤ r) (hrσ : r ≤ σ) :
    r ^ 2 * (σ / 4) ^ (-(5 : ℝ)) ≤ 4 ^ 5 * r * σ ^ (-(4 : ℝ)) := by
  rw [rpow_neg_five_eq _ (by positivity), rpow_neg_four_eq _ hσ.le, div_pow, inv_div]
  have h5 : 0 < σ ^ 5 := by positivity
  have h4 : 0 < σ ^ 4 := by positivity
  rw [show r ^ 2 * (4 ^ 5 / σ ^ 5) = (4 ^ 5 * r) * (r / σ ^ 5) by ring,
    show 4 ^ 5 * r * (σ ^ 4)⁻¹ = (4 ^ 5 * r) * (1 / σ ^ 4) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_div_iff₀ h5 h4]
  nlinarith [pow_pos hσ 4]

private theorem sqrt_le_add_sqrt {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : c ≤ a + b) :
    √c ≤ √a + √b := by
  have h1 := sqrt_abs_add_le a b
  rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (add_nonneg ha hb)] at h1
  exact (Real.sqrt_le_sqrt h).trans h1

private theorem exp_le_of_mul_le {σ C τ : ℝ} (hσ : 0 < σ) (h : exp (-τ) * σ ^ 4 ≤ C) :
    exp (-τ) ≤ C * σ ^ (-(4 : ℝ)) := by
  have hσ4pos : 0 < σ ^ 4 := by positivity
  have hnr : σ ^ (-(4 : ℝ)) = (σ ^ 4)⁻¹ := by
    rw [Real.rpow_neg hσ.le]
    congr 1
    exact_mod_cast Real.rpow_natCast σ 4
  rw [hnr, ← div_eq_mul_inv, le_div_iff₀ hσ4pos]
  exact h

private theorem early_case {C₅ : ℝ} (hC₅ : 0 ≤ C₅)
    (hearly : ∀ (τ : ℝ) (x : Torus3), 0 < τ → τ ≤ 1 → 0 < torusSpatialNorm x →
      massiveHeatKernel (τ, x) ≤ C₅ * √τ * torusSpatialNorm x ^ (-(4 : ℝ)))
    {τ r σ : ℝ} {x : Torus3} (hτ : 0 < τ) (hτr : τ ≤ r ^ 2) (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 16)
    (hσ : 0 < σ) (hν : (63 / 64) * σ ≤ torusSpatialNorm x) :
    massiveHeatKernel (τ, x) ≤ C₅ * (64 / 63) ^ 4 * r * σ ^ (-(4 : ℝ)) := by
  have hτ1 : τ ≤ 1 := by nlinarith
  have hq0 : 0 < (63 / 64) * σ := by positivity
  have hν0 : 0 < torusSpatialNorm x := lt_of_lt_of_le hq0 hν
  have h1 := hearly τ x hτ hτ1 hν0
  have hsq : √τ ≤ r := by
    calc
      √τ ≤ √(r ^ 2) := Real.sqrt_le_sqrt hτr
      _ = r := Real.sqrt_sq hr0
  have hpow : torusSpatialNorm x ^ (-(4 : ℝ)) ≤ ((63 / 64) * σ) ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hq0 hν (by norm_num)
  have hmul : ((63 / 64) * σ) ^ (-(4 : ℝ)) = (64 / 63) ^ 4 * σ ^ (-(4 : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) hσ.le, Real.rpow_neg (by norm_num),
      show ((63 / 64 : ℝ) ^ (4 : ℝ)) = (63 / 64 : ℝ) ^ (4 : ℕ) by
        exact_mod_cast Real.rpow_natCast (63 / 64 : ℝ) 4]
    norm_num
  calc
    massiveHeatKernel (τ, x) ≤ C₅ * √τ * torusSpatialNorm x ^ (-(4 : ℝ)) := h1
    _ ≤ C₅ * r * ((63 / 64) * σ) ^ (-(4 : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsq hC₅
      · exact hpow
      · exact Real.rpow_nonneg hν0.le _
      · positivity
    _ = C₅ * (64 / 63) ^ 4 * r * σ ^ (-(4 : ℝ)) := by rw [hmul]; ring

theorem constantsRate_massive_time_part :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z h : SpaceTime, 0 < torusParabolicSize z →
      64 * torusParabolicSize h ≤ torusParabolicSize z → torusParabolicSize h ≤ 1 / 16 →
      |massiveHeatKernel (z.1 - h.1, z.2) - massiveHeatKernel z| ≤
        B * torusParabolicSize h * torusParabolicSize z ^ (-(4 : ℝ)) := by
  obtain ⟨C₄, hC₄, hinv⟩ := constantsRate_massive_le_inv_four
  obtain ⟨C₅, hC₅, hearly⟩ := constantsRate_massive_early
  obtain ⟨C₆, hC₆, hexp⟩ := constantsRate_exp_mul_size_pow_four
  obtain ⟨C₇, hC₇, hsmall⟩ := constantsRate_massive_time_small
  obtain ⟨C₈, hC₈, hlarge⟩ := constantsRate_massive_time_large
  refine ⟨C₅ * (64 / 63) ^ 4 + C₇ * 4 ^ 5 + 2 * C₄ + C₈ * C₆, by positivity, ?_⟩
  intro z h hσ hzh hr1
  set r : ℝ := torusParabolicSize h with hr
  set σ : ℝ := torusParabolicSize z with hσdef
  set t : ℝ := z.1 with htdef
  set t' : ℝ := z.1 - h.1 with ht'def
  have hr0 : 0 ≤ r := torusParabolicSize_nonneg h
  have hσ4 : 0 ≤ σ ^ (-(4 : ℝ)) := Real.rpow_nonneg hσ.le _
  have hs2 := abs_shift_sq_le h
  have hsr : √|h.1| ≤ r := sqrt_abs_shift_le h
  have hs1 : |h.1| ≤ 1 / 256 := by nlinarith
  have hsrr : |h.1| ≤ r := by nlinarith
  have hGz : massiveHeatKernel z ≤ C₄ * σ ^ (-(4 : ℝ)) := hinv z hσ
  have hGz0 : 0 ≤ massiveHeatKernel z := massiveHeatKernel_nonneg z
  have hσeq : σ = √|t| + torusSpatialNorm z.2 := rfl
  have hzeta : massiveHeatKernel (t, z.2) = massiveHeatKernel z := rfl
  have hrσ : r ≤ σ / 64 := by linarith
  have hxν := torusSpatialNorm_nonneg z.2
  have hB0 : 0 ≤ C₅ * (64 / 63) ^ 4 * r * σ ^ (-(4 : ℝ)) := by positivity
  have hsq_abs : ∀ a b : ℝ, √|a| ≤ √|a - b| + √|b| := sqrt_abs_le_of_sub
  by_cases ht : 0 < t
  · by_cases ht' : 0 < t'
    · -- both positive
      have hη : |(-h.1)| ≤ 1 := by rw [abs_neg]; linarith
      have hsum : t + (-h.1) = t' := by rw [ht'def, htdef]; ring
      have hGeq : massiveHeatKernel (z.1 - h.1, z.2) = massiveHeatKernel (t + (-h.1), z.2) := by
        rw [hsum]
      have hGeq2 : massiveHeatKernel (t, z.2) = massiveHeatKernel z := hzeta
      have hlow : ∀ σ' ∈ uIcc t (t + (-h.1)), t - |h.1| ≤ σ' ∧ σ' ≤ t + |h.1| := by
        intro σ' hσ'
        rw [mem_uIcc] at hσ'
        have := neg_abs_le h.1
        have := le_abs_self h.1
        rcases hσ' with ⟨a, b⟩ | ⟨a, b⟩ <;> constructor <;> linarith
      by_cases h34 : t ≤ 3 / 4
      · have hQ : ∀ σ' ∈ uIcc t (t + (-h.1)), 0 < σ' ∧ σ' ≤ 1 ∧
            σ / 4 ≤ √σ' + torusSpatialNorm z.2 := by
          intro σ' hσ'
          obtain ⟨hl, hh⟩ := hlow σ' hσ'
          have hpos : 0 < σ' := by
            rw [mem_uIcc] at hσ'
            rcases hσ' with ⟨a, b⟩ | ⟨a, b⟩
            · linarith
            · have ht'' : 0 < t + (-h.1) := by rw [hsum]; exact ht'
              linarith
          refine ⟨hpos, by linarith, ?_⟩
          by_cases hν : σ / 4 ≤ torusSpatialNorm z.2
          · have := Real.sqrt_nonneg σ'
            linarith
          · push Not at hν
            have hsqt : 3 / 4 * σ ≤ √t := by
              have : √|t| = √t := by rw [abs_of_pos ht]
              linarith
            have h1 : √t ≤ √σ' + r := by
              have := sqrt_le_add_sqrt hpos.le (abs_nonneg h.1) (c := t) (by linarith)
              linarith
            linarith
        have h1 := hsmall t (-h.1) (σ / 4) z.2 (by positivity) ht (by rw [hsum]; exact ht') hη hQ
        have h1' : |massiveHeatKernel (z.1 - h.1, z.2) - massiveHeatKernel z| ≤
            C₇ * |h.1| * (σ / 4) ^ (-(5 : ℝ)) + 2 * |h.1| * massiveHeatKernel z := by
          rw [hGeq, ← hzeta]
          simpa [abs_neg] using h1
        have hq5 : 0 ≤ (σ / 4) ^ (-(5 : ℝ)) := Real.rpow_nonneg (by positivity) _
        have ht1 := term_quarter_bound hσ hr0 (by linarith : r ≤ σ)
        have e1 : C₇ * |h.1| * (σ / 4) ^ (-(5 : ℝ)) ≤ C₇ * (4 ^ 5 * r * σ ^ (-(4 : ℝ))) := by
          calc
            C₇ * |h.1| * (σ / 4) ^ (-(5 : ℝ)) ≤ C₇ * r ^ 2 * (σ / 4) ^ (-(5 : ℝ)) := by
              apply mul_le_mul_of_nonneg_right _ hq5
              exact mul_le_mul_of_nonneg_left hs2 hC₇
            _ = C₇ * (r ^ 2 * (σ / 4) ^ (-(5 : ℝ))) := by ring
            _ ≤ C₇ * (4 ^ 5 * r * σ ^ (-(4 : ℝ))) := mul_le_mul_of_nonneg_left ht1 hC₇
        have e2 : 2 * |h.1| * massiveHeatKernel z ≤ 2 * r * (C₄ * σ ^ (-(4 : ℝ))) := by
          apply mul_le_mul
          · linarith
          · exact hGz
          · exact hGz0
          · positivity
        have hfin : 0 ≤ (C₅ * (64 / 63) ^ 4 + C₈ * C₆) * (r * σ ^ (-(4 : ℝ))) :=
          mul_nonneg (by positivity) (mul_nonneg hr0 hσ4)
        calc
          _ ≤ C₇ * (4 ^ 5 * r * σ ^ (-(4 : ℝ))) + 2 * r * (C₄ * σ ^ (-(4 : ℝ))) := by linarith
          _ ≤ _ := by linarith [hfin]
      · have h34' : 3 / 4 < t := lt_of_not_ge h34
        have hlarge' := hlarge t (-h.1) z.2 ht (by rw [hsum]; exact ht') hη (by
          intro σ' hσ'
          obtain ⟨hl, _⟩ := hlow σ' hσ'
          linarith)
        have h1' : |massiveHeatKernel (z.1 - h.1, z.2) - massiveHeatKernel z| ≤
            C₈ * |h.1| * exp (-t') + 2 * |h.1| * massiveHeatKernel z := by
          rw [hGeq, ← hzeta]
          simpa [abs_neg, hsum] using hlarge'
        have hz1 : |z.1 - t'| ≤ 1 := by
          have : z.1 - t' = h.1 := by rw [ht'def]; ring
          rw [this]
          linarith
        have hle := le_abs_self h.1
        have he := exp_le_of_mul_le hσ (hexp z t' (by rw [ht'def]; linarith) hz1)
        have e1 : C₈ * |h.1| * exp (-t') ≤ C₈ * r * (C₆ * σ ^ (-(4 : ℝ))) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hsrr hC₈
          · exact he
          · exact exp_nonneg _
          · positivity
        have e2 : 2 * |h.1| * massiveHeatKernel z ≤ 2 * r * (C₄ * σ ^ (-(4 : ℝ))) := by
          apply mul_le_mul
          · linarith
          · exact hGz
          · exact hGz0
          · positivity
        have hfin : 0 ≤ (C₅ * (64 / 63) ^ 4 + C₇ * 4 ^ 5) * (r * σ ^ (-(4 : ℝ))) :=
          mul_nonneg (by positivity) (mul_nonneg hr0 hσ4)
        calc
          _ ≤ C₈ * r * (C₆ * σ ^ (-(4 : ℝ))) + 2 * r * (C₄ * σ ^ (-(4 : ℝ))) := by linarith
          _ ≤ _ := by linarith [hfin]
    · -- t > 0, t' ≤ 0
      have h1 : massiveHeatKernel (z.1 - h.1, z.2) = 0 :=
        massive_eq_zero_of_nonpos _ _ (not_lt.mp ht')
      rw [h1, zero_sub, abs_neg, abs_of_nonneg hGz0]
      have htle : t ≤ |h.1| := by
        have : t - h.1 ≤ 0 := not_lt.mp ht'
        have := le_abs_self h.1
        linarith
      have hν : (63 / 64) * σ ≤ torusSpatialNorm z.2 := by
        have h2 : √t ≤ r := by
          calc
            √t ≤ √|h.1| := Real.sqrt_le_sqrt htle
            _ ≤ r := hsr
        have : √|t| = √t := by rw [abs_of_pos ht]
        linarith
      have := early_case hC₅ hearly (τ := t) (r := r) (σ := σ) (x := z.2) ht
        (htle.trans hs2) hr0 hr1 hσ hν
      rw [hzeta] at this
      have hfin : 0 ≤ (C₇ * 4 ^ 5 + 2 * C₄ + C₈ * C₆) * (r * σ ^ (-(4 : ℝ))) :=
        mul_nonneg (by positivity) (mul_nonneg hr0 hσ4)
      linarith [hfin]
  · have hGz0' : massiveHeatKernel z = 0 := massive_eq_zero_of_nonpos z.1 z.2 (not_lt.mp ht)
    rw [hGz0']
    by_cases ht' : 0 < t'
    · rw [sub_zero, abs_of_nonneg (massiveHeatKernel_nonneg _)]
      have hs_lt : h.1 < t := by
        have : 0 < t - h.1 := ht'
        linarith
      have ht0 : t ≤ 0 := not_lt.mp ht
      have habs : |t| ≤ |h.1| := by
        rw [abs_of_nonpos ht0]
        have := neg_abs_le h.1
        have := le_abs_self h.1
        linarith
      have htle : t' ≤ |h.1| := by
        have : t' = t - h.1 := rfl
        have := neg_abs_le h.1
        linarith
      have hν : (63 / 64) * σ ≤ torusSpatialNorm z.2 := by
        have h2 : √|t| ≤ r := by
          calc
            √|t| ≤ √|h.1| := Real.sqrt_le_sqrt habs
            _ ≤ r := hsr
        linarith
      have := early_case hC₅ hearly (τ := t') (r := r) (σ := σ) (x := z.2) ht'
        (htle.trans hs2) hr0 hr1 hσ hν
      have hfin : 0 ≤ (C₇ * 4 ^ 5 + 2 * C₄ + C₈ * C₆) * (r * σ ^ (-(4 : ℝ))) :=
        mul_nonneg (by positivity) (mul_nonneg hr0 hσ4)
      linarith [hfin]
    · have h1 : massiveHeatKernel (z.1 - h.1, z.2) = 0 :=
        massive_eq_zero_of_nonpos _ _ (not_lt.mp ht')
      rw [h1]
      simp only [sub_self, abs_zero]
      positivity

theorem constantsRate_massive_increment :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z h : SpaceTime, 0 < torusParabolicSize z →
      64 * torusParabolicSize h ≤ torusParabolicSize z → torusParabolicSize h ≤ 1 / 16 →
      |massiveHeatKernel (z - h) - massiveHeatKernel z| ≤
        B * torusParabolicSize h * torusParabolicSize z ^ (-(4 : ℝ)) := by
  obtain ⟨B₁, hB₁, h₁⟩ := constantsRate_massive_space_part
  obtain ⟨B₂, hB₂, h₂⟩ := constantsRate_massive_time_part
  refine ⟨B₁ + B₂, add_nonneg hB₁ hB₂, ?_⟩
  intro z h hσ hzh hr
  have e1 := h₁ z h hσ hzh hr
  have e2 := h₂ z h hσ hzh hr
  have hsplit : massiveHeatKernel (z - h) - massiveHeatKernel z =
      (massiveHeatKernel (z.1 - h.1, z.2 - h.2) - massiveHeatKernel (z.1 - h.1, z.2)) +
        (massiveHeatKernel (z.1 - h.1, z.2) - massiveHeatKernel z) := by
    have : z - h = (z.1 - h.1, z.2 - h.2) := rfl
    rw [this]
    ring
  rw [hsplit]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ B₁ * torusParabolicSize h * torusParabolicSize z ^ (-(4 : ℝ)) +
        B₂ * torusParabolicSize h * torusParabolicSize z ^ (-(4 : ℝ)) := add_le_add e1 e2
    _ = _ := by ring

end RegularityStructures.Phi43

end
