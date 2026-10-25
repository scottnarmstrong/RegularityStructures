/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramCross

/-!
# Single integrals of the kernel increment against two covariance weights

For `A(w) = K(y - w) - K(x - w)` and covariance weights `|c₁(w)| ≤ 2 B s(g₁ - w)^(-1)`,
`|c₂(w)| ≤ 2 B s(g₂ - w)^(-1)`, with `θ ∈ [0, 1)`, `ε ≥ 0`, `θ + ε > 0`:
`∫ |A| |c₁| |c₂| ≲ B³ s(y - x)^θ (s(y - g₂)^(-(θ+ε)) + s(x - g₂)^(-(θ+ε)) + 2 s(g₁ - g₂)^(-(θ+ε)))`
(`i2Psi2LintBound_cov_pair`).  The parameter `ε` weakens `s(g₂ - w)^(-1)` to
`3^ε s(g₂ - w)^(-1-ε)` on the time slab, which is how the borderline case `θ = 0` (total order
exactly `5`) is reached at the price of a power `ε`.  [Hai14, p. 170, (10.42) region].
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- On `0 < s ≤ 3`, `s^(-1) ≤ 3^ε s^(-1-ε)`. -/
theorem rpow_neg_one_le_three_rpow_mul {s ε : ℝ} (hε : 0 ≤ ε) (hs : 0 < s) (h3 : s ≤ 3) :
    s ^ (-(1 : ℝ)) ≤ 3 ^ ε * s ^ (-(1 + ε)) := by
  have h1 : (3 : ℝ) ^ (-ε) ≤ s ^ (-ε) := Real.rpow_le_rpow_of_nonpos hs h3 (neg_nonpos.2 hε)
  have e : s ^ (-(1 + ε)) = s ^ (-(1 : ℝ)) * s ^ (-ε) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have h3p : (3 : ℝ) ^ ε * (3 : ℝ) ^ (-ε) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have n1 : 0 ≤ s ^ (-(1 : ℝ)) := Real.rpow_nonneg hs.le _
  have n3 : 0 ≤ (3 : ℝ) ^ ε := Real.rpow_nonneg (by norm_num) _
  rw [e]
  calc s ^ (-(1 : ℝ)) = s ^ (-(1 : ℝ)) * ((3 : ℝ) ^ ε * (3 : ℝ) ^ (-ε)) := by rw [h3p, mul_one]
    _ = 3 ^ ε * (s ^ (-(1 : ℝ)) * (3 : ℝ) ^ (-ε)) := by ring
    _ ≤ 3 ^ ε * (s ^ (-(1 : ℝ)) * s ^ (-ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 n1) n3

/-- **Single pairing with two covariance weights** [Hai14, p. 170]. -/
theorem i2Psi2LintBound_cov_pair {θ ε : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hε : 0 ≤ ε)
    (hε4 : ε < 4) (hθε : 0 < θ + ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ} {c₁ c₂ : SpaceTime → ℝ}, 0 ≤ B →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      ∀ x y g₁ g₂ : SpaceTime, |y.1 - x.1| ≤ 1 → |g₂.1 - x.1| ≤ 2 →
        0 < torusParabolicSize (y - g₂) → 0 < torusParabolicSize (x - g₂) →
        0 < torusParabolicSize (g₁ - g₂) →
        (∀ w, 0 < torusParabolicSize (g₁ - w) →
          |c₁ w| ≤ 2 * B * torusParabolicSize (g₁ - w) ^ (-(1 : ℝ))) →
        (∀ w, 0 < torusParabolicSize (g₂ - w) →
          |c₂ w| ≤ 2 * B * torusParabolicSize (g₂ - w) ^ (-(1 : ℝ))) →
        i2Psi2LintBound volume (fun w => |i2Psi2Increment K x y w| * (|c₁ w| * |c₂ w|))
          (C * B ^ 3 * torusParabolicSize (y - x) ^ θ *
            (torusParabolicSize (y - g₂) ^ (-(θ + ε)) + torusParabolicSize (x - g₂) ^ (-(θ + ε)) +
              2 * torusParabolicSize (g₁ - g₂) ^ (-(θ + ε)))) := by
  obtain ⟨CI, hCI, hI⟩ := i2Psi2LintBound_kernel_sub_three (θ := θ) (κ := 1 + ε) hθ0 hθ1
    (by linarith) (by linarith) (by linarith)
  refine ⟨4 * 3 ^ ε * CI, mul_nonneg (mul_nonneg (by norm_num)
    (Real.rpow_nonneg (by norm_num) _)) hCI, ?_⟩
  intro K B c₁ c₂ hB hKs hKb hKi x y g₁ g₂ hxy hg₂ hy hx hg hc₁ hc₂
  have e1 : θ + (1 + ε) - 1 = θ + ε := by ring
  have hin := hI hB hKb hKi x y g₁ g₂ hy hx hg
  rw [e1] at hin
  have hc := hin.const_mul (c := 4 * B ^ 2 * 3 ^ ε) (mul_nonneg (by positivity)
    (Real.rpow_nonneg (by norm_num) _))
  refine hc.mono_ae ?_ (le_of_eq (by ring))
  filter_upwards [ae_torusParabolicSize_sub_pos g₁, ae_torusParabolicSize_sub_pos g₂]
    with w hw1 hw2
  have b1 := hc₁ w hw1
  have b2 := hc₂ w hw2
  have n1 : 0 ≤ 2 * B * torusParabolicSize (g₁ - w) ^ (-(1 : ℝ)) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have h12 := mul_le_mul b1 b2 (abs_nonneg _) n1
  have hA := abs_nonneg (i2Psi2Increment K x y w)
  by_cases hs : i2Psi2Slab x.1 w = 0
  · have h0 := kernel_sub_eq_zero_of_not_slab hKs hxy hs
    have : i2Psi2Increment K x y w = 0 := h0
    simp only [this, abs_zero, zero_mul]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (abs_nonneg _) (mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)))
  · have hsl := abs_sub_le_two_of_i2Psi2Slab_ne_zero hs
    have h4 : |(g₂ - w).1| ≤ 4 := by
      have : (g₂ - w).1 = (g₂.1 - x.1) - (w.1 - x.1) := by simp only [Prod.fst_sub]; ring
      rw [this]
      calc |(g₂.1 - x.1) - (w.1 - x.1)| ≤ |g₂.1 - x.1| + |w.1 - x.1| := abs_sub _ _
        _ ≤ 4 := by linarith
    have h3 := torusParabolicSize_le_three_of_abs_le h4
    have hw := rpow_neg_one_le_three_rpow_mul hε hw2 h3
    have n2 : 0 ≤ torusParabolicSize (g₁ - w) ^ (-(1 : ℝ)) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    calc |i2Psi2Increment K x y w| * (|c₁ w| * |c₂ w|)
        ≤ |i2Psi2Increment K x y w| * (2 * B * torusParabolicSize (g₁ - w) ^ (-(1 : ℝ)) *
          (2 * B * torusParabolicSize (g₂ - w) ^ (-(1 : ℝ)))) :=
          mul_le_mul_of_nonneg_left h12 hA
      _ ≤ |i2Psi2Increment K x y w| * (2 * B * torusParabolicSize (g₁ - w) ^ (-(1 : ℝ)) *
          (2 * B * (3 ^ ε * torusParabolicSize (g₂ - w) ^ (-(1 + ε))))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hw (by positivity)) n1) hA
      _ = _ := by simp only [i2Psi2Increment]; ring

private theorem alg_pair {C1 C2 B ra ra' d1 d2 p q a2 b1 b2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hra : 0 ≤ ra) (hra' : 0 ≤ ra') (hd1 : 0 ≤ d1) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (h1 : a2 ≤ 2 * p) (h2 : b1 ≤ 2 * d2)
    (h3 : b2 ≤ 2 * q) :
    C1 * B ^ 3 * ra * (d1 + a2 + 2 * d1) * (C2 * B ^ 3 * ra' * (b1 + b2 + 2 * b1)) ≤
      18 * C1 * C2 * B ^ 6 * ra * ra' * (d1 + p) * (d2 + q) := by
  have e1 : d1 + a2 + 2 * d1 ≤ 3 * (d1 + p) := by linarith
  have e2 : b1 + b2 + 2 * b1 ≤ 6 * (d2 + q) := by linarith
  have k : 0 ≤ C1 * C2 * B ^ 6 * ra * ra' := by positivity
  have e3 : (d1 + a2 + 2 * d1) * (b1 + b2 + 2 * b1) ≤ 3 * (d1 + p) * (6 * (d2 + q)) :=
    mul_le_mul e1 e2 (by linarith) (by linarith)
  calc C1 * B ^ 3 * ra * (d1 + a2 + 2 * d1) * (C2 * B ^ 3 * ra' * (b1 + b2 + 2 * b1))
      = (C1 * C2 * B ^ 6 * ra * ra') * ((d1 + a2 + 2 * d1) * (b1 + b2 + 2 * b1)) := by ring
    _ ≤ (C1 * C2 * B ^ 6 * ra * ra') * (3 * (d1 + p) * (6 * (d2 + q))) :=
        mul_le_mul_of_nonneg_left e3 k
    _ = _ := by ring

/-- **The product pairing of chaos `2`**:
`(∫ |A| |Q₀₁(w - y)| |Q₀₃(w - y')|) (∫ |A'| |Q₂₃(w' - y')| |Q₁₂(y - w')|)`, with independent
exponent pairs `(θ, ε)` and `(θ', ε')` for the two factors. -/
theorem i2Psi2LintBound_chaos2_prod {θ ε θ' ε' : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hε : 0 ≤ ε)
    (hθε : 0 < θ + ε) (hθε1 : θ + ε ≤ 1) (hθ0' : 0 ≤ θ') (hθ1' : θ' < 1) (hε' : 0 ≤ ε')
    (hθε' : 0 < θ' + ε') (hθε1' : θ' + ε' ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q₀₁ Q₀₃ Q₂₃ Q₁₂ : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable K →
      Measurable Q₀₁ → Measurable Q₀₃ → Measurable Q₂₃ → Measurable Q₁₂ →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |Q₀₁ u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |Q₀₃ u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |Q₂₃ u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |Q₁₂ u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) →
      ∀ x y y' : SpaceTime, |y.1 - x.1| ≤ 1 → |y'.1 - x.1| ≤ 1 →
        0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') →
        i2Psi2LintBound volume (fun q : SpaceTime × SpaceTime =>
          (|i2Psi2Increment K x y q.1| * (|Q₀₁ (q.1 - y)| * |Q₀₃ (q.1 - y')|)) *
            (|i2Psi2Increment K x y' q.2| * (|Q₂₃ (q.2 - y')| * |Q₁₂ (y - q.2)|)))
          (C * B ^ 6 * torusParabolicSize (y - x) ^ θ * torusParabolicSize (y' - x) ^ θ' *
            (torusParabolicSize (y - y') ^ (-(θ + ε)) + torusParabolicSize (y' - x) ^ (-(θ + ε))) *
            (torusParabolicSize (y - y') ^ (-(θ' + ε')) +
              torusParabolicSize (y - x) ^ (-(θ' + ε')))) := by
  obtain ⟨C1, hC1, h1⟩ := i2Psi2LintBound_cov_pair hθ0 hθ1 hε (by linarith) hθε
  obtain ⟨C2, hC2, h2⟩ := i2Psi2LintBound_cov_pair hθ0' hθ1' hε' (by linarith) hθε'
  refine ⟨18 * C1 * C2, by positivity, ?_⟩
  intro K Q₀₁ Q₀₃ Q₂₃ Q₁₂ B hB hKm hm₀₁ hm₀₃ hm₂₃ hm₁₂ hKs hKb hKi hQ₀₁ hQ₀₃ hQ₂₃ hQ₁₂ x y y'
    hxy hxy' hr hr' hd
  have mA := measurable_i2Psi2Increment hKm
  have hyx : 0 < torusParabolicSize (x - y) := torusParabolicSize_pos_of_sub_pos hr
  have hyx' : 0 < torusParabolicSize (x - y') := torusParabolicSize_pos_of_sub_pos hr'
  have hdd : 0 < torusParabolicSize (y' - y) := torusParabolicSize_pos_of_sub_pos hd
  have nrpow : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have fc := h1 hB hKs hKb hKi x y y y' hxy (by linarith) hd hyx' hd
    (fun w hw => abs_cov_flip_le hB hQ₀₁ hw) (fun w hw => abs_cov_flip_le hB hQ₀₃ hw)
  have fd := h2 hB hKs hKb hKi x y' y' y hxy' (by linarith) hdd hyx hdd
    (fun w hw => abs_cov_flip_le hB hQ₂₃ hw)
    (fun w hw => by
      have := hQ₁₂ (y - w) hw
      exact this.trans (mul_le_mul_of_nonneg_right (by linarith) (nrpow _ _)))
  have hMa : 0 ≤ C1 * B ^ 3 * torusParabolicSize (y - x) ^ θ *
      (torusParabolicSize (y - y') ^ (-(θ + ε)) + torusParabolicSize (x - y') ^ (-(θ + ε)) +
        2 * torusParabolicSize (y - y') ^ (-(θ + ε))) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC1 (pow_nonneg hB 3)) (nrpow _ _))
      (add_nonneg (add_nonneg (nrpow _ _) (nrpow _ _)) (mul_nonneg (by norm_num) (nrpow _ _)))
  have hprod := i2Psi2LintBound.prod_mul (μ := volume) (ν := volume)
    ((((continuous_abs.measurable.comp (mA x y)).mul
      ((continuous_abs.measurable.comp (hm₀₁.comp (measurable_id.sub measurable_const))).mul
        (continuous_abs.measurable.comp (hm₀₃.comp (measurable_id.sub measurable_const)))))).aemeasurable)
    ((((continuous_abs.measurable.comp (mA x y')).mul
      ((continuous_abs.measurable.comp (hm₂₃.comp (measurable_id.sub measurable_const))).mul
        (continuous_abs.measurable.comp (hm₁₂.comp (measurable_const.sub measurable_id)))))).aemeasurable)
    (fun w => mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))) hMa fc fd
  refine hprod.mono (fun q => le_rfl) ?_
  have t1 := torusParabolicSize_sub_rpow_neg_le (a := x) (b := y') (e := θ + ε) hθε.le hθε1 hr'
  have t2 := torusParabolicSize_sub_rpow_neg_le (a := y') (b := y) (e := θ' + ε') hθε'.le hθε1' hd
  have t3 := torusParabolicSize_sub_rpow_neg_le (a := x) (b := y) (e := θ' + ε') hθε'.le hθε1' hr
  have := alg_pair (B := B) hC1 hC2 (nrpow (y - x) θ) (nrpow (y' - x) θ')
    (nrpow (y - y') (-(θ + ε))) (nrpow (y' - x) (-(θ + ε)))
    (nrpow (y - x) (-(θ' + ε'))) (nrpow (y' - y) (-(θ' + ε')))
    (nrpow (x - y) (-(θ' + ε'))) t1 t2 t3
  calc _ ≤ _ := this
    _ = _ := by ring

end RegularityStructures

end
