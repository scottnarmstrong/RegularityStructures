/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramChaosFour

/-!
# Chaos `2` of the tree `I(Ψ²) Ψ²`: the deterministic bound

[Hai14, p. 170, (10.42) region].  With the notation of `TreeI2Psi2DiagramChaosFour`, for
`a ∈ (0, 1/2)`:
`|∫∫ A(w) A'(w') χ₂(w, w')| ≤ C B⁶ r^a r'^a d^(-1)`, `χ₂ = 16 c₀₁ c₂₃ (c₀₂ c₁₃ + c₀₃ c₁₂)`.
-/

public section

open MeasureTheory

namespace RegularityStructures

private theorem abs_chaos2_pointwise (a a' c01 c23 c02 c03 c12 c13 : ℝ) :
    |a| * |a'| * |16 * c01 * c23 * (c02 * c13 + c03 * c12)| ≤
      16 * |c13| * (|a| * |a'| * (|c01| * |c02| * |c23|)) +
        16 * ((|a| * (|c01| * |c03|)) * (|a'| * (|c23| * |c12|))) := by
  have hS : |c02 * c13 + c03 * c12| ≤ |c02| * |c13| + |c03| * |c12| :=
    (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16)]
  calc |a| * |a'| * (16 * |c01| * |c23| * |c02 * c13 + c03 * c12|)
      ≤ |a| * |a'| * (16 * |c01| * |c23| * (|c02| * |c13| + |c03| * |c12|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS (by positivity)) (by positivity)
    _ = _ := by ring

/-- The product term of chaos `2`, lower-integral form. -/
theorem i2Psi2LintBound_chaos2_prodterm {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable K → Measurable Q →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → torusParabolicSize (y - x) ≤ 1 →
        0 < torusParabolicSize (y' - x) → torusParabolicSize (y' - x) ≤ 1 →
        0 < torusParabolicSize (y - y') →
        i2Psi2LintBound volume (fun q : SpaceTime × SpaceTime =>
          (|i2Psi2Increment K x y q.1| * (|Q (q.1 - y)| * |Q (q.1 - y')|)) *
            (|i2Psi2Increment K x y' q.2| * (|Q (q.2 - y')| * |Q (y - q.2)|)))
          (C * B ^ 6 * (torusParabolicSize (y - x) ^ a * torusParabolicSize (y' - x) ^ a *
            torusParabolicSize (y - y') ^ (-(1 : ℝ)))) := by
  obtain ⟨C1, hC1, h1⟩ := i2Psi2LintBound_chaos2_prod (θ := 1 / 2) (ε := 0) (θ' := 0)
    (ε' := 1 / 2 - a) (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) le_rfl
    (by norm_num) (by linarith) (by linarith) (by linarith)
  obtain ⟨C2, hC2, h2⟩ := i2Psi2LintBound_chaos2_prod (θ := 0) (ε := 1 / 2 - a) (θ' := 1 / 2)
    (ε' := 0) le_rfl (by norm_num) (by linarith) (by linarith) (by linarith) (by norm_num)
    (by norm_num) le_rfl (by norm_num) (by norm_num)
  refine ⟨40 * (C1 + C2), by positivity, ?_⟩
  intro K Q B hB hKm hQm hKs hKb hKi hQb x y y' hr hr1 hr' hr1' hd
  have hxy : |y.1 - x.1| ≤ 1 := abs_le_one_of_torusParabolicSize_le_one hr1
  have hxy' : |y'.1 - x.1| ≤ 1 := abs_le_one_of_torusParabolicSize_le_one hr1'
  have hdd8 : torusParabolicSize (y - y') ≤ 8 * (torusParabolicSize (y - x) +
      torusParabolicSize (y' - x)) := torusParabolicSize_sub_le_of_sub
  set d := torusParabolicSize (y - y')
  set r := torusParabolicSize (y - x)
  set r' := torusParabolicSize (y' - x)
  have nr : ∀ (u : ℝ) (e : ℝ), 0 < u → 0 ≤ u ^ e := fun u e hu => Real.rpow_nonneg hu.le e
  have hX : 0 ≤ r ^ a * r' ^ a * d ^ (-(1 : ℝ)) :=
    mul_nonneg (mul_nonneg (nr _ _ hr) (nr _ _ hr')) (nr _ _ hd)
  rcases le_total r r' with hrr | hrr
  · have hl := h1 hB hKm hQm hQm hQm hQm hKs hKb hKi hQb hQb hQb hQb x y y' hxy hxy' hr hr' hd
    simp only [Real.rpow_zero, add_zero, zero_add, mul_one] at hl
    have e := alg_chaos2_prod (a := a) hr hrr hr1' hd (by linarith) ha ha2
    refine hl.mono (fun q => le_rfl) ?_
    have := mul_le_mul_of_nonneg_left e (by positivity : 0 ≤ C1 * B ^ 6)
    have h3 : 0 ≤ C2 * B ^ 6 * (r ^ a * r' ^ a * d ^ (-(1 : ℝ))) :=
      mul_nonneg (by positivity) hX
    calc _ = C1 * B ^ 6 * (r ^ (1 / 2 : ℝ) * (d ^ (-(1 / 2 : ℝ)) + r' ^ (-(1 / 2 : ℝ))) *
          (d ^ (-(1 / 2 - a)) + r ^ (-(1 / 2 - a)))) := by ring
      _ ≤ _ := this
      _ ≤ _ := by nlinarith [mul_nonneg (by positivity : 0 ≤ C1 * B ^ 6) hX,
        mul_nonneg (by positivity : 0 ≤ C2 * B ^ 6) hX]
  · have hl := h2 hB hKm hQm hQm hQm hQm hKs hKb hKi hQb hQb hQb hQb x y y' hxy hxy' hr hr' hd
    simp only [Real.rpow_zero, add_zero, zero_add] at hl
    have e := alg_chaos2_prod (a := a) hr' hrr hr1 hd (by linarith) ha ha2
    refine hl.mono (fun q => le_rfl) ?_
    have := mul_le_mul_of_nonneg_left e (by positivity : 0 ≤ C2 * B ^ 6)
    calc _ = C2 * B ^ 6 * (r' ^ (1 / 2 : ℝ) * (d ^ (-(1 / 2 : ℝ)) + r ^ (-(1 / 2 : ℝ))) *
          (d ^ (-(1 / 2 - a)) + r' ^ (-(1 / 2 - a)))) := by ring
      _ ≤ _ := this
      _ ≤ _ := by nlinarith [mul_nonneg (by positivity : 0 ≤ C1 * B ^ 6) hX,
        mul_nonneg (by positivity : 0 ≤ C2 * B ^ 6) hX]

/-- **Chaos `2` of the tree `I(Ψ²) Ψ²`** [Hai14, p. 170, (10.42) region]: for `a ∈ (0, 1/2)`,
`|∫∫ δK_x(y, w) δK_x(y', w') χ₂(w, w')| ≤ C B⁶ r^a r'^a d^(-1)`,
`χ₂ = 16 c₀₁ c₂₃ (c₀₂ c₁₃ + c₀₃ c₁₂)` (`c₀₁ = Q(w - y)`, `c₂₃ = Q(w' - y')`, `c₀₂ = Q(w - w')`,
`c₀₃ = Q(w - y')`, `c₁₂ = Q(y - w')`, `c₁₃ = Q(y - y')`; this is `hairerI2Psi2Chaos2` at a single
scale).  `C` depends on `a` only. -/
theorem integrable_and_abs_integral_chaos2_le {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable K → Measurable Q →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → torusParabolicSize (y - x) ≤ 1 →
        0 < torusParabolicSize (y' - x) → torusParabolicSize (y' - x) ≤ 1 →
        0 < torusParabolicSize (y - y') →
        Integrable (fun q : SpaceTime × SpaceTime =>
          i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
            (16 * Q (q.1 - y) * Q (q.2 - y') *
              (Q (q.1 - q.2) * Q (y - y') + Q (q.1 - y') * Q (y - q.2)))) ∧
        |∫ q : SpaceTime × SpaceTime, i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
            (16 * Q (q.1 - y) * Q (q.2 - y') *
              (Q (q.1 - q.2) * Q (y - y') + Q (q.1 - y') * Q (y - q.2)))| ≤
          C * B ^ 6 * (torusParabolicSize (y - x) ^ a * torusParabolicSize (y' - x) ^ a *
            torusParabolicSize (y - y') ^ (-(1 : ℝ))) := by
  obtain ⟨Cp, hCp, hp⟩ := i2Psi2LintBound_chaos2_prodterm ha ha2
  obtain ⟨Cc, hCc, hc⟩ := i2Psi2LintBound_chaos4_cross ha ha2
  refine ⟨16 * Cp + 16 * Cc, by positivity, ?_⟩
  intro K Q B hB hKm hQm hKs hKb hKi hQb x y y' hr hr1 hr' hr1' hd
  have hxy : |y.1 - x.1| ≤ 1 := abs_le_one_of_torusParabolicSize_le_one hr1
  have hxy' : |y'.1 - x.1| ≤ 1 := abs_le_one_of_torusParabolicSize_le_one hr1'
  have mA := measurable_i2Psi2Increment hKm
  have mAy := mA x y
  have mAy' := mA x y'
  set d := torusParabolicSize (y - y') with hdd
  set r := torusParabolicSize (y - x) with hrr
  set r' := torusParabolicSize (y' - x) with hrr'
  have nr : ∀ (u : ℝ) (e : ℝ), 0 < u → 0 ≤ u ^ e := fun u e hu => Real.rpow_nonneg hu.le e
  have hX : 0 ≤ r ^ a * r' ^ a * d ^ (-(1 : ℝ)) :=
    mul_nonneg (mul_nonneg (nr _ _ hr) (nr _ _ hr')) (nr _ _ hd)
  have hQd1 : |Q (y - y')| ≤ B * d ^ (-(1 : ℝ)) := hQb _ hd
  have t2 := (hp hB hKm hQm hKs hKb hKi hQb x y y' hr hr1 hr' hr1' hd).const_mul (c := 16)
    (by norm_num)
  have t1 := (hc (K := K) (B := B) (c₁ := fun w => Q (w - y)) (c₃ := fun w' => Q (w' - y'))
    (c₂ := fun w w' => Q (w - w')) hB hKm hKs hKb hKi
    (hQm.comp (measurable_id.sub measurable_const))
    (hQm.comp (measurable_id.sub measurable_const))
    (hQm.comp (measurable_fst.sub measurable_snd)) x y y' y y' hxy hxy' (by linarith) (by linarith)
    (fun w hw => abs_cov_flip_le hB hQb hw) (fun w w' hw => abs_cov_flip_le hB hQb hw)
    (fun w' hw => abs_cov_flip_le hB hQb hw)).const_mul (c := 16 * |Q (y - y')|) (by positivity)
  have m1 : Measurable (fun q : SpaceTime × SpaceTime => 16 * |Q (y - y')| *
      (|i2Psi2Increment K x y q.1| * |i2Psi2Increment K x y' q.2| *
        (|Q (q.1 - y)| * |Q (q.1 - q.2)| * |Q (q.2 - y')|))) := by fun_prop
  have n1 : ∀ q : SpaceTime × SpaceTime, 0 ≤ 16 * |Q (y - y')| *
      (|i2Psi2Increment K x y q.1| * |i2Psi2Increment K x y' q.2| *
        (|Q (q.1 - y)| * |Q (q.1 - q.2)| * |Q (q.2 - y')|)) := fun q => by positivity
  have n2 : ∀ q : SpaceTime × SpaceTime, 0 ≤ 16 *
      ((|i2Psi2Increment K x y q.1| * (|Q (q.1 - y)| * |Q (q.1 - y')|)) *
        (|i2Psi2Increment K x y' q.2| * (|Q (q.2 - y')| * |Q (y - q.2)|))) :=
    fun q => by positivity
  have hM1 : 16 * |Q (y - y')| * (Cc * B ^ 5 * r ^ a * r' ^ a) ≤
      16 * Cc * B ^ 6 * (r ^ a * r' ^ a * d ^ (-(1 : ℝ))) := by
    have h5 : 0 ≤ Cc * B ^ 5 * (r ^ a * r' ^ a) :=
      mul_nonneg (by positivity) (mul_nonneg (nr _ _ hr) (nr _ _ hr'))
    have := mul_le_mul_of_nonneg_right hQd1 h5
    nlinarith
  have hM2 : 16 * (Cp * B ^ 6 * (r ^ a * r' ^ a * d ^ (-(1 : ℝ)))) =
      16 * Cp * B ^ 6 * (r ^ a * r' ^ a * d ^ (-(1 : ℝ))) := by ring
  have s := t1.add m1.aemeasurable n1 (fun q => by positivity) (by positivity) (by positivity)
    t2
  have hm : AEStronglyMeasurable (fun q : SpaceTime × SpaceTime =>
      i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
        (16 * Q (q.1 - y) * Q (q.2 - y') *
          (Q (q.1 - q.2) * Q (y - y') + Q (q.1 - y') * Q (y - q.2)))) volume := by
    have : Measurable (fun q : SpaceTime × SpaceTime =>
      i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
        (16 * Q (q.1 - y) * Q (q.2 - y') *
          (Q (q.1 - q.2) * Q (y - y') + Q (q.1 - y') * Q (y - q.2)))) := by fun_prop
    exact this.aestronglyMeasurable
  have hM : 0 ≤ (16 * Cp + 16 * Cc) * B ^ 6 * (r ^ a * r' ^ a * d ^ (-(1 : ℝ))) :=
    mul_nonneg (by positivity) hX
  have hl : i2Psi2LintBound volume (fun q : SpaceTime × SpaceTime =>
      |i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
        (16 * Q (q.1 - y) * Q (q.2 - y') *
          (Q (q.1 - q.2) * Q (y - y') + Q (q.1 - y') * Q (y - q.2)))|)
      ((16 * Cp + 16 * Cc) * B ^ 6 * (r ^ a * r' ^ a * d ^ (-(1 : ℝ)))) := by
    refine s.mono (fun q => ?_) ?_
    · rw [abs_mul, abs_mul]
      refine (abs_chaos2_pointwise _ _ (Q (q.1 - y)) (Q (q.2 - y')) (Q (q.1 - q.2))
        (Q (q.1 - y')) (Q (y - q.2)) (Q (y - y'))).trans (le_of_eq ?_)
      ring
    · nlinarith [hM1, hM2]
  exact abs_integral_le_of_i2Psi2LintBound hm hl hM

end RegularityStructures

end
