/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramBound

/-!
# Chaos `4` of the tree `I(Ψ²) Ψ²`: the deterministic bound

[Hai14, (10.39)-(10.42), p. 169]: with `A = δK_x(y, ·)`, `A' = δK_x(y', ·)`, one covariance `Q`
(`|Q| ≤ B s^(-1)`) and `d = s(y - y')`, `r = s(y - x)`, `r' = s(y' - x)`,
`|∫∫ A(w) A'(w') χ₄(w, w')| ≤ C B⁶ (d^(-δ) + d^(-2) (r^(2-δ) + r'^(2-δ)))` for `δ ∈ (0, 1/4]`,
`r, r' ≤ 1`, with `C = C(δ)` independent of `K`, `Q`, `B`, `x`, `y`, `y'`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Chaos `4`, lower-integral form.** -/
theorem i2Psi2LintBound_chaos4 {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
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
          |i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
            (4 * Q (q.1 - q.2) ^ 2 * Q (y - y') ^ 2 + 4 * Q (q.1 - y') ^ 2 * Q (y - q.2) ^ 2 +
              16 * (Q (q.1 - q.2) * Q (q.1 - y') * Q (y - q.2) * Q (y - y')))|)
          (C * B ^ 6 * (torusParabolicSize (y - y') ^ (-δ) +
            torusParabolicSize (y - y') ^ (-(2 : ℝ)) *
              (torusParabolicSize (y - x) ^ (2 - δ) + torusParabolicSize (y' - x) ^ (2 - δ)))) := by
  obtain ⟨C0, hC0, h0⟩ := i2Psi2LintBound_chaos4_sq hδ (by linarith)
  obtain ⟨Cp, hCp, hp⟩ := i2Psi2LintBound_chaos4_prod (θ := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Cc, hCc, hc⟩ := i2Psi2LintBound_chaos4_cross (a := (1 - δ) / 2) (by linarith)
    (by linarith)
  refine ⟨4 * C0 + 32 * Cp + 32 * Cc, by positivity, ?_⟩
  intro K Q B hB hKm hQm hKs hKb hKi hQb x y y' hr hr1 hr' hr1' hd
  have hxy : |y.1 - x.1| ≤ 1 := abs_le_one_of_torusParabolicSize_le_one hr1
  have hxy' : |y'.1 - x.1| ≤ 1 := abs_le_one_of_torusParabolicSize_le_one hr1'
  have mA := measurable_i2Psi2Increment hKm
  set d := torusParabolicSize (y - y') with hdd
  set r := torusParabolicSize (y - x) with hrr
  set r' := torusParabolicSize (y' - x) with hrr'
  have nr : ∀ (u : ℝ) (e : ℝ), 0 < u → 0 ≤ u ^ e := fun u e hu => Real.rpow_nonneg hu.le e
  set R := r ^ (2 - δ) + r' ^ (2 - δ) with hR
  have hR0 : 0 ≤ R := add_nonneg (nr _ _ hr) (nr _ _ hr')
  have hP0 : 0 ≤ d ^ (-(2 : ℝ)) * R := mul_nonneg (nr _ _ hd) hR0
  have hT0 : 0 ≤ d ^ (-δ) := nr _ _ hd
  have hQd : Q (y - y') ^ 2 ≤ B ^ 2 * d ^ (-(2 : ℝ)) := sq_cov_le hQb hd
  have hQd1 : |Q (y - y')| ≤ B * d ^ (-(1 : ℝ)) := hQb _ hd
  have hdd8 : d ≤ 8 * (r + r') := torusParabolicSize_sub_le_of_sub
  -- term 1
  have t1 := (h0 hB hKm hQm hKs hKb hKi hQb x y y' hxy hxy').const_mul
    (c := 4 * Q (y - y') ^ 2) (by positivity)
  have hθ := rpow_mul_rpow_sq_le hr hr' (δ := δ)
  -- term 2
  have t2 := (hp hB hKm hQm hQm hKs hKb hKi hQb hQb x y y' hr hr' hd).const_mul (c := 4)
    (by norm_num)
  -- term 3
  have t3 := (hc (K := K) (B := B) (c₁ := fun w => Q (w - y')) (c₃ := fun w' => Q (y - w'))
    (c₂ := fun w w' => Q (w - w')) hB hKm hKs hKb hKi (hQm.comp (measurable_id.sub measurable_const))
    (hQm.comp (measurable_const.sub measurable_id))
    (hQm.comp (measurable_fst.sub measurable_snd)) x y y' y' y hxy hxy' (by linarith [hxy']) (by linarith [hxy])
    (fun w hw => abs_cov_flip_le hB hQb hw) (fun w w' hw => abs_cov_flip_le hB hQb hw)
    (fun w' hw => (hQb _ hw).trans (mul_le_mul_of_nonneg_right (by linarith) (nr _ _ hw)))).const_mul (c := 16 * |Q (y - y')|)
    (by positivity)
  have mAy := mA x y
  have mAy' := mA x y'
  have m1 : Measurable (fun q : SpaceTime × SpaceTime => 4 * Q (y - y') ^ 2 *
      (|i2Psi2Increment K x y q.1| * |i2Psi2Increment K x y' q.2| * Q (q.1 - q.2) ^ 2)) := by
    fun_prop
  have m2 : Measurable (fun q : SpaceTime × SpaceTime => 4 *
      (|i2Psi2Increment K x y q.1| * Q (q.1 - y') ^ 2 *
        (|i2Psi2Increment K x y' q.2| * Q (y - q.2) ^ 2))) := by
    fun_prop
  have n1 : ∀ q : SpaceTime × SpaceTime, 0 ≤ 4 * Q (y - y') ^ 2 *
      (|i2Psi2Increment K x y q.1| * |i2Psi2Increment K x y' q.2| * Q (q.1 - q.2) ^ 2) :=
    fun q => by positivity
  have n2 : ∀ q : SpaceTime × SpaceTime, 0 ≤ 4 *
      (|i2Psi2Increment K x y q.1| * Q (q.1 - y') ^ 2 *
        (|i2Psi2Increment K x y' q.2| * Q (y - q.2) ^ 2)) := fun q => by positivity
  have n3 : ∀ q : SpaceTime × SpaceTime, 0 ≤ 16 * |Q (y - y')| *
      (|i2Psi2Increment K x y q.1| * |i2Psi2Increment K x y' q.2| *
        (|Q (q.1 - y')| * |Q (q.1 - q.2)| * |Q (y - q.2)|)) := fun q => by positivity
  -- the three bounds
  have hX0 : 0 ≤ C0 * B ^ 4 * (r ^ (1 - δ / 2) * r' ^ (1 - δ / 2)) :=
    mul_nonneg (by positivity) (mul_nonneg (nr _ _ hr) (nr _ _ hr'))
  have hM1 : 4 * Q (y - y') ^ 2 * (C0 * B ^ 4 * r ^ (1 - δ / 2) * r' ^ (1 - δ / 2)) ≤
      4 * C0 * B ^ 6 * (d ^ (-(2 : ℝ)) * R) := by
    have h := mul_le_mul hQd (mul_le_mul_of_nonneg_left hθ (by positivity : 0 ≤ C0 * B ^ 4)) hX0
      (mul_nonneg (by positivity) (nr _ _ hd))
    calc 4 * Q (y - y') ^ 2 * (C0 * B ^ 4 * r ^ (1 - δ / 2) * r' ^ (1 - δ / 2))
        = 4 * (Q (y - y') ^ 2 * (C0 * B ^ 4 * (r ^ (1 - δ / 2) * r' ^ (1 - δ / 2)))) := by ring
      _ ≤ 4 * (B ^ 2 * d ^ (-(2 : ℝ)) * (C0 * B ^ 4 * R)) := by linarith
      _ = _ := by ring
  have hE2 := alg_chaos4_prod hr hr1 hr' hr1' hd hdd8 hδ hδ4
  have hM2 : 4 * (Cp * B ^ 6 * r ^ (1 / 2 : ℝ) * r' ^ (1 / 2 : ℝ) *
      (d ^ (-(1 / 2 : ℝ)) + r' ^ (-(1 / 2 : ℝ))) * (d ^ (-(1 / 2 : ℝ)) + r ^ (-(1 / 2 : ℝ)))) ≤
      32 * Cp * B ^ 6 * (d ^ (-δ) + d ^ (-(2 : ℝ)) * R) := by
    have := mul_le_mul_of_nonneg_left hE2 (by positivity : 0 ≤ 4 * (Cp * B ^ 6))
    calc _ = 4 * (Cp * B ^ 6) * (r ^ (1 / 2 : ℝ) * r' ^ (1 / 2 : ℝ) *
        (d ^ (-(1 / 2 : ℝ)) + r' ^ (-(1 / 2 : ℝ))) * (d ^ (-(1 / 2 : ℝ)) + r ^ (-(1 / 2 : ℝ)))) := by
          ring
      _ ≤ _ := this
      _ = _ := by ring
  have hE3 := alg_chaos4_cross hr hr1 hr' hr1' hd hdd8 hδ hδ4
  have hM3 : 16 * |Q (y - y')| * (Cc * B ^ 5 * r ^ ((1 - δ) / 2) * r' ^ ((1 - δ) / 2)) ≤
      32 * Cc * B ^ 6 * (d ^ (-δ) + d ^ (-(2 : ℝ)) * R) := by
    have h1 := mul_le_mul_of_nonneg_left hE3 (by positivity : 0 ≤ 16 * (Cc * B ^ 6))
    have h2 : 16 * |Q (y - y')| * (Cc * B ^ 5 * r ^ ((1 - δ) / 2) * r' ^ ((1 - δ) / 2)) ≤
        16 * (B * d ^ (-(1 : ℝ))) * (Cc * B ^ 5 * (r ^ ((1 - δ) / 2) * r' ^ ((1 - δ) / 2))) := by
      have := mul_le_mul_of_nonneg_right hQd1 (by positivity :
        0 ≤ Cc * B ^ 5 * (r ^ ((1 - δ) / 2) * r' ^ ((1 - δ) / 2)))
      have h5 : 0 ≤ Cc * B ^ 5 * (r ^ ((1 - δ) / 2) * r' ^ ((1 - δ) / 2)) :=
        mul_nonneg (by positivity) (mul_nonneg (nr _ _ hr) (nr _ _ hr'))
      linarith
    calc _ ≤ _ := h2
      _ = 16 * (Cc * B ^ 6) * (d ^ (-(1 : ℝ)) * (r ^ ((1 - δ) / 2) * r' ^ ((1 - δ) / 2))) := by
          ring
      _ ≤ _ := h1
      _ = _ := by ring
  have hPT : 4 * C0 * B ^ 6 * (d ^ (-(2 : ℝ)) * R) ≤ 4 * C0 * B ^ 6 *
      (d ^ (-δ) + d ^ (-(2 : ℝ)) * R) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have s := t1.add_three m1 m2 n1 n2 n3 (by positivity) (by positivity) (by positivity) t2 t3
  refine s.mono (fun q => ?_) ?_
  · rw [abs_mul, abs_mul]
    have h := abs_chaos4_pointwise (i2Psi2Increment K x y q.1) (i2Psi2Increment K x y' q.2)
      (Q (q.1 - q.2)) (Q (q.1 - y')) (Q (y - q.2)) (Q (y - y'))
    rw [abs_mul, abs_mul] at h
    refine h.trans (le_of_eq ?_)
    simp only
  · linarith [hM1, hM2, hM3, hPT]

/-- **Chaos `4` of the tree `I(Ψ²) Ψ²`** [Hai14, (10.39)-(10.42)]: for `δ ∈ (0, 1/4]`,
`|∫∫ δK_x(y, w) δK_x(y', w') χ₄(w, w')| ≤ C B⁶ (d^(-δ) + d^(-2) (r^(2-δ) + r'^(2-δ)))`,
`d = s(y - y')`, `r = s(y - x)`, `r' = s(y' - x)`, with `χ₄` the chaos-`4` kernel
`4 c₀₂² c₁₃² + 4 c₀₃² c₁₂² + 16 c₀₂ c₀₃ c₁₂ c₁₃`
(`c₀₂ = Q(w - w')`, `c₀₃ = Q(w - y')`, `c₁₂ = Q(y - w')`, `c₁₃ = Q(y - y')`; this is
`hairerI2Psi2Chaos4` at a single scale).  `C` depends on `δ` only. -/
theorem integrable_and_abs_integral_chaos4_le {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
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
            (4 * Q (q.1 - q.2) ^ 2 * Q (y - y') ^ 2 + 4 * Q (q.1 - y') ^ 2 * Q (y - q.2) ^ 2 +
              16 * (Q (q.1 - q.2) * Q (q.1 - y') * Q (y - q.2) * Q (y - y')))) ∧
        |∫ q : SpaceTime × SpaceTime, i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
            (4 * Q (q.1 - q.2) ^ 2 * Q (y - y') ^ 2 + 4 * Q (q.1 - y') ^ 2 * Q (y - q.2) ^ 2 +
              16 * (Q (q.1 - q.2) * Q (q.1 - y') * Q (y - q.2) * Q (y - y')))| ≤
          C * B ^ 6 * (torusParabolicSize (y - y') ^ (-δ) +
            torusParabolicSize (y - y') ^ (-(2 : ℝ)) *
              (torusParabolicSize (y - x) ^ (2 - δ) + torusParabolicSize (y' - x) ^ (2 - δ))) := by
  obtain ⟨C, hC, h⟩ := i2Psi2LintBound_chaos4 hδ hδ4
  refine ⟨C, hC, ?_⟩
  intro K Q B hB hKm hQm hKs hKb hKi hQb x y y' hr hr1 hr' hr1' hd
  have mA := measurable_i2Psi2Increment hKm
  have mAy := mA x y
  have mAy' := mA x y'
  have hm : AEStronglyMeasurable (fun q : SpaceTime × SpaceTime =>
      i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
        (4 * Q (q.1 - q.2) ^ 2 * Q (y - y') ^ 2 + 4 * Q (q.1 - y') ^ 2 * Q (y - q.2) ^ 2 +
          16 * (Q (q.1 - q.2) * Q (q.1 - y') * Q (y - q.2) * Q (y - y')))) volume := by
    have : Measurable (fun q : SpaceTime × SpaceTime =>
      i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
        (4 * Q (q.1 - q.2) ^ 2 * Q (y - y') ^ 2 + 4 * Q (q.1 - y') ^ 2 * Q (y - q.2) ^ 2 +
          16 * (Q (q.1 - q.2) * Q (q.1 - y') * Q (y - q.2) * Q (y - y')))) := by fun_prop
    exact this.aestronglyMeasurable
  have hM : 0 ≤ C * B ^ 6 * (torusParabolicSize (y - y') ^ (-δ) +
      torusParabolicSize (y - y') ^ (-(2 : ℝ)) *
        (torusParabolicSize (y - x) ^ (2 - δ) + torusParabolicSize (y' - x) ^ (2 - δ))) :=
    mul_nonneg (by positivity) (add_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (add_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
          (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))))
  exact abs_integral_le_of_i2Psi2LintBound hm (h hB hKm hQm hKs hKb hKi hQb x y y' hr hr1 hr' hr1' hd) hM

end RegularityStructures

end
