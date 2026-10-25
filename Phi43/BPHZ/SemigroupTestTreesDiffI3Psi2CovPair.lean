/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2Double3
public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2Chaos1
public import Phi43.BPHZ.TreeI3Psi2DifferenceCovEstimate

/-!
# The global deterministic bound for the covariance of the difference of `I(Ψ³)Ψ²`

`i3Psi2CovPair_second_diff_bound_global`: for kernels `J_a`, `J_b` as in
`i3Psi2CovPair_second_diff_bound` (the Hölder increments of `K` are not needed), arbitrary
`z, z'` and `D` bounding `s(a - b)` on the time window `|a.1|, |b.1| ≤ |z.1| + |z'.1| + 2`,
the second difference of the abstract covariances is bounded by
`C μ² ((1 + D)² (1 + |z.1| + |z'.1|)) treeTheta z z'`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

theorem rpow_le_one_add_of_le_one {D δ : ℝ} (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    D ^ δ ≤ 1 + D := by
  rcases le_total D 1 with h | h
  · have := Real.rpow_le_one hD h hδ
    linarith
  · have : D ^ δ ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hδ1
    rw [Real.rpow_one] at this
    linarith

theorem diffPoly_combine_alg {A B I μ D δ C5 C3 C1 t t' Θ : ℝ} (hD0 : 0 ≤ D)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8) (hC5 : 0 ≤ C5) (hC3 : 0 ≤ C3) (hC1 : 0 ≤ C1) (ht : 0 ≤ t)
    (ht' : 0 ≤ t') (hΘ : 0 ≤ Θ) (x1 : |A + B + 36 * I| ≤ |A + B| + 36 * |I|)
    (x2 : |A + B| ≤ |A| + |B|) (bF5 : |A| ≤ C5 * μ ^ 2 * (1 + t + D ^ δ) * Θ)
    (bF3 : |B| ≤ C3 * μ ^ 2 * (1 + t + D ^ δ) * Θ)
    (bI : |I| ≤ C1 * μ ^ 2 * (1 + D ^ δ) ^ 2 * Θ) :
    |A + B + 36 * I| ≤ (2 * C5 + 2 * C3 + 144 * C1) * μ ^ 2 * ((1 + D) ^ 2 * (1 + t + t')) * Θ := by
  have hd0 : 0 ≤ D ^ δ := Real.rpow_nonneg hD0 _
  have hd1 : D ^ δ ≤ 1 + D := rpow_le_one_add_of_le_one hD0 hδ.le (by linarith)
  set d := D ^ δ with hd
  have hP : 0 ≤ (1 + D) ^ 2 * (1 + t + t') := by positivity
  have p0 : 1 + t + d ≤ 2 * ((1 + D) ^ 2 * (1 + t + t')) := by
    calc 1 + t + d ≤ (1 + t) * (1 + d) := by linarith [mul_nonneg ht hd0]
      _ ≤ (1 + t + t') * (2 * (1 + D)) :=
          mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      _ ≤ (1 + t + t') * (2 * (1 + D) ^ 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
      _ = _ := by ring
  have p1 : (1 + d) ^ 2 ≤ 4 * ((1 + D) ^ 2 * (1 + t + t')) := by
    calc (1 + d) ^ 2 ≤ (2 * (1 + D)) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      _ = 4 * (1 + D) ^ 2 * 1 := by ring
      _ ≤ 4 * (1 + D) ^ 2 * (1 + t + t') :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have m5 : C5 * μ ^ 2 * (1 + t + d) * Θ ≤ C5 * μ ^ 2 * (2 * ((1 + D) ^ 2 * (1 + t + t'))) * Θ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p0 (by positivity)) hΘ
  have m3 : C3 * μ ^ 2 * (1 + t + d) * Θ ≤ C3 * μ ^ 2 * (2 * ((1 + D) ^ 2 * (1 + t + t'))) * Θ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p0 (by positivity)) hΘ
  have m1 : C1 * μ ^ 2 * (1 + d) ^ 2 * Θ ≤ C1 * μ ^ 2 * (4 * ((1 + D) ^ 2 * (1 + t + t'))) * Θ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p1 (by positivity)) hΘ
  linarith only [x1, x2, bF5, bF3, bI, m5, m3, m1]

/-- **Global deterministic bound for the covariance of the difference.** -/
theorem i3Psi2CovPair_second_diff_bound_global {B A δ θ : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 8) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Ja Jb Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ} {μ Ma Mb c₁ c₂ D : ℝ}, 0 ≤ μ → 0 ≤ D →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) → Integrable K → Measurable K →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      Measurable Ja → Measurable Jb → (∀ x, |Ja x| ≤ Ma) → (∀ x, |Jb x| ≤ Mb) →
      Integrable Ja → Integrable Jb →
      (∀ x, 0 < torusParabolicSize x → |Ja x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |Ja (u + h) - Ja u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x →
        |Ja x - Jb x| ≤ B * μ * torusParabolicSize x ^ (-(3 + θ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |(Ja (u + h) - Jb (u + h)) - (Ja u - Jb u)| ≤
          B * μ * torusParabolicSize h ^ (1 - θ) * torusParabolicSize u ^ (-(3 + θ) - (1 - θ))) →
      (∀ x, Q₁₁ x = ∫ w, Ja (x + w) * Ja w) → (∀ x, Q₁₂ x = ∫ w, Ja (x + w) * Jb w) →
      (∀ x, Q₂₁ x = ∫ w, Jb (x + w) * Ja w) → (∀ x, Q₂₂ x = ∫ w, Jb (x + w) * Jb w) →
      c₁ = 2 * ∫ x, K x * Q₁₁ x ^ 2 → c₂ = 2 * ∫ x, K x * Q₂₂ x ^ 2 →
      I3Psi2TablesBd A μ θ Q₁₁ Q₁₂ Q₂₁ Q₂₂ →
      ∀ z z' : SpaceTime,
        (∀ a b : SpaceTime, |a.1| ≤ |z.1| + |z'.1| + 2 → |b.1| ≤ |z.1| + |z'.1| + 2 →
          torusParabolicSize (a - b) ≤ D) →
        0 < torusParabolicSize z → 0 < torusParabolicSize z' →
        0 < torusParabolicSize (z - z') →
        |i3Psi2CovPair K Q₁₁ Q₁₁ Q₁₁ Q₁₁ c₁ c₁ z z' - i3Psi2CovPair K Q₁₁ Q₁₂ Q₂₁ Q₂₂ c₁ c₂ z z' -
          i3Psi2CovPair K Q₂₂ Q₂₁ Q₁₂ Q₁₁ c₂ c₁ z z' + i3Psi2CovPair K Q₂₂ Q₂₂ Q₂₂ Q₂₂ c₂ c₂ z z'| ≤
          C * μ ^ 2 * ((1 + D) ^ 2 * (1 + |z.1| + |z'.1|)) * treeTheta z z' := by
  have hB' : 0 ≤ B + 4 * A := by positivity
  obtain ⟨C5, hC5, h5⟩ := i3Psi2DiffDouble5_bound_global (B := B) (A := A) hB hA hδ hδ1 hθ hθ1
  obtain ⟨C3, hC3, h3⟩ := i3Psi2DiffDouble3_bound_global (B := B) (A := A) hB hA hδ hδ1 hθ hθ1
  obtain ⟨C1, hC1, h1⟩ := i3Psi2Chaos1Diff_bound_global (B := B + 4 * A) hB' hδ hδ1 hθ hθ1
  refine ⟨2 * C5 + 2 * C3 + 144 * C1, by positivity, ?_⟩
  intro K Ja Jb Q11 Q12 Q21 Q22 μ Ma Mb c1 c2 D hμ hD0 hKs hKi hKm hK hJam hJbm hJab hJbb hJai
    hJbi hJa hJainc hΔJ hΔJinc hQ11 hQ12 hQ21 hQ22 hc1 hc2 hT z z' hD hz hz' hzz
  have hm11 := measurable_Q_of_hQJ hJam hJam hQ11
  have hm12 := measurable_Q_of_hQJ hJam hJbm hQ12
  have hm21 := measurable_Q_of_hQJ hJbm hJam hQ21
  have hm22 := measurable_Q_of_hQJ hJbm hJbm hQ22
  set MQ : ℝ := Ma * (∫ w, |Ja w|) + Ma * (∫ w, |Jb w|) + Mb * (∫ w, |Ja w|) +
    Mb * (∫ w, |Jb w|) with hMQ
  have hMa : 0 ≤ Ma := (abs_nonneg _).trans (hJab 0)
  have hMb : 0 ≤ Mb := (abs_nonneg _).trans (hJbb 0)
  have iA : 0 ≤ ∫ w, |Ja w| := integral_nonneg fun _ => abs_nonneg _
  have iB : 0 ≤ ∫ w, |Jb w| := integral_nonneg fun _ => abs_nonneg _
  have b11 := abs_Q_le_pair hJam hJam hJab hJai hQ11
  have b12 := abs_Q_le_pair hJam hJbm hJab hJbi hQ12
  have b21 := abs_Q_le_pair hJbm hJam hJbb hJai hQ21
  have b22 := abs_Q_le_pair hJbm hJbm hJbb hJbi hQ22
  have hb11 : ∀ x, |Q11 x| ≤ MQ := fun x => by
    have := b11 x
    have := mul_nonneg hMa iB
    have := mul_nonneg hMb iA
    have := mul_nonneg hMb iB
    have := mul_nonneg hMa iA
    simp only [hMQ]; linarith
  have hb12 : ∀ x, |Q12 x| ≤ MQ := fun x => by
    have := b12 x
    have := mul_nonneg hMa iB
    have := mul_nonneg hMb iA
    have := mul_nonneg hMb iB
    have := mul_nonneg hMa iA
    simp only [hMQ]; linarith
  have hb21 : ∀ x, |Q21 x| ≤ MQ := fun x => by
    have := b21 x
    have := mul_nonneg hMa iB
    have := mul_nonneg hMb iA
    have := mul_nonneg hMb iB
    have := mul_nonneg hMa iA
    simp only [hMQ]; linarith
  have hb22 : ∀ x, |Q22 x| ≤ MQ := fun x => by
    have := b22 x
    have := mul_nonneg hMa iB
    have := mul_nonneg hMb iA
    have := mul_nonneg hMb iB
    have := mul_nonneg hMa iA
    simp only [hMQ]; linarith
  have hsd := i3Psi2CovPair_second_diff_eq hKi hJam hJbm hJab hJbb hJai hJbi hQ12 hQ21 hQ11 hQ22
    hm11 hm12 hm21 hm22 hb11 hb12 hb21 hb22 (c1 := c1) (c2 := c2) z z'
  rw [hsd]
  obtain ⟨iF5, bF5⟩ := h5 hμ hD0 hKm hm11 hm12 hm21 hm22 hK hKs hT z z' hD hzz hz hz'
  obtain ⟨iF3, bF3⟩ := h3 hμ hD0 hKm hm11 hm12 hm21 hm22 hK hKs hT z z' hD hzz hz hz'
  have hQ1 : ∀ x, 0 < torusParabolicSize x →
      |Q11 x| ≤ (B + 4 * A) * torusParabolicSize x ^ (-(1 : ℝ)) := fun x hx => by
    have := (hT.abs_entries_le hx).1
    have p : 0 ≤ torusParabolicSize x ^ (-(1 : ℝ)) := Real.rpow_nonneg hx.le _
    linarith [mul_nonneg hB p, mul_nonneg hA p]
  have hQ2 : ∀ x, 0 < torusParabolicSize x →
      |Q22 x| ≤ (B + 4 * A) * torusParabolicSize x ^ (-(1 : ℝ)) := fun x hx => by
    have := (hT.abs_entries_le hx).2.2.2
    have p : 0 ≤ torusParabolicSize x ^ (-(1 : ℝ)) := Real.rpow_nonneg hx.le _
    linarith [mul_nonneg hB p, mul_nonneg hA p]
  have hΔQ : ∀ x, 0 < torusParabolicSize x →
      |Q11 x - Q22 x| ≤ (B + 4 * A) * μ * torusParabolicSize x ^ (-(1 + θ)) := fun x hx => by
    have := hT.abs_diag_sub_le hx
    have p : 0 ≤ μ * torusParabolicSize x ^ (-(1 + θ)) :=
      mul_nonneg hμ (Real.rpow_nonneg hx.le _)
    linarith [mul_nonneg hB p, mul_nonneg hA p]
  have hJa' : ∀ x, 0 < torusParabolicSize x →
      |Ja x| ≤ (B + 4 * A) * torusParabolicSize x ^ (-(3 : ℝ)) := fun x hx => by
    have := hJa x hx
    have p : 0 ≤ torusParabolicSize x ^ (-(3 : ℝ)) := Real.rpow_nonneg hx.le _
    linarith [mul_nonneg hB p, mul_nonneg hA p]
  have hK' : ∀ x, 0 < torusParabolicSize x →
      |K x| ≤ (B + 4 * A) * torusParabolicSize x ^ (-(3 : ℝ)) := fun x hx => by
    have := hK x hx
    have p : 0 ≤ torusParabolicSize x ^ (-(3 : ℝ)) := Real.rpow_nonneg hx.le _
    linarith [mul_nonneg hB p, mul_nonneg hA p]
  have hn : ∀ e : ℝ, 0 ≤ torusParabolicSize z ^ e := fun e => Real.rpow_nonneg
    (torusParabolicSize_nonneg _) _
  have hJainc' : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |Ja (u + h) - Ja u| ≤ (B + 4 * A) * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) :=
    fun u h hu hh => (hJainc u h hu hh).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (torusParabolicSize_nonneg _))
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have hΔJ' : ∀ x, 0 < torusParabolicSize x →
      |Ja x - Jb x| ≤ (B + 4 * A) * μ * torusParabolicSize x ^ (-(3 + θ)) := fun x hx =>
    (hΔJ x hx).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hμ)
      (Real.rpow_nonneg hx.le _))
  have hΔJinc' : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |(Ja (u + h) - Jb (u + h)) - (Ja u - Jb u)| ≤ (B + 4 * A) * μ *
          torusParabolicSize h ^ (1 - θ) * torusParabolicSize u ^ (-(3 + θ) - (1 - θ)) :=
    fun u h hu hh => (hΔJinc u h hu hh).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hμ)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  obtain ⟨-, bI⟩ := h1 (M := Ma + Mb) (MQ := MQ) hμ hD0 hKs hKi hKm hJam hJbm hm11 hm22 (fun x => (hJab x).trans (by linarith)) (fun x => (hJbb x).trans (by linarith)) hJai hJbi hb11 hb22 hK' hJa'
    hJainc' hQ1 hQ2 hΔQ hΔJ' hΔJinc' hQ11 hQ22 hc1 hc2 z z' hz hz' hzz
    (fun w hw => hD z w (by linarith [abs_nonneg z.1, abs_nonneg z'.1])
      (by linarith [abs_nonneg z.1, abs_nonneg z'.1]))
    (fun w hw => hD z' w (by linarith [abs_nonneg z.1, abs_nonneg z'.1])
      (by linarith [abs_nonneg z.1, abs_nonneg z'.1]))
  have x1 := abs_add_le ((∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v *
          i3Psi2DiffChi5 Q11 Q12 Q21 Q22 (w - v) (w - z') (z - v) (z - z')) +
        (∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v *
          i3Psi2DiffChi3 Q11 Q12 Q21 Q22 (w - z) (v - z') (w - v) (w - z') (z - v) (z - z')))
    (36 * ∫ y, (i3Psi2D K Q11 Ja c1 z y - i3Psi2D K Q22 Jb c2 z y) *
          (i3Psi2D K Q11 Ja c1 z' y - i3Psi2D K Q22 Jb c2 z' y))
  have x2 := abs_add_le (∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v *
          i3Psi2DiffChi5 Q11 Q12 Q21 Q22 (w - v) (w - z') (z - v) (z - z'))
    (∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v *
          i3Psi2DiffChi3 Q11 Q12 Q21 Q22 (w - z) (v - z') (w - v) (w - z') (z - v) (z - z'))
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 36)] at x1
  exact diffPoly_combine_alg hD0 hδ hδ1 hC5 hC3 hC1 (abs_nonneg z.1) (abs_nonneg z'.1)
    (treeTheta_nonneg z z') x1 x2 bF5 bF3 bI

end RegularityStructures.Phi43

end
