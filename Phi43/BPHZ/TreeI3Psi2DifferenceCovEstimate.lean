/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DifferenceCovBound
public import Phi43.BPHZ.TreeI3Psi2DifferenceCovTables
public import Phi43.BPHZ.TreeI3Psi2DifferenceDouble5
public import Phi43.BPHZ.TreeI3Psi2DifferenceDouble3
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOneBound

/-!
# The deterministic bound for the covariance of the difference of the fields of `I(Ψ³)Ψ²`

`i3Psi2CovPair_second_diff_bound`: for kernels `J_a`, `J_b` with covariances `Q_ij = J_i ⋆ J_j`
satisfying the table bounds `I3Psi2TablesBd A μ θ` and the kernel bounds
`|J_a| ≲ s^(-3)`, `|J_a - J_b| ≲ μ s^(-(3+θ))` (with Hölder increments of exponent `1 - θ`), the
second difference of the abstract covariances is bounded by `C μ² T(z, z')`,
`T = i3Psi2DiffTarget δ θ`, uniformly in the kernels.  This is the deterministic half of the
difference estimate (10.3) for the tree `I(Ψ³)Ψ²`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Deterministic bound for the covariance of the difference.** -/
theorem i3Psi2CovPair_second_diff_bound {B A δ θ : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 8) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Ja Jb Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ} {μ Ma Mb c₁ c₂ : ℝ}, 0 ≤ μ →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) → Integrable K → Measurable K →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
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
      ∀ z z' : SpaceTime, 0 < torusParabolicSize z → 0 < torusParabolicSize z' →
        0 < torusParabolicSize (z - z') → torusParabolicSize z ≤ 1 → torusParabolicSize z' ≤ 1 →
        |i3Psi2CovPair K Q₁₁ Q₁₁ Q₁₁ Q₁₁ c₁ c₁ z z' - i3Psi2CovPair K Q₁₁ Q₁₂ Q₂₁ Q₂₂ c₁ c₂ z z' -
          i3Psi2CovPair K Q₂₂ Q₂₁ Q₁₂ Q₁₁ c₂ c₁ z z' + i3Psi2CovPair K Q₂₂ Q₂₂ Q₂₂ Q₂₂ c₂ c₂ z z'| ≤
          C * μ ^ 2 * i3Psi2DiffTarget δ θ z z' := by
  have hB' : 0 ≤ B + 4 * A := by positivity
  obtain ⟨C5, hC5, h5⟩ := i3Psi2DiffDouble5_bound (B := B) (A := A) hB hA hδ hδ1 hθ hθ1
  obtain ⟨C3, hC3, h3⟩ := i3Psi2DiffDouble3_bound (B := B) (A := A) hB hA hδ hδ1 hθ hθ1
  obtain ⟨C1, hC1, h1⟩ := i3Psi2Chaos1Diff_bound (B := B + 4 * A) hB' hδ hδ1 hθ hθ1
  refine ⟨C5 + C3 + 36 * C1, by positivity, ?_⟩
  intro K Ja Jb Q11 Q12 Q21 Q22 μ Ma Mb c1 c2 hμ hKs hKi hKm hK hKinc hJam hJbm hJab hJbb hJai
    hJbi hJa hJainc hΔJ hΔJinc hQ11 hQ12 hQ21 hQ22 hc1 hc2 hT z z' hz hz' hzz hz1 hz1'
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
  obtain ⟨iF5, bF5⟩ := h5 hμ hKm hm11 hm12 hm21 hm22 hK hKinc hKs hT z z' hzz hz hz' hz1 hz1'
  obtain ⟨iF3, bF3⟩ := h3 hμ hKm hm11 hm12 hm21 hm22 hK hKs hT z z' hzz hz hz' hz1 hz1'
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
  obtain ⟨-, bI⟩ := h1 (M := Ma + Mb) (MQ := MQ) hμ hKs hKi hKm hJam hJbm hm11 hm22 (fun x => (hJab x).trans (by linarith)) (fun x => (hJbb x).trans (by linarith)) hJai hJbi hb11 hb22 hK' hJa'
    hJainc' hQ1 hQ2 hΔQ hΔJ' hΔJinc' hQ11 hQ22 hc1 hc2 z z' hz hz' hzz hz1 hz1'
  have T0 := i3Psi2DiffTarget_nonneg δ θ z z'
  have m0 : 0 ≤ μ ^ 2 * i3Psi2DiffTarget δ θ z z' := mul_nonneg (sq_nonneg μ) T0
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
  have bF5' : |∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v *
          i3Psi2DiffChi5 Q11 Q12 Q21 Q22 (w - v) (w - z') (z - v) (z - z')| ≤
      C5 * (μ ^ 2 * i3Psi2DiffTarget δ θ z z') := by rw [← mul_assoc]; exact bF5
  have bF3' : |∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v *
          i3Psi2DiffChi3 Q11 Q12 Q21 Q22 (w - z) (v - z') (w - v) (w - z') (z - v) (z - z')| ≤
      C3 * (μ ^ 2 * i3Psi2DiffTarget δ θ z z') := by rw [← mul_assoc]; exact bF3
  have bI' : |∫ y, (i3Psi2D K Q11 Ja c1 z y - i3Psi2D K Q22 Jb c2 z y) *
          (i3Psi2D K Q11 Ja c1 z' y - i3Psi2D K Q22 Jb c2 z' y)| ≤
      C1 * (μ ^ 2 * i3Psi2DiffTarget δ θ z z') := by rw [← mul_assoc]; exact bI
  have e : (C5 + C3 + 36 * C1) * μ ^ 2 * i3Psi2DiffTarget δ θ z z' =
      (C5 * (μ ^ 2 * i3Psi2DiffTarget δ θ z z') + C3 * (μ ^ 2 * i3Psi2DiffTarget δ θ z z')) +
        36 * (C1 * (μ ^ 2 * i3Psi2DiffTarget δ θ z z')) := by ring
  rw [e]
  linarith

end RegularityStructures.Phi43

end
