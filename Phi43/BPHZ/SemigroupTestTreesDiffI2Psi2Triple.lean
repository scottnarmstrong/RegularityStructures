/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI2Psi2IntBd
public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Sq
public import Phi43.BPHZ.TreeI2Psi2DiagramDiffBound

/-!
# The chain monomials of the difference of `I(Ψ²) Ψ²`, for arbitrary `x, y, y'`

`i2Psi2Diff_triple_global`: for the integrand
`i2Psi2Triple K x y y' g h a b c = |A_y(w)| |A_{y'}(w')| s(g - w)^(-a) s(w' - w)^(-b) s(h - w')^(-c)`
with `a, c ≥ 0`, `b > 0`, `3 + c + b + δ = 5 + η`, `3 + a + η < 5`,
`∫∫ Triple ≤ C B² D^δ (1 + |y.1 - x.1|)` whenever `D` bounds `s(w - w')` on the slabs of
`A_y`, `A_{y'}`.  No smallness of `s(y - x)`, `s(y' - x)` is assumed.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

private theorem triple_pointwise {A A' Iw Iv sa sb sc mw nv B : ℝ} (hB : 0 ≤ B)
    (hA : |A| ≤ B * Iw) (hA' : |A'| ≤ B * Iv) (hIw : 0 ≤ Iw) (hIv : 0 ≤ Iv) (hsa : 0 ≤ sa)
    (hsb : 0 ≤ sb) (hsc : 0 ≤ sc) (hm : Iw * sa ≤ mw) (hn : Iv * sc ≤ nv) :
    |A| * |A'| * (sa * sb * sc) ≤ B ^ 2 * (mw * (sb * nv)) := by
  have h1 : |A| * |A'| ≤ (B * Iw) * (B * Iv) :=
    mul_le_mul hA hA' (abs_nonneg _) (mul_nonneg hB hIw)
  have h2 : (Iw * sa) * (Iv * sc) ≤ mw * nv :=
    mul_le_mul hm hn (mul_nonneg hIv hsc) ((mul_nonneg hIw hsa).trans hm)
  have h3 : 0 ≤ sa * sb * sc := mul_nonneg (mul_nonneg hsa hsb) hsc
  calc |A| * |A'| * (sa * sb * sc) ≤ ((B * Iw) * (B * Iv)) * (sa * sb * sc) :=
        mul_le_mul_of_nonneg_right h1 h3
    _ = B ^ 2 * sb * ((Iw * sa) * (Iv * sc)) := by ring
    _ ≤ B ^ 2 * sb * (mw * nv) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (sq_nonneg B) hsb)
    _ = B ^ 2 * (mw * (sb * nv)) := by ring

/-- **The chain monomial, globally.** -/
theorem i2Psi2Diff_triple_global {a b c δ η : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c)
    (hδ : 0 < δ) (hη : 0 < η) (hc2 : 3 + c < 5) (hbδ : b + δ < 5)
    (hsum : 3 + c + b + δ = 5 + η) (haη : 3 + a + η < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, SingularKernelData K Q B →
      ∀ (x y y' g h : SpaceTime) {D : ℝ}, 0 ≤ D →
      (∀ w v : SpaceTime, |w.1 - x.1| ≤ |y.1 - x.1| + 1 → |v.1 - x.1| ≤ |y'.1 - x.1| + 1 →
        torusParabolicSize (w - v) ≤ D) →
      I2Psi2DiffIntBd (i2Psi2Triple K x y y' g h a b c)
        (C * B ^ 2 * D ^ δ * (1 + |y.1 - x.1|)) := by
  obtain ⟨C0, hC0, h0⟩ := i2Psi2Diff_coupled_sum_integral (α := 3 + a) (β := 3 + c) (k := b)
    (δ := δ) (η := η) (by linarith) (by linarith) hb hδ hη hc2 hbδ (by linarith) haη
  have hA0 : 0 ≤ (80 / (5 - (3 + a + η)) + 2) := by
    have : 0 < 5 - (3 + a + η) := by linarith
    positivity
  refine ⟨C0 * 16 * (80 / (5 - (3 + a + η)) + 2), by positivity, ?_⟩
  intro K Q B hK x y y' g h D hD0 hD
  have hB := hK.nonneg
  have hDδ : 0 ≤ D ^ δ := Real.rpow_nonneg hD0 _
  set F : SpaceTime → SpaceTime → ℝ := fun w v => i2Psi2Triple K x y y' g h a b c (w, v) with hF
  have hmeas : Measurable (Function.uncurry F) := by
    have := measurable_i2Psi2Triple hK.measurable_K x y y' g h a b c
    exact this
  have key := h0 (F := F) (Λ := B ^ 2) (τ := x.1) (τ' := x.1) (T := |y.1 - x.1| + 1)
    (T' := |y'.1 - x.1| + 1) (D := D) (c := ![1, 1, 2]) (c' := ![1, 1, 2])
    (q := ![y, x, g]) (q' := ![y', x, h]) (by positivity) (by positivity) (by positivity) hD0
    (by intro i; fin_cases i <;> simp) (by intro j; fin_cases j <;> simp)
    hmeas.aestronglyMeasurable hD ?_
  · have hnn : ∀ w v, 0 ≤ F w v := fun w v => i2Psi2Triple_nonneg K x y y' g h a b c (w, v)
    have hint : Integrable (fun q : SpaceTime × SpaceTime => i2Psi2Triple K x y y' g h a b c q)
        (volume : Measure (SpaceTime × SpaceTime)) := by
      rw [Measure.volume_eq_prod]
      exact key.1
    refine ⟨hint, ?_⟩
    have e1 : ∫ q : SpaceTime × SpaceTime, i2Psi2Triple K x y y' g h a b c q =
        ∫ w, ∫ v, F w v := by
      rw [Measure.volume_eq_prod]
      exact integral_prod (Function.uncurry F) key.1
    rw [e1]
    refine (le_abs_self _).trans (key.2.trans ?_)
    have e3 : (∑ i, (![1, 1, 2] : Fin 3 → ℝ) i) = 4 := by
      simp [Fin.sum_univ_three]; norm_num
    rw [e3]
    have ha0 : 0 ≤ 80 / (5 - (3 + a + η)) := div_nonneg (by norm_num) (by linarith)
    have hab : 0 ≤ |y.1 - x.1| := abs_nonneg _
    have hpos : 0 ≤ C0 * B ^ 2 * D ^ δ := by positivity
    calc C0 * B ^ 2 * D ^ δ * (4 * 4) * (80 / (5 - (3 + a + η)) + 2 * (|y.1 - x.1| + 1))
        = (C0 * B ^ 2 * D ^ δ) * (16 * (80 / (5 - (3 + a + η)) + 2 * (|y.1 - x.1| + 1))) := by
          ring
      _ ≤ (C0 * B ^ 2 * D ^ δ) * (16 * ((80 / (5 - (3 + a + η)) + 2) * (1 + |y.1 - x.1|))) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hpos
      _ = _ := by ring
  · have hex : ∀ᵐ w : SpaceTime ∂volume, 0 < torusParabolicSize (y - w) ∧
        0 < torusParabolicSize (x - w) ∧ 0 < torusParabolicSize (g - w) := by
      filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x,
        ae_torusParabolicSize_sub_pos g] with w a b c
      exact ⟨a, b, c⟩
    filter_upwards [ae_abs_i2Psi2Increment_le hK x y, hex] with w hw hpos
    obtain ⟨p1, p2, p3⟩ := hpos
    have hexv : ∀ᵐ v : SpaceTime ∂volume, 0 < torusParabolicSize (y' - v) ∧
        0 < torusParabolicSize (x - v) ∧ 0 < torusParabolicSize (h - v) := by
      filter_upwards [ae_torusParabolicSize_sub_pos y', ae_torusParabolicSize_sub_pos x,
        ae_torusParabolicSize_sub_pos h] with w a b c
      exact ⟨a, b, c⟩
    filter_upwards [ae_abs_i2Psi2Increment_le hK x y', hexv] with v hv hpos'
    obtain ⟨p1', p2', p3'⟩ := hpos'
    have m1 := i2Psi2Diff_ind_merge {w : SpaceTime | |w.1 - x.1| ≤ |y.1 - x.1| + 1} ha p1 p2 p3
    have m2 := i2Psi2Diff_ind_merge {w : SpaceTime | |w.1 - x.1| ≤ |y'.1 - x.1| + 1} hc p1' p2' p3'
    have nI : ∀ (S : Set SpaceTime) (p q : SpaceTime) (z : SpaceTime),
        0 ≤ Set.indicator S (fun w => singularPow 3 p w + singularPow 3 q w) z := fun S p q z =>
      Set.indicator_nonneg (fun w _ => add_nonneg (singularPow_nonneg _ _ _)
        (singularPow_nonneg _ _ _)) z
    have hsw : torusParabolicSize (v - w) = torusParabolicSize (w - v) :=
      i2Psi2Diff_size_swap v w
    have := triple_pointwise (A := i2Psi2Increment K x y w) (A' := i2Psi2Increment K x y' v)
      (sa := singularPow a g w) (sb := singularPow b w v) (sc := singularPow c h v)
      hB hw hv (nI _ y x w) (nI _ y' x v) (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)
      (singularPow_nonneg _ _ _) m1 m2
    have hFe : F w v = |i2Psi2Increment K x y w| * |i2Psi2Increment K x y' v| *
        (singularPow a g w * singularPow b w v * singularPow c h v) := by
      simp only [hF, i2Psi2Triple, singularPow, hsw]
    have hnn : 0 ≤ F w v := i2Psi2Triple_nonneg K x y y' g h a b c (w, v)
    rw [abs_of_nonneg hnn, hFe]
    exact this

end RegularityStructures

end
