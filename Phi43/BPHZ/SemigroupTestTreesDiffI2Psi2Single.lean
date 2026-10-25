/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI2Psi2Triple

/-!
# The single and product monomials of the difference of `I(Ψ²) Ψ²`, for arbitrary `x, y, y'`

* `i2Psi2Diff_single_global`: for `a ≥ 0`, `b > 0`, `3 + a + b + δ = 5 + η`,
  `∫ |A_p(w)| s_a(p; w) s_b(e; w) dw ≤ C B D^δ (s(p - e)^(-η) + s(x - e)^(-η))` when `D` bounds
  `s(e - w)` on the slab of `A_p`;
* `I2Psi2DiffIntBd.of_product`: a product `f(w) g(w')` of nonnegative integrable functions.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- **Single integral against two centred powers.** -/
theorem i2Psi2Diff_single_global {a b δ η : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hδ : 0 < δ)
    (hη : 0 < η) (haa : 3 + a < 5) (hbδ : b + δ < 5) (hsum : 3 + a + b + δ = 5 + η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, SingularKernelData K Q B →
      ∀ (x p e : SpaceTime) {D : ℝ}, 0 ≤ D →
      0 < torusParabolicSize (p - e) → 0 < torusParabolicSize (x - e) →
      (∀ w : SpaceTime, |w.1 - x.1| ≤ |p.1 - x.1| + 1 → torusParabolicSize (e - w) ≤ D) →
      Integrable (fun w => |i2Psi2Increment K x p w| *
          (singularPow a p w * singularPow b e w)) ∧
        ∫ w, |i2Psi2Increment K x p w| * (singularPow a p w * singularPow b e w) ≤
          C * B * D ^ δ * (torusParabolicSize (p - e) ^ (-η) +
            torusParabolicSize (x - e) ^ (-η)) := by
  obtain ⟨C1, hC1, h1⟩ := singularIntLe_mul_two (a := 3 + a) (b := b + δ) (η := η)
    (by linarith) haa (by linarith) hbδ hη (by linarith)
  refine ⟨C1 * 3, by positivity, ?_⟩
  intro K Q B h x p e D hD0 hpe hxe hD
  have hB := h.nonneg
  have hDδ : 0 ≤ D ^ δ := Real.rpow_nonneg hD0 _
  have hs := (((h1 p e hpe).const_mul (c := 3) (by norm_num)).add (h1 x e hxe)).const_mul
    (c := B * D ^ δ) (by positivity)
  have hmeas : AEStronglyMeasurable (fun w => |i2Psi2Increment K x p w| *
      (singularPow a p w * singularPow b e w)) volume :=
    (((continuous_abs.measurable.comp (h.measurable_increment x p)).mul
      ((measurable_singularPow a p).mul (measurable_singularPow b e)))).aestronglyMeasurable
  have key := integrable_abs_integral_le_of_singularIntLe
    (G := fun w => |i2Psi2Increment K x p w| * (singularPow a p w * singularPow b e w))
    (M := fun w => B * D ^ δ * (3 * (singularPow (3 + a) p w * singularPow (b + δ) e w) +
      singularPow (3 + a) x w * singularPow (b + δ) e w)) hs hmeas ?_
  · refine ⟨key.1, (le_abs_self _).trans (key.2.trans ?_)⟩
    have n1 : 0 ≤ torusParabolicSize (p - e) ^ (-η) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have n2 : 0 ≤ torusParabolicSize (x - e) ^ (-η) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have hBD : 0 ≤ B * D ^ δ := mul_nonneg hB hDδ
    have := mul_nonneg (mul_nonneg hBD hC1) n2
    nlinarith [this]
  · filter_upwards [ae_abs_i2Psi2Increment_le h x p, ae_torusParabolicSize_sub_pos e,
      ae_torusParabolicSize_sub_pos p, ae_torusParabolicSize_sub_pos x] with w hw hpos hpp hpx
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg (singularPow_nonneg _ _ _)
      (singularPow_nonneg _ _ _)))]
    by_cases hS : w ∈ {w : SpaceTime | |w.1 - x.1| ≤ |p.1 - x.1| + 1}
    · simp only [Set.indicator_of_mem hS] at hw
      have hpad := rpow_neg_le_pad (k := b) hpos (hD w hS) (δ := δ) hδ.le
      have hsp : singularPow b e w ≤ D ^ δ * singularPow (b + δ) e w := by
        simpa [singularPow] using hpad
      have hind := i2Psi2Diff_ind_merge Set.univ ha (p₁ := p) (p₂ := x) (e := p) (w := w)
        hpp hpx hpp
      simp only [Set.indicator_univ, Fin.sum_univ_three] at hind
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at hind
      have hn : 0 ≤ singularPow 3 p w + singularPow 3 x w :=
        add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)
      have hn4 : 0 ≤ singularPow (3 + a) p w := singularPow_nonneg _ _ _
      have hn5 : 0 ≤ singularPow (3 + a) x w := singularPow_nonneg _ _ _
      have hsa := singularPow_nonneg a p w
      have hsb := singularPow_nonneg b e w
      calc |i2Psi2Increment K x p w| * (singularPow a p w * singularPow b e w)
          ≤ (B * (singularPow 3 p w + singularPow 3 x w)) *
              (singularPow a p w * singularPow b e w) :=
            mul_le_mul_of_nonneg_right hw (mul_nonneg hsa hsb)
        _ = B * (((singularPow 3 p w + singularPow 3 x w) * singularPow a p w) *
              singularPow b e w) := by ring
        _ ≤ B * ((3 * singularPow (3 + a) p w + singularPow (3 + a) x w) *
              (D ^ δ * singularPow (b + δ) e w)) := by
            refine mul_le_mul_of_nonneg_left ?_ hB
            exact mul_le_mul (by linarith) hsp hsb (by positivity)
        _ = _ := by ring
    · simp only [Set.indicator_of_notMem hS, mul_zero] at hw
      have : |i2Psi2Increment K x p w| = 0 := le_antisymm hw (abs_nonneg _)
      rw [this, zero_mul]
      have := singularPow_nonneg (3 + a) p w
      have := singularPow_nonneg (3 + a) x w
      have := singularPow_nonneg (b + δ) e w
      positivity

/-- A product of nonnegative integrable functions of the two variables. -/
theorem I2Psi2DiffIntBd.of_product {f g : SpaceTime → ℝ} {X Y : ℝ} (hf : Integrable f)
    (hg : Integrable g) (hf0 : ∀ w, 0 ≤ f w) (hg0 : ∀ w, 0 ≤ g w) (hX : ∫ w, f w ≤ X)
    (hY : ∫ w, g w ≤ Y) : I2Psi2DiffIntBd (fun q => f q.1 * g q.2) (X * Y) := by
  refine ⟨?_, ?_⟩
  · exact hf.mul_prod hg
  · have e : ∫ q : SpaceTime × SpaceTime, f q.1 * g q.2 = (∫ w, f w) * ∫ w, g w :=
      integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume) f g
    rw [Measure.volume_eq_prod]
    refine (le_of_eq e).trans ?_
    exact mul_le_mul hX hY (integral_nonneg hg0) ((integral_nonneg hf0).trans hX)

end RegularityStructures

end
