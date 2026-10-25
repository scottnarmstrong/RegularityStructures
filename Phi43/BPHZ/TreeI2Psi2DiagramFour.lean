/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramCov

/-!
# The chaos-`4` monomials of the tree `I(Ψ²) Ψ²`: squared pairing

For `A(w) = K(y - w) - K(x - w)`, `A'(w') = K(y' - w') - K(x - w')` and a covariance `Q`
with `|Q| ≤ B s^(-1)`, the principal pairing
`∫∫ |A(w)| |A'(w')| Q(w - w')² dw dw' ≲ B⁴ s(y - x)^θ s(y' - x)^θ`, `θ = 1 - δ/2`
(`i2Psi2LintBound_chaos4_sq`): the inner integral is `≲ B³ r^θ (s(y - w')^(-θ) + s(x - w')^(-θ))`
(`i2Psi2LintBound_kernel_sub_two`, total order `5 + θ > 5`), and the outer one is bounded
(`i2Psi2LintBound_kernel_sub_slab`, total order `3 + θ + θ < 5`).  [Hai14, p. 169, after (10.39)].
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Principal pairing of chaos `4`**, `∫∫ |A| |A'| Q(w - w')²`. -/
theorem i2Psi2LintBound_chaos4_sq {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable K → Measurable Q →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) →
      ∀ x y y' : SpaceTime, |y.1 - x.1| ≤ 1 → |y'.1 - x.1| ≤ 1 →
        i2Psi2LintBound volume (fun q : SpaceTime × SpaceTime =>
          |i2Psi2Increment K x y q.1| * |i2Psi2Increment K x y' q.2| * Q (q.1 - q.2) ^ 2)
          (C * B ^ 4 * torusParabolicSize (y - x) ^ (1 - δ / 2) *
            torusParabolicSize (y' - x) ^ (1 - δ / 2)) := by
  have hθ0 : 0 < 1 - δ / 2 := by linarith
  have hθ1 : 1 - δ / 2 ≤ 1 := by linarith
  obtain ⟨CA, hCA, hA⟩ := i2Psi2LintBound_kernel_sub_two hθ0 hθ1
  obtain ⟨CO, hCO, hO⟩ := i2Psi2LintBound_kernel_sub_slab (θ := 1 - δ / 2) (l₁ := 1 - δ / 2)
    (l₂ := 0) hθ0.le hθ1 hθ0.le le_rfl (by linarith)
  refine ⟨8 * CA * CO, by positivity, ?_⟩
  intro K Q B hB hKm hQm hKs hKb hKi hQb x y y' hxy hxy'
  have mA := measurable_i2Psi2Increment hKm
  set θ := 1 - δ / 2 with hθ
  set r := torusParabolicSize (y - x) with hr
  set r' := torusParabolicSize (y' - x) with hr'
  have hr0 : 0 ≤ r ^ θ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hr0' : 0 ≤ r' ^ θ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  show i2Psi2LintBound (volume.prod volume) _ _
  refine i2Psi2LintBound.of_prod_symm
    (G := fun w' => |i2Psi2Increment K x y' w'| * (4 * B ^ 2) *
      (CA * B * r ^ θ * (torusParabolicSize (y - w') ^ (-θ) +
        torusParabolicSize (x - w') ^ (-θ)))) ?_ ?_ ?_
  · exact (((continuous_abs.measurable.comp (mA x y)).comp measurable_fst).mul
      ((continuous_abs.measurable.comp (mA x y')).comp measurable_snd)).mul
      ((hQm.comp (measurable_fst.sub measurable_snd)).pow_const 2)
  · filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x]
      with w' hy hx
    have h1 := (hA hB hKb hKi x y w' hy hx).const_mul (c := |i2Psi2Increment K x y' w'| *
      (4 * B ^ 2)) (mul_nonneg (abs_nonneg _) (by positivity))
    refine h1.mono_ae ?_ (le_of_eq (by ring))
    filter_upwards [ae_torusParabolicSize_sub_pos w'] with w hw
    have hq := sq_cov_flip_le hB hQb hw
    have n1 : 0 ≤ |i2Psi2Increment K x y w| * |i2Psi2Increment K x y' w'| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc |i2Psi2Increment K x y w| * |i2Psi2Increment K x y' w'| * Q (w - w') ^ 2
        ≤ |i2Psi2Increment K x y w| * |i2Psi2Increment K x y' w'| *
          (4 * B ^ 2 * torusParabolicSize (w' - w) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left hq n1
      _ = _ := by simp only [i2Psi2Increment]; ring
  · have e0 : ∀ u : SpaceTime, torusParabolicSize u ^ (-(0 : ℝ)) = 1 := fun u => by simp
    have hOy := hO hB hKs hKb hKi x y' y x hxy' (by linarith) (by simp)
    have hOx := hO hB hKs hKb hKi x y' x y hxy' (by simp) (by linarith)
    have nn : ∀ (g₁ g₂ : SpaceTime) w', 0 ≤ |i2Psi2Increment K x y' w'| *
        (torusParabolicSize (g₁ - w') ^ (-θ) * torusParabolicSize (g₂ - w') ^ (-(0 : ℝ))) :=
      fun g₁ g₂ w' => mul_nonneg (abs_nonneg _) (mul_nonneg
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
    have hM : 0 ≤ CO * B * r' ^ θ := mul_nonneg (mul_nonneg hCO hB) hr0'
    have mm : Measurable fun w' : SpaceTime => |i2Psi2Increment K x y' w'| *
        (torusParabolicSize (y - w') ^ (-θ) * torusParabolicSize (x - w') ^ (-(0 : ℝ))) :=
      (continuous_abs.measurable.comp (mA x y')).mul
        ((measurable_torusParabolicSize_sub_rpow y _).mul
          (measurable_torusParabolicSize_sub_rpow x _))
    have s := hOy.add mm.aemeasurable (nn y x) (nn x y) hM hM hOx
    have c := s.const_mul (c := 4 * B ^ 2 * CA * B * r ^ θ)
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCA) hB) hr0)
    refine c.mono (fun w' => ?_) (le_of_eq (by ring))
    simp only [e0, mul_one]
    ring_nf
    exact le_rfl

private theorem alg_prod {CA B ra ra' d1 p q a2 b1 b2 : ℝ}
    (hra : 0 ≤ ra) (hra' : 0 ≤ ra') (hd1 : 0 ≤ d1) (hp : 0 ≤ p)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (h1 : a2 ≤ 2 * p) (h2 : b1 ≤ 2 * d1) (h3 : b2 ≤ 2 * q) :
    4 * B ^ 2 * (CA * B * ra * (d1 + a2)) * (B ^ 2 * (CA * B * ra' * (b1 + b2))) ≤
      16 * CA ^ 2 * B ^ 6 * ra * ra' * (d1 + p) * (d1 + q) := by
  have e1 : d1 + a2 ≤ 2 * (d1 + p) := by linarith
  have e2 : b1 + b2 ≤ 2 * (d1 + q) := by linarith
  have k : 0 ≤ CA ^ 2 * B ^ 6 * ra * ra' := by positivity
  have e3 : (d1 + a2) * (b1 + b2) ≤ 2 * (d1 + p) * (2 * (d1 + q)) :=
    mul_le_mul e1 e2 (by linarith) (by linarith)
  calc 4 * B ^ 2 * (CA * B * ra * (d1 + a2)) * (B ^ 2 * (CA * B * ra' * (b1 + b2)))
      = 4 * (CA ^ 2 * B ^ 6 * ra * ra') * ((d1 + a2) * (b1 + b2)) := by ring
    _ ≤ 4 * (CA ^ 2 * B ^ 6 * ra * ra') * (2 * (d1 + p) * (2 * (d1 + q))) :=
        mul_le_mul_of_nonneg_left e3 (by positivity)
    _ = _ := by ring

/-- **The product pairing of chaos `4`**: `(∫ |A| Q(w - y')²) (∫ |A'| Q'(y - w')²)`. -/
theorem i2Psi2LintBound_chaos4_prod {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q Q' : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable K → Measurable Q →
      Measurable Q' → (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |Q' u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') →
        i2Psi2LintBound volume (fun q : SpaceTime × SpaceTime =>
          (|i2Psi2Increment K x y q.1| * Q (q.1 - y') ^ 2) *
            (|i2Psi2Increment K x y' q.2| * Q' (y - q.2) ^ 2))
          (C * B ^ 6 * torusParabolicSize (y - x) ^ θ * torusParabolicSize (y' - x) ^ θ *
            (torusParabolicSize (y - y') ^ (-θ) + torusParabolicSize (y' - x) ^ (-θ)) *
            (torusParabolicSize (y - y') ^ (-θ) + torusParabolicSize (y - x) ^ (-θ))) := by
  obtain ⟨CA, hCA, hA⟩ := i2Psi2LintBound_kernel_sub_two hθ hθ1
  refine ⟨16 * CA ^ 2, by positivity, ?_⟩
  intro K Q Q' B hB hKm hQm hQm' hKs hKb hKi hQb hQb' x y y' hr hr' hd
  have mA := measurable_i2Psi2Increment hKm
  have hyx : 0 < torusParabolicSize (x - y) := torusParabolicSize_pos_of_sub_pos hr
  have hyx' : 0 < torusParabolicSize (x - y') := torusParabolicSize_pos_of_sub_pos hr'
  have hdd : 0 < torusParabolicSize (y' - y) := torusParabolicSize_pos_of_sub_pos hd
  have nrpow : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  -- the first factor
  have fa := (hA hB hKb hKi x y y' hd hyx').const_mul (c := 4 * B ^ 2) (by positivity)
  have fa' : i2Psi2LintBound volume (fun w => |i2Psi2Increment K x y w| * Q (w - y') ^ 2)
      (4 * B ^ 2 * (CA * B * torusParabolicSize (y - x) ^ θ *
        (torusParabolicSize (y - y') ^ (-θ) + torusParabolicSize (x - y') ^ (-θ)))) := by
    refine fa.mono_ae ?_ le_rfl
    filter_upwards [ae_torusParabolicSize_sub_pos y'] with w hw
    have hq := sq_cov_flip_le hB hQb hw
    calc |i2Psi2Increment K x y w| * Q (w - y') ^ 2
        ≤ |i2Psi2Increment K x y w| * (4 * B ^ 2 * torusParabolicSize (y' - w) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hq (abs_nonneg _)
      _ = _ := by simp only [i2Psi2Increment]; ring
  -- the second factor
  have fb := (hA hB hKb hKi x y' y hdd hyx).const_mul (c := B ^ 2) (by positivity)
  have fb' : i2Psi2LintBound volume (fun w => |i2Psi2Increment K x y' w| * Q' (y - w) ^ 2)
      (B ^ 2 * (CA * B * torusParabolicSize (y' - x) ^ θ *
        (torusParabolicSize (y' - y) ^ (-θ) + torusParabolicSize (x - y) ^ (-θ)))) := by
    refine fb.mono_ae ?_ le_rfl
    filter_upwards [ae_torusParabolicSize_sub_pos y] with w hw
    have hq := sq_cov_le hQb' hw
    calc |i2Psi2Increment K x y' w| * Q' (y - w) ^ 2
        ≤ |i2Psi2Increment K x y' w| * (B ^ 2 * torusParabolicSize (y - w) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hq (abs_nonneg _)
      _ = _ := by simp only [i2Psi2Increment]; ring
  have hMa : 0 ≤ 4 * B ^ 2 * (CA * B * torusParabolicSize (y - x) ^ θ *
        (torusParabolicSize (y - y') ^ (-θ) + torusParabolicSize (x - y') ^ (-θ))) :=
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (mul_nonneg hCA hB) (nrpow _ _))
      (add_nonneg (nrpow _ _) (nrpow _ _)))
  have hprod := i2Psi2LintBound.prod_mul (μ := volume) (ν := volume)
    (((continuous_abs.measurable.comp (mA x y)).mul ((hQm.comp
      (measurable_id.sub measurable_const)).pow_const 2)).aemeasurable)
    (((continuous_abs.measurable.comp (mA x y')).mul ((hQm'.comp
      (measurable_const.sub measurable_id)).pow_const 2)).aemeasurable)
    (fun w => mul_nonneg (abs_nonneg _) (sq_nonneg _)) hMa fa' fb'
  refine hprod.mono (fun q => le_rfl) ?_
  have t1 := torusParabolicSize_sub_rpow_neg_le (a := x) (b := y') (e := θ) hθ.le hθ1 hr'
  have t2 := torusParabolicSize_sub_rpow_neg_le (a := y') (b := y) (e := θ) hθ.le hθ1 hd
  have t3 := torusParabolicSize_sub_rpow_neg_le (a := x) (b := y) (e := θ) hθ.le hθ1 hr
  have := alg_prod (CA := CA) (B := B) (nrpow (y - x) θ) (nrpow (y' - x) θ) (nrpow (y - y') (-θ))
    (nrpow (y' - x) (-θ)) (nrpow (y' - y) (-θ)) (nrpow (x - y) (-θ)) t1 t2 t3
  calc _ ≤ _ := this
    _ = _ := by ring

end RegularityStructures

end
