/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2ChaosOneCross
public import RegularityStructures.BPHZ.TreeI3Psi2ChaosOneParts
public import Phi43.BPHZ.TreeI3Psi2DiagramTarget
public import RegularityStructures.BPHZ.TreeI3Psi2DiagramYoung

/-!
# Bound for the chaos-`1` part with the counterterm cross terms

`i3Psi2Chaos1Total_bound_uniform`: for `0 < s(z), s(z') ≤ 1` and `s(z - z') > 0`,
`|i3Psi2Chaos1Total K Q c z z'| ≤ C · i3Psi2Target δ z z'`, with `C` depending only on `B, δ`.

The proof: `i3Psi2Chaos1Total = 36 ∫ (Ā(z - y) - B_z(y)) (Ā(z' - y) - B_{z'}(y)) dy`, with `Ā` of
order `-(3 + δ/2)` (Lemma 10.16) and `|B_z| ≤ Pot h_z`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem target_ge_pure {δ : ℝ} {z z' : SpaceTime} :
    torusParabolicSize (z - z') ^ (-(1 + δ)) + torusParabolicSize z ^ (-(1 + 2 * δ)) +
      torusParabolicSize z' ^ (-(1 + 2 * δ)) ≤ i3Psi2Target δ z z' := by
  have h2 : 0 ≤ torusParabolicSize (z - z') ^ (-(2 : ℝ)) *
      (torusParabolicSize z ^ (1 - δ) + torusParabolicSize z' ^ (1 - δ)) :=
    mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (add_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have h3 : 0 ≤ torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
      (torusParabolicSize z ^ (-δ) + torusParabolicSize z' ^ (-δ)) :=
    mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (add_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  unfold i3Psi2Target
  linarith

theorem rpow_neg_le_of_le_one {x e e' : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (h : e ≤ e') :
    x ^ (-e) ≤ x ^ (-e') :=
  Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)

theorem abs_i3Psi2Bz_le_pot {K J Q : SpaceTime → ℝ} (z y : SpaceTime) :
    |i3Psi2Bz K J Q z y| ≤ i3Psi2Pot J (i3Psi2Hz K Q z) y := by
  unfold i3Psi2Bz i3Psi2Pot
  calc |∫ w, K (-w) * Q (w - z) ^ 2 * J (w - y)|
      ≤ ∫ w, |K (-w) * Q (w - z) ^ 2 * J (w - y)| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun w => K (-w) * Q (w - z) ^ 2 * J (w - y))
    _ = ∫ w, i3Psi2Hz K Q z w * |J (w - y)| := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        simp only [i3Psi2Hz, abs_mul, abs_pow, sq_abs]

/-- **The chaos-`1` part with the counterterm cross terms**, uniform in `K, J, Q`. -/
theorem i3Psi2Chaos1Total_bound_uniform {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K J Q : SpaceTime → ℝ} {M c : ℝ}, Measurable K →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      Measurable J →
      (∀ x, 0 < torusParabolicSize x → |J x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |J (u + h) - J u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      (∀ x, |J x| ≤ M) → Integrable J → Measurable Q →
      (∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, Q x = ∫ w, J (x + w) * J w) → c = 2 * ∫ x, K x * Q x ^ 2 →
      ∀ z z' : SpaceTime, 0 < torusParabolicSize z → 0 < torusParabolicSize z' →
        0 < torusParabolicSize (z - z') → torusParabolicSize z ≤ 1 → torusParabolicSize z' ≤ 1 →
          |i3Psi2Chaos1Total K Q c z z'| ≤ C * i3Psi2Target δ z z' := by
  have hδ2 : 0 < δ / 2 := by linarith
  obtain ⟨C1, hC1, hA⟩ := abs_i3Psi2Abar_le hB hδ2 (by linarith)
  obtain ⟨Cu, hCu, hu⟩ := integrable_and_integral_singularPow_mul_le (a := 3 + δ / 2)
    (b := 3 + δ / 2) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨Cx, hCx, hx⟩ := chaosOne_cross_le hB hδ hδ1 hδ2 (by linarith)
  obtain ⟨Cp, hCp, hp⟩ := chaosOne_pp_le hB hδ hδ1
  refine ⟨36 * (C1 ^ 2 * Cu + 2 * C1 * Cx + 2 * Cp), by positivity, ?_⟩
  intro K J Q M c hKm hKs hK hJm hJ hJinc hJb hJi hQm hQ hQJ hc z z' hz hz' hzz hz1 hz1'
  have hKi := integrable_K hB hKm hKs hK
  have hQe := i3Psi2_Q_neg hQJ
  have hQb := abs_Q_le_of_hQJ hJm hJb hJi hQJ
  rw [i3Psi2Chaos1Total_eq hJm hJb hJi hQJ hQm hQb hKi z z']
  have iρ := integrable_i3Psi2Rho hKi hQm hQb z
  have iρ' := integrable_i3Psi2Rho hKi hQm hQb z'
  have iS := integrable_i3Psi2Smear iρ hJi
  have iS' := integrable_i3Psi2Smear iρ' hJi
  have mJz : AEStronglyMeasurable (fun y => J (z - y)) :=
    (hJm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have mJz' : AEStronglyMeasurable (fun y => J (z' - y)) :=
    (hJm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hFm : AEStronglyMeasurable (fun y => (i3Psi2Smear J (i3Psi2Rho K Q z) y - c / 2 * J (z - y)) *
      (i3Psi2Smear J (i3Psi2Rho K Q z') y - c / 2 * J (z' - y))) volume :=
    (iS.aestronglyMeasurable.sub (mJz.const_mul _)).mul
      (iS'.aestronglyMeasurable.sub (mJz'.const_mul _))
  have hsplit : ∀ y, (i3Psi2Smear J (i3Psi2Rho K Q z) y - c / 2 * J (z - y)) *
      (i3Psi2Smear J (i3Psi2Rho K Q z') y - c / 2 * J (z' - y)) =
      (i3Psi2Abar K J Q (z - y) - i3Psi2Bz K J Q z y) *
        (i3Psi2Abar K J Q (z' - y) - i3Psi2Bz K J Q z' y) := fun y => by
    rw [i3Psi2_smear_sub_eq hJm hJb hQJ hQm hQb hKi hc z y,
      i3Psi2_smear_sub_eq hJm hJb hQJ hQm hQb hKi hc z' y]
  -- the four parts
  obtain ⟨iu, bu⟩ := hu z z' hzz
  obtain ⟨ix, bx⟩ := hx hKm hKs hK hJm hJ hQm hQ hQe z z' hz hz' hz1'
  obtain ⟨ix', bx'⟩ := hx hKm hKs hK hJm hJ hQm hQ hQe z' z hz' hz hz1
  obtain ⟨ip, bp⟩ := hp hKm hKs hK hJm hJ hQm hQ hQe z z' hz hz' hz1 hz1'
  have e5 : (5 - (3 + δ / 2) - (3 + δ / 2) : ℝ) = -(1 + δ) := by ring
  rw [e5] at bu
  have n1 : 0 ≤ torusParabolicSize (z - z') ^ (-(1 + δ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have i1 : Integrable (fun y => (C1 * singularPow (3 + δ / 2) z y) *
      (C1 * singularPow (3 + δ / 2) z' y)) :=
    (iu.const_mul (C1 ^ 2)).congr (Filter.Eventually.of_forall fun y => by simp only; ring)
  have b1 : ∫ y, (C1 * singularPow (3 + δ / 2) z y) * (C1 * singularPow (3 + δ / 2) z' y) ≤
      C1 ^ 2 * (Cu * torusParabolicSize (z - z') ^ (-(1 + δ))) := by
    have : ∫ y, (C1 * singularPow (3 + δ / 2) z y) * (C1 * singularPow (3 + δ / 2) z' y) =
        C1 ^ 2 * ∫ y, singularPow (3 + δ / 2) z y * singularPow (3 + δ / 2) z' y := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left bu (sq_nonneg _)
  have i2 : Integrable (fun y => (C1 * singularPow (3 + δ / 2) z y) *
      i3Psi2Pot J (i3Psi2Hz K Q z') y) :=
    (ix.const_mul C1).congr (Filter.Eventually.of_forall fun y => by simp only; ring)
  have b2 : ∫ y, (C1 * singularPow (3 + δ / 2) z y) * i3Psi2Pot J (i3Psi2Hz K Q z') y ≤
      C1 * (Cx * (torusParabolicSize z' ^ (-(1 + δ + δ / 2)) +
        torusParabolicSize z ^ (-(1 + δ + δ / 2)))) := by
    have : ∫ y, (C1 * singularPow (3 + δ / 2) z y) * i3Psi2Pot J (i3Psi2Hz K Q z') y =
        C1 * ∫ y, singularPow (3 + δ / 2) z y * i3Psi2Pot J (i3Psi2Hz K Q z') y := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left bx hC1
  have i3 : Integrable (fun y => i3Psi2Pot J (i3Psi2Hz K Q z) y *
      (C1 * singularPow (3 + δ / 2) z' y)) :=
    (ix'.const_mul C1).congr (Filter.Eventually.of_forall fun y => by simp only; ring)
  have b3 : ∫ y, i3Psi2Pot J (i3Psi2Hz K Q z) y * (C1 * singularPow (3 + δ / 2) z' y) ≤
      C1 * (Cx * (torusParabolicSize z ^ (-(1 + δ + δ / 2)) +
        torusParabolicSize z' ^ (-(1 + δ + δ / 2)))) := by
    have : ∫ y, i3Psi2Pot J (i3Psi2Hz K Q z) y * (C1 * singularPow (3 + δ / 2) z' y) =
        C1 * ∫ y, singularPow (3 + δ / 2) z' y * i3Psi2Pot J (i3Psi2Hz K Q z) y := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left bx' hC1
  obtain ⟨hFi, hbd⟩ := integrable_and_abs_integral_le_of_parts
    (F := fun y => (i3Psi2Smear J (i3Psi2Rho K Q z) y - c / 2 * J (z - y)) *
      (i3Psi2Smear J (i3Psi2Rho K Q z') y - c / 2 * J (z' - y)))
    (a := fun y => i3Psi2Abar K J Q (z - y)) (a' := fun y => i3Psi2Abar K J Q (z' - y))
    (b := fun y => i3Psi2Bz K J Q z y) (b' := fun y => i3Psi2Bz K J Q z' y)
    (ua := fun y => C1 * singularPow (3 + δ / 2) z y)
    (ua' := fun y => C1 * singularPow (3 + δ / 2) z' y)
    (ub := fun y => i3Psi2Pot J (i3Psi2Hz K Q z) y)
    (ub' := fun y => i3Psi2Pot J (i3Psi2Hz K Q z') y)
    (I₁ := C1 ^ 2 * (Cu * torusParabolicSize (z - z') ^ (-(1 + δ))))
    (I₂ := C1 * (Cx * (torusParabolicSize z' ^ (-(1 + δ + δ / 2)) +
      torusParabolicSize z ^ (-(1 + δ + δ / 2)))))
    (I₃ := C1 * (Cx * (torusParabolicSize z ^ (-(1 + δ + δ / 2)) +
      torusParabolicSize z' ^ (-(1 + δ + δ / 2)))))
    (I₄ := Cp * (torusParabolicSize z ^ (-(1 + δ)) * torusParabolicSize z' ^ (-δ) +
      torusParabolicSize z' ^ (-(1 + 2 * δ))))
    hsplit hFm
    (by filter_upwards [ae_torusParabolicSize_sub_pos z] with y hy
        exact hA hKs hK hQ hJ hJinc (z - y) hy)
    (by filter_upwards [ae_torusParabolicSize_sub_pos z'] with y hy
        exact hA hKs hK hQ hJ hJinc (z' - y) hy)
    (Filter.Eventually.of_forall fun y => abs_i3Psi2Bz_le_pot z y)
    (Filter.Eventually.of_forall fun y => abs_i3Psi2Bz_le_pot z' y)
    i1 b1 i2 b2 i3 b3 ip bp
  -- numerics
  have hP : 0 ≤ torusParabolicSize z ^ (-(1 + 2 * δ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hP' : 0 ≤ torusParabolicSize z' ^ (-(1 + 2 * δ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have yb : torusParabolicSize z ^ (-(1 + δ + δ / 2)) ≤ torusParabolicSize z ^ (-(1 + 2 * δ)) :=
    rpow_neg_le_of_le_one hz hz1 (by linarith)
  have yb' : torusParabolicSize z' ^ (-(1 + δ + δ / 2)) ≤ torusParabolicSize z' ^ (-(1 + 2 * δ)) :=
    rpow_neg_le_of_le_one hz' hz1' (by linarith)
  have yy := rpow_neg_mul_two_le (p := torusParabolicSize z) (q := torusParabolicSize z')
    (a := 1 + δ) (b := δ) (E := 1 + 2 * δ) hz hz' (by linarith) hδ.le (by linarith) (by ring)
  have hT := target_ge_pure (δ := δ) (z := z) (z' := z')
  have T0 := i3Psi2Target_nonneg δ z z'
  show |(36 : ℝ) * ∫ y, (i3Psi2Smear J (i3Psi2Rho K Q z) y - c / 2 * J (z - y)) *
      (i3Psi2Smear J (i3Psi2Rho K Q z') y - c / 2 * J (z' - y))| ≤ _
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 36)]
  have K1 : 0 ≤ C1 ^ 2 * Cu := by positivity
  have K2 : 0 ≤ 2 * C1 * Cx := by positivity
  have K3 : 0 ≤ 2 * Cp := by positivity
  have hmain : |∫ y, (i3Psi2Smear J (i3Psi2Rho K Q z) y - c / 2 * J (z - y)) *
      (i3Psi2Smear J (i3Psi2Rho K Q z') y - c / 2 * J (z' - y))| ≤
      (C1 ^ 2 * Cu + 2 * C1 * Cx + 2 * Cp) * i3Psi2Target δ z z' := by
    refine hbd.trans ?_
    set X1 := torusParabolicSize (z - z') ^ (-(1 + δ))
    set P := torusParabolicSize z ^ (-(1 + 2 * δ))
    set P' := torusParabolicSize z' ^ (-(1 + 2 * δ))
    set a := torusParabolicSize z' ^ (-(1 + δ + δ / 2))
    set b := torusParabolicSize z ^ (-(1 + δ + δ / 2))
    set Y := torusParabolicSize z ^ (-(1 + δ)) * torusParabolicSize z' ^ (-δ)
    have hXn : 0 ≤ X1 := n1
    linarith [mul_nonneg K1 hXn, mul_nonneg K2 hP, mul_nonneg K2 hP', mul_nonneg K3 hP,
      mul_nonneg K3 hP', mul_nonneg K1 hP, mul_nonneg K1 hP', mul_nonneg K2 hXn,
      mul_nonneg K3 hXn, mul_le_mul_of_nonneg_left yb hC1, mul_le_mul_of_nonneg_left yb' hC1,
      mul_nonneg hC1 hCx, mul_nonneg hCp hP, mul_nonneg hCp hP', mul_nonneg hC1 hCx,
      mul_le_mul_of_nonneg_left yy hCp,
      mul_le_mul_of_nonneg_left (add_le_add yb' yb) (mul_nonneg hC1 hCx),
      mul_le_mul_of_nonneg_left hT (add_nonneg (add_nonneg K1 K2) K3)]
  calc 36 * _ ≤ 36 * ((C1 ^ 2 * Cu + 2 * C1 * Cx + 2 * Cp) * i3Psi2Target δ z z') :=
        mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = _ := by ring

end RegularityStructures

end
