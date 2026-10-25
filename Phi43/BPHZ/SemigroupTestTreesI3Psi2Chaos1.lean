/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI3Psi2Chaos1Cross

/-!
# The chaos-`1` part of `I(Ψ³)Ψ²` with the counterterm cross terms, for arbitrary `z, z'`

`i3Psi2Chaos1Total_raw_global`: the proof of `i3Psi2Chaos1Total_bound_uniform` with the global
cross and potential bounds.  The conclusion keeps the singular terms of the proof,
`(1 + D^δ)² (s(z - z')^(-(1+δ)) + s(z')^(-(1+δ+δ/2)) + s(z)^(-(1+δ+δ/2)) +
s(z)^(-(1+δ)) s(z')^(-δ) + s(z')^(-(1+2δ)))`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- Pure algebra of the final comparison in `i3Psi2Chaos1Total_raw_global`. -/
theorem chaos1_combine {u C1 Cu Cx Cp X1 a b Y Z I : ℝ} (hu : 0 ≤ u) (hC1 : 0 ≤ C1) (hCu : 0 ≤ Cu)
    (hCx : 0 ≤ Cx) (hCp : 0 ≤ Cp) (hX1 : 0 ≤ X1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hY : 0 ≤ Y)
    (hZ : 0 ≤ Z)
    (h : I ≤ C1 ^ 2 * (Cu * X1) + C1 * (Cx * u * (a + b)) + C1 * (Cx * u * (b + a)) +
      Cp * u ^ 2 * (Y + Z)) :
    I ≤ (C1 ^ 2 * Cu + 2 * C1 * Cx + Cp) * (1 + u) ^ 2 * (X1 + a + b + Y + Z) := by
  have hP1 : 1 ≤ (1 + u) ^ 2 := by nlinarith
  have hP2 : u ≤ (1 + u) ^ 2 := by nlinarith
  have hP3 : u ^ 2 ≤ (1 + u) ^ 2 := by linarith
  set P := (1 + u) ^ 2
  have e1 : C1 ^ 2 * (Cu * X1) ≤ C1 ^ 2 * Cu * P * X1 := by
    have : 0 ≤ C1 ^ 2 * Cu * X1 := by positivity
    nlinarith
  have e2 : C1 * (Cx * u * (a + b)) ≤ C1 * Cx * P * (a + b) := by
    have : 0 ≤ C1 * Cx * (a + b) := by positivity
    nlinarith
  have e3 : C1 * (Cx * u * (b + a)) ≤ C1 * Cx * P * (a + b) := by
    have : 0 ≤ C1 * Cx * (a + b) := by positivity
    linarith
  have e4 : Cp * u ^ 2 * (Y + Z) ≤ Cp * P * (Y + Z) := by
    have : 0 ≤ Cp * (Y + Z) := by positivity
    nlinarith
  have f1 : 0 ≤ C1 ^ 2 * Cu * P := by positivity
  have f2 : 0 ≤ C1 * Cx * P := by positivity
  have f3 : 0 ≤ Cp * P := by positivity
  linarith [mul_nonneg f1 (add_nonneg (add_nonneg (add_nonneg ha hb) hY) hZ),
    mul_nonneg f2 (add_nonneg (add_nonneg hX1 hY) hZ), mul_nonneg f3 (add_nonneg
    (add_nonneg (add_nonneg hX1 ha) hb) hX1), mul_nonneg f1 ha, mul_nonneg f1 hb,
    mul_nonneg f2 hX1, mul_nonneg f3 hX1, mul_nonneg f2 ha, mul_nonneg f2 hb,
    mul_nonneg f1 hY, mul_nonneg f1 hZ, mul_nonneg f3 ha, mul_nonneg f3 hb]

/-- **The chaos-`1` part with the counterterm cross terms**, uniform in `K, J, Q`. -/
theorem i3Psi2Chaos1Total_raw_global {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K J Q : SpaceTime → ℝ} {M c D : ℝ}, 0 ≤ D → Measurable K →
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
      ∀ z z' : SpaceTime, (∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (z - w) ≤ D) →
        (∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (z' - w) ≤ D) →
        0 < torusParabolicSize z → 0 < torusParabolicSize z' →
        0 < torusParabolicSize (z - z') →
          |i3Psi2Chaos1Total K Q c z z'| ≤ C * (1 + D ^ δ) ^ 2 *
            (torusParabolicSize (z - z') ^ (-(1 + δ)) +
              torusParabolicSize z' ^ (-(1 + δ + δ / 2)) +
              torusParabolicSize z ^ (-(1 + δ + δ / 2)) +
              torusParabolicSize z ^ (-(1 + δ)) * torusParabolicSize z' ^ (-δ) +
              torusParabolicSize z' ^ (-(1 + 2 * δ))) := by
  have hδ2 : 0 < δ / 2 := by linarith
  obtain ⟨C1, hC1, hA⟩ := abs_i3Psi2Abar_le hB hδ2 (by linarith)
  obtain ⟨Cu, hCu, hu⟩ := integrable_and_integral_singularPow_mul_le (a := 3 + δ / 2)
    (b := 3 + δ / 2) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨Cx, hCx, hx⟩ := chaosOne_cross_le_global hB hδ hδ1 hδ2 (by linarith)
  obtain ⟨Cp, hCp, hp⟩ := chaosOne_pp_le_global hB hδ hδ1
  refine ⟨36 * (C1 ^ 2 * Cu + 2 * C1 * Cx + Cp), by positivity, ?_⟩
  intro K J Q M c D hD0 hKm hKs hK hJm hJ hJinc hJb hJi hQm hQ hQJ hc z z' hDz hDz' hz hz' hzz
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
  obtain ⟨ix, bx⟩ := hx hD0 hKm hKs hK hJm hJ hQm hQ hQe z z' hDz' hz hz'
  obtain ⟨ix', bx'⟩ := hx hD0 hKm hKs hK hJm hJ hQm hQ hQe z' z hDz hz' hz
  obtain ⟨ip, bp⟩ := hp hD0 hKm hKs hK hJm hJ hQm hQ hQe z z' hDz hDz' hz hz'
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
      C1 * (Cx * D ^ δ * (torusParabolicSize z' ^ (-(1 + δ + δ / 2)) +
        torusParabolicSize z ^ (-(1 + δ + δ / 2)))) := by
    have : ∫ y, (C1 * singularPow (3 + δ / 2) z y) * i3Psi2Pot J (i3Psi2Hz K Q z') y =
        C1 * ∫ y, singularPow (3 + δ / 2) z y * i3Psi2Pot J (i3Psi2Hz K Q z') y := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    rw [this]
    have := mul_le_mul_of_nonneg_left bx hC1
    refine this.trans (le_of_eq ?_)
    ring
  have i3 : Integrable (fun y => i3Psi2Pot J (i3Psi2Hz K Q z) y *
      (C1 * singularPow (3 + δ / 2) z' y)) :=
    (ix'.const_mul C1).congr (Filter.Eventually.of_forall fun y => by simp only; ring)
  have b3 : ∫ y, i3Psi2Pot J (i3Psi2Hz K Q z) y * (C1 * singularPow (3 + δ / 2) z' y) ≤
      C1 * (Cx * D ^ δ * (torusParabolicSize z ^ (-(1 + δ + δ / 2)) +
        torusParabolicSize z' ^ (-(1 + δ + δ / 2)))) := by
    have : ∫ y, i3Psi2Pot J (i3Psi2Hz K Q z) y * (C1 * singularPow (3 + δ / 2) z' y) =
        C1 * ∫ y, singularPow (3 + δ / 2) z' y * i3Psi2Pot J (i3Psi2Hz K Q z) y := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    rw [this]
    have := mul_le_mul_of_nonneg_left bx' hC1
    refine this.trans (le_of_eq ?_)
    ring
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
    (I₂ := C1 * (Cx * D ^ δ * (torusParabolicSize z' ^ (-(1 + δ + δ / 2)) +
      torusParabolicSize z ^ (-(1 + δ + δ / 2)))))
    (I₃ := C1 * (Cx * D ^ δ * (torusParabolicSize z ^ (-(1 + δ + δ / 2)) +
      torusParabolicSize z' ^ (-(1 + δ + δ / 2)))))
    (I₄ := Cp * (D ^ δ) ^ 2 * (torusParabolicSize z ^ (-(1 + δ)) * torusParabolicSize z' ^ (-δ) +
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
  have hD1 : 0 ≤ D ^ δ := Real.rpow_nonneg hD0 _
  show |(36 : ℝ) * ∫ y, (i3Psi2Smear J (i3Psi2Rho K Q z) y - c / 2 * J (z - y)) *
      (i3Psi2Smear J (i3Psi2Rho K Q z') y - c / 2 * J (z' - y))| ≤ _
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 36)]
  have n1 := Real.rpow_nonneg (torusParabolicSize_nonneg (z - z')) (-(1 + δ))
  have n2 := Real.rpow_nonneg (torusParabolicSize_nonneg z') (-(1 + δ + δ / 2))
  have n3 := Real.rpow_nonneg (torusParabolicSize_nonneg z) (-(1 + δ + δ / 2))
  have n4 : 0 ≤ torusParabolicSize z ^ (-(1 + δ)) * torusParabolicSize z' ^ (-δ) :=
    mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg z) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg z') _)
  have n5 := Real.rpow_nonneg (torusParabolicSize_nonneg z') (-(1 + 2 * δ))
  have hsum := chaos1_combine hD1 hC1 hCu hCx hCp n1 n2 n3 n4 n5 hbd
  calc 36 * _ ≤ 36 * ((C1 ^ 2 * Cu + 2 * C1 * Cx + Cp) * (1 + D ^ δ) ^ 2 *
        (torusParabolicSize (z - z') ^ (-(1 + δ)) + torusParabolicSize z' ^ (-(1 + δ + δ / 2)) +
          torusParabolicSize z ^ (-(1 + δ + δ / 2)) +
          torusParabolicSize z ^ (-(1 + δ)) * torusParabolicSize z' ^ (-δ) +
          torusParabolicSize z' ^ (-(1 + 2 * δ)))) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

end RegularityStructures

end
