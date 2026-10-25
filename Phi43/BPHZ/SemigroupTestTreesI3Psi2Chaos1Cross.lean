/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI3Psi2N2
public import Phi43.BPHZ.TreeI3Psi2ChaosOneBound

/-!
# The cross and potential terms of the chaos-`1` part of `I(Ψ³)Ψ²`, for arbitrary `z, z'`

Global versions of `i3Psi2Hz_le`, `chaosOne_cross_le` and `chaosOne_pp_le`: the hypotheses
`s(z), s(z') ≤ 1` (used only to bound `s(w - z) ≤ 3` on the slab `|w.1| ≤ 1` carrying the support of
`K(-·)`) are replaced by a bound `s(z - w) ≤ D` for `|w.1| ≤ 1`, and `3^δ` by `D^δ`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- Majorant of `h_z`. -/
theorem i3Psi2Hz_le_global {K Q : SpaceTime → ℝ} {B δ D : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hD0 : 0 ≤ D)
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hQe : ∀ x, Q (-x) = Q x) {z : SpaceTime} (hD : ∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (z - w) ≤ D)
    {w : SpaceTime} (h0 : 0 < torusParabolicSize (0 - w)) (hzw : 0 < torusParabolicSize (z - w)) :
    i3Psi2Hz K Q z w ≤ (B ^ 3 * D ^ δ) * (singularPow 3 0 w * singularPow (2 + δ) z w) := by
  have n3 : (0 : ℝ) ≤ D ^ δ := Real.rpow_nonneg hD0 _
  have hrhs : 0 ≤ (B ^ 3 * D ^ δ) * (singularPow 3 0 w * singularPow (2 + δ) z w) :=
    mul_nonneg (mul_nonneg (pow_nonneg hB 3) n3)
      (mul_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
  by_cases hw : |w.1| ≤ 1
  · have a1 := hK (-w) (by simpa using h0)
    have a2 : |Q (w - z)| ^ 2 ≤ B ^ 2 * D ^ δ * singularPow (2 + δ) z w := by
      rw [Q_sub_comm hQe w z]
      have := abs_Q_sq_le_of_le hδ hQ hzw (hD w hw)
      simpa [singularPow] using this
    have e1 : singularPow 3 0 w = torusParabolicSize (-w) ^ (-(3 : ℝ)) := by simp [singularPow]
    unfold i3Psi2Hz
    rw [← sq_abs (Q (w - z))]
    calc |K (-w)| * |Q (w - z)| ^ 2 ≤ (B * singularPow 3 0 w) *
          (B ^ 2 * D ^ δ * singularPow (2 + δ) z w) := by
          rw [e1]
          exact mul_le_mul a1 a2 (sq_nonneg _) (mul_nonneg hB (Real.rpow_nonneg
            (torusParabolicSize_nonneg _) _))
      _ = _ := by ring
  · have : K (-w) = 0 := by
      apply hKs
      have : (-w).1 = -w.1 := rfl
      rw [this, abs_neg]; exact not_le.1 hw
    unfold i3Psi2Hz
    rw [this]
    simpa using hrhs

/-- The cross term `∫ s(z - y)^(-(3+δ')) Pot h_{z'}(y) dy`. -/
theorem chaosOne_cross_le_global {B δ δ' : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K J Q : SpaceTime → ℝ} {D : ℝ}, 0 ≤ D → Measurable K →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      Measurable J →
      (∀ x, 0 < torusParabolicSize x → |J x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      Measurable Q →
      (∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, Q (-x) = Q x) →
      ∀ z z' : SpaceTime, (∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (z' - w) ≤ D) →
        0 < torusParabolicSize z → 0 < torusParabolicSize z' →
          Integrable (fun y => singularPow (3 + δ') z y * i3Psi2Pot J (i3Psi2Hz K Q z') y) ∧
            ∫ y, singularPow (3 + δ') z y * i3Psi2Pot J (i3Psi2Hz K Q z') y ≤
              C * D ^ δ * (torusParabolicSize z' ^ (-(1 + δ + δ')) +
                torusParabolicSize z ^ (-(1 + δ + δ'))) := by
  obtain ⟨Cp, hCp, hp⟩ := power_mul_abs_J_le (a := 3 + δ') hB (by linarith) (by linarith)
    (by linarith)
  obtain ⟨Cl, hCl, hl⟩ := chaosOne_leaf_cross hδ hδ' hδ1 hδ'1
  refine ⟨B ^ 3 * (Cp * B) * Cl, by positivity, ?_⟩
  intro K J Q D hD0 hKm hKs hK hJm hJ hQm hQ hQe z z' hz1' hz hz'
  have n3 : (0 : ℝ) ≤ D ^ δ := Real.rpow_nonneg hD0 _
  have pz : 0 < torusParabolicSize (z - 0) := by rwa [sub_zero]
  have pz' : 0 < torusParabolicSize (z' - 0) := by rwa [sub_zero]
  have hX : SingularIntLe (fun w => ((B ^ 3 * D ^ δ) * (singularPow 3 0 w *
      singularPow (2 + δ) z' w)) * ((Cp * B) * singularPow (1 + δ') z w))
      (B ^ 3 * (Cp * B) * Cl * D ^ δ * (torusParabolicSize z' ^ (-(1 + δ + δ')) +
        torusParabolicSize z ^ (-(1 + δ + δ')))) := by
    have := ((hl pz' pz).const_mul (c := (B ^ 3 * D ^ δ) * (Cp * B))
      (mul_nonneg (mul_nonneg (pow_nonneg hB 3) n3) (mul_nonneg hCp hB)))
    simp only [sub_zero] at this
    refine (this.congr_fun (g := fun w => ((B ^ 3 * D ^ δ) * (singularPow 3 0 w *
      singularPow (2 + δ) z' w)) * ((Cp * B) * singularPow (1 + δ') z w)) (fun w => by ring)
      ).mono_right (le_of_eq (by ring))
  refine integral_mul_pot_le (H := fun w => (B ^ 3 * D ^ δ) * (singularPow 3 0 w *
    singularPow (2 + δ) z' w)) (U := fun w => (Cp * B) * singularPow (1 + δ') z w) hJm
    (fun y => singularPow_nonneg _ _ _) (measurable_singularPow _ _)
    (i3Psi2Hz_nonneg K Q z') (measurable_i3Psi2Hz hKm hQm z') ?_ ?_ hX
  · filter_upwards [ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos z'] with w a b
    exact i3Psi2Hz_le_global hB hδ.le hD0 hKs hK hQ hQe hz1' a b
  · filter_upwards [ae_torusParabolicSize_sub_pos z] with w hw
    obtain ⟨i, b⟩ := hp hJm hJ z w hw
    have e : (5 - (3 + δ') - 3 : ℝ) = -(1 + δ') := by ring
    rw [e] at b
    refine ⟨i, ?_⟩
    simpa [singularPow, mul_assoc] using b

/-- The term `∫ Pot h_z Pot h_{z'} dy`. -/
theorem chaosOne_pp_le_global {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K J Q : SpaceTime → ℝ} {D : ℝ}, 0 ≤ D → Measurable K →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      Measurable J →
      (∀ x, 0 < torusParabolicSize x → |J x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      Measurable Q →
      (∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, Q (-x) = Q x) →
      ∀ z z' : SpaceTime, (∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (z - w) ≤ D) →
        (∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (z' - w) ≤ D) →
        0 < torusParabolicSize z → 0 < torusParabolicSize z' →
          Integrable (fun y => i3Psi2Pot J (i3Psi2Hz K Q z) y * i3Psi2Pot J (i3Psi2Hz K Q z') y) ∧
            ∫ y, i3Psi2Pot J (i3Psi2Hz K Q z) y * i3Psi2Pot J (i3Psi2Hz K Q z') y ≤
              C * (D ^ δ) ^ 2 * (torusParabolicSize z ^ (-(1 + δ)) * torusParabolicSize z' ^ (-δ) +
                torusParabolicSize z' ^ (-(1 + 2 * δ))) := by
  obtain ⟨C0, hC0, h0⟩ := abs_J_mul_J_le hB
  obtain ⟨Ci, hCi, hi⟩ := chaosOne_leaf_inner hδ hδ1
  obtain ⟨Co, hCo, ho⟩ := chaosOne_leaf_outer hδ hδ1
  have n2 : (0 : ℝ) ≤ 2 ^ (1 + δ) := Real.rpow_nonneg (by norm_num) _
  refine ⟨B ^ 3 * (B ^ 3 * (2 * (C0 * B ^ 2)) * Ci) * Co * (1 + 2 ^ (1 + δ)), by positivity, ?_⟩
  intro K J Q D hD0 hKm hKs hK hJm hJ hQm hQ hQe z z' hz1 hz1' hz hz'
  have n3 : (0 : ℝ) ≤ D ^ δ := Real.rpow_nonneg hD0 _
  set A : ℝ := (B ^ 3 * D ^ δ) * (2 * (C0 * B ^ 2)) * Ci with hA
  have hA0 : 0 ≤ A := by positivity
  have pz : 0 < torusParabolicSize (z - 0) := by rwa [sub_zero]
  have pz' : 0 < torusParabolicSize (z' - 0) := by rwa [sub_zero]
  have hΛ : ∀ w w' : SpaceTime, 0 < torusParabolicSize (w - w') →
      Integrable (fun y => |J (w - y)| * |J (w' - y)|) ∧
        ∫ y, |J (w - y)| * |J (w' - y)| ≤ 2 * (C0 * B ^ 2) * singularPow 1 w' w := by
    intro w w' hww
    obtain ⟨i, b⟩ := h0 hJm hJ w w' hww
    refine ⟨i, b.trans ?_⟩
    have f := rpow_neg_flip_singularPow (p := 1) (by norm_num) (c := w') (w := w)
      (torusParabolicSize_sub_pos_symm hww)
    have e : (5 - 3 - 3 : ℝ) = -1 := by norm_num
    rw [e]
    rw [Real.rpow_one] at f
    have hc : 0 ≤ C0 * B ^ 2 := mul_nonneg hC0 (sq_nonneg B)
    calc C0 * B ^ 2 * torusParabolicSize (w - w') ^ (-1 : ℝ) ≤
        C0 * B ^ 2 * (2 * singularPow 1 w' w) := mul_le_mul_of_nonneg_left f hc
      _ = _ := by ring
  let R : SpaceTime → ℝ := fun w' => (B ^ 3 * D ^ δ) * (2 * (C0 * B ^ 2)) * Ci *
    (torusParabolicSize z ^ (-(1 + δ)) + 2 ^ (1 + δ) * singularPow (1 + δ) 0 w')
  have hR : ∀ᵐ w' : SpaceTime ∂volume, SingularIntLe (fun w => ((B ^ 3 * D ^ δ) *
      (singularPow 3 0 w * singularPow (2 + δ) z w)) * (2 * (C0 * B ^ 2) * singularPow 1 w' w))
      (R w') := by
    filter_upwards [ae_torusParabolicSize_pos_spaceTime, ae_torusParabolicSize_sub_pos 0] with w' a b
    have pw' : 0 < torusParabolicSize (w' - 0) := by rwa [sub_zero]
    have := ((hi pz pw').const_mul (c := (B ^ 3 * D ^ δ) * (2 * (C0 * B ^ 2)))
      (by positivity))
    refine (this.congr_fun (g := fun w => ((B ^ 3 * D ^ δ) *
      (singularPow 3 0 w * singularPow (2 + δ) z w)) * (2 * (C0 * B ^ 2) * singularPow 1 w' w))
      (fun w => by ring)).mono_right ?_
    have f := rpow_neg_flip_singularPow (p := 1 + δ) (by linarith) (c := 0) (w := w') b
    simp only [sub_zero] at f ⊢
    simp only [R]
    have hz0 : 0 ≤ torusParabolicSize z ^ (-(1 + δ)) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    nlinarith [mul_le_mul_of_nonneg_left f (by positivity : 0 ≤ (B ^ 3 * D ^ δ) *
      (2 * (C0 * B ^ 2)) * Ci)]
  have hX : SingularIntLe (fun w' => ((B ^ 3 * D ^ δ) * (singularPow 3 0 w' *
      singularPow (2 + δ) z' w')) * R w')
      ((B ^ 3 * D ^ δ) * A * Co * (1 + 2 ^ (1 + δ)) *
        (torusParabolicSize z ^ (-(1 + δ)) * torusParabolicSize z' ^ (-δ) +
          torusParabolicSize z' ^ (-(1 + 2 * δ)))) := by
    obtain ⟨o1, o2⟩ := ho pz'
    have hz0 : 0 ≤ torusParabolicSize z ^ (-(1 + δ)) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have t1 := (o1.const_mul (c := torusParabolicSize z ^ (-(1 + δ))) hz0)
    have t2 := (o2.const_mul (c := 2 ^ (1 + δ)) n2)
    have := (t1.add t2).const_mul (c := (B ^ 3 * D ^ δ) * A) (by positivity)
    simp only [sub_zero] at this
    refine (this.congr_fun (g := fun w' => ((B ^ 3 * D ^ δ) * (singularPow 3 0 w' *
      singularPow (2 + δ) z' w')) * R w') (fun w' => by simp only [R, hA]; ring)).mono_right ?_
    have y0 : 0 ≤ torusParabolicSize z' ^ (-δ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have y1 : 0 ≤ torusParabolicSize z' ^ (-(1 + 2 * δ)) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have x0 : 0 ≤ torusParabolicSize z ^ (-(1 + δ)) * torusParabolicSize z' ^ (-δ) :=
      mul_nonneg hz0 y0
    have hP : 0 ≤ (B ^ 3 * D ^ δ) * A * Co := by positivity
    nlinarith [mul_nonneg hP x0, mul_nonneg hP y1, mul_nonneg (mul_nonneg hP n2) x0]
  obtain ⟨ipp, bpp⟩ := integral_pot_mul_pot_le (H₁ := fun w => (B ^ 3 * D ^ δ) * (singularPow 3 0 w *
    singularPow (2 + δ) z w)) (H₂ := fun w => (B ^ 3 * D ^ δ) * (singularPow 3 0 w *
    singularPow (2 + δ) z' w)) (Λ := fun w w' => 2 * (C0 * B ^ 2) * singularPow 1 w' w) hJm
    (i3Psi2Hz_nonneg K Q z) (measurable_i3Psi2Hz hKm hQm z) (i3Psi2Hz_nonneg K Q z')
    (measurable_i3Psi2Hz hKm hQm z')
    (by filter_upwards [ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos z]
          with w a b
        exact i3Psi2Hz_le_global hB hδ.le hD0 hKs hK hQ hQe hz1 a b)
    (by filter_upwards [ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos z']
          with w a b
        exact i3Psi2Hz_le_global hB hδ.le hD0 hKs hK hQ hQe hz1' a b) hΛ hR hX
  refine ⟨ipp, bpp.trans (le_of_eq ?_)⟩
  simp only [hA]
  ring

end RegularityStructures

end
