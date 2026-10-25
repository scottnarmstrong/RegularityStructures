/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramMultiN1
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiLevel

/-!
# Bound for the weighted diagram `N₁` with general exponents

`i3Psi2N1Weighted_bound`: every measurable `F` dominated by
`Λ |δK(z, w)| |δK(z', v)| s(w - z')^(-(2+x₁)) s(w - v)^(-(1+x₂)) s(z - v)^(-(2+x₃))` is integrable
on the product and `|∫∫ F| ≤ Λ C S_{1+δ+x₁+x₂+x₃}(z, z')`.  The proof is that of the a-priori
bound for `N₁` with the exponents `(2 + ν, 1 + x₂, 2 + x₃)` in place of `(2 + δ, 1, 2)`.
-/

public section

open MeasureTheory

namespace RegularityStructures

private theorem outer_leaves_gen {ν η : ℝ} (hν : 0 < ν) (hη : 0 < η) (hνη : ν + η < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z z' : SpaceTime}, 0 < torusParabolicSize (z - z') →
      0 < torusParabolicSize (z - 0) → 0 < torusParabolicSize (z' - 0) →
      SingularIntLe (fun w => singularPow 3 z w * singularPow (2 + ν) z' w) (C * i3Psi2S ν z z') ∧
      SingularIntLe (fun w => singularPow 3 0 w * singularPow (2 + ν) z' w) (C * i3Psi2S ν z z') ∧
      SingularIntLe (fun w => singularPow 3 z w * singularPow (2 + ν) z' w * singularPow η z' w)
        (C * i3Psi2S (ν + η) z z') ∧
      SingularIntLe (fun w => singularPow 3 z w * singularPow (2 + ν) z' w * singularPow η 0 w)
        (C * i3Psi2S (ν + η) z z') ∧
      SingularIntLe (fun w => singularPow 3 0 w * singularPow (2 + ν) z' w * singularPow η z' w)
        (C * i3Psi2S (ν + η) z z') ∧
      SingularIntLe (fun w => singularPow 3 0 w * singularPow (2 + ν) z' w * singularPow η 0 w)
        (C * i3Psi2S (ν + η) z z') := by
  obtain ⟨C1, hC1, h1⟩ := i3Psi2_leaf2 (a := 3) (b := 2 + ν) (η := ν) (by norm_num) (by norm_num)
    (by linarith) (by linarith) hν (by ring)
  obtain ⟨C2, hC2, h2⟩ := i3Psi2_leaf2 (a := 3) (b := 2 + ν + η) (η := ν + η) (by norm_num)
    (by norm_num) (by linarith) (by linarith) (by linarith) (by ring)
  obtain ⟨C3, hC3, h3⟩ := i3Psi2_leaf3 (a := 2 + ν) (b := η) (c := 3) (η := ν + η)
    (by linarith) hη (by linarith) (by norm_num) (by norm_num) (by linarith) (by ring)
  obtain ⟨C4, hC4, h4⟩ := i3Psi2_leaf2 (a := 3 + η) (b := 2 + ν) (η := ν + η) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
  refine ⟨C1 + C2 + C3 + C4, by positivity, fun {z z'} hx hu hu' => ?_⟩
  have pzz' := torusParabolicSize_sub_pos_symm hx
  have p0z := torusParabolicSize_sub_pos_symm hu
  have p0z' := torusParabolicSize_sub_pos_symm hu'
  have S0 := i3Psi2S_nonneg ν z z'
  have S1 := i3Psi2S_nonneg (ν + η) z z'
  have m1 : C1 * i3Psi2S ν z z' ≤ (C1 + C2 + C3 + C4) * i3Psi2S ν z z' :=
    mul_le_mul_of_nonneg_right (by linarith) S0
  have m2 : C2 * i3Psi2S (ν + η) z z' ≤ (C1 + C2 + C3 + C4) * i3Psi2S (ν + η) z z' :=
    mul_le_mul_of_nonneg_right (by linarith) S1
  have m3 : C3 * i3Psi2S (ν + η) z z' ≤ (C1 + C2 + C3 + C4) * i3Psi2S (ν + η) z z' :=
    mul_le_mul_of_nonneg_right (by linarith) S1
  have m4 : C4 * i3Psi2S (ν + η) z z' ≤ (C1 + C2 + C3 + C4) * i3Psi2S (ν + η) z z' :=
    mul_le_mul_of_nonneg_right (by linarith) S1
  have e3 := ae_singularPow_mul_self (a := 2 + ν) (b := η) (e := 2 + ν + η) (by ring) z'
  have e4 := ae_singularPow_mul_self (a := 3) (b := η) (e := 3 + η) (by ring) (0 : SpaceTime)
  have hz : (z = z ∨ z = z' ∨ z = 0) := Or.inl rfl
  have hz' : (z' = z ∨ z' = z' ∨ z' = 0) := Or.inr (Or.inl rfl)
  have h0 : ((0 : SpaceTime) = z ∨ (0 : SpaceTime) = z' ∨ (0 : SpaceTime) = 0) :=
    Or.inr (Or.inr rfl)
  have l1 := (h1 (z := z) (z' := z') (p := z) (q := z') hx hu hu' hz hz' hx).mono_right m1
  have l2 := (h1 (z := z) (z' := z') (p := 0) (q := z') hx hu hu' h0 hz' p0z').mono_right m1
  have l3 := ((h2 (z := z) (z' := z') (p := z) (q := z') hx hu hu' hz hz' hx).mono_right m2
    ).congr_ae (f := fun w => singularPow 3 z w * singularPow (2 + ν + η) z' w)
    (g := fun w => singularPow 3 z w * singularPow (2 + ν) z' w * singularPow η z' w)
    (by filter_upwards [e3] with w hw; rw [mul_assoc, hw])
  have l4 := ((h3 (z := z) (z' := z') (p := z') (q := 0) (r := z) hx hu hu' hz' h0 hz pzz'
    p0z).mono_right m3).congr_fun (f := fun w => singularPow (2 + ν) z' w * singularPow η 0 w *
      singularPow 3 z w) (g := fun w => singularPow 3 z w * singularPow (2 + ν) z' w *
        singularPow η 0 w) (fun w => by ring)
  have l5 := ((h2 (z := z) (z' := z') (p := 0) (q := z') hx hu hu' h0 hz' p0z').mono_right m2
    ).congr_ae (f := fun w => singularPow 3 0 w * singularPow (2 + ν + η) z' w)
    (g := fun w => singularPow 3 0 w * singularPow (2 + ν) z' w * singularPow η z' w)
    (by filter_upwards [e3] with w hw; rw [mul_assoc, hw])
  have l6 := ((h4 (z := z) (z' := z') (p := 0) (q := z') hx hu hu' h0 hz' p0z').mono_right m4
    ).congr_ae (f := fun w => singularPow (3 + η) 0 w * singularPow (2 + ν) z' w)
    (g := fun w => singularPow 3 0 w * singularPow (2 + ν) z' w * singularPow η 0 w)
    (by filter_upwards [e4] with w hw; rw [← hw]; ring)
  exact ⟨l1, l2, l3, l4, l5, l6⟩

/-- **Bound for the weighted diagram `N₁`**, uniform in `K`: the weight is a two-level majorant. -/
theorem i3Psi2N1Weighted_twoLevelLe {B δ x₁ x₂ x₃ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hx₁ : 0 ≤ x₁)
    (hx₂ : 0 ≤ x₂) (hx₃ : 0 ≤ x₃) (hsum : δ + x₁ + x₂ + x₃ ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {Λ : ℝ}, 0 ≤ Λ → Measurable K →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      ∀ z z' : SpaceTime, 0 < torusParabolicSize (z - z') → 0 < torusParabolicSize z →
        0 < torusParabolicSize z' → torusParabolicSize z ≤ 1 → torusParabolicSize z' ≤ 1 →
        TwoLevelLe (fun w v => Λ * (|i3Psi2dK K z w| * |i3Psi2dK K z' v| *
          (torusParabolicSize (w - z') ^ (-(2 + x₁)) * torusParabolicSize (w - v) ^ (-(1 + x₂)) *
            torusParabolicSize (z - v) ^ (-(2 + x₃)))))
          (Λ * C * i3Psi2S (1 + δ + x₁ + x₂ + x₃) z z') := by
  have hη : 0 < 1 + x₂ + x₃ := by linarith
  have hν : 0 < x₁ + δ := by linarith
  obtain ⟨Ci, hCi, hi⟩ := singularIntLe_mul_three (a := 2 + x₃) (b := 1 + x₂) (c := 3)
    (η := 1 + x₂ + x₃) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) hη
    (by ring)
  obtain ⟨Co, hCo, ho⟩ := outer_leaves_gen (ν := x₁ + δ) (η := 1 + x₂ + x₃) hν hη (by linarith)
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  have n2 : (0 : ℝ) ≤ 2 ^ (2 + x₁) := Real.rpow_nonneg (by norm_num) _
  have nP : (0 : ℝ) ≤ 2 ^ (1 + x₂ + x₃) := Real.rpow_nonneg (by norm_num) _
  have nQ : (0 : ℝ) ≤ 2 ^ (1 + x₂ + x₃ + (x₁ + δ)) := Real.rpow_nonneg (by norm_num) _
  have hc0 : 0 ≤ B ^ 2 * (2 ^ (2 + x₁) * 3 ^ δ) := mul_nonneg (sq_nonneg B) (mul_nonneg n2 n3)
  refine ⟨B ^ 2 * (2 ^ (2 + x₁) * 3 ^ δ) * Ci * Co *
    (18 * 2 ^ (1 + x₂ + x₃ + (x₁ + δ)) + 4 * 2 ^ (1 + x₂ + x₃)),
    mul_nonneg (mul_nonneg (mul_nonneg hc0 hCi) hCo) (by positivity), ?_⟩
  intro K Λ hΛ hKm hK hKs z z' hzz hz hz' hz1 hz1'
  have pz0 : 0 < torusParabolicSize (z - 0) := by rwa [sub_zero]
  have pz'0 : 0 < torusParabolicSize (z' - 0) := by rwa [sub_zero]
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := ho hzz pz0 pz'0
  set η : ℝ := 1 + x₂ + x₃ with hηdef
  set ν : ℝ := x₁ + δ with hνdef
  set c0 : ℝ := B ^ 2 * (2 ^ (2 + x₁) * 3 ^ δ) with hc0def
  set P : ℝ := 2 ^ η with hPdef
  set x1 : ℝ := torusParabolicSize (z - z') ^ (-η) with hx1
  set u1 : ℝ := torusParabolicSize (z - 0) ^ (-η) with hu1
  have nx1 : 0 ≤ x1 := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have nu1 : 0 ≤ u1 := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have nc : 0 ≤ x1 + u1 := add_nonneg nx1 nu1
  have hΛc : 0 ≤ Λ * c0 := mul_nonneg hΛ hc0
  let V : SpaceTime → ℝ := fun w => Ci * (x1 + u1 + P * (singularPow η z' w + singularPow η 0 w))
  let m : SpaceTime → ℝ := fun w => (Λ * c0) *
    ((singularPow 3 z w + singularPow 3 0 w) * singularPow (2 + ν) z' w)
  have hm : ∀ w, 0 ≤ m w := fun w => mul_nonneg hΛc (mul_nonneg (add_nonneg
    (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _))
  have hg : ∀ᵐ w : SpaceTime ∂volume, SingularIntLe (fun v => (singularPow 3 z' v +
      singularPow 3 0 v) * singularPow (2 + x₃) z v * singularPow (1 + x₂) w v) (V w) := by
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with w a b
    have f1 := rpow_neg_flip_singularPow (p := η) hη.le a
    have f2 := rpow_neg_flip_singularPow (p := η) hη.le b
    have t1 := hi z w z' hzz (torusParabolicSize_sub_pos_symm a)
    have t2 := hi z w 0 pz0 (torusParabolicSize_sub_pos_symm b)
    have := (t1.add t2).congr_fun (g := fun v => (singularPow 3 z' v + singularPow 3 0 v) *
      singularPow (2 + x₃) z v * singularPow (1 + x₂) w v) (fun v => by ring)
    refine this.mono_right ?_
    simp only [V, sub_zero] at f2 ⊢
    have g1 : torusParabolicSize (w - z') ^ (-η) ≤ P * singularPow η z' w := f1
    have g2 : torusParabolicSize w ^ (-η) ≤ P * singularPow η 0 w := f2
    have := mul_le_mul_of_nonneg_left (add_le_add g1 g2) hCi
    simp only [hx1, hu1, sub_zero] at *
    linarith
  have S0 := i3Psi2S_nonneg ν z z'
  have S1 := i3Psi2S_nonneg (ν + η) z z'
  have hSS := i3Psi2S_mul_le (a := η) (b := ν) hη.le hν.le (by linarith) hzz pz0 pz'0
  rw [show η + ν = ν + η by ring] at hSS
  have hnc : x1 + u1 ≤ i3Psi2S η z z' := by
    have : 0 ≤ torusParabolicSize (z' - 0) ^ (-η) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    simp only [i3Psi2S, hx1, hu1]
    linarith
  have hncS : (x1 + u1) * i3Psi2S ν z z' ≤ 9 * 2 ^ (η + ν) * i3Psi2S (ν + η) z z' :=
    (mul_le_mul_of_nonneg_right hnc S0).trans (by rw [show η + ν = ν + η by ring]; exact hSS)
  have sA := (o1.add o2).const_mul nc
  have sB := (((o3.add o4).add o5).add o6).const_mul (c := P) (by positivity)
  have sT := (sA.add sB).const_mul (mul_nonneg hΛc hCi)
  have hH : SingularIntLe (fun w => m w * V w)
      (Λ * (c0 * Ci * Co * (18 * 2 ^ (η + ν) + 4 * 2 ^ η)) * i3Psi2S (1 + δ + x₁ + x₂ + x₃) z z') := by
    have e : 1 + δ + x₁ + x₂ + x₃ = ν + η := by rw [hνdef, hηdef]; ring
    rw [e]
    refine (sT.congr_fun (g := fun w => m w * V w) (fun w => by simp only [m, V]; ring)).mono_right
      ?_
    have hP : 0 ≤ Λ * (c0 * Ci * Co) := mul_nonneg hΛ (mul_nonneg (mul_nonneg hc0 hCi) hCo)
    calc Λ * c0 * Ci * ((x1 + u1) * (Co * i3Psi2S ν z z' + Co * i3Psi2S ν z z') +
          P * (Co * i3Psi2S (ν + η) z z' + Co * i3Psi2S (ν + η) z z' +
            Co * i3Psi2S (ν + η) z z' + Co * i3Psi2S (ν + η) z z'))
        = (Λ * (c0 * Ci * Co)) * (2 * ((x1 + u1) * i3Psi2S ν z z') +
            4 * P * i3Psi2S (ν + η) z z') := by ring
      _ ≤ (Λ * (c0 * Ci * Co)) * (2 * (9 * 2 ^ (η + ν) * i3Psi2S (ν + η) z z') +
            4 * P * i3Psi2S (ν + η) z z') := by gcongr
      _ = _ := by rw [hPdef]; ring
  have hG := twoLevelLe_of_inner (m := m) (g := fun w v => (singularPow 3 z' v +
    singularPow 3 0 v) * singularPow (2 + x₃) z v * singularPow (1 + x₂) w v) (V := V) hm hg hH
  refine hG.of_le (fun w => ?_) (fun w v => ?_) ?_
  · have hdK : Measurable (fun v => i3Psi2dK K z' v) := by
      unfold i3Psi2dK; fun_prop
    have hW1 : Measurable (fun v => torusParabolicSize (w - v) ^ (-(1 + x₂))) :=
      (Phi43.measurable_torusParabolicSize.comp (measurable_const.sub measurable_id)).pow_const _
    have hW3 : Measurable (fun v => torusParabolicSize (z - v) ^ (-(2 + x₃))) :=
      (Phi43.measurable_torusParabolicSize.comp (measurable_const.sub measurable_id)).pow_const _
    exact measurable_const.mul ((measurable_const.mul (continuous_abs.measurable.comp hdK)).mul
      ((measurable_const.mul hW1).mul hW3))
  · exact mul_nonneg hΛ (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)))
  · filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos z'] with w a b c
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with
      v a' b'
    have := abs_dK_dK_N1_le (x₂ := x₂) (x₃ := x₃) hB hδ.le hx₁ hK hKs hz1 hz1' a b c a' b'
    have h2 := mul_le_mul_of_nonneg_left this hΛ
    refine h2.trans (le_of_eq ?_)
    simp only [m, i3Psi2N1Majorant, hc0def]
    ring

end RegularityStructures

end
