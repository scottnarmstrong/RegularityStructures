/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramN2

/-!
# Bound for the diagram `N₂`

`i3Psi2N2_bound_uniform`: the diagram `∫∫ i3Psi2N2 K Q z z'` is absolutely integrable and bounded
by `C S_{1+δ}(z, z')`, with `C` depending only on `B, δ`.
-/

public section

open MeasureTheory

namespace RegularityStructures

private theorem outer_leaves_N2 {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z z' : SpaceTime}, 0 < torusParabolicSize (z - z') →
      0 < torusParabolicSize (z - 0) → 0 < torusParabolicSize (z' - 0) →
      SingularIntLe (fun w => singularPow 3 z w * singularPow (1 + δ) z w * singularPow 1 z' w)
        (C * i3Psi2S δ z z') ∧
      SingularIntLe (fun w => singularPow 3 0 w * singularPow (1 + δ) z w * singularPow 1 z' w)
        (C * i3Psi2S δ z z') ∧
      SingularIntLe (fun w => singularPow 3 z w * singularPow (1 + δ) z w * singularPow 1 z' w *
        singularPow 1 z' w) (C * i3Psi2S (1 + δ) z z') ∧
      SingularIntLe (fun w => singularPow 3 0 w * singularPow (1 + δ) z w * singularPow 1 z' w *
        singularPow 1 z' w) (C * i3Psi2S (1 + δ) z z') ∧
      SingularIntLe (fun w => singularPow 3 z w * singularPow (1 + δ) z w * singularPow 1 z' w *
        singularPow 1 0 w) (C * i3Psi2S (1 + δ) z z') ∧
      SingularIntLe (fun w => singularPow 3 0 w * singularPow (1 + δ) z w * singularPow 1 z' w *
        singularPow 1 0 w) (C * i3Psi2S (1 + δ) z z') := by
  obtain ⟨C1, hC1, h1⟩ := i3Psi2_leaf2 (a := 4 + δ) (b := 1) (η := δ) (by linarith)
    (by linarith) (by norm_num) (by norm_num) hδ (by ring)
  obtain ⟨C2, hC2, h2⟩ := i3Psi2_leaf3 (a := 1 + δ) (b := 1) (c := 3) (η := δ) (by linarith)
    (by norm_num) (by linarith) (by norm_num) (by norm_num) hδ (by ring)
  obtain ⟨C3, hC3, h3⟩ := i3Psi2_leaf2 (a := 4 + δ) (b := 2) (η := 1 + δ) (by linarith)
    (by linarith) (by norm_num) (by norm_num) (by linarith) (by ring)
  obtain ⟨C4, hC4, h4⟩ := i3Psi2_leaf3 (a := 1 + δ) (b := 2) (c := 3) (η := 1 + δ) (by linarith)
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by linarith) (by ring)
  obtain ⟨C5, hC5, h5⟩ := i3Psi2_leaf3 (a := 1) (b := 1) (c := 4 + δ) (η := 1 + δ)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) (by ring)
  obtain ⟨C6, hC6, h6⟩ := i3Psi2_leaf3 (a := 1 + δ) (b := 1) (c := 4) (η := 1 + δ)
    (by linarith) (by norm_num) (by linarith) (by norm_num) (by norm_num) (by linarith) (by ring)
  refine ⟨C1 + C2 + C3 + C4 + C5 + C6, by positivity, fun {z z'} hx hu hu' => ?_⟩
  have pzz' := torusParabolicSize_sub_pos_symm hx
  have p0z := torusParabolicSize_sub_pos_symm hu
  have p0z' := torusParabolicSize_sub_pos_symm hu'
  have S0 := i3Psi2S_nonneg δ z z'
  have S1 := i3Psi2S_nonneg (1 + δ) z z'
  have hsum : ∀ c, c ≤ C1 + C2 + C3 + C4 + C5 + C6 → ∀ S : ℝ, 0 ≤ S →
      c * S ≤ (C1 + C2 + C3 + C4 + C5 + C6) * S :=
    fun c hc S hS => mul_le_mul_of_nonneg_right hc hS
  have m1 := hsum C1 (by linarith) _ S0
  have m2 := hsum C2 (by linarith) _ S0
  have m3 := hsum C3 (by linarith) _ S1
  have m4 := hsum C4 (by linarith) _ S1
  have m5 := hsum C5 (by linarith) _ S1
  have m6 := hsum C6 (by linarith) _ S1
  have e3 := ae_singularPow_mul_self (a := 3) (b := 1 + δ) (e := 4 + δ) (by ring) z
  have e4 := ae_singularPow_mul_self (a := 1) (b := 1) (e := 2) (by norm_num) z'
  have e6 := ae_singularPow_mul_self (a := 3) (b := 1) (e := 4) (by norm_num) (0 : SpaceTime)
  have hz : (z = z ∨ z = z' ∨ z = 0) := Or.inl rfl
  have hz' : (z' = z ∨ z' = z' ∨ z' = 0) := Or.inr (Or.inl rfl)
  have h0 : ((0 : SpaceTime) = z ∨ (0 : SpaceTime) = z' ∨ (0 : SpaceTime) = 0) :=
    Or.inr (Or.inr rfl)
  -- a)
  have l1 := ((h1 (z := z) (z' := z') (p := z) (q := z') hx hu hu' hz hz' hx).mono_right m1
    ).congr_ae (f := fun w => singularPow (4 + δ) z w * singularPow 1 z' w)
    (g := fun w => singularPow 3 z w * singularPow (1 + δ) z w * singularPow 1 z' w)
    (by filter_upwards [e3] with w hw; rw [← hw])
  have l2 := ((h2 (z := z) (z' := z') (p := z) (q := z') (r := 0) hx hu hu' hz hz' h0 hu hu'
    ).mono_right m2).congr_fun (f := fun w => singularPow (1 + δ) z w * singularPow 1 z' w *
      singularPow 3 0 w) (g := fun w => singularPow 3 0 w * singularPow (1 + δ) z w *
        singularPow 1 z' w) (fun w => by ring)
  have l3 := ((h3 (z := z) (z' := z') (p := z) (q := z') hx hu hu' hz hz' hx).mono_right m3
    ).congr_ae (f := fun w => singularPow (4 + δ) z w * singularPow 2 z' w)
    (g := fun w => singularPow 3 z w * singularPow (1 + δ) z w * singularPow 1 z' w *
      singularPow 1 z' w)
    (by filter_upwards [e3, e4] with w hw hw'; rw [← hw, ← hw']; ring)
  have l4 := ((h4 (z := z) (z' := z') (p := z) (q := z') (r := 0) hx hu hu' hz hz' h0 hu hu'
    ).mono_right m4).congr_ae (f := fun w => singularPow (1 + δ) z w * singularPow 2 z' w *
      singularPow 3 0 w) (g := fun w => singularPow 3 0 w * singularPow (1 + δ) z w *
        singularPow 1 z' w * singularPow 1 z' w)
    (by filter_upwards [e4] with w hw; rw [← hw]; ring)
  have l5 := ((h5 (z := z) (z' := z') (p := z') (q := 0) (r := z) hx hu hu' hz' h0 hz pzz' p0z
    ).mono_right m5).congr_ae (f := fun w => singularPow 1 z' w * singularPow 1 0 w *
      singularPow (4 + δ) z w) (g := fun w => singularPow 3 z w * singularPow (1 + δ) z w *
        singularPow 1 z' w * singularPow 1 0 w)
    (by filter_upwards [e3] with w hw; rw [← hw]; ring)
  have l6 := ((h6 (z := z) (z' := z') (p := z) (q := z') (r := 0) hx hu hu' hz hz' h0 hu hu'
    ).mono_right m6).congr_ae (f := fun w => singularPow (1 + δ) z w * singularPow 1 z' w *
      singularPow 4 0 w) (g := fun w => singularPow 3 0 w * singularPow (1 + δ) z w *
        singularPow 1 z' w * singularPow 1 0 w)
    (by filter_upwards [e6] with w hw; rw [← hw]; ring)
  exact ⟨l1, l2, l3, l4, l5, l6⟩

/-- **Bound for the diagram `N₂`**, uniform in `K, Q`. -/
theorem i3Psi2N2_bound_uniform {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ}, Measurable K →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) → Measurable Q →
      (∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, Q (-x) = Q x) → ∀ z z' : SpaceTime, 0 < torusParabolicSize (z - z') →
      0 < torusParabolicSize z → 0 < torusParabolicSize z' → torusParabolicSize z ≤ 1 →
      Integrable (Function.uncurry (i3Psi2N2 K Q z z')) (volume.prod volume) ∧
        |∫ w, ∫ v, i3Psi2N2 K Q z z' w v| ≤ C * i3Psi2S (1 + δ) z z' := by
  obtain ⟨Ci, hCi, hi⟩ := singularIntLe_mul_three (a := 1) (b := 1) (c := 4) (η := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨Co, hCo, ho⟩ := outer_leaves_N2 hδ hδ1
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  have hΛ : 0 ≤ 2 * B ^ 7 * 3 ^ δ := by positivity
  refine ⟨2 * B ^ 7 * 3 ^ δ * Ci * Co * (54 * 2 ^ (1 + δ) + 16),
    mul_nonneg (mul_nonneg (mul_nonneg hΛ hCi) hCo) (by positivity), ?_⟩
  intro K Q hKm hK hKs hQm hQ hQe z z' hzz hz hz' hz1
  have pz0 : 0 < torusParabolicSize (z - 0) := by rwa [sub_zero]
  have pz'0 : 0 < torusParabolicSize (z' - 0) := by rwa [sub_zero]
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := ho hzz pz0 pz'0
  set x1 : ℝ := torusParabolicSize (z - z') ^ (-(1 : ℝ)) with hx1
  set u1 : ℝ := torusParabolicSize (z - 0) ^ (-(1 : ℝ)) with hu1
  have nx1 : 0 ≤ x1 := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have nu1 : 0 ≤ u1 := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have nc : 0 ≤ 3 * x1 + u1 := by positivity
  let V : SpaceTime → ℝ := fun w => Ci * (3 * x1 + u1 + 6 * singularPow 1 z' w +
    2 * singularPow 1 0 w)
  let m : SpaceTime → ℝ := fun w => (2 * B ^ 7 * 3 ^ δ) *
    ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + δ) z w * singularPow 1 z' w)
  have hm : ∀ w, 0 ≤ m w := fun w => mul_nonneg hΛ (mul_nonneg (mul_nonneg (add_nonneg
    (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _))
    (singularPow_nonneg _ _ _))
  have hg : ∀ᵐ w : SpaceTime ∂volume, SingularIntLe (fun v => (3 * singularPow 4 z' v +
      singularPow 4 0 v) * singularPow 1 z v * singularPow 1 w v) (V w) := by
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with w a b
    have f1 := rpow_neg_flip_singularPow (p := 1) (by norm_num) a
    have f2 := rpow_neg_flip_singularPow (p := 1) (by norm_num) b
    rw [Real.rpow_one] at f1 f2
    have t1 := hi z w z' hzz (torusParabolicSize_sub_pos_symm a)
    have t2 := hi z w 0 pz0 (torusParabolicSize_sub_pos_symm b)
    have := ((t1.const_mul (c := 3) (by norm_num)).add t2).congr_fun
      (g := fun v => (3 * singularPow 4 z' v + singularPow 4 0 v) * singularPow 1 z v *
        singularPow 1 w v) (fun v => by ring)
    refine this.mono_right ?_
    have g1 : torusParabolicSize (w - z') ^ (-(1 : ℝ)) ≤ 2 * singularPow 1 z' w := f1
    have g2 : torusParabolicSize (w - 0) ^ (-(1 : ℝ)) ≤ 2 * singularPow 1 0 w := by
      simpa using f2
    simp only [V]
    nlinarith
  have sA := (o1.add o2).const_mul nc
  have sB := (o3.add o4).const_mul (c := 6) (by norm_num)
  have sC := (o5.add o6).const_mul (c := 2) (by norm_num)
  have sT := ((sA.add sB).add sC).const_mul (mul_nonneg hΛ hCi)
  have S0 := i3Psi2S_nonneg δ z z'
  have S1 := i3Psi2S_nonneg (1 + δ) z z'
  have S1' := i3Psi2S_nonneg 1 z z'
  have hSS := i3Psi2S_mul_le (a := 1) (b := δ) (by norm_num) hδ.le (by linarith) hzz pz0 pz'0
  have hnc : 3 * x1 + u1 ≤ 3 * i3Psi2S 1 z z' := by
    have : 0 ≤ torusParabolicSize (z' - 0) ^ (-(1 : ℝ)) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    simp only [i3Psi2S, hx1, hu1]
    linarith
  have hncS : (3 * x1 + u1) * i3Psi2S δ z z' ≤ 3 * (9 * 2 ^ (1 + δ) * i3Psi2S (1 + δ) z z') := by
    calc (3 * x1 + u1) * i3Psi2S δ z z' ≤ (3 * i3Psi2S 1 z z') * i3Psi2S δ z z' :=
          mul_le_mul_of_nonneg_right hnc S0
      _ = 3 * (i3Psi2S 1 z z' * i3Psi2S δ z z') := by ring
      _ ≤ _ := by gcongr
  have hH : SingularIntLe (fun w => m w * V w)
      (2 * B ^ 7 * 3 ^ δ * Ci * Co * (54 * 2 ^ (1 + δ) + 16) * i3Psi2S (1 + δ) z z') := by
    refine (sT.congr_fun (g := fun w => m w * V w) (fun w => by simp only [m, V]; ring)).mono_right
      ?_
    have hP : 0 ≤ 2 * B ^ 7 * 3 ^ δ * Ci * Co := mul_nonneg (mul_nonneg hΛ hCi) hCo
    calc 2 * B ^ 7 * 3 ^ δ * Ci * ((3 * x1 + u1) * (Co * i3Psi2S δ z z' + Co * i3Psi2S δ z z') +
          6 * (Co * i3Psi2S (1 + δ) z z' + Co * i3Psi2S (1 + δ) z z') +
          2 * (Co * i3Psi2S (1 + δ) z z' + Co * i3Psi2S (1 + δ) z z'))
        = (2 * B ^ 7 * 3 ^ δ * Ci * Co) * (2 * ((3 * x1 + u1) * i3Psi2S δ z z') +
            16 * i3Psi2S (1 + δ) z z') := by ring
      _ ≤ (2 * B ^ 7 * 3 ^ δ * Ci * Co) * (2 * (3 * (9 * 2 ^ (1 + δ) * i3Psi2S (1 + δ) z z')) +
          16 * i3Psi2S (1 + δ) z z') := by gcongr
      _ = _ := by ring
  have hmeas : Measurable (fun p : SpaceTime × SpaceTime => i3Psi2N2 K Q z z' p.1 p.2) := by
    unfold i3Psi2N2 i3Psi2dK
    fun_prop
  have hFG : ∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume,
      |i3Psi2N2 K Q z z' w v| ≤ m w * ((3 * singularPow 4 z' v + singularPow 4 0 v) *
        singularPow 1 z v * singularPow 1 w v) := by
    filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos z'] with w a b c
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos w] with v a' b' c' d'
    have := abs_i3Psi2N2_le hB hδ.le hK hKs hQ hQe hz1 a b c a' b' c' d'
    refine this.trans (le_of_eq ?_)
    simp only [m]
    ring
  obtain ⟨hint, hbd⟩ := integrable_and_abs_le_of_majorant (F := fun w v => i3Psi2N2 K Q z z' w v)
    (m := m) (g := fun w v => (3 * singularPow 4 z' v + singularPow 4 0 v) *
      singularPow 1 z v * singularPow 1 w v) (V := V) hmeas.aestronglyMeasurable hm hg hH hFG
  exact ⟨hint, hbd⟩

end RegularityStructures

end
