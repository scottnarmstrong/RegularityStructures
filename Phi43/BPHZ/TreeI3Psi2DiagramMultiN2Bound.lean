/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramMultiN2
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiLevel

/-!
# Bound for the weighted diagram `N₂` with general exponents

`i3Psi2N2Weighted_bound`: every measurable `F` dominated by
`Λ |δK(z, w)| |δK(z', v)| s(w - z)^(-(1+y₁)) s(w - z')^(-(1+y₂)) s(w - v)^(-(1+y₃))
s(v - z')^(-(1+y₄)) s(z - v)^(-(1+y₅))` is integrable on the product and
`|∫∫ F| ≤ Λ C S_{1+δ+y₁+⋯+y₅}(z, z')`.  The proof is that of the a-priori bound for `N₂` with the
exponents `(1 + ν₁, 1 + y₂, 1 + y₃, 4 + y₄, 1 + y₅)` in place of `(1 + δ, 1, 1, 4, 1)`.
-/

public section

open MeasureTheory

namespace RegularityStructures

private theorem outer_leaves_N2_gen {ν₁ y₂ η : ℝ} (hν : 0 < ν₁) (hν1 : ν₁ < 1) (hy₂ : 0 ≤ y₂)
    (hη : 0 < η) (hs : ν₁ + y₂ + η < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z z' : SpaceTime}, 0 < torusParabolicSize (z - z') →
      0 < torusParabolicSize (z - 0) → 0 < torusParabolicSize (z' - 0) →
      SingularIntLe (fun w => singularPow 3 z w * singularPow (1 + ν₁) z w *
        singularPow (1 + y₂) z' w) (C * i3Psi2S (ν₁ + y₂) z z') ∧
      SingularIntLe (fun w => singularPow 3 0 w * singularPow (1 + ν₁) z w *
        singularPow (1 + y₂) z' w) (C * i3Psi2S (ν₁ + y₂) z z') ∧
      SingularIntLe (fun w => singularPow 3 z w * singularPow (1 + ν₁) z w *
        singularPow (1 + y₂) z' w * singularPow η z' w) (C * i3Psi2S (ν₁ + y₂ + η) z z') ∧
      SingularIntLe (fun w => singularPow 3 0 w * singularPow (1 + ν₁) z w *
        singularPow (1 + y₂) z' w * singularPow η z' w) (C * i3Psi2S (ν₁ + y₂ + η) z z') ∧
      SingularIntLe (fun w => singularPow 3 z w * singularPow (1 + ν₁) z w *
        singularPow (1 + y₂) z' w * singularPow η 0 w) (C * i3Psi2S (ν₁ + y₂ + η) z z') ∧
      SingularIntLe (fun w => singularPow 3 0 w * singularPow (1 + ν₁) z w *
        singularPow (1 + y₂) z' w * singularPow η 0 w) (C * i3Psi2S (ν₁ + y₂ + η) z z') := by
  obtain ⟨C1, hC1, h1⟩ := i3Psi2_leaf2 (a := 4 + ν₁) (b := 1 + y₂) (η := ν₁ + y₂) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
  obtain ⟨C2, hC2, h2⟩ := i3Psi2_leaf3 (a := 1 + ν₁) (b := 1 + y₂) (c := 3) (η := ν₁ + y₂)
    (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by linarith)
    (by ring)
  obtain ⟨C3, hC3, h3⟩ := i3Psi2_leaf2 (a := 4 + ν₁) (b := 1 + y₂ + η) (η := ν₁ + y₂ + η)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
  obtain ⟨C4, hC4, h4⟩ := i3Psi2_leaf3 (a := 1 + y₂) (b := η) (c := 4 + ν₁) (η := ν₁ + y₂ + η)
    (by linarith) hη (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
  obtain ⟨C5, hC5, h5⟩ := i3Psi2_leaf3 (a := 1 + ν₁) (b := 1 + y₂ + η) (c := 3)
    (η := ν₁ + y₂ + η) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num)
    (by linarith) (by ring)
  obtain ⟨C6, hC6, h6⟩ := i3Psi2_leaf3 (a := 1 + ν₁) (b := 1 + y₂) (c := 3 + η)
    (η := ν₁ + y₂ + η) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by ring)
  refine ⟨C1 + C2 + C3 + C4 + C5 + C6, by positivity, fun {z z'} hx hu hu' => ?_⟩
  have pzz' := torusParabolicSize_sub_pos_symm hx
  have p0z := torusParabolicSize_sub_pos_symm hu
  have p0z' := torusParabolicSize_sub_pos_symm hu'
  have S0 := i3Psi2S_nonneg (ν₁ + y₂) z z'
  have S1 := i3Psi2S_nonneg (ν₁ + y₂ + η) z z'
  have hsum : ∀ c, c ≤ C1 + C2 + C3 + C4 + C5 + C6 → ∀ S : ℝ, 0 ≤ S →
      c * S ≤ (C1 + C2 + C3 + C4 + C5 + C6) * S :=
    fun c hc S hS => mul_le_mul_of_nonneg_right hc hS
  have m1 := hsum C1 (by linarith) _ S0
  have m2 := hsum C2 (by linarith) _ S0
  have m3 := hsum C3 (by linarith) _ S1
  have m4 := hsum C4 (by linarith) _ S1
  have m5 := hsum C5 (by linarith) _ S1
  have m6 := hsum C6 (by linarith) _ S1
  have e1 := ae_singularPow_mul_self (a := 3) (b := 1 + ν₁) (e := 4 + ν₁) (by ring) z
  have e3 := ae_singularPow_mul_self (a := 1 + y₂) (b := η) (e := 1 + y₂ + η) (by ring) z'
  have e6 := ae_singularPow_mul_self (a := 3) (b := η) (e := 3 + η) (by ring) (0 : SpaceTime)
  have hz : (z = z ∨ z = z' ∨ z = 0) := Or.inl rfl
  have hz' : (z' = z ∨ z' = z' ∨ z' = 0) := Or.inr (Or.inl rfl)
  have h0 : ((0 : SpaceTime) = z ∨ (0 : SpaceTime) = z' ∨ (0 : SpaceTime) = 0) :=
    Or.inr (Or.inr rfl)
  have l1 := ((h1 (z := z) (z' := z') (p := z) (q := z') hx hu hu' hz hz' hx).mono_right m1
    ).congr_ae (f := fun w => singularPow (4 + ν₁) z w * singularPow (1 + y₂) z' w)
    (g := fun w => singularPow 3 z w * singularPow (1 + ν₁) z w * singularPow (1 + y₂) z' w)
    (by filter_upwards [e1] with w hw; rw [← hw])
  have l2 := ((h2 (z := z) (z' := z') (p := z) (q := z') (r := 0) hx hu hu' hz hz' h0 hu hu'
    ).mono_right m2).congr_fun (f := fun w => singularPow (1 + ν₁) z w *
      singularPow (1 + y₂) z' w * singularPow 3 0 w) (g := fun w => singularPow 3 0 w *
        singularPow (1 + ν₁) z w * singularPow (1 + y₂) z' w) (fun w => by ring)
  have l3 := ((h3 (z := z) (z' := z') (p := z) (q := z') hx hu hu' hz hz' hx).mono_right m3
    ).congr_ae (f := fun w => singularPow (4 + ν₁) z w * singularPow (1 + y₂ + η) z' w)
    (g := fun w => singularPow 3 z w * singularPow (1 + ν₁) z w * singularPow (1 + y₂) z' w *
      singularPow η z' w)
    (by filter_upwards [e1, e3] with w hw hw'; rw [← hw, ← hw']; ring)
  have l4 := ((h5 (z := z) (z' := z') (p := z) (q := z') (r := 0) hx hu hu' hz hz' h0 hu hu'
    ).mono_right m5).congr_ae (f := fun w => singularPow (1 + ν₁) z w *
      singularPow (1 + y₂ + η) z' w * singularPow 3 0 w) (g := fun w => singularPow 3 0 w *
        singularPow (1 + ν₁) z w * singularPow (1 + y₂) z' w * singularPow η z' w)
    (by filter_upwards [e3] with w hw; rw [← hw]; ring)
  have l5 := ((h4 (z := z) (z' := z') (p := z') (q := 0) (r := z) hx hu hu' hz' h0 hz pzz'
    p0z).mono_right m4).congr_ae (f := fun w => singularPow (1 + y₂) z' w *
      singularPow η 0 w * singularPow (4 + ν₁) z w) (g := fun w => singularPow 3 z w *
        singularPow (1 + ν₁) z w * singularPow (1 + y₂) z' w * singularPow η 0 w)
    (by filter_upwards [e1] with w hw; rw [← hw]; ring)
  have l6 := ((h6 (z := z) (z' := z') (p := z) (q := z') (r := 0) hx hu hu' hz hz' h0 hu hu'
    ).mono_right m6).congr_ae (f := fun w => singularPow (1 + ν₁) z w *
      singularPow (1 + y₂) z' w * singularPow (3 + η) 0 w) (g := fun w => singularPow 3 0 w *
        singularPow (1 + ν₁) z w * singularPow (1 + y₂) z' w * singularPow η 0 w)
    (by filter_upwards [e6] with w hw; rw [← hw]; ring)
  exact ⟨l1, l2, l3, l4, l5, l6⟩

/-- **Bound for the weighted diagram `N₂`**, uniform in `K`: the weight is a two-level majorant. -/
theorem i3Psi2N2Weighted_twoLevelLe {B δ y₁ y₂ y₃ y₄ y₅ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (hy₃ : 0 ≤ y₃) (hy₄ : 0 ≤ y₄) (hy₅ : 0 ≤ y₅)
    (hsum : δ + y₁ + y₂ + y₃ + y₄ + y₅ ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {Λ : ℝ}, 0 ≤ Λ → Measurable K →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      ∀ z z' : SpaceTime, 0 < torusParabolicSize (z - z') → 0 < torusParabolicSize z →
        0 < torusParabolicSize z' → torusParabolicSize z ≤ 1 → torusParabolicSize z' ≤ 1 →
        TwoLevelLe (fun w v => Λ * (|i3Psi2dK K z w| * |i3Psi2dK K z' v| *
          (torusParabolicSize (w - z) ^ (-(1 + y₁)) * torusParabolicSize (w - z') ^ (-(1 + y₂)) *
            torusParabolicSize (w - v) ^ (-(1 + y₃)) * torusParabolicSize (v - z') ^ (-(1 + y₄)) *
            torusParabolicSize (z - v) ^ (-(1 + y₅)))))
          (Λ * C * i3Psi2S (1 + δ + y₁ + y₂ + y₃ + y₄ + y₅) z z') := by
  have hη : 0 < 1 + y₃ + y₄ + y₅ := by linarith
  have hν1 : 0 < y₁ + δ := by linarith
  obtain ⟨Ci, hCi, hi⟩ := singularIntLe_mul_three (a := 1 + y₅) (b := 1 + y₃) (c := 4 + y₄)
    (η := 1 + y₃ + y₄ + y₅) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) hη (by ring)
  obtain ⟨Co, hCo, ho⟩ := outer_leaves_N2_gen (ν₁ := y₁ + δ) (y₂ := y₂) (η := 1 + y₃ + y₄ + y₅)
    hν1 (by linarith) hy₂ hη (by linarith)
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  have n21 : (0 : ℝ) ≤ 2 ^ (1 + y₁) := Real.rpow_nonneg (by norm_num) _
  have n22 : (0 : ℝ) ≤ 2 ^ (1 + y₂) := Real.rpow_nonneg (by norm_num) _
  have n24 : (0 : ℝ) ≤ 2 ^ (1 + y₄) := Real.rpow_nonneg (by norm_num) _
  have nP : (0 : ℝ) ≤ 2 ^ (1 + y₃ + y₄ + y₅) := Real.rpow_nonneg (by norm_num) _
  have nQ : (0 : ℝ) ≤ 2 ^ (1 + y₃ + y₄ + y₅ + (y₁ + δ + y₂)) := Real.rpow_nonneg (by norm_num) _
  have hc0 : 0 ≤ B ^ 2 * (2 ^ (1 + y₁) * 3 ^ δ * 2 ^ (1 + y₂) * 2 ^ (1 + y₄)) :=
    mul_nonneg (sq_nonneg B) (mul_nonneg (mul_nonneg (mul_nonneg n21 n3) n22) n24)
  refine ⟨B ^ 2 * (2 ^ (1 + y₁) * 3 ^ δ * 2 ^ (1 + y₂) * 2 ^ (1 + y₄)) * Ci * Co *
    (54 * 2 ^ (1 + y₃ + y₄ + y₅ + (y₁ + δ + y₂)) + 8 * 2 ^ (1 + y₃ + y₄ + y₅)),
    mul_nonneg (mul_nonneg (mul_nonneg hc0 hCi) hCo) (by positivity), ?_⟩
  intro K Λ hΛ hKm hK hKs z z' hzz hz hz' hz1 hz1'
  have pz0 : 0 < torusParabolicSize (z - 0) := by rwa [sub_zero]
  have pz'0 : 0 < torusParabolicSize (z' - 0) := by rwa [sub_zero]
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := ho hzz pz0 pz'0
  set η : ℝ := 1 + y₃ + y₄ + y₅ with hηdef
  set ν : ℝ := y₁ + δ + y₂ with hνdef
  set c0 : ℝ := B ^ 2 * (2 ^ (1 + y₁) * 3 ^ δ * 2 ^ (1 + y₂) * 2 ^ (1 + y₄)) with hc0def
  set P : ℝ := 2 ^ η with hPdef
  set x1 : ℝ := torusParabolicSize (z - z') ^ (-η) with hx1
  set u1 : ℝ := torusParabolicSize (z - 0) ^ (-η) with hu1
  have nx1 : 0 ≤ x1 := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have nu1 : 0 ≤ u1 := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have nc : 0 ≤ 3 * x1 + u1 := by positivity
  have hΛc : 0 ≤ Λ * c0 := mul_nonneg hΛ hc0
  let V : SpaceTime → ℝ := fun w => Ci * (3 * x1 + u1 +
    P * (3 * singularPow η z' w + singularPow η 0 w))
  let m : SpaceTime → ℝ := fun w => (Λ * c0) *
    ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + (y₁ + δ)) z w *
      singularPow (1 + y₂) z' w)
  have hm : ∀ w, 0 ≤ m w := fun w => mul_nonneg hΛc (mul_nonneg (mul_nonneg (add_nonneg
    (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _))
    (singularPow_nonneg _ _ _))
  have hg : ∀ᵐ w : SpaceTime ∂volume, SingularIntLe (fun v => (3 * singularPow (4 + y₄) z' v +
      singularPow (4 + y₄) 0 v) * singularPow (1 + y₅) z v * singularPow (1 + y₃) w v) (V w) := by
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with w a b
    have f1 := rpow_neg_flip_singularPow (p := η) hη.le a
    have f2 := rpow_neg_flip_singularPow (p := η) hη.le b
    have t1 := hi z w z' hzz (torusParabolicSize_sub_pos_symm a)
    have t2 := hi z w 0 pz0 (torusParabolicSize_sub_pos_symm b)
    have := ((t1.const_mul (c := 3) (by norm_num)).add t2).congr_fun
      (g := fun v => (3 * singularPow (4 + y₄) z' v + singularPow (4 + y₄) 0 v) *
        singularPow (1 + y₅) z v * singularPow (1 + y₃) w v) (fun v => by ring)
    refine this.mono_right ?_
    simp only [V, sub_zero] at f2 ⊢
    have g1 : torusParabolicSize (w - z') ^ (-η) ≤ P * singularPow η z' w := f1
    have g2 : torusParabolicSize w ^ (-η) ≤ P * singularPow η 0 w := f2
    have := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left g1
      (by norm_num : (0 : ℝ) ≤ 3)) g2) hCi
    simp only [hx1, hu1, sub_zero] at *
    linarith
  have S0 := i3Psi2S_nonneg ν z z'
  have S1 := i3Psi2S_nonneg (ν + η) z z'
  have hν0 : 0 < ν := by rw [hνdef]; linarith
  have hSS := i3Psi2S_mul_le (a := η) (b := ν) hη.le hν0.le (by linarith) hzz pz0 pz'0
  rw [show η + ν = ν + η by ring] at hSS
  have hnc : 3 * x1 + u1 ≤ 3 * i3Psi2S η z z' := by
    have : 0 ≤ torusParabolicSize (z' - 0) ^ (-η) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    simp only [i3Psi2S, hx1, hu1]
    linarith
  have hncS : (3 * x1 + u1) * i3Psi2S ν z z' ≤ 3 * (9 * 2 ^ (η + ν) * i3Psi2S (ν + η) z z') := by
    calc (3 * x1 + u1) * i3Psi2S ν z z' ≤ (3 * i3Psi2S η z z') * i3Psi2S ν z z' :=
          mul_le_mul_of_nonneg_right hnc S0
      _ = 3 * (i3Psi2S η z z' * i3Psi2S ν z z') := by ring
      _ ≤ 3 * (9 * 2 ^ (η + ν) * i3Psi2S (ν + η) z z') := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [show η + ν = ν + η by ring]; exact hSS
  have sA := (o1.add o2).const_mul nc
  have sB := (((o3.add o4).const_mul (c := 3) (by norm_num)).add (o5.add o6)).const_mul
    (c := P) (by positivity)
  have sT := (sA.add sB).const_mul (mul_nonneg hΛc hCi)
  have hH : SingularIntLe (fun w => m w * V w)
      (Λ * (c0 * Ci * Co * (54 * 2 ^ (η + ν) + 8 * 2 ^ η)) *
        i3Psi2S (1 + δ + y₁ + y₂ + y₃ + y₄ + y₅) z z') := by
    have e : 1 + δ + y₁ + y₂ + y₃ + y₄ + y₅ = ν + η := by rw [hνdef, hηdef]; ring
    rw [e]
    refine (sT.congr_fun (g := fun w => m w * V w) (fun w => by simp only [m, V]; ring)).mono_right
      ?_
    calc Λ * c0 * Ci * ((3 * x1 + u1) * (Co * i3Psi2S ν z z' + Co * i3Psi2S ν z z') +
          P * (3 * (Co * i3Psi2S (ν + η) z z' + Co * i3Psi2S (ν + η) z z') +
            (Co * i3Psi2S (ν + η) z z' + Co * i3Psi2S (ν + η) z z')))
        = (Λ * (c0 * Ci * Co)) * (2 * ((3 * x1 + u1) * i3Psi2S ν z z') +
            8 * P * i3Psi2S (ν + η) z z') := by ring
      _ ≤ (Λ * (c0 * Ci * Co)) * (2 * (3 * (9 * 2 ^ (η + ν) * i3Psi2S (ν + η) z z')) +
            8 * P * i3Psi2S (ν + η) z z') := by
          have hP : 0 ≤ Λ * (c0 * Ci * Co) :=
            mul_nonneg hΛ (mul_nonneg (mul_nonneg hc0 hCi) hCo)
          gcongr
      _ = _ := by rw [hPdef]; ring
  have hG := twoLevelLe_of_inner (m := m) (g := fun w v => (3 * singularPow (4 + y₄) z' v +
    singularPow (4 + y₄) 0 v) * singularPow (1 + y₅) z v * singularPow (1 + y₃) w v) (V := V)
    hm hg hH
  refine hG.of_le (fun w => ?_) (fun w v => ?_) ?_
  · have hdK : Measurable (fun v => i3Psi2dK K z' v) := by
      unfold i3Psi2dK; fun_prop
    have hW3 : Measurable (fun v => torusParabolicSize (w - v) ^ (-(1 + y₃))) :=
      (Phi43.measurable_torusParabolicSize.comp (measurable_const.sub measurable_id)).pow_const _
    have hW4 : Measurable (fun v => torusParabolicSize (v - z') ^ (-(1 + y₄))) :=
      (Phi43.measurable_torusParabolicSize.comp (measurable_id.sub measurable_const)).pow_const _
    have hW5 : Measurable (fun v => torusParabolicSize (z - v) ^ (-(1 + y₅))) :=
      (Phi43.measurable_torusParabolicSize.comp (measurable_const.sub measurable_id)).pow_const _
    exact measurable_const.mul ((measurable_const.mul (continuous_abs.measurable.comp hdK)).mul
      ((((measurable_const.mul measurable_const).mul hW3).mul hW4).mul hW5))
  · exact mul_nonneg hΛ (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg
        (torusParabolicSize_nonneg _) _) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)))
  · filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos z'] with w a b c
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with
      v a' b'
    have := abs_dK_dK_N2_le (y₃ := y₃) (y₅ := y₅) hB hδ.le hy₁ hy₂ hy₄ hK hKs hz1 hz1' a b c a' b'
    have h2 := mul_le_mul_of_nonneg_left this hΛ
    refine h2.trans (le_of_eq ?_)
    simp only [m, i3Psi2N2Majorant, hc0def]
    ring

end RegularityStructures

end
