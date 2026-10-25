/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramChaos5

/-!
# Bounds for the chaos `5` and chaos `3` double integrals

`i3Psi2Double5_bound_uniform` and `i3Psi2Double3_bound_uniform`: the double integrals
`∫∫ δK(z, w) δK(z', w') χ₅` and `∫∫ δK(z, w) δK(z', w') χ₃` are integrable on the product and
bounded by `C · i3Psi2Target δ z z'`, with `C` depending only on `B, δ`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- Integrability and the iterated integral of a three-term decomposition. -/
theorem integrable_double_of_three {F P C N : SpaceTime → SpaceTime → ℝ} {a b c : ℝ}
    (hF : ∀ w v, F w v = a * P w v + b * C w v + c * N w v)
    (iP : Integrable (Function.uncurry P) (volume.prod volume))
    (iC : Integrable (Function.uncurry C) (volume.prod volume))
    (iN : Integrable (Function.uncurry N) (volume.prod volume)) :
    Integrable (Function.uncurry F) (volume.prod volume) ∧
      ∫ q : SpaceTime × SpaceTime, F q.1 q.2 =
        a * (∫ w, ∫ v, P w v) + b * (∫ w, ∫ v, C w v) + c * (∫ w, ∫ v, N w v) := by
  have e : Function.uncurry F = fun p => a * Function.uncurry P p + b * Function.uncurry C p +
      c * Function.uncurry N p := funext fun p => hF p.1 p.2
  have i1 : Integrable (fun p => a * Function.uncurry P p) (volume.prod volume) := iP.const_mul a
  have i2 : Integrable (fun p => b * Function.uncurry C p) (volume.prod volume) := iC.const_mul b
  have i3 : Integrable (fun p => c * Function.uncurry N p) (volume.prod volume) := iN.const_mul c
  have iF : Integrable (Function.uncurry F) (volume.prod volume) := by
    rw [e]; exact (i1.add i2).add i3
  refine ⟨iF, ?_⟩
  have key : ∀ G : SpaceTime → SpaceTime → ℝ,
      Integrable (Function.uncurry G) (volume.prod volume) →
        ∫ p, Function.uncurry G p ∂(volume.prod volume) = ∫ w, ∫ v, G w v :=
    fun G hG => integral_prod _ hG
  have h1 : ∫ q : SpaceTime × SpaceTime, F q.1 q.2 = ∫ p, Function.uncurry F p ∂(volume.prod volume) :=
    rfl
  rw [h1, e]
  beta_reduce
  have i12 : Integrable (fun p => a * Function.uncurry P p + b * Function.uncurry C p)
      (volume.prod volume) := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul,
    integral_const_mul, integral_const_mul, key _ iP, key _ iC, key _ iN]

/-- Integrability and the iterated integral of a two-term decomposition. -/
theorem integrable_double_of_two {F P C : SpaceTime → SpaceTime → ℝ} {a b : ℝ}
    (hF : ∀ w v, F w v = a * P w v + b * C w v)
    (iP : Integrable (Function.uncurry P) (volume.prod volume))
    (iC : Integrable (Function.uncurry C) (volume.prod volume)) :
    Integrable (Function.uncurry F) (volume.prod volume) ∧
      ∫ q : SpaceTime × SpaceTime, F q.1 q.2 =
        a * (∫ w, ∫ v, P w v) + b * (∫ w, ∫ v, C w v) := by
  have e : Function.uncurry F = fun p => a * Function.uncurry P p + b * Function.uncurry C p :=
    funext fun p => hF p.1 p.2
  have i1 : Integrable (fun p => a * Function.uncurry P p) (volume.prod volume) := iP.const_mul a
  have i2 : Integrable (fun p => b * Function.uncurry C p) (volume.prod volume) := iC.const_mul b
  have iF : Integrable (Function.uncurry F) (volume.prod volume) := by
    rw [e]; exact i1.add i2
  refine ⟨iF, ?_⟩
  have key : ∀ G : SpaceTime → SpaceTime → ℝ,
      Integrable (Function.uncurry G) (volume.prod volume) →
        ∫ p, Function.uncurry G p ∂(volume.prod volume) = ∫ w, ∫ v, G w v :=
    fun G hG => integral_prod _ hG
  have h1 : ∫ q : SpaceTime × SpaceTime, F q.1 q.2 = ∫ p, Function.uncurry F p ∂(volume.prod volume) :=
    rfl
  rw [h1, e]
  beta_reduce
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul, key _ iP, key _ iC]

/-- **Chaos-`5` double integral of `I(Ψ³)Ψ²`**, uniform in `K, Q`. -/
theorem i3Psi2Double5_bound_uniform {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ}, Measurable K →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      Measurable Q →
      (∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, Q (-x) = Q x) → ∀ z z' : SpaceTime, 0 < torusParabolicSize z →
        0 < torusParabolicSize z' → 0 < torusParabolicSize (z - z') → torusParabolicSize z ≤ 1 →
        torusParabolicSize z' ≤ 1 →
          Integrable (Function.uncurry fun w v => i3Psi2dK K z w * i3Psi2dK K z' v *
            i3Psi2Chaos5 Q z z' w v) (volume.prod volume) ∧
          |i3Psi2Double K (i3Psi2Chaos5 Q) z z'| ≤ C * i3Psi2Target δ z z' := by
  obtain ⟨CA, hCA, hA⟩ := i3PsiChain_bound_uniform hB hδ hδ1
  obtain ⟨CP, hCP, hP⟩ := i3PsiPrincipal_bound_uniform (B := B) (θ := 1 - δ) hB
    (by linarith) (by linarith)
  obtain ⟨CN, hCN, hN⟩ := i3Psi2N1_bound_uniform hB hδ hδ1
  refine ⟨12 * B ^ 2 * CP + 72 * B * CA + 36 * CN, by positivity, ?_⟩
  intro K Q hKm hKs hK hinc hQm hQ hQe z z' hz hz' hzz hz1 hz1'
  obtain ⟨iA, bA⟩ := hA hKm hK hKs hQm hQ z z' z' z hzz hz hz' hz1 hz1' (Or.inr ⟨rfl, rfl⟩)
  obtain ⟨iP, bP⟩ := hP hKm hKs hK hinc hQm hQ z z' hz1 hz1'
  obtain ⟨iN, bN⟩ := hN hKm hK hKs hQm hQ hQe z z' hzz hz hz' hz1 hz1'
  obtain ⟨iF, hI⟩ := integrable_double_of_three
    (F := fun w v => i3Psi2dK K z w * i3Psi2dK K z' v * i3Psi2Chaos5 Q z z' w v)
    (a := 12 * Q (z - z') ^ 2) (b := 72 * Q (z - z')) (c := 36)
    (fun w v => i3Psi2_integrand5_eq K Q hQe z z' w v) iP iA iN
  refine ⟨iF, ?_⟩
  unfold i3Psi2Double
  rw [hI]
  have T0 := i3Psi2Target_nonneg δ z z'
  have q1 := abs_Q_le_singularPow hQ hzz
  have q2 := abs_Q_sq_le_singularPow hQ hzz
  have t1 : torusParabolicSize (z - z') ^ (-(2 : ℝ)) * torusParabolicSize z' ^ (1 - δ) ≤
      i3Psi2Target δ z z' := inv_sq_mul_le_target_right
  have t2 := inv_mul_i3Psi2S_le_target (δ := δ) (z := z) (z' := z') hzz
  have t3 := (i3Psi2S_one_add_le_target hδ hz hz' hz1 hz1')
  have eS : i3Psi2S δ z z' = torusParabolicSize (z - z') ^ (-δ) + torusParabolicSize z ^ (-δ) +
      torusParabolicSize z' ^ (-δ) := by simp [i3Psi2S]
  have sq : Q (z - z') ^ 2 = |Q (z - z')| ^ 2 := (sq_abs _).symm
  have b1 : |12 * Q (z - z') ^ 2 * (∫ w, ∫ v, i3PsiPrincipal K Q z z' w v)| ≤
      12 * B ^ 2 * CP * (torusParabolicSize (z - z') ^ (-(2 : ℝ)) *
        torusParabolicSize z' ^ (1 - δ)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 12 * Q (z - z') ^ 2)]
    calc 12 * Q (z - z') ^ 2 * |∫ w, ∫ v, i3PsiPrincipal K Q z z' w v|
        ≤ 12 * (B ^ 2 * singularPow 2 z z') * (CP * torusParabolicSize z' ^ (1 - δ)) := by
          rw [sq]
          exact mul_le_mul (mul_le_mul_of_nonneg_left q2 (by norm_num)) bP (abs_nonneg _)
            (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg B) (singularPow_nonneg _ _ _)))
      _ = _ := by unfold singularPow; ring
  have b2 : |72 * Q (z - z') * (∫ w, ∫ v, i3PsiChain K Q z z' z' z w v)| ≤
      72 * B * CA * (torusParabolicSize (z - z') ^ (-(1 : ℝ)) * i3Psi2S δ z z') := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 72)]
    calc 72 * |Q (z - z')| * |∫ w, ∫ v, i3PsiChain K Q z z' z' z w v|
        ≤ 72 * (B * singularPow 1 z z') * (CA * i3Psi2S δ z z') := by
          rw [eS]
          exact mul_le_mul (mul_le_mul_of_nonneg_left q1 (by norm_num)) bA (abs_nonneg _)
            (mul_nonneg (by norm_num) (mul_nonneg hB (singularPow_nonneg _ _ _)))
      _ = _ := by unfold singularPow; ring
  have b3 : |36 * (∫ w, ∫ v, i3Psi2N1 K Q z z' w v)| ≤ 36 * CN * i3Psi2S (1 + δ) z z' := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 36)]
    calc 36 * |∫ w, ∫ v, i3Psi2N1 K Q z z' w v| ≤ 36 * (CN * i3Psi2S (1 + δ) z z') :=
          mul_le_mul_of_nonneg_left bN (by norm_num)
      _ = _ := by ring
  have hc1 : 0 ≤ 12 * B ^ 2 * CP := by positivity
  have hc2 : 0 ≤ 72 * B * CA := by positivity
  have hc3 : 0 ≤ 36 * CN := by positivity
  have u1 := mul_le_mul_of_nonneg_left t1 hc1
  have u2 := mul_le_mul_of_nonneg_left t2 hc2
  have u3 := mul_le_mul_of_nonneg_left t3 hc3
  have x1 := abs_add_le (12 * Q (z - z') ^ 2 * (∫ w, ∫ v, i3PsiPrincipal K Q z z' w v) +
    72 * Q (z - z') * (∫ w, ∫ v, i3PsiChain K Q z z' z' z w v))
    (36 * (∫ w, ∫ v, i3Psi2N1 K Q z z' w v))
  have x2 := abs_add_le (12 * Q (z - z') ^ 2 * (∫ w, ∫ v, i3PsiPrincipal K Q z z' w v))
    (72 * Q (z - z') * (∫ w, ∫ v, i3PsiChain K Q z z' z' z w v))
  calc _ ≤ _ := x1
    _ ≤ (12 * B ^ 2 * CP + 72 * B * CA + 36 * CN) * i3Psi2Target δ z z' := by
      linarith [mul_nonneg hc1 T0, mul_nonneg hc2 T0, mul_nonneg hc3 T0]

end RegularityStructures

end
