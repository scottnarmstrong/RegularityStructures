/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramChaos5Bound

/-!
# Bound for the chaos `3` double integral

`i3Psi2Double3_bound_uniform`: `∫∫ δK(z, w) δK(z', w') χ₃(w, w')` is integrable on the product and
bounded by `C · i3Psi2Target δ z z'`, with `C` depending only on `B, δ`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Chaos-`3` double integral of `I(Ψ³)Ψ²`**, uniform in `K, Q`. -/
theorem i3Psi2Double3_bound_uniform {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ}, Measurable K →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      Measurable Q →
      (∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, Q (-x) = Q x) → ∀ z z' : SpaceTime, 0 < torusParabolicSize z →
        0 < torusParabolicSize z' → 0 < torusParabolicSize (z - z') → torusParabolicSize z ≤ 1 →
        torusParabolicSize z' ≤ 1 →
          Integrable (Function.uncurry fun w v => i3Psi2dK K z w * i3Psi2dK K z' v *
            i3Psi2Chaos3 Q z z' w v) (volume.prod volume) ∧
          |i3Psi2Double K (i3Psi2Chaos3 Q) z z'| ≤ C * i3Psi2Target δ z z' := by
  obtain ⟨CA, hCA, hA⟩ := i3PsiChain_bound_uniform hB hδ hδ1
  obtain ⟨CN, hCN, hN⟩ := i3Psi2N2_bound_uniform hB hδ hδ1
  refine ⟨72 * B * CA + 144 * CN, by positivity, ?_⟩
  intro K Q hKm hKs hK hQm hQ hQe z z' hz hz' hzz hz1 hz1'
  obtain ⟨iA, bA⟩ := hA hKm hK hKs hQm hQ z z' z z' hzz hz hz' hz1 hz1' (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨iN, bN⟩ := hN hKm hK hKs hQm hQ hQe z z' hzz hz hz' hz1
  obtain ⟨iF, hI⟩ := integrable_double_of_two
    (F := fun w v => i3Psi2dK K z w * i3Psi2dK K z' v * i3Psi2Chaos3 Q z z' w v)
    (a := 72 * Q (z - z')) (b := 144)
    (fun w v => i3Psi2_integrand3_eq K Q hQe z z' w v) iA iN
  refine ⟨iF, ?_⟩
  unfold i3Psi2Double
  rw [hI]
  have T0 := i3Psi2Target_nonneg δ z z'
  have q1 := abs_Q_le_singularPow hQ hzz
  have t2 := inv_mul_i3Psi2S_le_target (δ := δ) (z := z) (z' := z') hzz
  have t3 := (i3Psi2S_one_add_le_target hδ hz hz' hz1 hz1')
  have eS : i3Psi2S δ z z' = torusParabolicSize (z - z') ^ (-δ) + torusParabolicSize z ^ (-δ) +
      torusParabolicSize z' ^ (-δ) := by simp [i3Psi2S]
  have b2 : |72 * Q (z - z') * (∫ w, ∫ v, i3PsiChain K Q z z' z z' w v)| ≤
      72 * B * CA * (torusParabolicSize (z - z') ^ (-(1 : ℝ)) * i3Psi2S δ z z') := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 72)]
    calc 72 * |Q (z - z')| * |∫ w, ∫ v, i3PsiChain K Q z z' z z' w v|
        ≤ 72 * (B * singularPow 1 z z') * (CA * i3Psi2S δ z z') := by
          rw [eS]
          exact mul_le_mul (mul_le_mul_of_nonneg_left q1 (by norm_num)) bA (abs_nonneg _)
            (mul_nonneg (by norm_num) (mul_nonneg hB (singularPow_nonneg _ _ _)))
      _ = _ := by unfold singularPow; ring
  have b3 : |144 * (∫ w, ∫ v, i3Psi2N2 K Q z z' w v)| ≤ 144 * CN * i3Psi2S (1 + δ) z z' := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 144)]
    calc 144 * |∫ w, ∫ v, i3Psi2N2 K Q z z' w v| ≤ 144 * (CN * i3Psi2S (1 + δ) z z') :=
          mul_le_mul_of_nonneg_left bN (by norm_num)
      _ = _ := by ring
  have hc2 : 0 ≤ 72 * B * CA := by positivity
  have hc3 : 0 ≤ 144 * CN := by positivity
  have u2 := mul_le_mul_of_nonneg_left t2 hc2
  have u3 := mul_le_mul_of_nonneg_left t3 hc3
  have x1 := abs_add_le (72 * Q (z - z') * (∫ w, ∫ v, i3PsiChain K Q z z' z z' w v))
    (144 * (∫ w, ∫ v, i3Psi2N2 K Q z z' w v))
  calc _ ≤ _ := x1
    _ ≤ (72 * B * CA + 144 * CN) * i3Psi2Target δ z z' := by
      nlinarith [mul_nonneg hc2 T0, mul_nonneg hc3 T0]

end RegularityStructures

end
