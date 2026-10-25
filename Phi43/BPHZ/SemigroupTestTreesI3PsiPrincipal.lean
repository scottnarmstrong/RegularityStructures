/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesSlab
public import Phi43.BPHZ.SemigroupTestTreesI3PsiChain
public import Phi43.BPHZ.TreeI3PsiDiagramUniform

/-!
# The principal diagram of `I(Ψ³)Ψ`, for arbitrary `z, z'`

Without Hölder gains (these need `s(z), s(z') ≤ 1`) the principal diagram
`∫∫ δK(z, w) δK(z', v) Q(w - v)³` is bounded by absolute values:
`∫ s₃(z', 0; v) s₃(w; v) dv ≤ C (s₁(z'; w) + s₁(0; w))` (total order `6`), and the `w`-integral of
`s₃(z, 0; w) (s₁(z'; w) + s₁(0; w))` over the slab `|w.1| ≤ T` is bounded by `C (1 + T)`
uniformly in the centres (`singularIntLe_slab_singularPow`).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- **Principal integral for a dominated integrand.** -/
theorem i3PsiPrincipal_majorant_integral :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : SpaceTime → SpaceTime → ℝ} {Λ T : ℝ}, 0 ≤ Λ → 0 ≤ T →
      AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) →
      ∀ z z' : SpaceTime,
      (∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume, |F w v| ≤
        Λ * (Set.indicator {w : SpaceTime | |w.1| ≤ T}
            (fun w => singularPow 3 z w + singularPow 3 0 w) w *
          ((singularPow 3 z' v + singularPow 3 0 v) * singularPow 3 w v))) →
      Integrable (Function.uncurry F) (volume.prod volume) ∧
        |∫ w, ∫ v, F w v| ≤ C * Λ * (80 + 2 * T) := by
  obtain ⟨C1, hC1, h1⟩ := singularIntLe_mul_two (a := 3) (b := 3) (η := 1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨8 * C1, by positivity, ?_⟩
  intro F Λ T hΛ hT hmeas z z' hFG
  set S : Set SpaceTime := {w : SpaceTime | |w.1| ≤ T} with hS
  set m : SpaceTime → ℝ := Set.indicator S (fun w => singularPow 3 z w + singularPow 3 0 w) with hm
  have hm0 : ∀ w, 0 ≤ m w := fun w => Set.indicator_nonneg (fun w _ =>
    add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)) w
  have hmm : Measurable m := (((measurable_singularPow 3 z).add (measurable_singularPow 3 0))
    ).indicator (measurableSet_abs_fst_le T)
  have sl : ∀ c : SpaceTime, SingularIntLe (Set.indicator S (singularPow 4 c))
      (80 / (5 - 4) + 2 * T) := fun c => singularIntLe_slab_singularPow (by norm_num)
    (by norm_num) hT c
  have hsum : SingularIntLe (fun w => 2 * Set.indicator S (singularPow 4 z) w +
      2 * Set.indicator S (singularPow 4 z') w + 4 * Set.indicator S (singularPow 4 0) w)
      (2 * (80 / (5 - 4) + 2 * T) + 2 * (80 / (5 - 4) + 2 * T) + 4 * (80 / (5 - 4) + 2 * T)) :=
    (((sl z).const_mul (c := 2) (by norm_num)).add ((sl z').const_mul (c := 2)
      (by norm_num))).add ((sl 0).const_mul (c := 4) (by norm_num))
  set H : SpaceTime → ℝ := fun w => (Λ * m w) * (C1 * (singularPow 1 z' w + singularPow 1 0 w))
    with hH
  have hHle : SingularIntLe H (Λ * C1 * (2 * (80 / (5 - 4) + 2 * T) +
      2 * (80 / (5 - 4) + 2 * T) + 4 * (80 / (5 - 4) + 2 * T))) := by
    refine ((hsum.const_mul (c := Λ * C1) (mul_nonneg hΛ hC1))).of_le ?_ ?_ ?_
    · exact (((measurable_const.mul hmm)).mul (measurable_const.mul
        ((measurable_singularPow 1 z').add (measurable_singularPow 1 0)))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun w => mul_nonneg (mul_nonneg hΛ (hm0 w))
        (mul_nonneg hC1 (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)))
    · filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos z',
        ae_torusParabolicSize_sub_pos 0] with w a b c
      by_cases hw : w ∈ S
      · simp only [hH, hm, Set.indicator_of_mem hw]
        have e1 := singularPow_mul_le (a := 3) (b := 1) (by norm_num) (by norm_num) a b
        have e2 := singularPow_mul_le (a := 3) (b := 1) (by norm_num) (by norm_num) a c
        have e3 := singularPow_mul_le (a := 3) (b := 1) (by norm_num) (by norm_num) c b
        have e4 := singularPow_mul_le (a := 3) (b := 1) (by norm_num) (by norm_num) c c
        have hΛC : 0 ≤ Λ * C1 := mul_nonneg hΛ hC1
        norm_num at e1 e2 e3 e4
        have : (singularPow 3 z w + singularPow 3 0 w) *
            (singularPow 1 z' w + singularPow 1 0 w) ≤
            2 * singularPow 4 z w + 2 * singularPow 4 z' w + 4 * singularPow 4 0 w := by
          calc _ = singularPow 3 z w * singularPow 1 z' w + singularPow 3 z w * singularPow 1 0 w +
                singularPow 3 0 w * singularPow 1 z' w + singularPow 3 0 w * singularPow 1 0 w := by
                ring
            _ ≤ _ := by linarith
        calc Λ * (singularPow 3 z w + singularPow 3 0 w) *
            (C1 * (singularPow 1 z' w + singularPow 1 0 w))
            = Λ * C1 * ((singularPow 3 z w + singularPow 3 0 w) *
              (singularPow 1 z' w + singularPow 1 0 w)) := by ring
          _ ≤ Λ * C1 * (2 * singularPow 4 z w + 2 * singularPow 4 z' w +
              4 * singularPow 4 0 w) := mul_le_mul_of_nonneg_left this hΛC
      · simp [hH, hm, hw]
  -- the two-level argument
  have hG : ∀ᵐ w : SpaceTime ∂volume, Integrable (fun v =>
      (Λ * m w) * ((singularPow 3 z' v + singularPow 3 0 v) * singularPow 3 w v)) := by
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with w a b
    have i1 := (h1 z' w a).1
    have i2 := (h1 0 w b).1
    exact ((i1.add i2).congr (Filter.Eventually.of_forall fun v => by
      simp only [Pi.add_apply]; ring)).const_mul
      (Λ * m w)
  have hGH : ∀ᵐ w : SpaceTime ∂volume, ∫ v,
      (Λ * m w) * ((singularPow 3 z' v + singularPow 3 0 v) * singularPow 3 w v) ≤ H w := by
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with w a b
    have j1 := h1 z' w a
    have j2 := h1 0 w b
    have hs := j1.add j2
    have hnn : 0 ≤ Λ * m w := mul_nonneg hΛ (hm0 w)
    rw [integral_const_mul]
    have := hs.2
    simp only at this
    rw [show (∫ v, (singularPow 3 z' v + singularPow 3 0 v) * singularPow 3 w v) =
      ∫ v, (singularPow 3 z' v * singularPow 3 w v + singularPow 3 0 v * singularPow 3 w v) from
        integral_congr_ae (Filter.Eventually.of_forall fun v => by ring)]
    refine mul_le_mul_of_nonneg_left (this.trans (le_of_eq ?_)) hnn
    simp only [singularPow, zero_sub]
    ring_nf
  have hFG' : ∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume, |F w v| ≤
      (Λ * m w) * ((singularPow 3 z' v + singularPow 3 0 v) * singularPow 3 w v) := by
    filter_upwards [hFG] with w hw
    filter_upwards [hw] with v hv
    refine hv.trans (le_of_eq ?_)
    simp only [hm]
    ring
  obtain ⟨hint, hbd⟩ := integrable_prod_of_two_level (F := F) hmeas hG hGH hHle.1 hFG'
  refine ⟨hint, hbd.trans (hHle.2.trans (le_of_eq ?_))⟩
  norm_num
  ring

/-- **Principal diagram of `I(Ψ³)Ψ`, for arbitrary `z, z'`.**  The bound grows linearly in
`|z.1|`. -/
theorem i3PsiPrincipal_bound_global {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ}, Measurable K →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) → Measurable Q →
      (∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      ∀ z z' : SpaceTime,
      Integrable (Function.uncurry (i3PsiPrincipal K Q z z')) (volume.prod volume) ∧
        |∫ w, ∫ v, i3PsiPrincipal K Q z z' w v| ≤ C * (80 + 2 * (|z.1| + 1)) := by
  obtain ⟨C0, hC0, h0⟩ := i3PsiPrincipal_majorant_integral
  refine ⟨C0 * B ^ 5, by positivity, ?_⟩
  intro K Q hKm hK hKs hQm hQ z z'
  have hΛ : 0 ≤ B ^ 5 := pow_nonneg hB 5
  have hmeas : Measurable (fun p : SpaceTime × SpaceTime => i3PsiPrincipal K Q z z' p.1 p.2) := by
    unfold i3PsiPrincipal
    fun_prop
  have := h0 (F := i3PsiPrincipal K Q z z') (Λ := B ^ 5) (T := |z.1| + 1) hΛ
    (by positivity) hmeas.aestronglyMeasurable z z' (by
    filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0] with w a b
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos w] with v a' b' c'
    have hnn : 0 ≤ B ^ 5 * (Set.indicator {w : SpaceTime | |w.1| ≤ |z.1| + 1}
        (fun w => singularPow 3 z w + singularPow 3 0 w) w *
        ((singularPow 3 z' v + singularPow 3 0 v) * singularPow 3 w v)) := by
      refine mul_nonneg hΛ (mul_nonneg (Set.indicator_nonneg (fun w _ => add_nonneg
        (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)) w) (mul_nonneg (add_nonneg
        (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _)))
    by_cases hw : |w.1| ≤ |z.1| + 1
    · rw [Set.indicator_of_mem (show w ∈ {w : SpaceTime | |w.1| ≤ |z.1| + 1} from hw)]
      have e : |i3PsiPrincipal K Q z z' w v| =
          |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| * |Q (w - v)| ^ 3 := by
        unfold i3PsiPrincipal
        simp only [abs_mul, abs_pow]
      rw [e]
      have d1 := abs_dK_le hK a b
      have d2 := abs_dK_le hK a' b'
      have d3 := abs_Q_cube_le hQ c'
      have n1 : 0 ≤ B * (singularPow 3 z w + singularPow 3 0 w) :=
        mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
      have n2 : 0 ≤ B * (singularPow 3 z' v + singularPow 3 0 v) :=
        mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
      have key : |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| * |Q (w - v)| ^ 3 ≤
          (B * (singularPow 3 z w + singularPow 3 0 w)) *
            (B * (singularPow 3 z' v + singularPow 3 0 v)) * (B ^ 3 * singularPow 3 w v) :=
        mul_le_mul (mul_le_mul d1 d2 (abs_nonneg _) n1) d3 (pow_nonneg (abs_nonneg _) 3)
          (mul_nonneg n1 n2)
      refine key.trans (le_of_eq ?_)
      simp only [singularPow]
      ring
    · have e0 : K (z - w) - K (-w) = 0 := dK_eq_zero_of_abs_lt hKs (not_le.1 hw)
      have : i3PsiPrincipal K Q z z' w v = 0 := by
        unfold i3PsiPrincipal
        rw [e0]; ring
      rw [this, abs_zero]
      exact hnn)
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  ring

end RegularityStructures

end
