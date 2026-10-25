/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI3PsiDom
public import Phi43.BPHZ.SemigroupTestTreesI3PsiPrincipal
public import Phi43.BPHZ.TreeI3PsiCrossPrincipal

/-!
# The principal piece of the cross-mollifier difference diagram of `I(Ψ³)Ψ`, for arbitrary `z, z'`

`i3PsiPrincipal_majorant_integral_gen`: the principal integral for a dominated integrand with
`s(w - v)^(-(3+τ))`, `0 ≤ τ < 1`; `i3PsiDiffPiece2Cross_bound_global`: without Hölder gains (these
need `s(z), s(z') ≤ 1`) the principal piece is bounded by absolute values,
`C (max ε ε')^(2θ) (s(z - z')^(-1) + s(z - z')^(-(1+2θ))) (1 + |z.1|)`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- **Principal integral for a dominated integrand.** -/
theorem i3PsiPrincipal_majorant_integral_gen {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : SpaceTime → SpaceTime → ℝ} {Λ T : ℝ}, 0 ≤ Λ → 0 ≤ T →
      AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) →
      ∀ z z' : SpaceTime,
      (∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume, |F w v| ≤
        Λ * (Set.indicator {w : SpaceTime | |w.1| ≤ T}
            (fun w => singularPow 3 z w + singularPow 3 0 w) w *
          ((singularPow 3 z' v + singularPow 3 0 v) * singularPow (3 + τ) w v))) →
      Integrable (Function.uncurry F) (volume.prod volume) ∧
        |∫ w, ∫ v, F w v| ≤ C * Λ * (80 / (1 - τ) + 2 * T) := by
  obtain ⟨C1, hC1, h1⟩ := singularIntLe_mul_two (a := 3) (b := 3 + τ) (η := 1 + τ) (by norm_num)
    (by norm_num) (by linarith) (by linarith) (by linarith) (by ring)
  refine ⟨8 * C1, by positivity, ?_⟩
  intro F Λ T hΛ hT hmeas z z' hFG
  set S : Set SpaceTime := {w : SpaceTime | |w.1| ≤ T} with hS
  set m : SpaceTime → ℝ := Set.indicator S (fun w => singularPow 3 z w + singularPow 3 0 w) with hm
  have hm0 : ∀ w, 0 ≤ m w := fun w => Set.indicator_nonneg (fun w _ =>
    add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)) w
  have hmm : Measurable m := (((measurable_singularPow 3 z).add (measurable_singularPow 3 0))
    ).indicator (measurableSet_abs_fst_le T)
  have sl : ∀ c : SpaceTime, SingularIntLe (Set.indicator S (singularPow (4 + τ) c))
      (80 / (5 - (4 + τ)) + 2 * T) := fun c => singularIntLe_slab_singularPow (by linarith)
    (by linarith) hT c
  have hsum : SingularIntLe (fun w => 2 * Set.indicator S (singularPow (4 + τ) z) w +
      2 * Set.indicator S (singularPow (4 + τ) z') w + 4 * Set.indicator S (singularPow (4 + τ) 0) w)
      (2 * (80 / (5 - (4 + τ)) + 2 * T) + 2 * (80 / (5 - (4 + τ)) + 2 * T) + 4 * (80 / (5 - (4 + τ)) + 2 * T)) :=
    (((sl z).const_mul (c := 2) (by norm_num)).add ((sl z').const_mul (c := 2)
      (by norm_num))).add ((sl 0).const_mul (c := 4) (by norm_num))
  set H : SpaceTime → ℝ := fun w => (Λ * m w) * (C1 * (singularPow (1 + τ) z' w + singularPow (1 + τ) 0 w))
    with hH
  have hHle : SingularIntLe H (Λ * C1 * (2 * (80 / (5 - (4 + τ)) + 2 * T) +
      2 * (80 / (5 - (4 + τ)) + 2 * T) + 4 * (80 / (5 - (4 + τ)) + 2 * T))) := by
    refine ((hsum.const_mul (c := Λ * C1) (mul_nonneg hΛ hC1))).of_le ?_ ?_ ?_
    · exact (((measurable_const.mul hmm)).mul (measurable_const.mul
        ((measurable_singularPow (1 + τ) z').add (measurable_singularPow (1 + τ) 0)))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun w => mul_nonneg (mul_nonneg hΛ (hm0 w))
        (mul_nonneg hC1 (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)))
    · filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos z',
        ae_torusParabolicSize_sub_pos 0] with w a b c
      by_cases hw : w ∈ S
      · simp only [hH, hm, Set.indicator_of_mem hw]
        have e1 := singularPow_mul_le (a := 3) (b := 1 + τ) (by norm_num) (by linarith) a b
        have e2 := singularPow_mul_le (a := 3) (b := 1 + τ) (by norm_num) (by linarith) a c
        have e3 := singularPow_mul_le (a := 3) (b := 1 + τ) (by norm_num) (by linarith) c b
        have e4 := singularPow_mul_le (a := 3) (b := 1 + τ) (by norm_num) (by linarith) c c
        have hΛC : 0 ≤ Λ * C1 := mul_nonneg hΛ hC1
        have e5 : (3 : ℝ) + (1 + τ) = 4 + τ := by ring
        rw [e5] at e1 e2 e3 e4
        have : (singularPow 3 z w + singularPow 3 0 w) *
            (singularPow (1 + τ) z' w + singularPow (1 + τ) 0 w) ≤
            2 * singularPow (4 + τ) z w + 2 * singularPow (4 + τ) z' w + 4 * singularPow (4 + τ) 0 w := by
          calc _ = singularPow 3 z w * singularPow (1 + τ) z' w + singularPow 3 z w * singularPow (1 + τ) 0 w +
                singularPow 3 0 w * singularPow (1 + τ) z' w + singularPow 3 0 w * singularPow (1 + τ) 0 w := by
                ring
            _ ≤ _ := by linarith
        calc Λ * (singularPow 3 z w + singularPow 3 0 w) *
            (C1 * (singularPow (1 + τ) z' w + singularPow (1 + τ) 0 w))
            = Λ * C1 * ((singularPow 3 z w + singularPow 3 0 w) *
              (singularPow (1 + τ) z' w + singularPow (1 + τ) 0 w)) := by ring
          _ ≤ Λ * C1 * (2 * singularPow (4 + τ) z w + 2 * singularPow (4 + τ) z' w +
              4 * singularPow (4 + τ) 0 w) := mul_le_mul_of_nonneg_left this hΛC
      · simp [hH, hm, hw]
  -- the two-level argument
  have hG : ∀ᵐ w : SpaceTime ∂volume, Integrable (fun v =>
      (Λ * m w) * ((singularPow 3 z' v + singularPow 3 0 v) * singularPow (3 + τ) w v)) := by
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with w a b
    have i1 := (h1 z' w a).1
    have i2 := (h1 0 w b).1
    exact ((i1.add i2).congr (Filter.Eventually.of_forall fun v => by
      simp only [Pi.add_apply]; ring)).const_mul
      (Λ * m w)
  have hGH : ∀ᵐ w : SpaceTime ∂volume, ∫ v,
      (Λ * m w) * ((singularPow 3 z' v + singularPow 3 0 v) * singularPow (3 + τ) w v) ≤ H w := by
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with w a b
    have j1 := h1 z' w a
    have j2 := h1 0 w b
    have hs := j1.add j2
    have hnn : 0 ≤ Λ * m w := mul_nonneg hΛ (hm0 w)
    rw [integral_const_mul]
    have := hs.2
    simp only at this
    rw [show (∫ v, (singularPow 3 z' v + singularPow 3 0 v) * singularPow (3 + τ) w v) =
      ∫ v, (singularPow 3 z' v * singularPow (3 + τ) w v + singularPow 3 0 v * singularPow (3 + τ) w v) from
        integral_congr_ae (Filter.Eventually.of_forall fun v => by ring)]
    refine mul_le_mul_of_nonneg_left (this.trans (le_of_eq ?_)) hnn
    simp only [singularPow, zero_sub]
    ring_nf
  have hFG' : ∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume, |F w v| ≤
      (Λ * m w) * ((singularPow 3 z' v + singularPow 3 0 v) * singularPow (3 + τ) w v) := by
    filter_upwards [hFG] with w hw
    filter_upwards [hw] with v hv
    refine hv.trans (le_of_eq ?_)
    simp only [hm]
    ring
  obtain ⟨hint, hbd⟩ := integrable_prod_of_two_level (F := F) hmeas hG hGH hHle.1 hFG'
  refine ⟨hint, hbd.trans (hHle.2.trans (le_of_eq ?_))⟩
  have e6 : (5 : ℝ) - (4 + τ) = 1 - τ := by ring
  rw [e6]
  ring


end RegularityStructures

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **The principal piece of the difference diagram, for arbitrary `z, z'`.**  `D` bounds
`s(w - v)` on the slab `|w.1| ≤ |z.1| + 1`, `|v.1| ≤ |z'.1| + 1`. -/
theorem i3PsiDiffPiece2Cross_bound_global (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ z z' : SpaceTime, ∀ {D : ℝ}, 0 ≤ D →
        (∀ w v : SpaceTime, |w.1| ≤ |z.1| + 1 → |v.1| ≤ |z'.1| + 1 →
          torusParabolicSize (w - v) ≤ D) →
        0 < torusParabolicSize (z - z') →
        Integrable (Function.uncurry (i3PsiDiffPiece2Cross N ρ ρ' ε ε' z z')) (volume.prod volume) ∧
          |∫ w, ∫ v, i3PsiDiffPiece2Cross N ρ ρ' ε ε' z z' w v| ≤
            C * (max ε ε') ^ (2 * θ) * (torusParabolicSize (z - z') ^ (-(1 : ℝ)) +
              D ^ (2 * θ) * torusParabolicSize (z - z') ^ (-(1 + 2 * θ))) * (1 + |z.1|) := by
  obtain ⟨B, hB, hKm, hKs, hK, hinc⟩ := hairerKernelTorus_diagram_data N
  obtain ⟨K2, hK2, hD⟩ := i3PsiDiff_piece_two_abs_le_cross N ρ ρ' hρ hρ' hθ (by linarith)
  obtain ⟨Cg, hCg, hg⟩ := i3PsiPrincipal_majorant_integral_gen (τ := 2 * θ) (by linarith)
    (by linarith)
  refine ⟨Cg * B ^ 2 * K2 * 162, by positivity, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 z z' D hD0 hDs hzz
  have hM : 0 < max ε ε' := lt_max_of_lt_left hε
  have hm2 : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg hM.le _
  set m2 : ℝ := (max ε ε') ^ (2 * θ) with hm2def
  set X : ℝ := torusParabolicSize (z - z') ^ (-(1 : ℝ)) +
    D ^ (2 * θ) * torusParabolicSize (z - z') ^ (-(1 + 2 * θ)) with hX
  have hX0 : 0 ≤ X := add_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
    (mul_nonneg (Real.rpow_nonneg hD0 _) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have hΛ : 0 ≤ B ^ 2 * (K2 * m2 * X) := by positivity
  have hmeas : Measurable (fun p : SpaceTime × SpaceTime =>
      i3PsiDiffPiece2Cross N ρ ρ' ε ε' z z' p.1 p.2) := by
    unfold i3PsiDiffPiece2Cross i3PsiDiffD2Cross
    have h11 := measurable_hairerCrossCovarianceTwo N hρ hρ
    have h12 := measurable_hairerCrossCovarianceTwo N hρ hρ'
    have h21 := measurable_hairerCrossCovarianceTwo N hρ' hρ
    have h22 := measurable_hairerCrossCovarianceTwo N hρ' hρ'
    fun_prop
  have := hg (F := i3PsiDiffPiece2Cross N ρ ρ' ε ε' z z') (Λ := B ^ 2 * (K2 * m2 * X))
    (T := |z.1| + 1) hΛ (by positivity) hmeas.aestronglyMeasurable z z' (by
    filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0] with w a b
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos w] with v a' b' c'
    have hnn : 0 ≤ B ^ 2 * (K2 * m2 * X) * (Set.indicator {w : SpaceTime | |w.1| ≤ |z.1| + 1}
        (fun w => singularPow 3 z w + singularPow 3 0 w) w *
        ((singularPow 3 z' v + singularPow 3 0 v) * singularPow (3 + 2 * θ) w v)) := by
      refine mul_nonneg hΛ (mul_nonneg (Set.indicator_nonneg (fun w _ => add_nonneg
        (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)) w) (mul_nonneg (add_nonneg
        (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _)))
    by_cases hw : |w.1| ≤ |z.1| + 1
    · by_cases hv : |v.1| ≤ |z'.1| + 1
      · rw [Set.indicator_of_mem (show w ∈ {w : SpaceTime | |w.1| ≤ |z.1| + 1} from hw)]
        have e : |i3PsiDiffPiece2Cross N ρ ρ' ε ε' z z' w v| =
            |hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
              |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| *
              |i3PsiDiffD2Cross N ρ ρ' ε ε' (w - v) (z - z')| := by
          unfold i3PsiDiffPiece2Cross
          rw [abs_mul, abs_mul]
        rw [e]
        have hd := hD hε hε1 hε' hε'1 (w - v) (z - z') c' hzz
        have d1 := abs_dK_le hK a b
        have d2 := abs_dK_le hK a' b'
        have hsv := hDs w v hw hv
        have hs3 : torusParabolicSize (w - v) ^ (-(3 : ℝ)) ≤
            D ^ (2 * θ) * torusParabolicSize (w - v) ^ (-(3 + 2 * θ)) := by
          have hpow : torusParabolicSize (w - v) ^ (-(3 : ℝ)) =
              torusParabolicSize (w - v) ^ (2 * θ) * torusParabolicSize (w - v) ^ (-(3 + 2 * θ)) := by
            rw [← Real.rpow_add c']; congr 1; ring
          rw [hpow]
          exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow c'.le hsv (by linarith))
            (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        have hd' : |i3PsiDiffD2Cross N ρ ρ' ε ε' (w - v) (z - z')| ≤
            K2 * m2 * X * torusParabolicSize (w - v) ^ (-(3 + 2 * θ)) := by
          refine hd.trans ?_
          have n1 := Real.rpow_nonneg (torusParabolicSize_nonneg (z - z')) (-(1 + 2 * θ))
          have n2 := Real.rpow_nonneg (torusParabolicSize_nonneg (w - v)) (-(3 + 2 * θ))
          have key : torusParabolicSize (w - v) ^ (-(3 + 2 * θ)) *
              torusParabolicSize (z - z') ^ (-(1 : ℝ)) +
              torusParabolicSize (w - v) ^ (-(3 : ℝ)) *
                torusParabolicSize (z - z') ^ (-(1 + 2 * θ)) ≤
              X * torusParabolicSize (w - v) ^ (-(3 + 2 * θ)) := by
            rw [hX]
            linarith [mul_le_mul_of_nonneg_right hs3 n1]
          calc K2 * m2 * (torusParabolicSize (w - v) ^ (-(3 + 2 * θ)) *
                torusParabolicSize (z - z') ^ (-(1 : ℝ)) +
              torusParabolicSize (w - v) ^ (-(3 : ℝ)) *
                torusParabolicSize (z - z') ^ (-(1 + 2 * θ)))
              ≤ K2 * m2 * (X * torusParabolicSize (w - v) ^ (-(3 + 2 * θ))) :=
                mul_le_mul_of_nonneg_left key (mul_nonneg hK2 hm2)
            _ = _ := by ring
        have n1 : 0 ≤ B * (singularPow 3 z w + singularPow 3 0 w) :=
          mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
        have n2 : 0 ≤ B * (singularPow 3 z' v + singularPow 3 0 v) :=
          mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
        have key : |hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
            |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| *
              |i3PsiDiffD2Cross N ρ ρ' ε ε' (w - v) (z - z')| ≤
            (B * (singularPow 3 z w + singularPow 3 0 w)) *
              (B * (singularPow 3 z' v + singularPow 3 0 v)) *
                (K2 * m2 * X * torusParabolicSize (w - v) ^ (-(3 + 2 * θ))) :=
          mul_le_mul (mul_le_mul d1 d2 (abs_nonneg _) n1) hd' (abs_nonneg _) (mul_nonneg n1 n2)
        refine key.trans (le_of_eq ?_)
        simp only [singularPow]
        ring
      · have e0 : hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v) = 0 :=
          dK_eq_zero_of_abs_lt hKs (not_le.1 hv)
        have : i3PsiDiffPiece2Cross N ρ ρ' ε ε' z z' w v = 0 := by
          unfold i3PsiDiffPiece2Cross
          rw [e0]; ring
        rw [this, abs_zero]
        exact hnn
    · have e0 : hairerKernelTorus N (z - w) - hairerKernelTorus N (-w) = 0 :=
        dK_eq_zero_of_abs_lt hKs (not_le.1 hw)
      have : i3PsiDiffPiece2Cross N ρ ρ' ε ε' z z' w v = 0 := by
        unfold i3PsiDiffPiece2Cross
        rw [e0]; ring
      rw [this, abs_zero]
      exact hnn)
  refine ⟨this.1, this.2.trans ?_⟩
  have h80 : 80 / (1 - 2 * θ) ≤ 160 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have habs := abs_nonneg z.1
  have hbd : 80 / (1 - 2 * θ) + 2 * (|z.1| + 1) ≤ 162 * (1 + |z.1|) := by linarith
  calc Cg * (B ^ 2 * (K2 * m2 * X)) * (80 / (1 - 2 * θ) + 2 * (|z.1| + 1))
      ≤ Cg * (B ^ 2 * (K2 * m2 * X)) * (162 * (1 + |z.1|)) :=
        mul_le_mul_of_nonneg_left hbd (mul_nonneg hCg hΛ)
    _ = _ := by ring

end RegularityStructures.Phi43

end
