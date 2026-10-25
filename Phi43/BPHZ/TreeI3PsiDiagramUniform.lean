/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiDiagramSlab
public import Phi43.BPHZ.TreeI3PsiPrincipalBound

/-!
# The diagram bound for `I(Ψ³)Ψ`, uniform in the kernels

`i3PsiPairing_bound_uniform`: for `B ≥ 0`, `δ ∈ (0, 1/4]` there is a constant `C`, depending only on
`B, δ`, such that for **all** kernels `K, Q` satisfying the hypotheses of `i3PsiPairing_bound`
(except the time-support hypothesis on `Q`, which is not needed), the integrated diagram is bounded
as in `i3PsiPairing_bound`.  The uniformity in `(K, Q)` is what allows `Q = Q_ε` to vary with
`ε`.  The proofs are those of `i3PsiPrincipal_bound` and `i3PsiPairing_bound` with the order of the
quantifiers changed.

Source: [Hai14] = arXiv:1303.5113v4, (10.36)--(10.38), p. 167--168.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- The principal pairing is integrable with a Hölder-gain bound; the constant depends only on
`B, θ`, not on `K, Q`.  (Uniform form of `i3PsiPrincipal_bound`.) -/
theorem i3PsiPrincipal_bound_uniform {B θ : ℝ} (hB : 0 ≤ B) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ}, Measurable K →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      Measurable Q →
      (∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      ∀ z z' : SpaceTime, torusParabolicSize z ≤ 1 → torusParabolicSize z' ≤ 1 →
        Integrable (Function.uncurry (i3PsiPrincipal K Q z z')) (volume.prod volume) ∧
          |∫ w, ∫ v, i3PsiPrincipal K Q z z' w v| ≤ C * torusParabolicSize z' ^ θ := by
  obtain ⟨Cin, hCin, hin⟩ := singularIntLe_inner_principal hθ hθ1
  obtain ⟨Cs, hCs, hs⟩ := singularIntLe_slab_mul_two (a := 3) (b := 1 + θ) (by norm_num)
    (by linarith) (by linarith)
  refine ⟨48 * B ^ 5 * Cin * Cs, by positivity, ?_⟩
  intro K Q hKm hKs hK hinc hQm hQ z z' hz hz'
  have hs0 : torusParabolicSize (0 : SpaceTime) ≤ 1 := by
    rw [torusParabolicSize_zero_spaceTime]; norm_num
  have hP : 0 ≤ torusParabolicSize z' ^ θ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  set P : ℝ := torusParabolicSize z' ^ θ with hPdef
  -- the cut-off majorant of `δK(z, ·)`
  set S : Set SpaceTime := {w : SpaceTime | |w.1| ≤ 2} with hSdef
  let m : SpaceTime → ℝ := fun w => Set.indicator S
    (fun w => B * (singularPow 3 z w + singularPow 3 0 w)) w
  have hm0 : ∀ w, 0 ≤ m w := fun w => Set.indicator_nonneg (fun w _ =>
    mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))) w
  -- the six leaves
  have t1 := hs z z' hz hz'
  have t2 := hs z 0 hz hs0
  have t3 := hs 0 z' hs0 hz'
  have t4 := hs 0 0 hs0 hs0
  have hsum := ((t1.add t2).add t3).add t4
  have hH := (hsum.const_mul (c := 12 * B ^ 4 * P * Cin * B) (by positivity)).congr_fun
    (g := fun w => (m w * (12 * B ^ 4 * P)) *
      (Cin * (singularPow (1 + θ) z' w + singularPow (1 + θ) 0 w))) (fun w => by
      by_cases hw : w ∈ S
      · simp only [m, Set.indicator_of_mem hw]
        ring
      · simp only [m, Set.indicator_of_notMem hw]
        ring)
  have hmeas : Measurable (fun p : SpaceTime × SpaceTime =>
      i3PsiPrincipal K Q z z' p.1 p.2) := by
    unfold i3PsiPrincipal
    fun_prop
  have hG : ∀ᵐ w : SpaceTime ∂volume, Integrable (fun v =>
      (m w * (12 * B ^ 4 * P)) * ((singularPow (3 + θ) z' v + singularPow (3 + θ) 0 v) *
        singularPow 3 w v)) := by
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with w a b
    exact ((hin z' 0 w a b).1).const_mul _
  have hGH : ∀ᵐ w : SpaceTime ∂volume, ∫ v, (m w * (12 * B ^ 4 * P)) *
      ((singularPow (3 + θ) z' v + singularPow (3 + θ) 0 v) * singularPow 3 w v) ≤
      (m w * (12 * B ^ 4 * P)) *
        (Cin * (singularPow (1 + θ) z' w + singularPow (1 + θ) 0 w)) := by
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with w a b
    have := (hin z' 0 w a b).2
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left this (mul_nonneg (hm0 w) (by positivity))
  have hFG : ∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume,
      |i3PsiPrincipal K Q z z' w v| ≤ (m w * (12 * B ^ 4 * P)) *
        ((singularPow (3 + θ) z' v + singularPow (3 + θ) 0 v) * singularPow 3 w v) := by
    filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0] with w a b
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos w] with v a' b' c'
    have nn : 0 ≤ (m w * (12 * B ^ 4 * P)) *
        ((singularPow (3 + θ) z' v + singularPow (3 + θ) 0 v) * singularPow 3 w v) :=
      mul_nonneg (mul_nonneg (hm0 w) (by positivity)) (mul_nonneg
        (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
        (singularPow_nonneg _ _ _))
    by_cases hw : w ∈ S
    · have d1 := abs_dK_le hK a b
      have d2 := abs_dK_le_holder hB hθ.le hθ1.le hK hinc a' b'
      have d3 := abs_Q_cube_le hQ c'
      have e : |i3PsiPrincipal K Q z z' w v| =
          |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| * |Q (w - v)| ^ 3 := by
        unfold i3PsiPrincipal
        simp only [abs_mul, abs_pow]
      rw [e]
      have n1 : 0 ≤ B * (singularPow 3 z w + singularPow 3 0 w) :=
        mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
      have n2 : 0 ≤ 12 * B * P * (singularPow (3 + θ) z' v + singularPow (3 + θ) 0 v) :=
        mul_nonneg (by positivity) (add_nonneg (singularPow_nonneg _ _ _)
          (singularPow_nonneg _ _ _))
      have key : |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| * |Q (w - v)| ^ 3 ≤
          (B * (singularPow 3 z w + singularPow 3 0 w)) *
            (12 * B * P * (singularPow (3 + θ) z' v + singularPow (3 + θ) 0 v)) *
              (B ^ 3 * singularPow 3 w v) :=
        mul_le_mul (mul_le_mul d1 d2 (abs_nonneg _) n1) d3 (pow_nonneg (abs_nonneg _) 3)
          (mul_nonneg n1 n2)
      refine key.trans (le_of_eq ?_)
      simp only [m, Set.indicator_of_mem hw]
      ring
    · have hw2 : 2 < |w.1| := not_le.1 hw
      have e0 := dK_eq_zero_of_two_lt hKs hz hw2
      have : i3PsiPrincipal K Q z z' w v = 0 := by
        unfold i3PsiPrincipal
        rw [e0]; ring
      rw [this, abs_zero]
      exact nn
  obtain ⟨hint, hbd⟩ := integrable_prod_of_two_level
    (F := fun w v => i3PsiPrincipal K Q z z' w v)
    hmeas.aestronglyMeasurable hG hGH hH.1 hFG
  refine ⟨hint, hbd.trans (hH.2.trans (le_of_eq ?_))⟩
  rw [hPdef]
  ring

/-- **Deterministic diagram bound for `I(Ψ³)Ψ`, uniform in `K, Q`** ([Hai14, (10.36)--(10.38)]):
no time support hypothesis on `Q`, and the constant depends only on `B, δ`. -/
theorem i3PsiPairing_bound_uniform {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ}, Measurable K →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      Measurable Q →
      (∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      ∀ z z' : SpaceTime, 0 < torusParabolicSize z → 0 < torusParabolicSize z' →
        0 < torusParabolicSize (z - z') → torusParabolicSize z ≤ 1 → torusParabolicSize z' ≤ 1 →
          Integrable (Function.uncurry (i3PsiDiagramIntegrand K Q z z')) (volume.prod volume) ∧
            |i3PsiPairing K Q z z'| ≤ C * (torusParabolicSize (z - z') ^ (-δ) +
              torusParabolicSize z ^ (-δ) + torusParabolicSize z' ^ (-δ) +
              torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
                (torusParabolicSize z ^ (1 - δ) + torusParabolicSize z' ^ (1 - δ))) := by
  obtain ⟨CA, hCA, hA⟩ := i3PsiChain_bound_uniform hB hδ hδ1
  obtain ⟨CP, hCP, hP⟩ := i3PsiPrincipal_bound_uniform (B := B) (θ := 1 - δ) hB
    (by linarith) (by linarith)
  refine ⟨36 * CA + 6 * B * CP, by positivity, ?_⟩
  intro K Q hKm hKs hK hinc hQm hQ z z' hz hz' hzz hz1 hz1'
  obtain ⟨iA, bA⟩ := hA hKm hK hKs hQm hQ z z' z z' hzz hz hz' hz1 hz1' (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨iC, bC⟩ := hA hKm hK hKs hQm hQ z z' z' z hzz hz hz' hz1 hz1' (Or.inr ⟨rfl, rfl⟩)
  obtain ⟨iP, bP⟩ := hP hKm hKs hK hinc hQm hQ z z' hz1 hz1'
  have iF : Integrable (Function.uncurry (i3PsiDiagramIntegrand K Q z z')) (volume.prod volume) := by
    have := (iA.const_mul 18).add ((iP.const_mul (6 * Q (z - z'))).add (iC.const_mul 18))
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Pi.add_apply, i3PsiDiagramIntegrand_eq]
    ring
  refine ⟨iF, ?_⟩
  have key : ∀ G : SpaceTime → SpaceTime → ℝ,
      Integrable (Function.uncurry G) (volume.prod volume) →
        ∫ p, Function.uncurry G p ∂(volume.prod volume) = ∫ w, ∫ v, G w v :=
    fun G hG => integral_prod _ hG
  have hT : i3PsiPairing K Q z z' =
      18 * (∫ w, ∫ v, i3PsiChain K Q z z' z z' w v) +
        6 * Q (z - z') * (∫ w, ∫ v, i3PsiPrincipal K Q z z' w v) +
          18 * (∫ w, ∫ v, i3PsiChain K Q z z' z' z w v) := by
    unfold i3PsiPairing
    rw [← key _ iF, ← key _ iA, ← key _ iP, ← key _ iC]
    have hA' : Integrable (fun p => 18 * Function.uncurry (i3PsiChain K Q z z' z z') p)
        (volume.prod volume) := iA.const_mul 18
    have hP' : Integrable (fun p => 6 * Q (z - z') *
        Function.uncurry (i3PsiPrincipal K Q z z') p) (volume.prod volume) :=
      iP.const_mul (6 * Q (z - z'))
    have hC' : Integrable (fun p => 18 * Function.uncurry (i3PsiChain K Q z z' z' z) p)
        (volume.prod volume) := iC.const_mul 18
    have hAP : Integrable (fun p => 18 * Function.uncurry (i3PsiChain K Q z z' z z') p +
        6 * Q (z - z') * Function.uncurry (i3PsiPrincipal K Q z z') p) (volume.prod volume) :=
      hA'.add hP'
    have e : Function.uncurry (i3PsiDiagramIntegrand K Q z z') = fun p =>
        18 * Function.uncurry (i3PsiChain K Q z z' z z') p +
          6 * Q (z - z') * Function.uncurry (i3PsiPrincipal K Q z z') p +
            18 * Function.uncurry (i3PsiChain K Q z z' z' z) p := by
      funext p
      exact i3PsiDiagramIntegrand_eq K Q z z' p.1 p.2
    rw [e, integral_add hAP hC', integral_add hA' hP', integral_const_mul,
      integral_const_mul, integral_const_mul]
  have hS0 : 0 ≤ torusParabolicSize (z - z') ^ (-δ) + torusParabolicSize z ^ (-δ) +
      torusParabolicSize z' ^ (-δ) := by
    have a1 : 0 ≤ torusParabolicSize (z - z') ^ (-δ) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have a2 : 0 ≤ torusParabolicSize z ^ (-δ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have a3 : 0 ≤ torusParabolicSize z' ^ (-δ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    linarith
  have hQzz := hQ (z - z') hzz
  have hinv : 0 ≤ torusParabolicSize (z - z') ^ (-(1 : ℝ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hz1p : 0 ≤ torusParabolicSize z ^ (1 - δ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hz1p' : 0 ≤ torusParabolicSize z' ^ (1 - δ) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  set S : ℝ := torusParabolicSize (z - z') ^ (-δ) + torusParabolicSize z ^ (-δ) +
    torusParabolicSize z' ^ (-δ) with hSdef
  have bP' : |6 * Q (z - z') * ∫ w, ∫ v, i3PsiPrincipal K Q z z' w v| ≤
      6 * B * CP * (torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
        torusParabolicSize z' ^ (1 - δ)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    calc 6 * |Q (z - z')| * |∫ w, ∫ v, i3PsiPrincipal K Q z z' w v|
        ≤ 6 * (B * torusParabolicSize (z - z') ^ (-(1 : ℝ))) *
            (CP * torusParabolicSize z' ^ (1 - δ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hQzz (by norm_num)) bP (abs_nonneg _)
            (mul_nonneg (by norm_num) (mul_nonneg hB hinv))
      _ = _ := by ring
  have hbound : |i3PsiPairing K Q z z'| ≤
      36 * CA * S + 6 * B * CP * (torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
          torusParabolicSize z' ^ (1 - δ)) := by
    rw [hT]
    have t1 := abs_add_le (18 * (∫ w, ∫ v, i3PsiChain K Q z z' z z' w v) +
      6 * Q (z - z') * (∫ w, ∫ v, i3PsiPrincipal K Q z z' w v))
      (18 * (∫ w, ∫ v, i3PsiChain K Q z z' z' z w v))
    have t2 := abs_add_le (18 * (∫ w, ∫ v, i3PsiChain K Q z z' z z' w v))
      (6 * Q (z - z') * (∫ w, ∫ v, i3PsiPrincipal K Q z z' w v))
    have t3 : |18 * (∫ w, ∫ v, i3PsiChain K Q z z' z z' w v)| ≤ 18 * (CA * S) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 18)]
      exact mul_le_mul_of_nonneg_left bA (by norm_num)
    have t4 : |18 * (∫ w, ∫ v, i3PsiChain K Q z z' z' z w v)| ≤ 18 * (CA * S) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 18)]
      exact mul_le_mul_of_nonneg_left bC (by norm_num)
    linarith
  refine hbound.trans ?_
  have hY : torusParabolicSize (z - z') ^ (-(1 : ℝ)) * torusParabolicSize z' ^ (1 - δ) ≤
      torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
        (torusParabolicSize z ^ (1 - δ) + torusParabolicSize z' ^ (1 - δ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hinv
  have hY0 : 0 ≤ torusParabolicSize (z - z') ^ (-(1 : ℝ)) * torusParabolicSize z' ^ (1 - δ) :=
    mul_nonneg hinv hz1p'
  generalize torusParabolicSize (z - z') ^ (-(1 : ℝ)) * torusParabolicSize z' ^ (1 - δ) = Y
    at hY hY0 ⊢
  generalize torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
    (torusParabolicSize z ^ (1 - δ) + torusParabolicSize z' ^ (1 - δ)) = Y' at hY ⊢
  have hBCP : 0 ≤ 6 * B * CP := by positivity
  linarith [mul_nonneg hBCP hS0, mul_nonneg hBCP (sub_nonneg.2 hY), mul_nonneg hCA (hY0.trans hY)]

end RegularityStructures

end
