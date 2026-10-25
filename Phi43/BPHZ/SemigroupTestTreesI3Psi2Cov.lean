/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI3Psi2Chaos1
public import Phi43.BPHZ.SemigroupTestTreesI3Psi2N1
public import Phi43.BPHZ.SemigroupTestTreesI3Psi2N2
public import Phi43.BPHZ.SemigroupTestTreesClean
public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Alg
public import Phi43.BPHZ.SemigroupTestTreesI3Psi2Alg
public import Phi43.BPHZ.SemigroupTestTreesI3PsiPrincipal
public import Phi43.BPHZ.TreeI3Psi2DiagramCov

/-!
# The global covariance bound of `I(Ψ³)Ψ²`: abstract form

`i3Psi2Cov_bound_global`: for kernels as in `i3Psi2Cov_bound_uniform` (without the Hölder increments
of `K`), arbitrary `z, z'` and `D` bounding `s(a - b)` on the time window
`|a.1|, |b.1| ≤ |z.1| + |z'.1| + 2`,
`|i3Psi2Cov K Q c z z'| ≤ C (1 + D)² (1 + |z.1| + |z'.1|) treeTheta z z'`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Global covariance bound for `I(Ψ³)Ψ²`, abstract form.** -/
theorem i3Psi2Cov_bound_global {B : ℝ} (hB : 0 ≤ B) :
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
      ∀ z z' : SpaceTime,
      (∀ a b : SpaceTime, |a.1| ≤ |z.1| + |z'.1| + 2 → |b.1| ≤ |z.1| + |z'.1| + 2 →
        torusParabolicSize (a - b) ≤ D) →
      0 < torusParabolicSize z → 0 < torusParabolicSize z' → 0 < torusParabolicSize (z - z') →
        |i3Psi2Cov K Q c z z'| ≤ C * ((1 + D) ^ 2 * (1 + |z.1| + |z'.1|)) * treeTheta z z' := by
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  have hδ1 : (1 / 4 : ℝ) ≤ 1 / 4 := le_rfl
  obtain ⟨C0, hC0, hch⟩ := i3PsiChain_bound_global hB hδ hδ1
  obtain ⟨Cp, hCp, hpr⟩ := i3PsiPrincipal_bound_global hB
  obtain ⟨CN1, hCN1, hN1⟩ := i3Psi2N1_bound_global hB hδ hδ1
  obtain ⟨CN2, hCN2, hN2⟩ := i3Psi2N2_bound_global hB hδ hδ1
  obtain ⟨Cc1, hCc1, hc1⟩ := i3Psi2Chaos1Total_raw_global hB hδ hδ1
  refine ⟨984 * B ^ 2 * Cp + 864 * B * C0 + 108 * CN1 + 432 * CN2 + 24 * Cc1,
    by positivity, ?_⟩
  intro K J Q M c D hD0 hKm hKs hK hJm hJ hJinc hJb hJi hQm hQ hQJ hc z z' hDall hz hz' hzz
  have hQe := i3Psi2_Q_neg hQJ
  have hz0 : 0 ≤ |z.1| := abs_nonneg _
  have hz0' : 0 ≤ |z'.1| := abs_nonneg _
  have hDc : ∀ w v : SpaceTime, |w.1| ≤ |z.1| + 1 → |v.1| ≤ |z'.1| + 1 →
      torusParabolicSize (w - v) ≤ D := fun w v hw hv => hDall w v (by linarith) (by linarith)
  have hDn1 : ∀ w : SpaceTime, |w.1| ≤ |z.1| + 1 → torusParabolicSize (z' - w) ≤ D :=
    fun w hw => hDall z' w (by linarith) (by linarith)
  have hDn2 : ∀ w : SpaceTime, |w.1| ≤ |z.1| + 1 → torusParabolicSize (z - w) ≤ D :=
    fun w hw => hDall z w (by linarith) (by linarith)
  have hDz : ∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (z - w) ≤ D :=
    fun w hw => hDall z w (by linarith) (by linarith)
  have hDz' : ∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (z' - w) ≤ D :=
    fun w hw => hDall z' w (by linarith) (by linarith)
  obtain ⟨iA, bA⟩ := hch hKm hK hKs hQm hQ z z' z' z hD0 hDc hzz hz hz' (Or.inr ⟨rfl, rfl⟩)
  obtain ⟨iC, bC⟩ := hch hKm hK hKs hQm hQ z z' z z' hD0 hDc hzz hz hz' (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨iP, bP⟩ := hpr hKm hK hKs hQm hQ z z'
  obtain ⟨iN1, bN1⟩ := hN1 hKm hK hKs hQm hQ hQe z z' hD0 hDn1 hzz hz hz'
  obtain ⟨iN2, bN2⟩ := hN2 hKm hK hKs hQm hQ hQe z z' hD0 hDn2 hzz hz hz'
  have bCh := hc1 hD0 hKm hKs hK hJm hJ hJinc hJb hJi hQm hQ hQJ hc z z' hDz hDz' hz hz' hzz
  obtain ⟨iF5, hI5⟩ := integrable_double_of_three
    (F := fun w v => i3Psi2dK K z w * i3Psi2dK K z' v * i3Psi2Chaos5 Q z z' w v)
    (a := 12 * Q (z - z') ^ 2) (b := 72 * Q (z - z')) (c := 36)
    (fun w v => i3Psi2_integrand5_eq K Q hQe z z' w v) iP iA iN1
  obtain ⟨iF3, hI3⟩ := integrable_double_of_two
    (F := fun w v => i3Psi2dK K z w * i3Psi2dK K z' v * i3Psi2Chaos3 Q z z' w v)
    (a := 72 * Q (z - z')) (b := 144)
    (fun w v => i3Psi2_integrand3_eq K Q hQe z z' w v) iC iN2
  rw [i3Psi2Cov_eq]
  unfold i3Psi2Double
  rw [hI5, hI3]
  -- singular quantities
  have hd : 0 < torusParabolicSize (z - z') := hzz
  have pz0 : 0 < torusParabolicSize (z - 0) := by rwa [sub_zero]
  have pz'0 : 0 < torusParabolicSize (z' - 0) := by rwa [sub_zero]
  have hΘ1 := treeTheta_ge_one z z'
  have hΘd : torusParabolicSize (z - z') ^ (-(5 / 2 : ℝ)) + 1 ≤ treeTheta z z' := by
    unfold treeTheta
    have := Real.rpow_nonneg hz.le (-(5 / 2 : ℝ))
    have := Real.rpow_nonneg hz'.le (-(5 / 2 : ℝ))
    linarith
  have hΘz : torusParabolicSize z ^ (-(5 / 2 : ℝ)) + 1 ≤ treeTheta z z' := by
    unfold treeTheta
    have := Real.rpow_nonneg hd.le (-(5 / 2 : ℝ))
    have := Real.rpow_nonneg hz'.le (-(5 / 2 : ℝ))
    linarith
  have hΘz' : torusParabolicSize z' ^ (-(5 / 2 : ℝ)) + 1 ≤ treeTheta z z' := by
    unfold treeTheta
    have := Real.rpow_nonneg hd.le (-(5 / 2 : ℝ))
    have := Real.rpow_nonneg hz.le (-(5 / 2 : ℝ))
    linarith
  have sing : ∀ {s : ℝ} (e : ℝ), 0 < s → 0 ≤ e → e ≤ 5 / 2 →
      s ^ (-(5 / 2 : ℝ)) + 1 ≤ treeTheta z z' → s ^ (-e) ≤ treeTheta z z' :=
    fun e hs he he' h => (rpow_neg_le_five_halves_add_one hs he he').trans h
  have prod : ∀ {s t : ℝ} (a b : ℝ), 0 < s → 0 < t → 0 ≤ a → 0 ≤ b → a ≤ 5 / 4 → b ≤ 5 / 4 →
      s ^ (-(5 / 2 : ℝ)) + 1 ≤ treeTheta z z' → t ^ (-(5 / 2 : ℝ)) + 1 ≤ treeTheta z z' →
      s ^ (-a) * t ^ (-b) ≤ 2 * treeTheta z z' := by
    intro s t a b hs ht ha hb ha' hb' h1 h2
    have := rpow_neg_mul_rpow_neg_le_clean hs ht ha hb ha' hb'
    linarith
  set Θ := treeTheta z z' with hΘ
  set U : ℝ := D ^ (1 / 4 : ℝ) with hU
  have hU0 : 0 ≤ U := Real.rpow_nonneg hD0 _
  have hUD : U ≤ 1 + D := rpow_quarter_le_one_add hD0
  have n0 : ∀ s e : ℝ, 0 ≤ s → 0 ≤ s ^ e := fun s e hs => Real.rpow_nonneg hs e
  have hdd' : torusParabolicSize (z - z') ^ (-(2 : ℝ)) ≤ Θ :=
    sing 2 hd (by norm_num) (by norm_num) hΘd
  have hq : torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
      (torusParabolicSize (z - z') ^ (-(1 / 4 : ℝ)) + torusParabolicSize z ^ (-(1 / 4 : ℝ)) +
        torusParabolicSize z' ^ (-(1 / 4 : ℝ))) ≤ 6 * Θ := by
    have a1 := prod 1 (1 / 4) hd hd (by norm_num) (by norm_num) (by norm_num) (by norm_num) hΘd hΘd
    have a2 := prod 1 (1 / 4) hd hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) hΘd hΘz
    have a3 := prod 1 (1 / 4) hd hz' (by norm_num) (by norm_num) (by norm_num) (by norm_num) hΘd
      hΘz'
    linarith [mul_add (torusParabolicSize (z - z') ^ (-(1 : ℝ))
      ) (torusParabolicSize (z - z') ^ (-(1 / 4 : ℝ)) + torusParabolicSize z ^ (-(1 / 4 : ℝ)))
      (torusParabolicSize z' ^ (-(1 / 4 : ℝ))), mul_add (torusParabolicSize (z - z') ^ (-(1 : ℝ)))
      (torusParabolicSize (z - z') ^ (-(1 / 4 : ℝ))) (torusParabolicSize z ^ (-(1 / 4 : ℝ)))]
  have hSe : i3Psi2S (1 + 1 / 4) z z' ≤ 3 * Θ := by
    unfold i3Psi2S
    rw [sub_zero, sub_zero]
    have := sing (1 + 1 / 4) hd (by norm_num) (by norm_num) hΘd
    have := sing (1 + 1 / 4) hz (by norm_num) (by norm_num) hΘz
    have := sing (1 + 1 / 4) hz' (by norm_num) (by norm_num) hΘz'
    linarith
  have hSc : torusParabolicSize (z - z') ^ (-(1 + 1 / 4 : ℝ)) +
      torusParabolicSize z' ^ (-(1 + 1 / 4 + 1 / 4 / 2 : ℝ)) +
      torusParabolicSize z ^ (-(1 + 1 / 4 + 1 / 4 / 2 : ℝ)) +
      torusParabolicSize z ^ (-(1 + 1 / 4 : ℝ)) * torusParabolicSize z' ^ (-(1 / 4 : ℝ)) +
      torusParabolicSize z' ^ (-(1 + 2 * (1 / 4) : ℝ)) ≤ 6 * Θ := by
    have a1 := sing (1 + 1 / 4) hd (by norm_num) (by norm_num) hΘd
    have a2 := sing (1 + 1 / 4 + 1 / 4 / 2) hz' (by norm_num) (by norm_num) hΘz'
    have a3 := sing (1 + 1 / 4 + 1 / 4 / 2) hz (by norm_num) (by norm_num) hΘz
    have a4 := prod (1 + 1 / 4) (1 / 4) hz hz' (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hΘz hΘz'
    have a5 := sing (1 + 2 * (1 / 4)) hz' (by norm_num) (by norm_num) hΘz'
    linarith
  have hc1' : |Q (z - z')| ≤ B * torusParabolicSize (z - z') ^ (-(1 : ℝ)) := hQ _ hzz
  have hc2' : Q (z - z') ^ 2 ≤ B ^ 2 * torusParabolicSize (z - z') ^ (-(2 : ℝ)) :=
    sq_cov_le hQ hzz
  have hpa : |∫ w, ∫ v, i3PsiPrincipal K Q z z' w v| ≤ Cp * (82 + 2 * |z.1|) := by
    refine bP.trans (le_of_eq ?_); ring
  have key := i3Psi2_combine (B := B) (Cp := Cp) (C0 := C0) (CN1 := CN1) (CN2 := CN2)
    (Cc1 := Cc1) (D := D) (U := U) (tz := |z.1|) (tz' := |z'.1|) (Θ := Θ)
    (d1 := torusParabolicSize (z - z') ^ (-(1 : ℝ)))
    (dd := torusParabolicSize (z - z') ^ (-(2 : ℝ)))
    (a := torusParabolicSize (z - z') ^ (-(1 / 4 : ℝ)) + torusParabolicSize z ^ (-(1 / 4 : ℝ)) +
      torusParabolicSize z' ^ (-(1 / 4 : ℝ)))
    (Se := i3Psi2S (1 + 1 / 4) z z')
    (Sc := torusParabolicSize (z - z') ^ (-(1 + 1 / 4 : ℝ)) +
      torusParabolicSize z' ^ (-(1 + 1 / 4 + 1 / 4 / 2 : ℝ)) +
      torusParabolicSize z ^ (-(1 + 1 / 4 + 1 / 4 / 2 : ℝ)) +
      torusParabolicSize z ^ (-(1 + 1 / 4 : ℝ)) * torusParabolicSize z' ^ (-(1 / 4 : ℝ)) +
      torusParabolicSize z' ^ (-(1 + 2 * (1 / 4) : ℝ)))
    (T1 := 12 * Q (z - z') ^ 2 * ∫ w, ∫ v, i3PsiPrincipal K Q z z' w v)
    (T2 := 72 * Q (z - z') * ∫ w, ∫ v, i3PsiChain K Q z z' z' z w v)
    (T3 := 36 * ∫ w, ∫ v, i3Psi2N1 K Q z z' w v)
    (T4 := 72 * Q (z - z') * ∫ w, ∫ v, i3PsiChain K Q z z' z z' w v)
    (T5 := 144 * ∫ w, ∫ v, i3Psi2N2 K Q z z' w v)
    (T6 := i3Psi2Chaos1Total K Q c z z') hB hCp hC0 hCN1 hCN2 hCc1 hD0 hU0 hUD (abs_nonneg _)
    (abs_nonneg _) (treeTheta_nonneg z z') (n0 _ _ (torusParabolicSize_nonneg _))
    (n0 _ _ (torusParabolicSize_nonneg _)) (add_nonneg (add_nonneg
      (n0 _ _ (torusParabolicSize_nonneg _)) (n0 _ _ (torusParabolicSize_nonneg _)))
      (n0 _ _ (torusParabolicSize_nonneg _))) hdd' hq hSe (i3Psi2S_nonneg _ _ _) hSc
    (by
      have := n0 (torusParabolicSize (z - z')) (-(1 + 1 / 4 : ℝ)) (torusParabolicSize_nonneg _)
      have := n0 (torusParabolicSize z') (-(1 + 1 / 4 + 1 / 4 / 2 : ℝ)) (torusParabolicSize_nonneg _)
      have := n0 (torusParabolicSize z) (-(1 + 1 / 4 + 1 / 4 / 2 : ℝ)) (torusParabolicSize_nonneg _)
      have := mul_nonneg (n0 (torusParabolicSize z) (-(1 + 1 / 4 : ℝ)) (torusParabolicSize_nonneg _))
        (n0 (torusParabolicSize z') (-(1 / 4 : ℝ)) (torusParabolicSize_nonneg _))
      have := n0 (torusParabolicSize z') (-(1 + 2 * (1 / 4) : ℝ)) (torusParabolicSize_nonneg _)
      linarith)
    (by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 12 * Q (z - z') ^ 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hc2' (by norm_num)) hpa (abs_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg B) (n0 _ _ (torusParabolicSize_nonneg _)))))
    (by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 72)]
      calc 72 * |Q (z - z')| * |∫ w, ∫ v, i3PsiChain K Q z z' z' z w v|
          ≤ 72 * (B * torusParabolicSize (z - z') ^ (-(1 : ℝ))) *
            (C0 * D ^ (1 / 4 : ℝ) * (torusParabolicSize (z - z') ^ (-(1 / 4 : ℝ)) +
              torusParabolicSize z ^ (-(1 / 4 : ℝ)) + torusParabolicSize z' ^ (-(1 / 4 : ℝ)))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hc1' (by norm_num)) bA (abs_nonneg _)
              (mul_nonneg (by norm_num) (mul_nonneg hB (n0 _ _ (torusParabolicSize_nonneg _))))
        _ = _ := by ring)
    (by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 36)]
      calc 36 * |∫ w, ∫ v, i3Psi2N1 K Q z z' w v|
          ≤ 36 * (CN1 * D ^ (1 / 4 : ℝ) * i3Psi2S (1 + 1 / 4) z z') :=
            mul_le_mul_of_nonneg_left bN1 (by norm_num)
        _ = _ := by ring)
    (by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 72)]
      calc 72 * |Q (z - z')| * |∫ w, ∫ v, i3PsiChain K Q z z' z z' w v|
          ≤ 72 * (B * torusParabolicSize (z - z') ^ (-(1 : ℝ))) *
            (C0 * D ^ (1 / 4 : ℝ) * (torusParabolicSize (z - z') ^ (-(1 / 4 : ℝ)) +
              torusParabolicSize z ^ (-(1 / 4 : ℝ)) + torusParabolicSize z' ^ (-(1 / 4 : ℝ)))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hc1' (by norm_num)) bC (abs_nonneg _)
              (mul_nonneg (by norm_num) (mul_nonneg hB (n0 _ _ (torusParabolicSize_nonneg _))))
        _ = _ := by ring)
    (by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 144)]
      calc 144 * |∫ w, ∫ v, i3Psi2N2 K Q z z' w v|
          ≤ 144 * (CN2 * D ^ (1 / 4 : ℝ) * i3Psi2S (1 + 1 / 4) z z') :=
            mul_le_mul_of_nonneg_left bN2 (by norm_num)
        _ = _ := by ring)
    (by exact bCh)
  have e : 12 * Q (z - z') ^ 2 * (∫ w, ∫ v, i3PsiPrincipal K Q z z' w v) +
      72 * Q (z - z') * (∫ w, ∫ v, i3PsiChain K Q z z' z' z w v) +
      36 * (∫ w, ∫ v, i3Psi2N1 K Q z z' w v) +
      (72 * Q (z - z') * (∫ w, ∫ v, i3PsiChain K Q z z' z z' w v) +
        144 * (∫ w, ∫ v, i3Psi2N2 K Q z z' w v)) + i3Psi2Chaos1Total K Q c z z' =
      12 * Q (z - z') ^ 2 * (∫ w, ∫ v, i3PsiPrincipal K Q z z' w v) +
      72 * Q (z - z') * (∫ w, ∫ v, i3PsiChain K Q z z' z' z w v) +
      36 * (∫ w, ∫ v, i3Psi2N1 K Q z z' w v) +
      72 * Q (z - z') * (∫ w, ∫ v, i3PsiChain K Q z z' z z' w v) +
      144 * (∫ w, ∫ v, i3Psi2N2 K Q z z' w v) + i3Psi2Chaos1Total K Q c z z' := by ring
  rw [e]
  exact key

end RegularityStructures

end
