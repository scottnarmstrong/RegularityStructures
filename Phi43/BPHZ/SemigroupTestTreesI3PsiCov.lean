/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI3PsiPrincipal
public import Phi43.BPHZ.TreeI3PsiTestedPairing

/-!
# The global covariance bound for `I₃Ψ`

`i3PsiPairing_bound_global`: for kernels `K, Q` as in `i3PsiPairing_bound_uniform` and arbitrary
`z, z'` (no smallness) and `D` bounding `s(w - v)` on the relevant slab,
`|i3PsiPairing K Q z z'| ≤ C (1 + D + |z.1|) (s(z - z')^(-1) + s(z - z')^(-δ) + s(z)^(-δ) + s(z')^(-δ))`.

`hairerI3PsiField_cov_bound_global` transfers this to the field `I₃Ψ_x` of the regularised noise,
uniformly in `ε ∈ (0, 1]`: for all `x, y, y'` (distinct)
`|E[I₃Ψ_x(y) I₃Ψ_x(y')]| ≤ C (1 + s(y - x)² + s(y' - x)²)
  (s(y - y')^(-1) + s(y - y')^(-δ) + s(y - x)^(-δ) + s(y' - x)^(-δ))`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures

theorem rpow_le_one_add_self {D δ : ℝ} (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    D ^ δ ≤ 1 + D := by
  rcases le_total D 1 with h | h
  · have := Real.rpow_le_one hD h hδ
    linarith
  · have : D ^ δ ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hδ1
    rw [Real.rpow_one] at this
    linarith

/-- **Global deterministic bound for the diagram of `I(Ψ³)Ψ`.** -/
theorem i3PsiPairing_bound_global {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ}, Measurable K →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) → Measurable Q →
      (∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      ∀ (z z' : SpaceTime) {D : ℝ}, 0 ≤ D →
      (∀ w v : SpaceTime, |w.1| ≤ |z.1| + 1 → |v.1| ≤ |z'.1| + 1 →
        torusParabolicSize (w - v) ≤ D) →
      0 < torusParabolicSize (z - z') → 0 < torusParabolicSize z → 0 < torusParabolicSize z' →
        |i3PsiPairing K Q z z'| ≤ C * (1 + D + |z.1|) * (torusParabolicSize (z - z') ^ (-(1 : ℝ)) +
          torusParabolicSize (z - z') ^ (-δ) + torusParabolicSize z ^ (-δ) +
          torusParabolicSize z' ^ (-δ)) := by
  obtain ⟨C0, hC0, h0⟩ := i3PsiChain_bound_global hB hδ hδ1
  obtain ⟨Cp, hCp, hp⟩ := i3PsiPrincipal_bound_global hB
  refine ⟨36 * C0 + 6 * B * Cp * 82, by positivity, ?_⟩
  intro K Q hKm hK hKs hQm hQ z z' D hD0 hD hzz hz hz'
  obtain ⟨iA, bA⟩ := h0 hKm hK hKs hQm hQ z z' z z' hD0 hD hzz hz hz' (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨iC, bC⟩ := h0 hKm hK hKs hQm hQ z z' z' z hD0 hD hzz hz hz' (Or.inr ⟨rfl, rfl⟩)
  obtain ⟨iP, bP⟩ := hp hKm hK hKs hQm hQ z z'
  have iF : Integrable (Function.uncurry (i3PsiDiagramIntegrand K Q z z')) (volume.prod volume) := by
    have := (iA.const_mul 18).add ((iP.const_mul (6 * Q (z - z'))).add (iC.const_mul 18))
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Pi.add_apply, i3PsiDiagramIntegrand_eq]
    ring
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
  rw [hT]
  have n1 : 0 ≤ torusParabolicSize (z - z') ^ (-(1 : ℝ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have n2 : 0 ≤ torusParabolicSize (z - z') ^ (-δ) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have n3 : 0 ≤ torusParabolicSize z ^ (-δ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have n4 : 0 ≤ torusParabolicSize z' ^ (-δ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hz0 : 0 ≤ |z.1| := abs_nonneg _
  have hDδ := rpow_le_one_add_self hD0 hδ.le (by linarith)
  have hDδ0 : 0 ≤ D ^ δ := Real.rpow_nonneg hD0 _
  set Sm : ℝ := torusParabolicSize (z - z') ^ (-δ) + torusParabolicSize z ^ (-δ) +
    torusParabolicSize z' ^ (-δ) with hSm
  have hSm0 : 0 ≤ Sm := by rw [hSm]; linarith
  have b1 : |18 * (∫ w, ∫ v, i3PsiChain K Q z z' z z' w v)| ≤ 18 * (C0 * D ^ δ * Sm) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 18)]
    exact mul_le_mul_of_nonneg_left bA (by norm_num)
  have b3 : |18 * (∫ w, ∫ v, i3PsiChain K Q z z' z' z w v)| ≤ 18 * (C0 * D ^ δ * Sm) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 18)]
    exact mul_le_mul_of_nonneg_left bC (by norm_num)
  have b2 : |6 * Q (z - z') * (∫ w, ∫ v, i3PsiPrincipal K Q z z' w v)| ≤
      6 * (B * torusParabolicSize (z - z') ^ (-(1 : ℝ))) * (Cp * (80 + 2 * (|z.1| + 1))) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hQ _ hzz) (by norm_num)) bP (abs_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg hB n1))
  have x1 := abs_add_three (18 * (∫ w, ∫ v, i3PsiChain K Q z z' z z' w v))
    (6 * Q (z - z') * (∫ w, ∫ v, i3PsiPrincipal K Q z z' w v))
    (18 * (∫ w, ∫ v, i3PsiChain K Q z z' z' z w v))
  have hfac : 0 ≤ 1 + D + |z.1| := by positivity
  have c1 : C0 * D ^ δ * Sm ≤ C0 * (1 + D + |z.1|) * Sm := by
    have : D ^ δ ≤ 1 + D + |z.1| := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hC0) hSm0
  have c2 : 6 * (B * torusParabolicSize (z - z') ^ (-(1 : ℝ))) * (Cp * (80 + 2 * (|z.1| + 1))) ≤
      6 * B * Cp * 82 * (1 + D + |z.1|) * torusParabolicSize (z - z') ^ (-(1 : ℝ)) := by
    have : Cp * (80 + 2 * (|z.1| + 1)) ≤ Cp * (82 * (1 + D + |z.1|)) :=
      mul_le_mul_of_nonneg_left (by linarith) hCp
    calc 6 * (B * torusParabolicSize (z - z') ^ (-(1 : ℝ))) * (Cp * (80 + 2 * (|z.1| + 1)))
        ≤ 6 * (B * torusParabolicSize (z - z') ^ (-(1 : ℝ))) * (Cp * (82 * (1 + D + |z.1|))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hR : 0 ≤ 6 * B * Cp * 82 := by positivity
  have e : (36 * C0 + 6 * B * Cp * 82) * (1 + D + |z.1|) *
      (torusParabolicSize (z - z') ^ (-(1 : ℝ)) + torusParabolicSize (z - z') ^ (-δ) +
        torusParabolicSize z ^ (-δ) + torusParabolicSize z' ^ (-δ)) =
      (36 * (C0 * (1 + D + |z.1|) * Sm) + 6 * B * Cp * 82 * (1 + D + |z.1|) *
        torusParabolicSize (z - z') ^ (-(1 : ℝ))) +
      (36 * (C0 * (1 + D + |z.1|) * torusParabolicSize (z - z') ^ (-(1 : ℝ))) +
        6 * B * Cp * 82 * (1 + D + |z.1|) * Sm) := by
    rw [hSm]; ring
  have p1 : 0 ≤ C0 * (1 + D + |z.1|) * torusParabolicSize (z - z') ^ (-(1 : ℝ)) := by positivity
  have p2 : 0 ≤ 6 * B * Cp * 82 * (1 + D + |z.1|) * Sm := by positivity
  rw [e]
  linarith [x1, b1, b3, b2, c1, c2, p1, p2]

end RegularityStructures

end
