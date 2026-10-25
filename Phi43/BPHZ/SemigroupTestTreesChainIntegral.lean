/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiChainBound
public import Phi43.BPHZ.TreeI3PsiDiagramSlab

/-!
# The chain integral for an arbitrary integrand dominated by the chain majorant

`i3PsiChain_majorant_integral`: let `F` be any function such that, almost everywhere,
`|F w v| ≤ Λ (s₃(z, 0; w) s₁(u; w)) (s₄(z', 0, u'; v) s_{2+δ}(w; v))`, where `s_a(c; w) = s(c - w)^(-a)`.
Then `F` is integrable on the product and
`|∫∫ F| ≤ C Λ (s(z - z')^(-δ) + s(z)^(-δ) + s(z')^(-δ))`, with `C` depending only on `δ`.
No assumption is made on the size of `z, z'`; the proof of `i3PsiChain_bound_uniform` after the
pointwise majorant is independent of the kernels.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- **Chain integral for a dominated integrand.** -/
theorem i3PsiChain_majorant_integral {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : SpaceTime → SpaceTime → ℝ} {Λ : ℝ}, 0 ≤ Λ →
      AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) →
      ∀ z z' u u' : SpaceTime, 0 < torusParabolicSize (z - z') → 0 < torusParabolicSize z →
      0 < torusParabolicSize z' → ((u = z ∧ u' = z') ∨ (u = z' ∧ u' = z)) →
      (∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume, |F w v| ≤
        Λ * (((singularPow 3 z w + singularPow 3 0 w) * singularPow 1 u w) *
          ((singularPow 4 z' v + singularPow 4 0 v + 2 * singularPow 4 u' v) *
            singularPow (2 + δ) w v))) →
      Integrable (Function.uncurry F) (volume.prod volume) ∧
        |∫ w, ∫ v, F w v| ≤ C * Λ * (torusParabolicSize (z - z') ^ (-δ) +
          torusParabolicSize z ^ (-δ) + torusParabolicSize z' ^ (-δ)) := by
  obtain ⟨Cin, hCin, hin⟩ := singularIntLe_inner hδ hδ1
  obtain ⟨L, hL0, hL⟩ := singularIntLe_outer_leaf hδ hδ1
  refine ⟨64 * Cin * L, mul_nonneg (mul_nonneg (by norm_num) hCin) hL0, ?_⟩
  intro F Λ hΛ hmeas z z' u u' hzz hz hz' hu hFG
  have pz0 : 0 < torusParabolicSize (z - 0) := by rwa [sub_zero]
  have pz'0 : 0 < torusParabolicSize (z' - 0) := by rwa [sub_zero]
  have p0z := torusParabolicSize_sub_pos_symm pz0
  have p0z' := torusParabolicSize_sub_pos_symm pz'0
  have pz'z := torusParabolicSize_sub_pos_symm hzz
  set Sf : ℝ := torusParabolicSize (z - z') ^ (-δ) + torusParabolicSize (z - 0) ^ (-δ) +
    torusParabolicSize (z' - 0) ^ (-δ) with hSf
  have hSf0 : 0 ≤ Sf := by
    have a1 : 0 ≤ torusParabolicSize (z - z') ^ (-δ) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have a2 : 0 ≤ torusParabolicSize (z - 0) ^ (-δ) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have a3 : 0 ≤ torusParabolicSize (z' - 0) ^ (-δ) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    rw [hSf]; linarith
  have huM : u = z ∨ u = z' ∨ u = 0 := by
    rcases hu with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  have hu'M : u' = z ∨ u' = z' ∨ u' = 0 := by
    rcases hu with ⟨_, h1⟩ | ⟨_, h1⟩
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h1
  have hX : ∀ y c : SpaceTime, (y = z ∨ y = 0) → (c = z' ∨ c = 0 ∨ c = u') →
      torusParabolicSize (y - c) ^ (-δ) + torusParabolicSize (u - c) ^ (-δ) +
        torusParabolicSize (y - u) ^ (-δ) + torusParabolicSize (u - y) ^ (-δ) ≤ 8 * Sf := by
    intro y c hy hc
    have hyM : y = z ∨ y = z' ∨ y = 0 := by
      rcases hy with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    have hcM : c = z ∨ c = z' ∨ c = 0 := by
      rcases hc with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · rw [h]; exact hu'M
    have e1 := torusParabolicSize_rpow_neg_le_two_mul_sum hδ (by linarith) hzz pz0 pz'0 hyM hcM
    have e2 := torusParabolicSize_rpow_neg_le_two_mul_sum hδ (by linarith) hzz pz0 pz'0 huM hcM
    have e3 := torusParabolicSize_rpow_neg_le_two_mul_sum hδ (by linarith) hzz pz0 pz'0 hyM huM
    have e4 := torusParabolicSize_rpow_neg_le_two_mul_sum hδ (by linarith) hzz pz0 pz'0 huM hyM
    rw [← hSf] at e1 e2 e3 e4
    linarith
  have hT : ∀ y c : SpaceTime, (y = z ∨ y = 0) → (c = z' ∨ c = 0 ∨ c = u') →
      SingularIntLe (fun w => singularPow 3 y w * singularPow 1 u w * singularPow (1 + δ) c w)
        (L * (8 * Sf)) := by
    intro y c hy hc
    exact (hL y u c (chain_outer_case y c hzz pz'z pz0 p0z pz'0 p0z' hu hy hc)).mono_right
      (mul_le_mul_of_nonneg_left (hX y c hy hc) hL0)
  have t1 := hT z z' (Or.inl rfl) (Or.inl rfl)
  have t2 := hT z 0 (Or.inl rfl) (Or.inr (Or.inl rfl))
  have t3 := hT z u' (Or.inl rfl) (Or.inr (Or.inr rfl))
  have t4 := hT 0 z' (Or.inr rfl) (Or.inl rfl)
  have t5 := hT 0 0 (Or.inr rfl) (Or.inr (Or.inl rfl))
  have t6 := hT 0 u' (Or.inr rfl) (Or.inr (Or.inr rfl))
  have hsum := ((((t1.add t2).add (t3.const_mul (c := (2 : ℝ)) (by norm_num))).add t4).add
    t5).add (t6.const_mul (c := (2 : ℝ)) (by norm_num))
  have hH := (hsum.const_mul (c := Λ * Cin) (mul_nonneg hΛ hCin)).congr_fun
    (g := fun w => (Λ * ((singularPow 3 z w + singularPow 3 0 w) * singularPow 1 u w)) *
      (Cin * (singularPow (1 + δ) z' w + singularPow (1 + δ) 0 w +
        2 * singularPow (1 + δ) u' w))) (fun w => by ring)
  have hG : ∀ᵐ w : SpaceTime ∂volume, Integrable (fun v =>
      (Λ * ((singularPow 3 z w + singularPow 3 0 w) * singularPow 1 u w)) *
      ((singularPow 4 z' v + singularPow 4 0 v + 2 * singularPow 4 u' v) *
        singularPow (2 + δ) w v)) := by
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u'] with w a b c
    exact ((hin z' 0 u' w a b c).1).const_mul _
  have hGH : ∀ᵐ w : SpaceTime ∂volume, ∫ v,
      (Λ * ((singularPow 3 z w + singularPow 3 0 w) * singularPow 1 u w)) *
      ((singularPow 4 z' v + singularPow 4 0 v + 2 * singularPow 4 u' v) *
        singularPow (2 + δ) w v) ≤
      (Λ * ((singularPow 3 z w + singularPow 3 0 w) * singularPow 1 u w)) *
      (Cin * (singularPow (1 + δ) z' w + singularPow (1 + δ) 0 w +
        2 * singularPow (1 + δ) u' w)) := by
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u'] with w a b c
    have := (hin z' 0 u' w a b c).2
    have hnn : 0 ≤ Λ * ((singularPow 3 z w + singularPow 3 0 w) * singularPow 1 u w) :=
      mul_nonneg hΛ (mul_nonneg (add_nonneg (singularPow_nonneg _ _ _)
        (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _))
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left this hnn
  have hFG' : ∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume, |F w v| ≤
      (Λ * ((singularPow 3 z w + singularPow 3 0 w) * singularPow 1 u w)) *
      ((singularPow 4 z' v + singularPow 4 0 v + 2 * singularPow 4 u' v) *
        singularPow (2 + δ) w v) := by
    filter_upwards [hFG] with w hw
    filter_upwards [hw] with v hv
    refine hv.trans (le_of_eq ?_)
    ring
  obtain ⟨hint, hbd⟩ := integrable_prod_of_two_level (F := F) hmeas hG hGH hH.1 hFG'
  refine ⟨hint, hbd.trans (hH.2.trans (le_of_eq ?_))⟩
  rw [hSf]
  simp only [sub_zero]
  ring

end RegularityStructures

end
