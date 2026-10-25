/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiDiagramMultiBasic
public import Phi43.BPHZ.TreeI3PsiChainBound

/-!
# The chain majorant with general exponents

The chain diagram of `I(Ψ³)Ψ` is dominated by
`(s₃(z,w) + s₃(0,w)) s_{1+α}(u,w) · (s_{4+γ}(z',v) + s_{4+γ}(0,v) + 2 s_{4+γ}(u',v)) s_{2+β}(w,v)`
(`s_a(c, w) = s(c - w)^(-a)`), which has the three exponents `α` (outer covariance), `β` (loss in
`Q²`) and `γ` (the covariance next to `δK(z', v)`) in place of `0, δ, 0`.  For `u = z, u' = z'`
(chaos-two pairing) or `u = z', u' = z` (secondary pairing) its double integral is bounded by
`C (s(z - z')^(-η) + s(z)^(-η) + s(z')^(-η))` with `η = α + β + γ`.

Source: [Hai14] = arXiv:1303.5113v4, p. 167--168.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

/-- The chain majorant with exponents `α, β, γ`. -/
def i3PsiChainMajorant (α β γ : ℝ) (z z' u u' w v : SpaceTime) : ℝ :=
  ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + α) u w) *
    ((singularPow (4 + γ) z' v + singularPow (4 + γ) 0 v + 2 * singularPow (4 + γ) u' v) *
      singularPow (2 + β) w v)

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

/-- **Two-level bound for the chain majorant.** -/
theorem twoLevelLe_chainMajorant {α β γ : ℝ} (hα1 : α < 1) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hβ : 0 < β) (hβ3 : β < 3) (hη : 0 < α + (γ + β)) (hη1 : α + (γ + β) ≤ 1)
    (hκ1 : γ + β < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z z' u u' : SpaceTime, 0 < torusParabolicSize (z - z') →
      0 < torusParabolicSize z → 0 < torusParabolicSize z' →
      ((u = z ∧ u' = z') ∨ (u = z' ∧ u' = z)) →
      TwoLevelLe (i3PsiChainMajorant α β γ z z' u u')
        (C * (torusParabolicSize (z - z') ^ (-(α + (γ + β))) +
          torusParabolicSize z ^ (-(α + (γ + β))) + torusParabolicSize z' ^ (-(α + (γ + β))))) := by
  obtain ⟨Cin, hCin, hin⟩ := singularIntLe_inner_gen hγ hγ1 hβ hβ3
  obtain ⟨L, hL0, hL⟩ := singularIntLe_outer_leaf_gen (α := α) (κ := γ + β) hα1 hκ1 hη
  refine ⟨64 * Cin * L, by positivity, ?_⟩
  intro z z' u u' hzz hz hz' hu
  have pz0 : 0 < torusParabolicSize (z - 0) := by rwa [sub_zero]
  have pz'0 : 0 < torusParabolicSize (z' - 0) := by rwa [sub_zero]
  have p0z := torusParabolicSize_sub_pos_symm pz0
  have p0z' := torusParabolicSize_sub_pos_symm pz'0
  have pz'z := torusParabolicSize_sub_pos_symm hzz
  set η : ℝ := α + (γ + β) with hηdef
  set Sf : ℝ := torusParabolicSize (z - z') ^ (-η) + torusParabolicSize (z - 0) ^ (-η) +
    torusParabolicSize (z' - 0) ^ (-η) with hSf
  have hSf0 : 0 ≤ Sf := by
    have a1 : 0 ≤ torusParabolicSize (z - z') ^ (-η) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have a2 : 0 ≤ torusParabolicSize (z - 0) ^ (-η) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have a3 : 0 ≤ torusParabolicSize (z' - 0) ^ (-η) :=
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
      torusParabolicSize (y - c) ^ (-η) + torusParabolicSize (u - c) ^ (-η) +
        torusParabolicSize (y - u) ^ (-η) + torusParabolicSize (u - y) ^ (-η) ≤ 8 * Sf := by
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
    have e1 := torusParabolicSize_rpow_neg_le_two_mul_sum hη hη1 hzz pz0 pz'0 hyM hcM
    have e2 := torusParabolicSize_rpow_neg_le_two_mul_sum hη hη1 hzz pz0 pz'0 huM hcM
    have e3 := torusParabolicSize_rpow_neg_le_two_mul_sum hη hη1 hzz pz0 pz'0 hyM huM
    have e4 := torusParabolicSize_rpow_neg_le_two_mul_sum hη hη1 hzz pz0 pz'0 huM hyM
    rw [← hSf] at e1 e2 e3 e4
    linarith
  have hT : ∀ y c : SpaceTime, (y = z ∨ y = 0) → (c = z' ∨ c = 0 ∨ c = u') →
      SingularIntLe (fun w => singularPow 3 y w * singularPow (1 + α) u w *
          singularPow (1 + (γ + β)) c w) (L * (8 * Sf)) := by
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
  have hH := (hsum.const_mul (c := Cin) hCin).congr_fun
    (g := fun w => ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + α) u w) *
      (Cin * (singularPow (1 + (γ + β)) z' w + singularPow (1 + (γ + β)) 0 w +
        2 * singularPow (1 + (γ + β)) u' w))) (fun w => by ring)
  refine ⟨?_, fun w => ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + α) u w) *
      (Cin * (singularPow (1 + (γ + β)) z' w + singularPow (1 + (γ + β)) 0 w +
        2 * singularPow (1 + (γ + β)) u' w)), ⟨hH.1, ?_⟩, ?_⟩
  · filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u'] with w a b c
    exact ((hin z' 0 u' w a b c).1).const_mul _
  · refine hH.2.trans (le_of_eq ?_)
    rw [hSf]
    simp only [sub_zero]
    ring
  · filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u'] with w a b c
    have := (hin z' 0 u' w a b c).2
    have hnn : 0 ≤ (singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + α) u w :=
      mul_nonneg (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
        (singularPow_nonneg _ _ _)
    calc ∫ v, i3PsiChainMajorant α β γ z z' u u' w v
        = ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + α) u w) *
          ∫ v, (singularPow (4 + γ) z' v + singularPow (4 + γ) 0 v +
            2 * singularPow (4 + γ) u' v) * singularPow (2 + β) w v := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left this hnn

/-- `twoLevelLe_chainMajorant` with the total exponent named `η`. -/
theorem twoLevelLe_chainMajorant_of_eq {α β γ η : ℝ} (hα1 : α < 1) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hβ : 0 < β) (hβ3 : β < 3) (he : α + (γ + β) = η) (hη : 0 < η) (hη1 : η ≤ 1)
    (hκ1 : γ + β < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z z' u u' : SpaceTime, 0 < torusParabolicSize (z - z') →
      0 < torusParabolicSize z → 0 < torusParabolicSize z' →
      ((u = z ∧ u' = z') ∨ (u = z' ∧ u' = z)) →
      TwoLevelLe (i3PsiChainMajorant α β γ z z' u u')
        (C * (torusParabolicSize (z - z') ^ (-η) + torusParabolicSize z ^ (-η) +
          torusParabolicSize z' ^ (-η))) := by
  subst he
  exact twoLevelLe_chainMajorant hα1 hγ hγ1 hβ hβ3 hη hη1 hκ1

end RegularityStructures

end
