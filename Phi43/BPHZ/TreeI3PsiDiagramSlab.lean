/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiDiagram

/-!
# The diagram bound for `I(Ψ³)Ψ` without a time support hypothesis on `Q`

`i3PsiPairing_bound` assumes that the covariance `Q` vanishes for `|t| > 2`.  The mollified
covariance `Q_ε = K_ε ⋆ K_ε^-` is supported in `|t| ≤ 2 (1 + ε² R)` where `R` is the time radius of the
mollifier, so this fails for every `ε > 0` as soon as `R > 0`.  The support is used only to bound
`Q(w - v)²` by `3^δ s(w - v)^(-2-δ)`; but the recentred kernels `δK(z, w)`, `δK(z', v)` vanish unless
`|w.1|, |v.1| ≤ 2` (for `s(z), s(z') ≤ 1`), hence only `|(w - v).1| ≤ 4` matters, where `s ≤ 3` still
holds.  This file re-proves the chain and total bounds with the support hypothesis on `Q` removed
(the support hypothesis on `K` is kept).

Source: [Hai14] = arXiv:1303.5113v4, (10.36)--(10.38), p. 167--168.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- On the slab `|t| ≤ 4` the parabolic size is at most `3`. -/
theorem torusParabolicSize_le_three_of_abs_le_four {w : SpaceTime} (hw : |w.1| ≤ 4) :
    torusParabolicSize w ≤ 3 := by
  have h1 : √|w.1| ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
  have h2 := torusSpatialNorm_le_seven_eighth w.2
  unfold torusParabolicSize
  linarith

/-- The covariance squared, with a loss `δ` of the exponent, on the slab `|t| ≤ 4`. -/
theorem abs_Q_sq_le_of_abs_le_four {Q : SpaceTime → ℝ} {B δ : ℝ} (hδ : 0 ≤ δ)
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {x : SpaceTime} (hx : 0 < torusParabolicSize x) (hx4 : |x.1| ≤ 4) :
    |Q x| ^ 2 ≤ B ^ 2 * 3 ^ δ * torusParabolicSize x ^ (-(2 + δ)) := by
  have h3 := torusParabolicSize_le_three_of_abs_le_four hx4
  have h1 := hQ x hx
  have hsq : |Q x| ^ 2 ≤ (B * torusParabolicSize x ^ (-(1 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e : (B * torusParabolicSize x ^ (-(1 : ℝ))) ^ 2 =
      B ^ 2 * torusParabolicSize x ^ (-(2 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast (torusParabolicSize x ^ (-(1 : ℝ))) 2,
      ← Real.rpow_mul hx.le]
    norm_num
  have hpow : torusParabolicSize x ^ (-(2 : ℝ)) =
      torusParabolicSize x ^ δ * torusParabolicSize x ^ (-(2 + δ)) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have hle : torusParabolicSize x ^ δ ≤ 3 ^ δ := Real.rpow_le_rpow hx.le h3 hδ
  have hnn : 0 ≤ torusParabolicSize x ^ (-(2 + δ)) := Real.rpow_nonneg hx.le _
  calc |Q x| ^ 2 ≤ B ^ 2 * torusParabolicSize x ^ (-(2 : ℝ)) := hsq.trans e.le
    _ = B ^ 2 * (torusParabolicSize x ^ δ * torusParabolicSize x ^ (-(2 + δ))) := by
      rw [hpow]
    _ ≤ B ^ 2 * (3 ^ δ * torusParabolicSize x ^ (-(2 + δ))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
      exact mul_le_mul_of_nonneg_right hle hnn
    _ = _ := by ring

/-- Pointwise majorant of the chain integrand, without a support hypothesis on `Q`. -/
theorem abs_i3PsiChain_le_slab {K Q : SpaceTime → ℝ} {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {z z' u u' w v : SpaceTime} (hz1 : torusParabolicSize z ≤ 1) (hz1' : torusParabolicSize z' ≤ 1)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (hu : 0 < torusParabolicSize (u - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v))
    (hu' : 0 < torusParabolicSize (u' - v)) (hwv : 0 < torusParabolicSize (w - v)) :
    |i3PsiChain K Q z z' u u' w v| ≤
      (4 * B ^ 6 * 3 ^ δ) * (((singularPow 3 z w + singularPow 3 0 w) * singularPow 1 u w) *
        ((singularPow 4 z' v + singularPow 4 0 v + 2 * singularPow 4 u' v) *
          singularPow (2 + δ) w v)) := by
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  have hrhs : 0 ≤ (4 * B ^ 6 * 3 ^ δ) * (((singularPow 3 z w + singularPow 3 0 w) *
      singularPow 1 u w) * ((singularPow 4 z' v + singularPow 4 0 v + 2 * singularPow 4 u' v) *
        singularPow (2 + δ) w v)) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hB 6)) n3)
      (mul_nonneg (mul_nonneg (add_nonneg (singularPow_nonneg _ _ _)
        (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _))
        (mul_nonneg ?_ (singularPow_nonneg _ _ _)))
    exact add_nonneg (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
      (mul_nonneg (by norm_num) (singularPow_nonneg _ _ _))
  by_cases hw : |w.1| ≤ 2
  · by_cases hv : |v.1| ≤ 2
    · have hwv4 : |(w - v).1| ≤ 4 := by
        have : (w - v).1 = w.1 - v.1 := rfl
        rw [this]
        exact (abs_sub _ _).trans (by linarith)
      have e : |i3PsiChain K Q z z' u u' w v| =
          |(K (z - w) - K (-w)) * Q (w - u)| *
            (|Q (w - v)| ^ 2 * |(K (z' - v) - K (-v)) * Q (v - u')|) := by
        unfold i3PsiChain
        simp only [abs_mul, abs_pow]
      rw [e]
      have a := abs_dK_mul_Q_le hB hK hQ h1 h0 hu
      have b := abs_dK_mul_Q_le_pow_four hB hK hQ h1' h0' hu'
      have c := abs_Q_sq_le_of_abs_le_four hδ hQ hwv hwv4
      have hbb : 0 ≤ |(K (z' - v) - K (-v)) * Q (v - u')| := abs_nonneg _
      have key : |(K (z - w) - K (-w)) * Q (w - u)| *
          (|Q (w - v)| ^ 2 * |(K (z' - v) - K (-v)) * Q (v - u')|) ≤
          (2 * B ^ 2 * ((singularPow 3 z w + singularPow 3 0 w) * singularPow 1 u w)) *
            ((B ^ 2 * 3 ^ δ * singularPow (2 + δ) w v) *
              (2 * B ^ 2 * (singularPow 4 z' v + singularPow 4 0 v + 2 * singularPow 4 u' v))) := by
        have nc : 0 ≤ B ^ 2 * 3 ^ δ * singularPow (2 + δ) w v :=
          mul_nonneg (mul_nonneg (sq_nonneg B) n3) (singularPow_nonneg _ _ _)
        have nl : 0 ≤ 2 * B ^ 2 * ((singularPow 3 z w + singularPow 3 0 w) *
            singularPow 1 u w) :=
          mul_nonneg (by positivity) (mul_nonneg (add_nonneg (singularPow_nonneg _ _ _)
            (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _))
        refine mul_le_mul a (mul_le_mul (by simpa [singularPow] using c) b hbb nc)
          (mul_nonneg (sq_nonneg _) hbb) nl
      refine key.trans (le_of_eq ?_)
      ring
    · have : K (z' - v) - K (-v) = 0 := dK_eq_zero_of_two_lt hKs hz1' (not_le.1 hv)
      have h0 : i3PsiChain K Q z z' u u' w v = 0 := by
        unfold i3PsiChain
        rw [this]
        ring
      rw [h0, abs_zero]
      exact hrhs
  · have : K (z - w) - K (-w) = 0 := dK_eq_zero_of_two_lt hKs hz1 (not_le.1 hw)
    have h0 : i3PsiChain K Q z z' u u' w v = 0 := by
      unfold i3PsiChain
      rw [this]
      ring
    rw [h0, abs_zero]
    exact hrhs

/-- Bound for the chain diagram: chaos-two pairing `(u, u') = (z, z')` and secondary pairing
`(u, u') = (z', z)`.  The constant depends only on `B, δ`, not on `K, Q`. -/
theorem i3PsiChain_bound_uniform {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ}, Measurable K →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) → Measurable Q →
      (∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      ∀ z z' u u' : SpaceTime, 0 < torusParabolicSize (z - z') →
      0 < torusParabolicSize z → 0 < torusParabolicSize z' → torusParabolicSize z ≤ 1 →
      torusParabolicSize z' ≤ 1 →
      ((u = z ∧ u' = z') ∨ (u = z' ∧ u' = z)) →
      Integrable (Function.uncurry (i3PsiChain K Q z z' u u')) (volume.prod volume) ∧
        |∫ w, ∫ v, i3PsiChain K Q z z' u u' w v| ≤
          C * (torusParabolicSize (z - z') ^ (-δ) + torusParabolicSize z ^ (-δ) +
            torusParabolicSize z' ^ (-δ)) := by
  obtain ⟨Cin, hCin, hin⟩ := singularIntLe_inner hδ hδ1
  obtain ⟨L, hL0, hL⟩ := singularIntLe_outer_leaf hδ hδ1
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  have hΛ : 0 ≤ 4 * B ^ 6 * 3 ^ δ :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hB 6)) n3
  refine ⟨64 * (4 * B ^ 6 * 3 ^ δ) * Cin * L,
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hΛ) hCin) hL0, ?_⟩
  intro K Q hKm hK hKs hQm hQ z z' u u' hzz hz hz' hz1 hz1' hu
  have pz0 : 0 < torusParabolicSize (z - 0) := by rwa [sub_zero]
  have pz'0 : 0 < torusParabolicSize (z' - 0) := by rwa [sub_zero]
  have p0z := torusParabolicSize_sub_pos_symm pz0
  have p0z' := torusParabolicSize_sub_pos_symm pz'0
  have pz'z := torusParabolicSize_sub_pos_symm hzz
  set Λ : ℝ := 4 * B ^ 6 * 3 ^ δ with hΛdef
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
  -- membership of the centres in `{z, z', 0}`
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
  -- measurability
  have hmeas : Measurable (fun p : SpaceTime × SpaceTime => i3PsiChain K Q z z' u u' p.1 p.2) := by
    unfold i3PsiChain
    fun_prop
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
  have hFG : ∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume,
      |i3PsiChain K Q z z' u u' w v| ≤
      (Λ * ((singularPow 3 z w + singularPow 3 0 w) * singularPow 1 u w)) *
      ((singularPow 4 z' v + singularPow 4 0 v + 2 * singularPow 4 u' v) *
        singularPow (2 + δ) w v) := by
    filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u] with w a b c
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u', ae_torusParabolicSize_sub_pos w] with v a' b' c' d'
    have := abs_i3PsiChain_le_slab hB hδ.le hK hKs hQ hz1 hz1' a b c a' b' c' d'
    refine this.trans (le_of_eq ?_)
    ring
  obtain ⟨hint, hbd⟩ := integrable_prod_of_two_level
    (F := fun w v => i3PsiChain K Q z z' u u' w v)
    hmeas.aestronglyMeasurable hG hGH hH.1 hFG
  refine ⟨hint, hbd.trans (hH.2.trans (le_of_eq ?_))⟩
  rw [hSf]
  simp only [sub_zero]
  ring

end RegularityStructures

end
