/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI3PsiChain
public import Phi43.BPHZ.SemigroupTestTreesDiffI3PsiPrincipal
public import Phi43.BPHZ.TreeI3PsiCrossBound
public import Phi43.BPHZ.SemigroupTestTreesI3PsiField

/-!
# The global covariance bound for the cross-mollifier difference `I₃Ψ_{ρ,ε} - I₃Ψ_{ρ',ε'}`

`hairerI3PsiField_sub_cov_bound_cross_global`: for `θ ∈ (0, 1/8]`, `δ ∈ (0, 1/4]`, scales
`ε, ε' ∈ (0, 1]`, a base point `x` and points `y, y'` with `y, y', x` distinct and *no smallness*,
with `r = s(y - x)`, `r' = s(y' - x)`, `d = s(y - y')`, `η = 2θ + δ`,
`|E[(F - F')(y) (F - F')(y')]| ≤ C (max ε ε')^(2θ) (1 + r² + r'²)²
  (d^(-1) + d^(-(1+2θ)) + d^(-η) + r^(-η) + r'^(-η))`.
The constant is independent of the scales, the points, the probability space and the noises.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem integral_integral_comb3_global {h₁ h₂ h₃ : SpaceTime → SpaceTime → ℝ}
    {c₁ c₂ c₃ : ℝ}
    (i₁ : Integrable (Function.uncurry h₁) (volume.prod volume))
    (i₂ : Integrable (Function.uncurry h₂) (volume.prod volume))
    (i₃ : Integrable (Function.uncurry h₃) (volume.prod volume)) :
    ∫ w, ∫ v, (c₁ * h₁ w v + c₂ * h₂ w v + c₃ * h₃ w v) =
      c₁ * (∫ w, ∫ v, h₁ w v) + c₂ * (∫ w, ∫ v, h₂ w v) + c₃ * ∫ w, ∫ v, h₃ w v := by
  have j1 : Integrable (fun p => c₁ * Function.uncurry h₁ p) (volume.prod volume) :=
    i₁.const_mul c₁
  have j2 : Integrable (fun p => c₂ * Function.uncurry h₂ p) (volume.prod volume) :=
    i₂.const_mul c₂
  have j3 : Integrable (fun p => c₃ * Function.uncurry h₃ p) (volume.prod volume) :=
    i₃.const_mul c₃
  have j12 : Integrable (fun p => c₁ * Function.uncurry h₁ p + c₂ * Function.uncurry h₂ p)
      (volume.prod volume) := j1.add j2
  have hs : Integrable (Function.uncurry fun w v => c₁ * h₁ w v + c₂ * h₂ w v + c₃ * h₃ w v)
      (volume.prod volume) := j12.add j3
  calc ∫ w, ∫ v, (c₁ * h₁ w v + c₂ * h₂ w v + c₃ * h₃ w v)
      = ∫ p, Function.uncurry (fun w v => c₁ * h₁ w v + c₂ * h₂ w v + c₃ * h₃ w v) p
          ∂(volume.prod volume) := (integral_prod _ hs).symm
    _ = ∫ p, (c₁ * Function.uncurry h₁ p + c₂ * Function.uncurry h₂ p +
          c₃ * Function.uncurry h₃ p) ∂(volume.prod volume) := rfl
    _ = c₁ * (∫ p, Function.uncurry h₁ p ∂(volume.prod volume)) +
          c₂ * (∫ p, Function.uncurry h₂ p ∂(volume.prod volume)) +
          c₃ * ∫ p, Function.uncurry h₃ p ∂(volume.prod volume) := by
        rw [integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
          integral_const_mul]
    _ = _ := by
        rw [integral_prod _ i₁, integral_prod _ i₂, integral_prod _ i₃]
        rfl

/-- Real algebra for the assembly of the three pieces. -/
private theorem cov_combine_i3Psi {C₁ C₂ C₃ m Dδ Dθ Q q S d₁ d₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hC₃ : 0 ≤ C₃) (hm : 0 ≤ m) (hQ : 1 ≤ Q) (hDδ : Dδ ≤ 4 * Q)
    (hDθ : Dθ ≤ 4 * Q) (hq0 : 0 ≤ q) (hq : q ≤ Q) (hS : 0 ≤ S) (hd₁ : 0 ≤ d₁)
    (hd₂ : 0 ≤ d₂) :
    18 * (C₁ * m * Dδ * S) + 6 * (C₂ * m * (d₁ + Dθ * d₂) * q) + 18 * (C₃ * m * Dδ * S) ≤
      (72 * C₁ + 24 * C₂ + 72 * C₃) * m * Q ^ 2 * (d₁ + d₂ + S) := by
  have hQ0 : 0 ≤ Q := by linarith
  have hQQ : Q ≤ Q ^ 2 := by nlinarith
  have hQ2 : 0 ≤ Q ^ 2 := sq_nonneg Q
  have e1 : Dδ * S ≤ 4 * Q ^ 2 * S := by
    have : Dδ ≤ 4 * Q ^ 2 := by linarith
    exact mul_le_mul_of_nonneg_right this hS
  have t1 : C₁ * m * (Dδ * S) ≤ C₁ * m * (4 * Q ^ 2 * (d₁ + d₂ + S)) := by
    refine mul_le_mul_of_nonneg_left (e1.trans ?_) (mul_nonneg hC₁ hm)
    linarith [mul_nonneg hQ2 hd₁, mul_nonneg hQ2 hd₂]
  have t3 : C₃ * m * (Dδ * S) ≤ C₃ * m * (4 * Q ^ 2 * (d₁ + d₂ + S)) := by
    refine mul_le_mul_of_nonneg_left (e1.trans ?_) (mul_nonneg hC₃ hm)
    linarith [mul_nonneg hQ2 hd₁, mul_nonneg hQ2 hd₂]
  have e2 : (d₁ + Dθ * d₂) * q ≤ 4 * Q ^ 2 * (d₁ + d₂) := by
    have h1 : d₁ + Dθ * d₂ ≤ 4 * Q * (d₁ + d₂) := by
      nlinarith [mul_le_mul_of_nonneg_right hDθ hd₂, mul_nonneg hQ0 hd₁, mul_nonneg hQ0 hd₂]
    calc (d₁ + Dθ * d₂) * q ≤ (4 * Q * (d₁ + d₂)) * Q :=
          mul_le_mul h1 hq hq0 (by positivity)
      _ = 4 * Q ^ 2 * (d₁ + d₂) := by ring
  have t2 : C₂ * m * ((d₁ + Dθ * d₂) * q) ≤ C₂ * m * (4 * Q ^ 2 * (d₁ + d₂ + S)) := by
    refine mul_le_mul_of_nonneg_left (e2.trans ?_) (mul_nonneg hC₂ hm)
    linarith [mul_nonneg hQ2 hS]
  linarith [t1, t2, t3]

/-- **Global covariance bound for the difference `I₃Ψ_{ρ,ε} - I₃Ψ_{ρ',ε'}`**, with the full gain
`(max ε ε')^(2θ)` and no smallness assumption on the points. -/
theorem hairerI3PsiField_sub_cov_bound_cross_global (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') →
          |∫ ω, (hairerI3PsiField N ρ ε ξ x ω y - hairerI3PsiField N ρ' ε' ξ' x ω y) *
              (hairerI3PsiField N ρ ε ξ x ω y' - hairerI3PsiField N ρ' ε' ξ' x ω y') ∂P| ≤
            C * (max ε ε') ^ (2 * θ) *
              (1 + torusParabolicSize (y - x) ^ 2 + torusParabolicSize (y' - x) ^ 2) ^ 2 *
              (torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
                torusParabolicSize (y - y') ^ (-(1 + 2 * θ)) +
                torusParabolicSize (y - y') ^ (-(2 * θ + δ)) +
                torusParabolicSize (y - x) ^ (-(2 * θ + δ)) +
                torusParabolicSize (y' - x) ^ (-(2 * θ + δ))) := by
  obtain ⟨C1, hC1, h1⟩ := i3PsiDiffPiece1Cross_bound_global N hρ hρ' hθ hθ1 hδ hδ1
  obtain ⟨C2, hC2, h2⟩ := i3PsiDiffPiece2Cross_bound_global N hρ hρ' hθ hθ1
  obtain ⟨C3, hC3, h3⟩ := i3PsiDiffPiece3Cross_bound_global N hρ hρ' hθ hθ1 hδ hδ1
  refine ⟨72 * C1 + 24 * C2 + 72 * C3, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y y' hz hz' hzz
  have hzz' : 0 < torusParabolicSize (y - x - (y' - x)) := by
    rwa [sub_sub_sub_cancel_right]
  set T : ℝ := |(y - x).1| + |(y' - x).1| + 2 with hT
  have hT0 : 0 ≤ T := by positivity
  have hD0 : 0 ≤ √T + 1 := by positivity
  have hD : ∀ w v : SpaceTime, |w.1| ≤ |(y - x).1| + 1 → |v.1| ≤ |(y' - x).1| + 1 →
      torusParabolicSize (w - v) ≤ √T + 1 := by
    intro w v hw hv
    refine torusParabolicSize_le_sqrt_add_one ?_
    have : (w - v).1 = w.1 - v.1 := rfl
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [hT]
    linarith
  obtain ⟨i1, b1⟩ := h1 hε.1 hε.2 hε'.1 hε'.2 (y - x) (y' - x) hD0 hD hzz' hz hz'
  obtain ⟨i2, b2⟩ := h2 hε.1 hε.2 hε'.1 hε'.2 (y - x) (y' - x) hD0 hD hzz'
  obtain ⟨i3, b3⟩ := h3 hε.1 hε.2 hε'.1 hε'.2 (y - x) (y' - x) hD0 hD hzz' hz hz'
  rw [sub_sub_sub_cancel_right] at b1 b2 b3
  rw [hairerI3PsiField_sub_integral_mul_cross N hρ hρ' hε.1 hε'.1 hW hξ hξ' x y y',
    integral_integral_comb3_global i1 i2 i3]
  set r : ℝ := torusParabolicSize (y - x) with hr
  set r' : ℝ := torusParabolicSize (y' - x) with hr'
  set d : ℝ := torusParabolicSize (y - y') with hd
  set m2 : ℝ := (max ε ε') ^ (2 * θ) with hm2
  have hm20 : 0 ≤ m2 := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  set Q : ℝ := 1 + r ^ 2 + r' ^ 2 with hQ
  have hQ1 : 1 ≤ Q := by
    have := sq_nonneg r
    have := sq_nonneg r'
    rw [hQ]; linarith
  have e1 := abs_fst_le_sq_torusParabolicSize (y - x)
  have e2 := abs_fst_le_sq_torusParabolicSize (y' - x)
  have hsq : √T ≤ (1 + T) / 2 := by linarith [Real.sq_sqrt hT0, sq_nonneg (√T - 1)]
  have hD4 : √T + 1 ≤ 4 * Q := by
    have := sq_nonneg r
    have := sq_nonneg r'
    rw [hT] at hsq
    rw [hQ]
    linarith
  have hDδ : (√T + 1) ^ δ ≤ 4 * Q := (rpow_le_one_add_self hD0 hδ.le (by linarith)).trans
    (by linarith)
  have hDθ : (√T + 1) ^ (2 * θ) ≤ 4 * Q :=
    (rpow_le_one_add_self hD0 (by linarith) (by linarith)).trans (by linarith)
  have hq : 1 + |(y - x).1| ≤ Q := by
    have := sq_nonneg r'
    rw [hQ]; linarith
  have rn : ∀ (z : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize z ^ e := fun z e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have t1 := abs_add_three (18 * (∫ w, ∫ v, i3PsiDiffPiece1Cross N ρ ρ' ε ε' (y - x) (y' - x) w v))
    (6 * (∫ w, ∫ v, i3PsiDiffPiece2Cross N ρ ρ' ε ε' (y - x) (y' - x) w v))
    (18 * ∫ w, ∫ v, i3PsiDiffPiece3Cross N ρ ρ' ε ε' (y - x) (y' - x) w v)
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 18),
    abs_of_pos (by norm_num : (0 : ℝ) < 6)] at t1
  have u1 := mul_le_mul_of_nonneg_left b1 (by norm_num : (0 : ℝ) ≤ 18)
  have u2 := mul_le_mul_of_nonneg_left b2 (by norm_num : (0 : ℝ) ≤ 6)
  have u3 := mul_le_mul_of_nonneg_left b3 (by norm_num : (0 : ℝ) ≤ 18)
  have hcomb := cov_combine_i3Psi (C₁ := C1) (C₂ := C2) (C₃ := C3) (m := m2)
    (Dδ := (√T + 1) ^ δ) (Dθ := (√T + 1) ^ (2 * θ)) (Q := Q) (q := 1 + |(y - x).1|)
    (S := d ^ (-(2 * θ + δ)) + r ^ (-(2 * θ + δ)) + r' ^ (-(2 * θ + δ)))
    (d₁ := d ^ (-(1 : ℝ))) (d₂ := d ^ (-(1 + 2 * θ))) hC1 hC2 hC3 hm20 hQ1
    hDδ hDθ (by positivity) hq
    (add_nonneg (add_nonneg (rn _ _) (rn _ _)) (rn _ _)) (rn _ _) (rn _ _)
  have hfin : (72 * C1 + 24 * C2 + 72 * C3) * m2 * Q ^ 2 *
      (d ^ (-(1 : ℝ)) + d ^ (-(1 + 2 * θ)) +
        (d ^ (-(2 * θ + δ)) + r ^ (-(2 * θ + δ)) + r' ^ (-(2 * θ + δ)))) =
      (72 * C1 + 24 * C2 + 72 * C3) * m2 * Q ^ 2 *
        (d ^ (-(1 : ℝ)) + d ^ (-(1 + 2 * θ)) + d ^ (-(2 * θ + δ)) + r ^ (-(2 * θ + δ)) +
          r' ^ (-(2 * θ + δ))) := by ring
  rw [hfin] at hcomb
  refine t1.trans (le_trans ?_ hcomb)
  linarith [u1, u2, u3]

end RegularityStructures.Phi43

end
