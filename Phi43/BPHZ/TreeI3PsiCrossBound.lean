/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiCrossCov

/-!
# The pointwise covariance bound for the difference `I₃Ψ_{ρ,ε} - I₃Ψ_{ρ',ε'}`

`hairerI3PsiField_sub_cov_bound_cross`: for `θ ∈ (0, 1/8]`, `δ ∈ (0, 1/4]`, scales `ε, ε' ∈ (0, 1]`, a
base point `x` and points `y, ȳ` with `s(y - x), s(ȳ - x) ≤ 1` and `y, ȳ, x` distinct,
`|E[(I₃Ψ_{ρ,ε} - I₃Ψ_{ρ',ε'})(y) (I₃Ψ_{ρ,ε} - I₃Ψ_{ρ',ε'})(ȳ)]| ≤ C (max ε ε')^(2θ) (S + Y)` with
`S = s(y-ȳ)^(-η) + s(y-x)^(-η) + s(ȳ-x)^(-η)`, `η = 2θ + δ`, and
`Y = s(y-ȳ)^(-1) s(ȳ-x)^(1-δ-2θ) + s(y-ȳ)^(-(1+2θ)) s(ȳ-x)^(1-δ)`.
The constant is independent of the scales, the points, the probability space and the noises.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem integral_integral_comb3_cross {h₁ h₂ h₃ : SpaceTime → SpaceTime → ℝ} {c₁ c₂ c₃ : ℝ}
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

/-- **Pointwise covariance bound for the difference `I₃Ψ_{ρ,ε} - I₃Ψ_{ρ',ε'}`**, with the full gain
`(max ε ε')^(2θ)`. -/
theorem hairerI3PsiField_sub_cov_bound_cross (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') → torusParabolicSize (y - x) ≤ 1 →
        torusParabolicSize (y' - x) ≤ 1 →
          |∫ ω, (hairerI3PsiField N ρ ε ξ x ω y - hairerI3PsiField N ρ' ε' ξ' x ω y) *
              (hairerI3PsiField N ρ ε ξ x ω y' - hairerI3PsiField N ρ' ε' ξ' x ω y') ∂P| ≤
            C * (max ε ε') ^ (2 * θ) *
              (torusParabolicSize (y - y') ^ (-(2 * θ + δ)) +
                torusParabolicSize (y - x) ^ (-(2 * θ + δ)) +
                torusParabolicSize (y' - x) ^ (-(2 * θ + δ)) +
                (torusParabolicSize (y - y') ^ (-(1 : ℝ)) *
                    torusParabolicSize (y' - x) ^ (1 - δ - 2 * θ) +
                  torusParabolicSize (y - y') ^ (-(1 + 2 * θ)) *
                    torusParabolicSize (y' - x) ^ (1 - δ))) := by
  obtain ⟨C1, hC1, h1⟩ := i3PsiDiffPiece1Cross_bound N hρ hρ' hθ hθ1 hδ hδ1
  obtain ⟨C2, hC2, h2⟩ := i3PsiDiffPiece2Cross_bound N hρ hρ' hθ hθ1 hδ hδ1
  obtain ⟨C3, hC3, h3⟩ := i3PsiDiffPiece3Cross_bound N hρ hρ' hθ hθ1 hδ hδ1
  refine ⟨18 * C1 + 6 * C2 + 18 * C3, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y y' hz hz' hzz hz1 hz1'
  have hzz' : 0 < torusParabolicSize (y - x - (y' - x)) := by
    rwa [sub_sub_sub_cancel_right]
  obtain ⟨i1, b1⟩ := h1 hε.1 hε.2 hε'.1 hε'.2 (y - x) (y' - x) hzz' hz hz' hz1 hz1'
  obtain ⟨i2, b2⟩ := h2 hε.1 hε.2 hε'.1 hε'.2 (y - x) (y' - x) hzz' hz1 hz1'
  obtain ⟨i3, b3⟩ := h3 hε.1 hε.2 hε'.1 hε'.2 (y - x) (y' - x) hzz' hz hz' hz1 hz1'
  rw [sub_sub_sub_cancel_right] at b1 b2 b3
  rw [hairerI3PsiField_sub_integral_mul_cross N hρ hρ' hε.1 hε'.1 hW hξ hξ' x y y',
    integral_integral_comb3_cross i1 i2 i3]
  set μ : ℝ := (max ε ε') ^ (2 * θ) with hμ
  have hμ0 : 0 ≤ μ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  set S : ℝ := torusParabolicSize (y - y') ^ (-(2 * θ + δ)) +
    torusParabolicSize (y - x) ^ (-(2 * θ + δ)) + torusParabolicSize (y' - x) ^ (-(2 * θ + δ))
    with hS
  set Y : ℝ := torusParabolicSize (y - y') ^ (-(1 : ℝ)) *
      torusParabolicSize (y' - x) ^ (1 - δ - 2 * θ) +
    torusParabolicSize (y - y') ^ (-(1 + 2 * θ)) * torusParabolicSize (y' - x) ^ (1 - δ)
    with hY
  have hS0 : 0 ≤ S := by
    have := fun u : ℝ => Real.rpow_nonneg (torusParabolicSize_nonneg (y - y')) u
    have h' := fun u : ℝ => Real.rpow_nonneg (torusParabolicSize_nonneg (y - x)) u
    have h'' := fun u : ℝ => Real.rpow_nonneg (torusParabolicSize_nonneg (y' - x)) u
    rw [hS]; linarith [this (-(2 * θ + δ)), h' (-(2 * θ + δ)), h'' (-(2 * θ + δ))]
  have hY0 : 0 ≤ Y := by
    rw [hY]
    exact add_nonneg (mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
      (mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have t1 := abs_add_le (18 * (∫ w, ∫ v, i3PsiDiffPiece1Cross N ρ ρ' ε ε' (y - x) (y' - x) w v) +
    6 * (∫ w, ∫ v, i3PsiDiffPiece2Cross N ρ ρ' ε ε' (y - x) (y' - x) w v))
    (18 * ∫ w, ∫ v, i3PsiDiffPiece3Cross N ρ ρ' ε ε' (y - x) (y' - x) w v)
  have t2 := abs_add_le (18 * (∫ w, ∫ v, i3PsiDiffPiece1Cross N ρ ρ' ε ε' (y - x) (y' - x) w v))
    (6 * (∫ w, ∫ v, i3PsiDiffPiece2Cross N ρ ρ' ε ε' (y - x) (y' - x) w v))
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 18)] at t1 t2
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)] at t2
  have u1 := mul_le_mul_of_nonneg_left b1 (by norm_num : (0 : ℝ) ≤ 18)
  have u2 := mul_le_mul_of_nonneg_left b2 (by norm_num : (0 : ℝ) ≤ 6)
  have u3 := mul_le_mul_of_nonneg_left b3 (by norm_num : (0 : ℝ) ≤ 18)
  have v1 := mul_nonneg (mul_nonneg hC1 hμ0) hS0
  have v3 := mul_nonneg (mul_nonneg hC3 hμ0) hS0
  have v2 := mul_nonneg (mul_nonneg hC2 hμ0) hY0
  have w1 := mul_nonneg (mul_nonneg hC2 hμ0) hS0
  have w2 := mul_nonneg (mul_nonneg hC1 hμ0) hY0
  have w3 := mul_nonneg (mul_nonneg hC3 hμ0) hY0
  linarith [t1, t2, u1, u2, u3, v1, v2, v3, w1, w2, w3]

end RegularityStructures.Phi43

end
