/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductDiagramDom

/-!
# The difference link piece of `I(Ψ²)Ψ`

For a second-difference function `E₁(x₁, x₂)` with
`|E₁(x₁, x₂)| ≤ K μ (s(x₁)^(-(2+σ)) s(x₂)^(-1) + s(x₁)^(-2) s(x₂)^(-(1+σ)))`, the integrand
`a(w) b(v) E₁(w - v, z - z')` is integrable and its iterated integral is bounded by
`C c₁ c₂ K μ (1 + T) (s(z - z')^(-1) s(z)^θA s(z')^θA + s(z - z')^(-(1+σ)) s(z)^θB s(z')^θB)`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

private theorem measurable_ab {a b : SpaceTime → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun p : SpaceTime × SpaceTime => |a p.1| * |b p.2|) :=
  ((continuous_abs.measurable.comp ha).comp measurable_fst).mul
    ((continuous_abs.measurable.comp hb).comp measurable_snd)

/-- The nonnegative link majorant `|a w| |b v| (M s(w - v)^(-γ))`. -/
theorem productLink_majorant_integral {Θ θ₁ θ₂ γ : ℝ} (hθ₁ : 0 ≤ θ₁) (hθ₁Θ : θ₁ ≤ Θ)
    (hθ₂ : 0 ≤ θ₂) (hθ₂Θ : θ₂ ≤ Θ) (hγ : 0 < γ) (hγ5 : γ < 5) (hβ5 : 3 + θ₂ < 5)
    (hβγ : 5 < 3 + θ₂ + γ) (hout : 3 + θ₁ + (3 + θ₂ + γ - 5) < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c₁ c₂ T T' M : ℝ} {z z' : SpaceTime} {a b : SpaceTime → ℝ},
      0 ≤ c₁ → 0 ≤ c₂ → 0 ≤ M → 0 ≤ T → IsGainKernel Θ c₁ T z a → IsGainKernel Θ c₂ T' z' b →
      Integrable (Function.uncurry fun w v => |a w| * |b v| * (M * singularPow γ w v))
          (volume.prod volume) ∧
        ∫ w, ∫ v, |a w| * |b v| * (M * singularPow γ w v) ≤ C * (c₁ * c₂ * M) *
          (torusParabolicSize z ^ θ₁ * torusParabolicSize z' ^ θ₂) * (1 + T) := by
  obtain ⟨C, hC, h⟩ := productLinkGen_bound (Θ := Θ) hθ₁ hθ₁Θ hθ₂ hθ₂Θ hγ hγ5 hβ5 hβγ hout
  refine ⟨C, hC, ?_⟩
  intro c₁ c₂ T T' M z z' a b hc₁ hc₂ hM hT ha hb
  have hm : Measurable (fun p : SpaceTime × SpaceTime =>
      |a p.1| * |b p.2| * (M * singularPow γ p.1 p.2)) :=
    (measurable_ab ha.1 hb.1).mul (measurable_const.mul (measurable_singularPow_pair γ))
  have := h (F := fun w v => |a w| * |b v| * (M * singularPow γ w v)) hc₁ hc₂ hM hT ha hb
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun w => Filter.Eventually.of_forall
      fun v => by
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (mul_nonneg hM (singularPow_nonneg _ _ _)))])
  refine ⟨this.1, ?_⟩
  refine (le_abs_self _).trans this.2

/-- **Difference link piece.** -/
theorem productDiffPiece1_bound {Θ σ θA θB : ℝ} (hσ : 0 < σ) (hθA : 0 < θA) (hθAΘ : θA ≤ Θ)
    (hAout : 2 * θA + σ < 2) (hθB : 0 < θB) (hθBΘ : θB ≤ Θ) (hBout : θB < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c₁ c₂ T T' K μ : ℝ} {z z' : SpaceTime} {a b : SpaceTime → ℝ}
      {E : SpaceTime → SpaceTime → ℝ}, 0 ≤ c₁ → 0 ≤ c₂ → 0 ≤ K → 0 ≤ μ → 0 ≤ T →
      IsGainKernel Θ c₁ T z a → IsGainKernel Θ c₂ T' z' b →
      Measurable (Function.uncurry E) → 0 < torusParabolicSize (z - z') →
      (∀ x₁ x₂ : SpaceTime, 0 < torusParabolicSize x₁ → 0 < torusParabolicSize x₂ →
        |E x₁ x₂| ≤ K * μ * (torusParabolicSize x₁ ^ (-(2 + σ)) * torusParabolicSize x₂ ^ (-(1 : ℝ)) +
          torusParabolicSize x₁ ^ (-(2 : ℝ)) * torusParabolicSize x₂ ^ (-(1 + σ)))) →
      Integrable (Function.uncurry fun w v => a w * b v * E (w - v) (z - z'))
          (volume.prod volume) ∧
        |∫ w, ∫ v, a w * b v * E (w - v) (z - z')| ≤
          C * (c₁ * c₂ * K * μ) * (1 + T) *
            (torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
                (torusParabolicSize z ^ θA * torusParabolicSize z' ^ θA) +
              torusParabolicSize (z - z') ^ (-(1 + σ)) *
                (torusParabolicSize z ^ θB * torusParabolicSize z' ^ θB)) := by
  obtain ⟨CA, hCA, hA⟩ := productLink_majorant_integral (Θ := Θ) (θ₁ := θA) (θ₂ := θA)
    hθA.le hθAΘ hθA.le hθAΘ (γ := 2 + σ) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)
  obtain ⟨CB, hCB, hB⟩ := productLink_majorant_integral (Θ := Θ) (θ₁ := θB) (θ₂ := θB)
    hθB.le hθBΘ hθB.le hθBΘ (γ := 2) (by linarith) (by norm_num) (by linarith)
    (by linarith) (by linarith)
  refine ⟨CA + CB, by positivity, ?_⟩
  intro c₁ c₂ T T' K μ z z' a b E hc₁ hc₂ hK hμ hT ha hb hEm hD hE
  set D := torusParabolicSize (z - z') with hDdef
  have hD0 : 0 ≤ D ^ (-(1 : ℝ)) := Real.rpow_nonneg hD.le _
  have hD1 : 0 ≤ D ^ (-(1 + σ)) := Real.rpow_nonneg hD.le _
  have MA : 0 ≤ K * μ * D ^ (-(1 : ℝ)) := by positivity
  have MB : 0 ≤ K * μ * D ^ (-(1 + σ)) := by positivity
  obtain ⟨iA, bA⟩ := hA hc₁ hc₂ MA hT ha hb
  obtain ⟨iB, bB⟩ := hB hc₁ hc₂ MB hT ha hb
  have hFm : Measurable (Function.uncurry fun w v => a w * b v * E (w - v) (z - z')) := by
    have h1 := ha.1
    have h2 := hb.1
    change Measurable (fun p : SpaceTime × SpaceTime => a p.1 * b p.2 * E (p.1 - p.2) (z - z'))
    exact (((h1.comp measurable_fst).mul (h2.comp measurable_snd))).mul
      (hEm.comp ((measurable_fst.sub measurable_snd).prodMk measurable_const))
  have h1m : Measurable (Function.uncurry fun w v =>
      |a w| * |b v| * (K * μ * D ^ (-(1 : ℝ)) * singularPow (2 + σ) w v)) :=
    (measurable_ab ha.1 hb.1).mul (measurable_const.mul (measurable_singularPow_pair _))
  have h2m : Measurable (Function.uncurry fun w v =>
      |a w| * |b v| * (K * μ * D ^ (-(1 + σ)) * singularPow 2 w v)) :=
    (measurable_ab ha.1 hb.1).mul (measurable_const.mul (measurable_singularPow_pair _))
  have h3m : Measurable (Function.uncurry fun (_ : SpaceTime) (_ : SpaceTime) => (0 : ℝ)) :=
    measurable_const
  obtain ⟨hint, hbd⟩ := abs_iterated_le_of_dominated3
    (F := fun w v => a w * b v * E (w - v) (z - z')) hFm h1m h2m h3m iA iB
    (integrable_zero _ _ _) (by
      filter_upwards with w
      filter_upwards [ae_torusParabolicSize_sub_pos w] with v hv
      have hEb := hE (w - v) (z - z') hv hD
      have e : |a w * b v * E (w - v) (z - z')| = |a w| * |b v| * |E (w - v) (z - z')| := by
        simp [abs_mul]
      rw [e]
      have hab : 0 ≤ |a w| * |b v| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      calc |a w| * |b v| * |E (w - v) (z - z')|
          ≤ |a w| * |b v| * (K * μ * (torusParabolicSize (w - v) ^ (-(2 + σ)) * D ^ (-(1 : ℝ)) +
            torusParabolicSize (w - v) ^ (-(2 : ℝ)) * D ^ (-(1 + σ)))) :=
            mul_le_mul_of_nonneg_left hEb hab
        _ = _ := by simp only [singularPow, add_zero]; ring)
  refine ⟨hint, hbd.trans ?_⟩
  have e0 : (∫ w, ∫ v, (fun (_ : SpaceTime) (_ : SpaceTime) => (0 : ℝ)) w v) = 0 := by simp
  rw [e0, add_zero]
  have hcc : 0 ≤ c₁ * c₂ := mul_nonneg hc₁ hc₂
  have s0 := Real.rpow_nonneg (torusParabolicSize_nonneg z)
  have s0' := Real.rpow_nonneg (torusParabolicSize_nonneg z')
  have T0 : 0 ≤ 1 + T := by linarith
  have eA : CA * (c₁ * c₂ * (K * μ * D ^ (-(1 : ℝ)))) *
      (torusParabolicSize z ^ θA * torusParabolicSize z' ^ θA) * (1 + T) =
      CA * (c₁ * c₂ * K * μ) * (1 + T) *
        (D ^ (-(1 : ℝ)) * (torusParabolicSize z ^ θA * torusParabolicSize z' ^ θA)) := by ring
  have eB : CB * (c₁ * c₂ * (K * μ * D ^ (-(1 + σ)))) *
      (torusParabolicSize z ^ θB * torusParabolicSize z' ^ θB) * (1 + T) =
      CB * (c₁ * c₂ * K * μ) * (1 + T) *
        (D ^ (-(1 + σ)) * (torusParabolicSize z ^ θB * torusParabolicSize z' ^ θB)) := by ring
  rw [eA] at bA
  rw [eB] at bB
  have fA : 0 ≤ (c₁ * c₂ * K * μ) * (1 + T) *
      (D ^ (-(1 : ℝ)) * (torusParabolicSize z ^ θA * torusParabolicSize z' ^ θA)) := by
    have := s0 θA; have := s0' θA; positivity
  have fB : 0 ≤ (c₁ * c₂ * K * μ) * (1 + T) *
      (D ^ (-(1 + σ)) * (torusParabolicSize z ^ θB * torusParabolicSize z' ^ θB)) := by
    have := s0 θB; have := s0' θB; positivity
  linarith [mul_nonneg hCA fA, mul_nonneg hCB fB, mul_nonneg hCA fB, mul_nonneg hCB fA]

end RegularityStructures

end
