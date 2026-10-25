/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductDiagramTerms2

/-!
# The deterministic diagram bound for `I(Ψ²)Ψ`

With gain kernels `a` (at `z`), `b` (at `z'`) and a propagator kernel `Q`, the covariance integrand
of `(∫ a :Ψ²:) Ψ(z)` against `(∫ b :Ψ²:) Ψ(z')` is the sum of the link, cross and chain diagrams
(Wick block `2 C_ac² C_bd + 4 C_ac C_ad C_bc + 4 C_ab C_ac C_cd` at `(a, b, c, d) = (w, z, v, z')`).
`isqPairing_bound`: it is integrable and
`|∫∫| ≤ C c₁ c₂ B³ (1 + T) (s(z - z')^(-1) s(z)^θ s(z')^θ + s(z)^η s(z')^η)`
for `θ ∈ (0, 1)`, `η ∈ (0, 1/2)`, `θ, η ≤ Θ`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The covariance integrand of the field `(∫ a :Ψ²:) Ψ(z)`. -/
def isqDiagramIntegrand (a b Q : SpaceTime → ℝ) (z z' w v : SpaceTime) : ℝ :=
  a w * b v * (2 * Q (w - v) ^ 2 * Q (z - z') + 4 * (Q (w - v) * Q (w - z') * Q (z - v)) +
    4 * (Q (w - z) * Q (w - v) * Q (v - z')))

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

/-- **Deterministic diagram bound for `I(Ψ²)Ψ`.** -/
theorem isqPairing_bound {Θ θ η : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hθΘ : θ ≤ Θ) (hη0 : 0 < η)
    (hη1 : η < 1 / 2) (hηΘ : η ≤ Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c₁ c₂ T T' B : ℝ} {z z' : SpaceTime} {a b Q : SpaceTime → ℝ},
      0 ≤ c₁ → 0 ≤ c₂ → IsGainKernel Θ c₁ T z a → IsGainKernel Θ c₂ T' z' b →
      IsPropKernel B Q → 0 ≤ T → 0 < torusParabolicSize (z - z') →
      Integrable (Function.uncurry (isqDiagramIntegrand a b Q z z')) (volume.prod volume) ∧
        |∫ w, ∫ v, isqDiagramIntegrand a b Q z z' w v| ≤
          C * (c₁ * c₂ * B ^ 3) * (1 + T) *
            (torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
              (torusParabolicSize z ^ θ * torusParabolicSize z' ^ θ) +
              torusParabolicSize z ^ η * torusParabolicSize z' ^ η) := by
  obtain ⟨C1, hC1, h1⟩ := productLinkSq_bound (Θ := Θ) hθ0 hθ1 hθΘ
  obtain ⟨C2, hC2, h2⟩ := productCross_bound (Θ := Θ) hη0 hη1 hηΘ
  obtain ⟨C3, hC3, h3⟩ := productChain3_bound (Θ := Θ) hη0 hη1 hηΘ
  refine ⟨2 * C1 + 4 * C2 + 4 * C3, by positivity, ?_⟩
  intro c₁ c₂ T T' B z z' a b Q hc₁ hc₂ ha hb hQ hT hzz
  have hB := hQ.2.1
  obtain ⟨i1, b1⟩ := h1 hc₁ hc₂ ha hb hQ hT
  obtain ⟨i2, b2⟩ := h2 hc₁ hc₂ ha hb hQ hT
  obtain ⟨i3, b3⟩ := h3 hc₁ hc₂ ha hb hQ hT
  set P1 : ℝ := ∫ w, ∫ v, a w * b v * Q (w - v) ^ 2 with hP1
  set P2 : ℝ := ∫ w, ∫ v, a w * b v * (Q (w - v) * Q (w - z') * Q (z - v)) with hP2
  set P3 : ℝ := ∫ w, ∫ v, a w * b v * (Q (w - z) * Q (w - v) * Q (v - z')) with hP3
  have eF : Function.uncurry (isqDiagramIntegrand a b Q z z') = fun p =>
      2 * Q (z - z') * Function.uncurry (fun w v => a w * b v * Q (w - v) ^ 2) p +
        4 * Function.uncurry (fun w v => a w * b v *
          (Q (w - v) * Q (w - z') * Q (z - v))) p +
        4 * Function.uncurry (fun w v => a w * b v *
          (Q (w - z) * Q (w - v) * Q (v - z'))) p := by
    funext p
    simp only [Function.uncurry, isqDiagramIntegrand]
    ring
  have hint : Integrable (Function.uncurry (isqDiagramIntegrand a b Q z z')) (volume.prod volume) := by
    rw [eF]
    exact ((i1.const_mul (2 * Q (z - z'))).add (i2.const_mul 4)).add (i3.const_mul 4)
  refine ⟨hint, ?_⟩
  have key : ∀ G : SpaceTime → SpaceTime → ℝ,
      Integrable (Function.uncurry G) (volume.prod volume) →
        ∫ p, Function.uncurry G p ∂(volume.prod volume) = ∫ w, ∫ v, G w v :=
    fun G hG => integral_prod _ hG
  have hT' : ∫ w, ∫ v, isqDiagramIntegrand a b Q z z' w v =
      2 * Q (z - z') * P1 + 4 * P2 + 4 * P3 := by
    set U1 : SpaceTime × SpaceTime → ℝ :=
      Function.uncurry (fun w v => a w * b v * Q (w - v) ^ 2) with hU1
    set U2 : SpaceTime × SpaceTime → ℝ := Function.uncurry (fun w v => a w * b v *
      (Q (w - v) * Q (w - z') * Q (z - v))) with hU2
    set U3 : SpaceTime × SpaceTime → ℝ := Function.uncurry (fun w v => a w * b v *
      (Q (w - z) * Q (w - v) * Q (v - z'))) with hU3
    have j1 : Integrable (fun p => 2 * Q (z - z') * U1 p) (volume.prod volume) :=
      i1.const_mul _
    have j2 : Integrable (fun p => 4 * U2 p) (volume.prod volume) := i2.const_mul _
    have j3 : Integrable (fun p => 4 * U3 p) (volume.prod volume) := i3.const_mul _
    have j12 : Integrable (fun p => 2 * Q (z - z') * U1 p + 4 * U2 p) (volume.prod volume) :=
      j1.add j2
    rw [← key _ hint, eF]
    rw [integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
      integral_const_mul, key _ i1, key _ i2, key _ i3]
  rw [hT']
  have hQz : |Q (z - z')| ≤ B * torusParabolicSize (z - z') ^ (-(1 : ℝ)) := hQ.2.2 _ hzz
  have n1 : 0 ≤ torusParabolicSize (z - z') ^ (-(1 : ℝ)) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have s0 : 0 ≤ torusParabolicSize z ^ θ * torusParabolicSize z' ^ θ :=
    mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have s1 : 0 ≤ torusParabolicSize z ^ η * torusParabolicSize z' ^ η :=
    mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have c0 : 0 ≤ c₁ * c₂ := mul_nonneg hc₁ hc₂
  have T0 : 0 ≤ 1 + T := by linarith
  have e1 : |2 * Q (z - z') * P1| ≤ 2 * C1 * (c₁ * c₂ * B ^ 3) * (1 + T) *
      (torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
        (torusParabolicSize z ^ θ * torusParabolicSize z' ^ θ)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc 2 * |Q (z - z')| * |P1| ≤ 2 * (B * torusParabolicSize (z - z') ^ (-(1 : ℝ))) *
          (C1 * (c₁ * c₂ * B ^ 2) * (torusParabolicSize z ^ θ * torusParabolicSize z' ^ θ) *
            (1 + T)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hQz (by norm_num)) b1 (abs_nonneg _)
            (by positivity)
      _ = _ := by ring
  have e2 : |4 * P2| ≤ 4 * C2 * (c₁ * c₂ * B ^ 3) * (1 + T) *
      (torusParabolicSize z ^ η * torusParabolicSize z' ^ η) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    calc 4 * |P2| ≤ 4 * (C2 * (c₁ * c₂ * B ^ 3) *
          (torusParabolicSize z ^ η * torusParabolicSize z' ^ η) * (1 + T)) :=
          mul_le_mul_of_nonneg_left b2 (by norm_num)
      _ = _ := by ring
  have e3 : |4 * P3| ≤ 4 * C3 * (c₁ * c₂ * B ^ 3) * (1 + T) *
      (torusParabolicSize z ^ η * torusParabolicSize z' ^ η) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    calc 4 * |P3| ≤ 4 * (C3 * (c₁ * c₂ * B ^ 3) *
          (torusParabolicSize z ^ η * torusParabolicSize z' ^ η) * (1 + T)) :=
          mul_le_mul_of_nonneg_left b3 (by norm_num)
      _ = _ := by ring
  have t1 := abs_add_le (2 * Q (z - z') * P1 + 4 * P2) (4 * P3)
  have t2 := abs_add_le (2 * Q (z - z') * P1) (4 * P2)
  have X0 : 0 ≤ (c₁ * c₂ * B ^ 3) * (1 + T) := by positivity
  have f1 : 0 ≤ (c₁ * c₂ * B ^ 3) * (1 + T) *
      (torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
        (torusParabolicSize z ^ θ * torusParabolicSize z' ^ θ)) := mul_nonneg X0 (mul_nonneg n1 s0)
  have f2 : 0 ≤ (c₁ * c₂ * B ^ 3) * (1 + T) *
      (torusParabolicSize z ^ η * torusParabolicSize z' ^ η) := mul_nonneg X0 s1
  linarith [mul_nonneg hC1 f1, mul_nonneg hC2 f2, mul_nonneg hC3 f2, mul_nonneg hC1 f2,
    mul_nonneg hC2 f1, mul_nonneg hC3 f1]

end RegularityStructures

end
