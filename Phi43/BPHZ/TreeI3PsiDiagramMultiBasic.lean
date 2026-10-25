/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiOuter
public import Phi43.BPHZ.TreeI3PsiTwoLevel
public import Phi43.BPHZ.TreeI3PsiSigma
public import Phi43.BPHZ.TreeI3PsiSlab
public import Phi43.BPHZ.TreeI3PsiChainBound

/-!
# Building blocks for the diagrams of `I(Ψ³)Ψ` with general exponents

* `TwoLevelLe G X`: a double-integral majorant `G` whose inner integrals are dominated by an
  integrable function of integral at most `X`; it yields integrability and a bound for every
  integrand dominated by `G`.
* the outer leaf and the inner integral of the chain diagram with the exponents
  `3`, `1 + α`, `1 + κ` (outer) and `4 + γ`, `2 + β` (inner), generalising the case
  `α = γ = 0`, `β = κ = δ` of `singularIntLe_outer_leaf` and `singularIntLe_inner`.

Source: [Hai14] = arXiv:1303.5113v4, (10.37a), Lemma 10.14, p. 167--168.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

/-- A function `G` of two space-time variables is a **two-level majorant with bound `X`** if, for
almost every `w`, `G w` is integrable and its integral is at most `H w`, where `H` is integrable
with `∫ H ≤ X`. -/
def TwoLevelLe (G : SpaceTime → SpaceTime → ℝ) (X : ℝ) : Prop :=
  (∀ᵐ w : SpaceTime ∂volume, Integrable (G w)) ∧
    ∃ H : SpaceTime → ℝ, SingularIntLe H X ∧ ∀ᵐ w : SpaceTime ∂volume, ∫ v, G w v ≤ H w

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

theorem TwoLevelLe.add {G G' : SpaceTime → SpaceTime → ℝ} {X X' : ℝ} (h : TwoLevelLe G X)
    (h' : TwoLevelLe G' X') : TwoLevelLe (fun w v => G w v + G' w v) (X + X') := by
  obtain ⟨hG, H, hH, hGH⟩ := h
  obtain ⟨hG', H', hH', hGH'⟩ := h'
  refine ⟨?_, fun w => H w + H' w, hH.add hH', ?_⟩
  · filter_upwards [hG, hG'] with w a b using a.add b
  · filter_upwards [hG, hG', hGH, hGH'] with w a b c d
    rw [integral_add a b]
    exact add_le_add c d

theorem TwoLevelLe.const_mul {G : SpaceTime → SpaceTime → ℝ} {X : ℝ} (h : TwoLevelLe G X) {c : ℝ}
    (hc : 0 ≤ c) : TwoLevelLe (fun w v => c * G w v) (c * X) := by
  obtain ⟨hG, H, hH, hGH⟩ := h
  refine ⟨?_, fun w => c * H w, hH.const_mul hc, ?_⟩
  · filter_upwards [hG] with w a using a.const_mul c
  · filter_upwards [hGH] with w a
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left a hc

theorem TwoLevelLe.mono_right {G : SpaceTime → SpaceTime → ℝ} {X Y : ℝ} (h : TwoLevelLe G X)
    (hXY : X ≤ Y) : TwoLevelLe G Y := by
  obtain ⟨hG, H, hH, hGH⟩ := h
  exact ⟨hG, H, hH.mono_right hXY, hGH⟩

theorem TwoLevelLe.congr_fun {G G' : SpaceTime → SpaceTime → ℝ} {X : ℝ}
    (h : ∀ w v, G w v = G' w v) (hG : TwoLevelLe G X) : TwoLevelLe G' X := by
  have : G = G' := funext fun w => funext fun v => h w v
  rwa [this] at hG

/-- Integrability and the bound for an integrand dominated by a two-level majorant. -/
theorem TwoLevelLe.integrable_bound {F G : SpaceTime → SpaceTime → ℝ} {X : ℝ}
    (hF : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume)) (hG : TwoLevelLe G X)
    (hFG : ∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume, |F w v| ≤ G w v) :
    Integrable (Function.uncurry F) (volume.prod volume) ∧ |∫ w, ∫ v, F w v| ≤ X := by
  obtain ⟨h1, H, hH, hGH⟩ := hG
  obtain ⟨hint, hbd⟩ := integrable_prod_of_two_level hF h1 hGH hH.1 hFG
  exact ⟨hint, hbd.trans hH.2⟩

private theorem alg_case_one {Ca Cb Cc s1 s2 s3 s4 : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (hCc : 0 ≤ Cc) (n1 : 0 ≤ s1) (n2 : 0 ≤ s2) (n3 : 0 ≤ s3) (n4 : 0 ≤ s4) :
    Ca * (s1 + s2) ≤ (Ca + 2 * Cb + 2 * Cc) * (s1 + s2 + s3 + s4) := by
  nlinarith [mul_nonneg hCa (add_nonneg n3 n4), mul_nonneg hCb (add_nonneg (add_nonneg n1 n2)
    (add_nonneg n3 n4)), mul_nonneg hCc (add_nonneg (add_nonneg n1 n2) (add_nonneg n3 n4))]

private theorem alg_case_two {Ca Cb Cc s1 s2 s3 s4 : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (hCc : 0 ≤ Cc) (n1 : 0 ≤ s1) (n2 : 0 ≤ s2) (n3 : 0 ≤ s3) (n4 : 0 ≤ s4) :
    Cc * (s3 + s3) ≤ (Ca + 2 * Cb + 2 * Cc) * (s1 + s2 + s3 + s4) := by
  nlinarith [mul_nonneg hCa (add_nonneg (add_nonneg n2 n3) n4), mul_nonneg hCb
    (add_nonneg (add_nonneg n2 n3) n4), mul_nonneg hCc n2, mul_nonneg hCc n4,
    mul_nonneg hCc n3, mul_nonneg hCa n1, mul_nonneg hCb n1, mul_nonneg hCc n1]

private theorem alg_case_three {Ca Cb Cc s1 s2 s3 s4 : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (hCc : 0 ≤ Cc) (n1 : 0 ≤ s1) (n2 : 0 ≤ s2) (n3 : 0 ≤ s3) (n4 : 0 ≤ s4) :
    Cb * (s4 + s4) ≤ (Ca + 2 * Cb + 2 * Cc) * (s1 + s2 + s3 + s4) := by
  nlinarith [mul_nonneg hCa (add_nonneg (add_nonneg n1 n3) n4), mul_nonneg hCc
    (add_nonneg (add_nonneg n1 n3) n4), mul_nonneg hCb n1, mul_nonneg hCb n3,
    mul_nonneg hCb n4, mul_nonneg hCa n2, mul_nonneg hCb n2, mul_nonneg hCc n2]

/-- The outer leaf with general exponents: integral of
`s(y-w)^(-3) s(u-w)^(-(1+α)) s(c-w)^(-(1+κ))`, of total order `5 + α + κ`. -/
theorem singularIntLe_outer_leaf_gen {α κ : ℝ} (hα1 : α < 1)
    (hκ1 : κ < 1) (hη : 0 < α + κ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y u c : SpaceTime,
      ((0 < torusParabolicSize (y - c) ∧ 0 < torusParabolicSize (u - c)) ∨
        (y = c ∧ 0 < torusParabolicSize (y - u) ∧ 0 < torusParabolicSize (u - y)) ∨
        (u = c ∧ 0 < torusParabolicSize (y - u) ∧ 0 < torusParabolicSize (u - y))) →
      SingularIntLe (fun w => singularPow 3 y w * singularPow (1 + α) u w *
          singularPow (1 + κ) c w)
        (L * (torusParabolicSize (y - c) ^ (-(α + κ)) + torusParabolicSize (u - c) ^ (-(α + κ)) +
          torusParabolicSize (y - u) ^ (-(α + κ)) + torusParabolicSize (u - y) ^ (-(α + κ)))) := by
  obtain ⟨Ca, hCa, ha⟩ := singularIntLe_mul_three (a := 3) (b := 1 + α) (c := 1 + κ)
    (η := α + κ) (by norm_num) (by linarith) (by linarith) (by linarith) (by linarith) hη
    (by ring)
  obtain ⟨Cb, hCb, hb⟩ := singularIntLe_mul_three (a := 1 + α) (b := 1 + κ) (c := 3)
    (η := α + κ) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) hη
    (by ring)
  obtain ⟨Cc, hCc, hc⟩ := singularIntLe_mul_three (a := 3) (b := 1 + κ) (c := 1 + α)
    (η := α + κ) (by norm_num) (by linarith) (by linarith) (by linarith) (by linarith) hη
    (by ring)
  refine ⟨Ca + 2 * Cb + 2 * Cc, by positivity, fun y u c h => ?_⟩
  have n1 : 0 ≤ torusParabolicSize (y - c) ^ (-(α + κ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have n2 : 0 ≤ torusParabolicSize (u - c) ^ (-(α + κ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have n3 : 0 ≤ torusParabolicSize (y - u) ^ (-(α + κ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have n4 : 0 ≤ torusParabolicSize (u - y) ^ (-(α + κ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  rcases h with ⟨h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
  · refine (ha y u c h1 h2).mono_right ?_
    exact alg_case_one hCa hCb hCc n1 n2 n3 n4
  · have e : (fun w => singularPow 3 y w * singularPow (1 + α) u w * singularPow (1 + κ) y w) =
        fun w => singularPow 3 y w * singularPow (1 + κ) y w * singularPow (1 + α) u w := by
      funext w; ring
    rw [e]
    refine (hc y y u h1 h1).mono_right ?_
    exact alg_case_two hCa hCb hCc n1 n2 n3 n4
  · have e : (fun w => singularPow 3 y w * singularPow (1 + α) u w * singularPow (1 + κ) u w) =
        fun w => singularPow (1 + α) u w * singularPow (1 + κ) u w * singularPow 3 y w := by
      funext w; ring
    rw [e]
    refine (hb u u y h2 h2).mono_right ?_
    exact alg_case_three hCa hCb hCc n1 n2 n3 n4

/-- The inner integral of the chain diagram with general exponents. -/
theorem singularIntLe_inner_gen {γ β : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hβ : 0 < β)
    (hβ3 : β < 3) :
    ∃ Cin : ℝ, 0 ≤ Cin ∧ ∀ c₁ c₂ c₃ w : SpaceTime, 0 < torusParabolicSize (c₁ - w) →
      0 < torusParabolicSize (c₂ - w) → 0 < torusParabolicSize (c₃ - w) →
      SingularIntLe (fun v => (singularPow (4 + γ) c₁ v + singularPow (4 + γ) c₂ v +
          2 * singularPow (4 + γ) c₃ v) * singularPow (2 + β) w v)
        (Cin * (singularPow (1 + (γ + β)) c₁ w + singularPow (1 + (γ + β)) c₂ w +
          2 * singularPow (1 + (γ + β)) c₃ w)) := by
  obtain ⟨C, hC, h⟩ := singularIntLe_mul_two (a := 4 + γ) (b := 2 + β) (η := 1 + (γ + β))
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
  refine ⟨C, hC, fun c₁ c₂ c₃ w p₁ p₂ p₃ => ?_⟩
  have h1 := h c₁ w p₁
  have h2 := h c₂ w p₂
  have h3 := h c₃ w p₃
  have := (h1.add h2).add (h3.const_mul (c := (2 : ℝ)) (by norm_num))
  refine (this.congr_fun (fun v => by ring)).mono_right (le_of_eq ?_)
  simp only [singularPow]
  ring

end RegularityStructures

end
