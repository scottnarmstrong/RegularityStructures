/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2Pot
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOnePieces

/-!
# Cross terms and pairings of the potentials in the chaos-`1` difference, for arbitrary `u, u'`

Global versions of `chaosOne_diff_cross_bound`, `chaosOne_diff_pp_bound`.  The right-hand sides are
the raw sums of singular terms (the exponents are not compared, since `s(u), s(u')` may exceed `1`).
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- The cross terms with the potentials, for arbitrary `u, u'`. -/
theorem chaosOne_diff_cross_bound_global {B δ θ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Ja Jb Qaa Qbb : SpaceTime → ℝ} {μ D : ℝ}, 0 ≤ μ → 0 ≤ D →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) → Measurable K → Measurable Ja → Measurable Jb →
      Measurable Qaa → Measurable Qbb →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x → |Ja x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x → |Qaa x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x → |Qbb x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x →
        |Qaa x - Qbb x| ≤ B * μ * torusParabolicSize x ^ (-(1 + θ))) →
      (∀ x, 0 < torusParabolicSize x →
        |Ja x - Jb x| ≤ B * μ * torusParabolicSize x ^ (-(3 + θ))) →
      (∀ x, Qaa (-x) = Qaa x) → (∀ x, Qbb (-x) = Qbb x) →
      ∀ u u' : SpaceTime, 0 < torusParabolicSize u → 0 < torusParabolicSize u' →
        (∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (u' - w) ≤ D) →
        Integrable (fun y => singularPow (3 + (δ / 2 + θ)) u y *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y)) ∧
        ∫ y, singularPow (3 + (δ / 2 + θ)) u y *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) ≤
          μ * C * D ^ δ * (torusParabolicSize u' ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
            torusParabolicSize u ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
            (torusParabolicSize u' ^ (-(1 + δ + θ + (δ / 2 + θ))) +
              torusParabolicSize u ^ (-(1 + δ + θ + (δ / 2 + θ))))) := by
  obtain ⟨Cx1, hCx1, hx1⟩ := chaosOne_cross_gen (ε₁ := θ + δ) (ε₂ := 0) (ε₃ := δ / 2 + θ)
    (by linarith) le_rfl (by linarith) (by linarith)
  obtain ⟨Cx2, hCx2, hx2⟩ := chaosOne_cross_gen (ε₁ := δ) (ε₂ := θ) (ε₃ := δ / 2 + θ)
    (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨Cx1 * (2 * B ^ 3) * B + Cx2 * B ^ 3 * B, by positivity, ?_⟩
  intro K Ja Jb Qaa Qbb μ D hμ hD0 hKs hKm hJam hJbm hQam hQbm hK hJa hQa hQb hΔQ hΔJ hQae hQbe u u'
    hu hu' hDu'
  have n3 : (0 : ℝ) ≤ D ^ δ := Real.rpow_nonneg hD0 _
  set Hd : ℝ := 2 * B ^ 3 * D ^ δ with hHd
  set Hb : ℝ := B ^ 3 * D ^ δ with hHb
  have hHd0 : 0 ≤ Hd := by rw [hHd]; positivity
  have hHb0 : 0 ≤ Hb := by rw [hHb]; positivity
  have hMajΔ : ∀ᵐ w : SpaceTime ∂volume, i3Psi2HzDelta K Qaa Qbb u' w ≤
      (Hd * μ) * (singularPow 3 0 w * singularPow (2 + (θ + δ)) u' w) := by
    filter_upwards [ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos u'] with w a b
    have := i3Psi2HzDelta_le_global (ν := δ) (θ := θ) hB hμ hδ.le hD0 hKs hK hQa hQb hΔQ hQae hQbe
      hDu' a b
    have e : 2 + θ + δ = 2 + (θ + δ) := by ring
    rw [e] at this
    refine this.trans (le_of_eq ?_)
    rw [hHd]; ring
  have hMajB : ∀ᵐ w : SpaceTime ∂volume, i3Psi2Hz K Qbb u' w ≤
      Hb * (singularPow 3 0 w * singularPow (2 + δ) u' w) := by
    filter_upwards [ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos u'] with w a b
    exact (i3Psi2Hz_le_global hB hδ.le hD0 hKs hK hQb hQbe hDu' a b).trans (le_of_eq (by rw [hHb]))
  have hJa3 : ∀ x, 0 < torusParabolicSize x → |Ja x| ≤ B * torusParabolicSize x ^ (-(3 + 0 : ℝ)) :=
    fun x hx => by simpa using hJa x hx
  obtain ⟨j1, k1⟩ := hx1 hB (mul_nonneg hHd0 hμ) hJam hJa3
    (measurable_i3Psi2HzDelta hKm hQam hQbm u') (i3Psi2HzDelta_nonneg K Qaa Qbb u') u u' hu hu'
    hMajΔ
  have hΔJm : Measurable (fun x => Ja x - Jb x) := hJam.sub hJbm
  obtain ⟨j2, k2⟩ := hx2 (mul_nonneg hB hμ) hHb0 hΔJm hΔJ
    (measurable_i3Psi2Hz hKm hQbm u') (i3Psi2Hz_nonneg K Qbb u') u u' hu hu' hMajB
  have jj : Integrable (fun y => singularPow (3 + (δ / 2 + θ)) u y *
      i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y + singularPow (3 + (δ / 2 + θ)) u y *
      i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) := j1.add j2
  refine ⟨jj.congr (Filter.Eventually.of_forall fun y => by simp only; ring), ?_⟩
  have e : ∫ y, singularPow (3 + (δ / 2 + θ)) u y * (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
      i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) =
      (∫ y, singularPow (3 + (δ / 2 + θ)) u y * i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y) +
      ∫ y, singularPow (3 + (δ / 2 + θ)) u y *
        i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y := by
    rw [← integral_add j1 j2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
  rw [e]
  have nn : ∀ (a : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize a ^ e := fun a e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  set X1 := torusParabolicSize u' ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
    torusParabolicSize u ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) with hX1
  set X2 := torusParabolicSize u' ^ (-(1 + δ + θ + (δ / 2 + θ))) +
    torusParabolicSize u ^ (-(1 + δ + θ + (δ / 2 + θ))) with hX2
  have hX10 : 0 ≤ X1 := add_nonneg (nn _ _) (nn _ _)
  have hX20 : 0 ≤ X2 := add_nonneg (nn _ _) (nn _ _)
  have c1 : 0 ≤ Cx1 * (2 * B ^ 3) * B := by positivity
  have c2 : 0 ≤ Cx2 * B ^ 3 * B := by positivity
  have hextra : 0 ≤ μ * D ^ δ * ((Cx1 * (2 * B ^ 3) * B) * X2 + (Cx2 * B ^ 3 * B) * X1) := by
    positivity
  have k1' : (∫ y, singularPow (3 + (δ / 2 + θ)) u y *
      i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y) ≤ μ * D ^ δ * ((Cx1 * (2 * B ^ 3) * B) * X1) := by
    refine k1.trans (le_of_eq ?_)
    rw [hHd, hX1]; ring
  have k2' : (∫ y, singularPow (3 + (δ / 2 + θ)) u y *
      i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) ≤
      μ * D ^ δ * ((Cx2 * B ^ 3 * B) * X2) := by
    refine k2.trans (le_of_eq ?_)
    rw [hHb, hX2]; ring
  have key : μ * (Cx1 * (2 * B ^ 3) * B + Cx2 * B ^ 3 * B) * D ^ δ * (X1 + X2) =
      μ * D ^ δ * ((Cx1 * (2 * B ^ 3) * B) * X1) + μ * D ^ δ * ((Cx2 * B ^ 3 * B) * X2) +
        μ * D ^ δ * ((Cx1 * (2 * B ^ 3) * B) * X2 + (Cx2 * B ^ 3 * B) * X1) := by ring
  rw [hX1, hX2] at key
  linarith

end RegularityStructures

end
