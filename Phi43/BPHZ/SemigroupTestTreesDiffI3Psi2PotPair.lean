/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2PotBound

/-!
# Pairings of the potentials in the chaos-`1` difference, for arbitrary `u, u'`

Global version of `chaosOne_diff_pp_bound`: the bound is `μ² C (D^δ)²` times the raw sum of the four
pairs of singular terms.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem four_mul_le {c₁ c₂ c₃ c₄ p₁ p₂ p₃ p₄ : ℝ} (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (h₃ : 0 ≤ c₃)
    (h₄ : 0 ≤ c₄) (q₁ : 0 ≤ p₁) (q₂ : 0 ≤ p₂) (q₃ : 0 ≤ p₃) (q₄ : 0 ≤ p₄) :
    c₁ * p₁ + c₂ * p₂ + c₃ * p₃ + c₄ * p₄ ≤ (c₁ + c₂ + c₃ + c₄) * (p₁ + p₂ + p₃ + p₄) := by
  nlinarith [mul_nonneg h₁ (add_nonneg (add_nonneg q₂ q₃) q₄),
    mul_nonneg h₂ (add_nonneg (add_nonneg q₁ q₃) q₄),
    mul_nonneg h₃ (add_nonneg (add_nonneg q₁ q₂) q₄),
    mul_nonneg h₄ (add_nonneg (add_nonneg q₁ q₂) q₃)]

/-- The pairings of potentials, for arbitrary `u, u'`. -/
theorem chaosOne_diff_pp_bound_global {B δ θ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
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
        (∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (u - w) ≤ D) →
        (∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (u' - w) ≤ D) →
        Integrable (fun y => (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u) y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u) y) *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y)) ∧
        ∫ y, (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u) y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u) y) *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) ≤
          μ ^ 2 * C * (D ^ δ) ^ 2 *
            ((torusParabolicSize u ^ (-(1 + (θ + δ) + 0 + 0)) * torusParabolicSize u' ^ (-(θ + δ)) +
                torusParabolicSize u' ^ (-(1 + (θ + δ) + 0 + 0 + (θ + δ)))) +
              (torusParabolicSize u ^ (-(1 + (θ + δ) + 0 + θ)) * torusParabolicSize u' ^ (-δ) +
                torusParabolicSize u' ^ (-(1 + (θ + δ) + 0 + θ + δ))) +
              (torusParabolicSize u ^ (-(1 + δ + θ + 0)) * torusParabolicSize u' ^ (-(θ + δ)) +
                torusParabolicSize u' ^ (-(1 + δ + θ + 0 + (θ + δ)))) +
              (torusParabolicSize u ^ (-(1 + δ + θ + θ)) * torusParabolicSize u' ^ (-δ) +
                torusParabolicSize u' ^ (-(1 + δ + θ + θ + δ)))) := by
  obtain ⟨Cp11, hCp11, hp11⟩ := chaosOne_pp_gen (ε₁ := θ + δ) (ε₁' := θ + δ) (ε₂ := 0) (ε₂' := 0)
    (by linarith) (by linarith) le_rfl le_rfl (by linarith)
  obtain ⟨Cp12, hCp12, hp12⟩ := chaosOne_pp_gen (ε₁ := θ + δ) (ε₁' := δ) (ε₂ := 0) (ε₂' := θ)
    (by linarith) (by linarith) le_rfl (by linarith) (by linarith)
  obtain ⟨Cp21, hCp21, hp21⟩ := chaosOne_pp_gen (ε₁ := δ) (ε₁' := θ + δ) (ε₂ := θ) (ε₂' := 0)
    (by linarith) (by linarith) (by linarith) le_rfl (by linarith)
  obtain ⟨Cp22, hCp22, hp22⟩ := chaosOne_pp_gen (ε₁ := δ) (ε₁' := δ) (ε₂ := θ) (ε₂' := θ)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨Cp11 * (2 * B ^ 3) * (2 * B ^ 3) * B ^ 2 + Cp12 * (2 * B ^ 3) * B ^ 3 * B ^ 2 +
    Cp21 * B ^ 3 * (2 * B ^ 3) * B ^ 2 + Cp22 * B ^ 3 * B ^ 3 * B ^ 2, by positivity, ?_⟩
  intro K Ja Jb Qaa Qbb μ D hμ hD0 hKs hKm hJam hJbm hQam hQbm hK hJa hQa hQb hΔQ hΔJ hQae hQbe u u'
    hu hu' hDu hDu'
  have n3 : (0 : ℝ) ≤ D ^ δ := Real.rpow_nonneg hD0 _
  set Hd : ℝ := 2 * B ^ 3 * D ^ δ with hHd
  set Hb : ℝ := B ^ 3 * D ^ δ with hHb
  have hHd0 : 0 ≤ Hd := by rw [hHd]; positivity
  have hHb0 : 0 ≤ Hb := by rw [hHb]; positivity
  have hMajΔ : ∀ v : SpaceTime, (∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (v - w) ≤ D) →
      ∀ᵐ w : SpaceTime ∂volume, i3Psi2HzDelta K Qaa Qbb v w ≤
        (Hd * μ) * (singularPow 3 0 w * singularPow (2 + (θ + δ)) v w) := by
    intro v hv
    filter_upwards [ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos v] with w a b
    have := i3Psi2HzDelta_le_global (ν := δ) (θ := θ) hB hμ hδ.le hD0 hKs hK hQa hQb hΔQ hQae hQbe
      hv a b
    have e : 2 + θ + δ = 2 + (θ + δ) := by ring
    rw [e] at this
    refine this.trans (le_of_eq ?_)
    rw [hHd]; ring
  have hMajB : ∀ v : SpaceTime, (∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (v - w) ≤ D) →
      ∀ᵐ w : SpaceTime ∂volume, i3Psi2Hz K Qbb v w ≤
        Hb * (singularPow 3 0 w * singularPow (2 + δ) v w) := by
    intro v hv
    filter_upwards [ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos v] with w a b
    exact (i3Psi2Hz_le_global hB hδ.le hD0 hKs hK hQb hQbe hv a b).trans
      (le_of_eq (by rw [hHb]))
  have hJa3 : ∀ x, 0 < torusParabolicSize x → |Ja x| ≤ B * torusParabolicSize x ^ (-(3 + 0 : ℝ)) :=
    fun x hx => by simpa using hJa x hx
  have hΔJm : Measurable (fun x => Ja x - Jb x) := hJam.sub hJbm
  have hmΔ : ∀ v, Measurable (i3Psi2HzDelta K Qaa Qbb v) := fun v =>
    measurable_i3Psi2HzDelta hKm hQam hQbm v
  have hmB : ∀ v, Measurable (i3Psi2Hz K Qbb v) := fun v => measurable_i3Psi2Hz hKm hQbm v
  obtain ⟨j11, k11⟩ := hp11 hB hB (mul_nonneg hHd0 hμ) (mul_nonneg hHd0 hμ) hJam hJam hJa3 hJa3
    (hmΔ u) (hmΔ u') (i3Psi2HzDelta_nonneg K Qaa Qbb u) (i3Psi2HzDelta_nonneg K Qaa Qbb u') u u'
    hu hu' (hMajΔ u hDu) (hMajΔ u' hDu')
  obtain ⟨j12, k12⟩ := hp12 hB (mul_nonneg hB hμ) (mul_nonneg hHd0 hμ) hHb0 hJam hΔJm hJa3 hΔJ
    (hmΔ u) (hmB u') (i3Psi2HzDelta_nonneg K Qaa Qbb u) (i3Psi2Hz_nonneg K Qbb u') u u' hu hu'
    (hMajΔ u hDu) (hMajB u' hDu')
  obtain ⟨j21, k21⟩ := hp21 (mul_nonneg hB hμ) hB hHb0 (mul_nonneg hHd0 hμ) hΔJm hJam hΔJ hJa3
    (hmB u) (hmΔ u') (i3Psi2Hz_nonneg K Qbb u) (i3Psi2HzDelta_nonneg K Qaa Qbb u') u u' hu hu'
    (hMajB u hDu) (hMajΔ u' hDu')
  obtain ⟨j22, k22⟩ := hp22 (mul_nonneg hB hμ) (mul_nonneg hB hμ) hHb0 hHb0 hΔJm hΔJm hΔJ hΔJ
    (hmB u) (hmB u') (i3Psi2Hz_nonneg K Qbb u) (i3Psi2Hz_nonneg K Qbb u') u u' hu hu'
    (hMajB u hDu) (hMajB u' hDu')
  have j12' : Integrable (fun y => i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u) y *
      i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
      i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u) y *
        i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) := j11.add j12
  have j123 : Integrable (fun y => i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u) y *
      i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
      i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u) y *
        i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y +
      i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u) y *
        i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y) := j12'.add j21
  have jall := j123.add j22
  refine ⟨jall.congr (Filter.Eventually.of_forall fun y => by simp only [Pi.add_apply]; ring), ?_⟩
  have e : ∫ y, (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u) y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u) y) *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) =
      (∫ y, i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u) y *
          i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y) +
      (∫ y, i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u) y *
          i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) +
      (∫ y, i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u) y *
          i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y) +
      ∫ y, i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u) y *
          i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y := by
    rw [← integral_add j11 j12, ← integral_add j12' j21, ← integral_add j123 j22]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
  rw [e]
  have nn : ∀ (a : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize a ^ e := fun a e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  set P11 := torusParabolicSize u ^ (-(1 + (θ + δ) + 0 + 0)) * torusParabolicSize u' ^ (-(θ + δ)) +
    torusParabolicSize u' ^ (-(1 + (θ + δ) + 0 + 0 + (θ + δ))) with hP11
  set P12 := torusParabolicSize u ^ (-(1 + (θ + δ) + 0 + θ)) * torusParabolicSize u' ^ (-δ) +
    torusParabolicSize u' ^ (-(1 + (θ + δ) + 0 + θ + δ)) with hP12
  set P21 := torusParabolicSize u ^ (-(1 + δ + θ + 0)) * torusParabolicSize u' ^ (-(θ + δ)) +
    torusParabolicSize u' ^ (-(1 + δ + θ + 0 + (θ + δ))) with hP21
  set P22 := torusParabolicSize u ^ (-(1 + δ + θ + θ)) * torusParabolicSize u' ^ (-δ) +
    torusParabolicSize u' ^ (-(1 + δ + θ + θ + δ))
    with hP22
  have hP11n : 0 ≤ P11 := add_nonneg (mul_nonneg (nn _ _) (nn _ _)) (nn _ _)
  have hP12n : 0 ≤ P12 := add_nonneg (mul_nonneg (nn _ _) (nn _ _)) (nn _ _)
  have hP21n : 0 ≤ P21 := add_nonneg (mul_nonneg (nn _ _) (nn _ _)) (nn _ _)
  have hP22n : 0 ≤ P22 := add_nonneg (mul_nonneg (nn _ _) (nn _ _)) (nn _ _)
  set c11 := Cp11 * (2 * B ^ 3) * (2 * B ^ 3) * B ^ 2 with hc11
  set c12 := Cp12 * (2 * B ^ 3) * B ^ 3 * B ^ 2 with hc12
  set c21 := Cp21 * B ^ 3 * (2 * B ^ 3) * B ^ 2 with hc21
  set c22 := Cp22 * B ^ 3 * B ^ 3 * B ^ 2 with hc22
  have n11 : 0 ≤ c11 := by rw [hc11]; positivity
  have n12 : 0 ≤ c12 := by rw [hc12]; positivity
  have n21 : 0 ≤ c21 := by rw [hc21]; positivity
  have n22 : 0 ≤ c22 := by rw [hc22]; positivity
  have W0 : 0 ≤ μ ^ 2 * (D ^ δ) ^ 2 := by positivity
  have k11' : (∫ y, i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u) y *
      i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y) ≤ (μ ^ 2 * (D ^ δ) ^ 2) * (c11 * P11) := by
    refine k11.trans (le_of_eq ?_)
    rw [hHd, hc11, hP11]; ring
  have k12' : (∫ y, i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u) y *
      i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) ≤
      (μ ^ 2 * (D ^ δ) ^ 2) * (c12 * P12) := by
    refine k12.trans (le_of_eq ?_)
    rw [hHd, hHb, hc12, hP12]; ring
  have k21' : (∫ y, i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u) y *
      i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y) ≤ (μ ^ 2 * (D ^ δ) ^ 2) * (c21 * P21) := by
    refine k21.trans (le_of_eq ?_)
    rw [hHd, hHb, hc21, hP21]; ring
  have k22' : (∫ y, i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u) y *
      i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) ≤
      (μ ^ 2 * (D ^ δ) ^ 2) * (c22 * P22) := by
    refine k22.trans (le_of_eq ?_)
    rw [hHb, hc22, hP22]; ring
  calc _ ≤ (μ ^ 2 * (D ^ δ) ^ 2) * (c11 * P11) + (μ ^ 2 * (D ^ δ) ^ 2) * (c12 * P12) +
        (μ ^ 2 * (D ^ δ) ^ 2) * (c21 * P21) + (μ ^ 2 * (D ^ δ) ^ 2) * (c22 * P22) := by
        linarith [k11', k12', k21', k22']
    _ = (μ ^ 2 * (D ^ δ) ^ 2) * (c11 * P11 + c12 * P12 + c21 * P21 + c22 * P22) := by ring
    _ ≤ (μ ^ 2 * (D ^ δ) ^ 2) * ((c11 + c12 + c21 + c22) * (P11 + P12 + P21 + P22)) :=
        mul_le_mul_of_nonneg_left (four_mul_le n11 n12 n21 n22 hP11n hP12n hP21n hP22n) W0
    _ = _ := by ring

end RegularityStructures

end
