/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOneHz
public import RegularityStructures.BPHZ.TreeI3Psi2DiagramYoung

/-!
# The potential parts of the chaos-`1` difference

For the potentials `P1_u = Pot_{J_a}(h^Δ_u)` and `P2_u = Pot_{ΔJ}(h^b_u)` (the two pieces of the
bound of `B^a_u - B^b_u`):

* `chaosOne_diff_cross_bound`: `∫ s(u - y)^(-(3 + δ/2 + θ)) (P1_{u'} + P2_{u'})(y) dy
  ≤ μ C (s(u')^(-E) + s(u)^(-E))`, `E = 1 + 2δ + 2θ`;
* `chaosOne_diff_pp_bound`: `∫ (P1_u + P2_u)(P1_{u'} + P2_{u'}) dy ≤ μ² C (s(u)^(-E) + 2 s(u')^(-E))`.
-/

public section

open MeasureTheory

namespace RegularityStructures

private theorem cross_le_E' {z z' : SpaceTime} {η E : ℝ} (hz : 0 < torusParabolicSize z)
    (hz' : 0 < torusParabolicSize z') (hz1 : torusParabolicSize z ≤ 1)
    (hz1' : torusParabolicSize z' ≤ 1) (h : η ≤ E) :
    torusParabolicSize z' ^ (-η) + torusParabolicSize z ^ (-η) ≤
      torusParabolicSize z' ^ (-E) + torusParabolicSize z ^ (-E) :=
  add_le_add (Real.rpow_le_rpow_of_exponent_ge hz' hz1' (by linarith))
    (Real.rpow_le_rpow_of_exponent_ge hz hz1 (by linarith))

private theorem pp_le_E' {z z' : SpaceTime} {a b e E : ℝ} (hz : 0 < torusParabolicSize z)
    (hz' : 0 < torusParabolicSize z') (hz1' : torusParabolicSize z' ≤ 1) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hE : 0 < E) (hab : a + b = E) (he : e ≤ E) :
    torusParabolicSize z ^ (-a) * torusParabolicSize z' ^ (-b) + torusParabolicSize z' ^ (-e) ≤
      torusParabolicSize z ^ (-E) + 2 * torusParabolicSize z' ^ (-E) := by
  have y := rpow_neg_mul_two_le hz hz' ha hb hE hab
  have m : torusParabolicSize z' ^ (-e) ≤ torusParabolicSize z' ^ (-E) :=
    Real.rpow_le_rpow_of_exponent_ge hz' hz1' (by linarith)
  linarith

/-- The cross terms with the potentials. -/
theorem chaosOne_diff_cross_bound {B δ θ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Ja Jb Qaa Qbb : SpaceTime → ℝ} {μ : ℝ}, 0 ≤ μ →
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
        torusParabolicSize u ≤ 1 → torusParabolicSize u' ≤ 1 →
        Integrable (fun y => singularPow (3 + (δ / 2 + θ)) u y *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y)) ∧
        ∫ y, singularPow (3 + (δ / 2 + θ)) u y *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) ≤
          μ * C * (torusParabolicSize u' ^ (-(1 + 2 * δ + 2 * θ)) +
            torusParabolicSize u ^ (-(1 + 2 * δ + 2 * θ))) := by
  obtain ⟨Cx1, hCx1, hx1⟩ := chaosOne_cross_gen (ε₁ := θ + δ) (ε₂ := 0) (ε₃ := δ / 2 + θ)
    (by linarith) le_rfl (by linarith) (by linarith)
  obtain ⟨Cx2, hCx2, hx2⟩ := chaosOne_cross_gen (ε₁ := δ) (ε₂ := θ) (ε₃ := δ / 2 + θ)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  set Hd : ℝ := 2 * B ^ 3 * 3 ^ δ with hHd
  set Hb : ℝ := B ^ 3 * 3 ^ δ with hHb
  have hHd0 : 0 ≤ Hd := by rw [hHd]; positivity
  have hHb0 : 0 ≤ Hb := by rw [hHb]; positivity
  refine ⟨Cx1 * Hd * B + Cx2 * Hb * B, by positivity, ?_⟩
  intro K Ja Jb Qaa Qbb μ hμ hKs hKm hJam hJbm hQam hQbm hK hJa hQa hQb hΔQ hΔJ hQae hQbe u u'
    hu hu' hu1 hu1'
  have hMajΔ : ∀ᵐ w : SpaceTime ∂volume, i3Psi2HzDelta K Qaa Qbb u' w ≤
      (Hd * μ) * (singularPow 3 0 w * singularPow (2 + (θ + δ)) u' w) := by
    filter_upwards [ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos u'] with w a b
    have := i3Psi2HzDelta_le (ν := δ) (θ := θ) hB hμ hδ.le hKs hK hQa hQb hΔQ hQae hQbe hu1' a b
    have e : 2 + θ + δ = 2 + (θ + δ) := by ring
    rw [e] at this
    refine this.trans (le_of_eq ?_)
    rw [hHd]; ring
  have hMajB : ∀ᵐ w : SpaceTime ∂volume, i3Psi2Hz K Qbb u' w ≤
      Hb * (singularPow 3 0 w * singularPow (2 + δ) u' w) := by
    filter_upwards [ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos u'] with w a b
    exact (i3Psi2Hz_le hB hδ.le hKs hK hQb hQbe hu1' a b).trans (le_of_eq (by rw [hHb]))
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
  have c1 := cross_le_E' hu hu' hu1 hu1' (η := 1 + (θ + δ) + 0 + (δ / 2 + θ))
    (E := 1 + 2 * δ + 2 * θ) (by linarith)
  have c2 := cross_le_E' hu hu' hu1 hu1' (η := 1 + δ + θ + (δ / 2 + θ))
    (E := 1 + 2 * δ + 2 * θ) (by linarith)
  have e : ∫ y, singularPow (3 + (δ / 2 + θ)) u y * (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
      i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) =
      (∫ y, singularPow (3 + (δ / 2 + θ)) u y * i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y) +
      ∫ y, singularPow (3 + (δ / 2 + θ)) u y *
        i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y := by
    rw [← integral_add j1 j2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
  rw [e]
  have m1 := mul_le_mul_of_nonneg_left c1 (by positivity : 0 ≤ μ * (Cx1 * Hd * B))
  have m2 := mul_le_mul_of_nonneg_left c2 (by positivity : 0 ≤ μ * (Cx2 * Hb * B))
  linarith

/-- The pairings of potentials. -/
theorem chaosOne_diff_pp_bound {B δ θ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Ja Jb Qaa Qbb : SpaceTime → ℝ} {μ : ℝ}, 0 ≤ μ →
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
        torusParabolicSize u ≤ 1 → torusParabolicSize u' ≤ 1 →
        Integrable (fun y => (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u) y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u) y) *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y)) ∧
        ∫ y, (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u) y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u) y) *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) ≤
          μ ^ 2 * C * (torusParabolicSize u ^ (-(1 + 2 * δ + 2 * θ)) +
            2 * torusParabolicSize u' ^ (-(1 + 2 * δ + 2 * θ))) := by
  obtain ⟨Cp11, hCp11, hp11⟩ := chaosOne_pp_gen (ε₁ := θ + δ) (ε₁' := θ + δ) (ε₂ := 0) (ε₂' := 0)
    (by linarith) (by linarith) le_rfl le_rfl (by linarith)
  obtain ⟨Cp12, hCp12, hp12⟩ := chaosOne_pp_gen (ε₁ := θ + δ) (ε₁' := δ) (ε₂ := 0) (ε₂' := θ)
    (by linarith) (by linarith) le_rfl (by linarith) (by linarith)
  obtain ⟨Cp21, hCp21, hp21⟩ := chaosOne_pp_gen (ε₁ := δ) (ε₁' := θ + δ) (ε₂ := θ) (ε₂' := 0)
    (by linarith) (by linarith) (by linarith) le_rfl (by linarith)
  obtain ⟨Cp22, hCp22, hp22⟩ := chaosOne_pp_gen (ε₁ := δ) (ε₁' := δ) (ε₂ := θ) (ε₂' := θ)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  set Hd : ℝ := 2 * B ^ 3 * 3 ^ δ with hHd
  set Hb : ℝ := B ^ 3 * 3 ^ δ with hHb
  have hHd0 : 0 ≤ Hd := by rw [hHd]; positivity
  have hHb0 : 0 ≤ Hb := by rw [hHb]; positivity
  refine ⟨Cp11 * Hd * Hd * B ^ 2 + Cp12 * Hd * Hb * B ^ 2 + Cp21 * Hb * Hd * B ^ 2 +
    Cp22 * Hb * Hb * B ^ 2, by positivity, ?_⟩
  intro K Ja Jb Qaa Qbb μ hμ hKs hKm hJam hJbm hQam hQbm hK hJa hQa hQb hΔQ hΔJ hQae hQbe u u'
    hu hu' hu1 hu1'
  have hMajΔ : ∀ v : SpaceTime, torusParabolicSize v ≤ 1 → ∀ᵐ w : SpaceTime ∂volume,
      i3Psi2HzDelta K Qaa Qbb v w ≤ (Hd * μ) * (singularPow 3 0 w * singularPow (2 + (θ + δ)) v w) := by
    intro v hv1
    filter_upwards [ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos v] with w a b
    have := i3Psi2HzDelta_le (ν := δ) (θ := θ) hB hμ hδ.le hKs hK hQa hQb hΔQ hQae hQbe hv1 a b
    have e : 2 + θ + δ = 2 + (θ + δ) := by ring
    rw [e] at this
    refine this.trans (le_of_eq ?_)
    rw [hHd]; ring
  have hMajB : ∀ v : SpaceTime, torusParabolicSize v ≤ 1 → ∀ᵐ w : SpaceTime ∂volume,
      i3Psi2Hz K Qbb v w ≤ Hb * (singularPow 3 0 w * singularPow (2 + δ) v w) := by
    intro v hv1
    filter_upwards [ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos v] with w a b
    exact (i3Psi2Hz_le hB hδ.le hKs hK hQb hQbe hv1 a b).trans (le_of_eq (by rw [hHb]))
  have hJa3 : ∀ x, 0 < torusParabolicSize x → |Ja x| ≤ B * torusParabolicSize x ^ (-(3 + 0 : ℝ)) :=
    fun x hx => by simpa using hJa x hx
  have hΔJm : Measurable (fun x => Ja x - Jb x) := hJam.sub hJbm
  have hmΔ : ∀ v, Measurable (i3Psi2HzDelta K Qaa Qbb v) := fun v =>
    measurable_i3Psi2HzDelta hKm hQam hQbm v
  have hmB : ∀ v, Measurable (i3Psi2Hz K Qbb v) := fun v => measurable_i3Psi2Hz hKm hQbm v
  obtain ⟨j11, k11⟩ := hp11 hB hB (mul_nonneg hHd0 hμ) (mul_nonneg hHd0 hμ) hJam hJam hJa3 hJa3
    (hmΔ u) (hmΔ u') (i3Psi2HzDelta_nonneg K Qaa Qbb u) (i3Psi2HzDelta_nonneg K Qaa Qbb u') u u'
    hu hu' (hMajΔ u hu1) (hMajΔ u' hu1')
  obtain ⟨j12, k12⟩ := hp12 hB (mul_nonneg hB hμ) (mul_nonneg hHd0 hμ) hHb0 hJam hΔJm hJa3 hΔJ
    (hmΔ u) (hmB u') (i3Psi2HzDelta_nonneg K Qaa Qbb u) (i3Psi2Hz_nonneg K Qbb u') u u' hu hu'
    (hMajΔ u hu1) (hMajB u' hu1')
  obtain ⟨j21, k21⟩ := hp21 (mul_nonneg hB hμ) hB hHb0 (mul_nonneg hHd0 hμ) hΔJm hJam hΔJ hJa3
    (hmB u) (hmΔ u') (i3Psi2Hz_nonneg K Qbb u) (i3Psi2HzDelta_nonneg K Qaa Qbb u') u u' hu hu'
    (hMajB u hu1) (hMajΔ u' hu1')
  obtain ⟨j22, k22⟩ := hp22 (mul_nonneg hB hμ) (mul_nonneg hB hμ) hHb0 hHb0 hΔJm hΔJm hΔJ hΔJ
    (hmB u) (hmB u') (i3Psi2Hz_nonneg K Qbb u) (i3Psi2Hz_nonneg K Qbb u') u u' hu hu'
    (hMajB u hu1) (hMajB u' hu1')
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
  have y11 := pp_le_E' hu hu' hu1' (a := 1 + (θ + δ) + 0 + 0) (b := θ + δ)
    (e := 1 + (θ + δ) + 0 + 0 + (θ + δ)) (E := 1 + 2 * δ + 2 * θ) (by linarith) (by linarith)
    (by linarith) (by ring) (by linarith)
  have y12 := pp_le_E' hu hu' hu1' (a := 1 + (θ + δ) + 0 + θ) (b := δ)
    (e := 1 + (θ + δ) + 0 + θ + δ) (E := 1 + 2 * δ + 2 * θ) (by linarith) (by linarith)
    (by linarith) (by ring) (by linarith)
  have y21 := pp_le_E' hu hu' hu1' (a := 1 + δ + θ + 0) (b := θ + δ)
    (e := 1 + δ + θ + 0 + (θ + δ)) (E := 1 + 2 * δ + 2 * θ) (by linarith) (by linarith)
    (by linarith) (by ring) (by linarith)
  have y22 := pp_le_E' hu hu' hu1' (a := 1 + δ + θ + θ) (b := δ)
    (e := 1 + δ + θ + θ + δ) (E := 1 + 2 * δ + 2 * θ) (by linarith) (by linarith)
    (by linarith) (by ring) (by linarith)
  have m11 := mul_le_mul_of_nonneg_left y11 (by positivity : 0 ≤ μ ^ 2 * (Cp11 * Hd * Hd * B ^ 2))
  have m12 := mul_le_mul_of_nonneg_left y12 (by positivity : 0 ≤ μ ^ 2 * (Cp12 * Hd * Hb * B ^ 2))
  have m21 := mul_le_mul_of_nonneg_left y21 (by positivity : 0 ≤ μ ^ 2 * (Cp21 * Hb * Hd * B ^ 2))
  have m22 := mul_le_mul_of_nonneg_left y22 (by positivity : 0 ≤ μ ^ 2 * (Cp22 * Hb * Hb * B ^ 2))
  linarith

end RegularityStructures

end
