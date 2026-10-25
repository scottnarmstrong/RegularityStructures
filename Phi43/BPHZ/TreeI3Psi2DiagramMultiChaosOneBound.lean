/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOnePieces
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOneAbar
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOneIdentity
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiTarget
public import RegularityStructures.BPHZ.TreeI3Psi2ChaosOneParts
public import RegularityStructures.BPHZ.TreeI3Psi2DiagramYoung

/-!
# Bound for the chaos-`1` part of the difference

`i3Psi2Chaos1Diff_bound`: for the functions `D^a_z = Ā_a(z - ·) - B^a_z` and `D^b_z`, the integral
`∫ (D^a_z - D^b_z)(D^a_{z'} - D^b_{z'}) dy` is bounded by `C μ² T(z, z')`, where
`T = i3Psi2DiffTarget δ θ`.  The proof splits the integrand into the four products of the
renormalised convolutions `ΔĀ(z - ·)`, `ΔĀ(z' - ·)` (order `3 + δ/2 + θ`, factor `μ`) and the
regular parts, dominated by the potentials `Pot_{J_a}(h^Δ_z) + Pot_{ΔJ}(h^b_z)` (factor `μ`).
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Bound for the chaos-`1` part of the difference.** -/
theorem i3Psi2Chaos1Diff_bound {B δ θ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Ja Jb Qaa Qbb : SpaceTime → ℝ} {μ M MQ ca cb : ℝ}, 0 ≤ μ →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      Integrable K → Measurable K → Measurable Ja → Measurable Jb → Measurable Qaa →
      Measurable Qbb → (∀ x, |Ja x| ≤ M) → (∀ x, |Jb x| ≤ M) → Integrable Ja → Integrable Jb →
      (∀ x, |Qaa x| ≤ MQ) → (∀ x, |Qbb x| ≤ MQ) →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x → |Ja x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |Ja (u + h) - Ja u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x → |Qaa x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x → |Qbb x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x →
        |Qaa x - Qbb x| ≤ B * μ * torusParabolicSize x ^ (-(1 + θ))) →
      (∀ x, 0 < torusParabolicSize x →
        |Ja x - Jb x| ≤ B * μ * torusParabolicSize x ^ (-(3 + θ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |(Ja (u + h) - Jb (u + h)) - (Ja u - Jb u)| ≤
            B * μ * torusParabolicSize h ^ (1 - θ) * torusParabolicSize u ^ (-(3 + θ) - (1 - θ))) →
      (∀ x, Qaa x = ∫ w, Ja (x + w) * Ja w) → (∀ x, Qbb x = ∫ w, Jb (x + w) * Jb w) →
      ca = 2 * ∫ x, K x * Qaa x ^ 2 → cb = 2 * ∫ x, K x * Qbb x ^ 2 →
      ∀ z z' : SpaceTime, 0 < torusParabolicSize z → 0 < torusParabolicSize z' →
        0 < torusParabolicSize (z - z') → torusParabolicSize z ≤ 1 → torusParabolicSize z' ≤ 1 →
        Integrable (fun y => (i3Psi2D K Qaa Ja ca z y - i3Psi2D K Qbb Jb cb z y) *
          (i3Psi2D K Qaa Ja ca z' y - i3Psi2D K Qbb Jb cb z' y)) ∧
        |∫ y, (i3Psi2D K Qaa Ja ca z y - i3Psi2D K Qbb Jb cb z y) *
          (i3Psi2D K Qaa Ja ca z' y - i3Psi2D K Qbb Jb cb z' y)| ≤
          C * μ ^ 2 * i3Psi2DiffTarget δ θ z z' := by
  have hν : 0 < δ / 2 := by linarith
  obtain ⟨C1, hC1, hA⟩ := abs_i3Psi2Abar_sub_le hB hδ hδ1 hθ hθ1
  obtain ⟨Cu, hCu, hu⟩ := integrable_and_integral_singularPow_mul_le (a := 3 + (δ / 2 + θ))
    (b := 3 + (δ / 2 + θ)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨Cc, hCc, hcross⟩ := chaosOne_diff_cross_bound hB hδ hδ1 hθ hθ1
  obtain ⟨Cq, hCq, hpp⟩ := chaosOne_diff_pp_bound hB hδ hδ1 hθ hθ1
  refine ⟨C1 ^ 2 * Cu + 4 * C1 * Cc + 3 * Cq, by positivity, ?_⟩
  intro K Ja Jb Qaa Qbb μ M MQ ca cb hμ hKs hKi hKm hJam hJbm hQam hQbm hJab hJbb hJai hJbi hQab
    hQbb hK hJa hJainc hQa hQb hΔQ hΔJ hΔJinc hQJa hQJb hca hcb z z' hz hz' hzz hz1 hz1'
  have hQae := i3Psi2_Q_neg hQJa
  have hQbe := i3Psi2_Q_neg hQJb
  have hDa : ∀ w y, i3Psi2D K Qaa Ja ca w y =
      i3Psi2Abar K Ja Qaa (w - y) - i3Psi2Bz K Ja Qaa w y := fun w y =>
    i3Psi2_smear_sub_eq hJam hJab hQJa hQam hQab hKi hca w y
  have hDb : ∀ w y, i3Psi2D K Qbb Jb cb w y =
      i3Psi2Abar K Jb Qbb (w - y) - i3Psi2Bz K Jb Qbb w y := fun w y =>
    i3Psi2_smear_sub_eq hJbm hJbb hQJb hQbm hQbb hKi hcb w y
  obtain ⟨iDaz, -⟩ := integrable_and_bdd_i3Psi2D (K := K) (Q := Qaa) (J := Ja) ca hJam hJab hJai
    hQam hQab hKi z
  obtain ⟨iDbz, -⟩ := integrable_and_bdd_i3Psi2D (K := K) (Q := Qbb) (J := Jb) cb hJbm hJbb hJbi
    hQbm hQbb hKi z
  obtain ⟨iDaz', -⟩ := integrable_and_bdd_i3Psi2D (K := K) (Q := Qaa) (J := Ja) ca hJam hJab hJai
    hQam hQab hKi z'
  obtain ⟨iDbz', -⟩ := integrable_and_bdd_i3Psi2D (K := K) (Q := Qbb) (J := Jb) cb hJbm hJbb hJbi
    hQbm hQbb hKi z'
  have hFm : AEStronglyMeasurable (fun y => (i3Psi2D K Qaa Ja ca z y - i3Psi2D K Qbb Jb cb z y) *
      (i3Psi2D K Qaa Ja ca z' y - i3Psi2D K Qbb Jb cb z' y)) volume :=
    (iDaz.aestronglyMeasurable.sub iDbz.aestronglyMeasurable).mul
      (iDaz'.aestronglyMeasurable.sub iDbz'.aestronglyMeasurable)
  have hE : (0 : ℝ) < 1 + 2 * δ + 2 * θ := by linarith
  have eA : (3 + δ / 2 + θ : ℝ) = 3 + (δ / 2 + θ) := by ring
  have hA' : ∀ x : SpaceTime, 0 < torusParabolicSize x →
      |i3Psi2Abar K Ja Qaa x - i3Psi2Abar K Jb Qbb x| ≤
        C1 * μ * torusParabolicSize x ^ (-(3 + (δ / 2 + θ))) := by
    intro x hx
    have := hA hμ hKs hKi hKm hJam hJbm hQam hQbm hJab hJbb hQab hQbb hK hJa hJainc hQa hQb hΔQ
      hΔJ hΔJinc x hx
    rwa [eA] at this
  have hF : ∀ y, (i3Psi2D K Qaa Ja ca z y - i3Psi2D K Qbb Jb cb z y) *
      (i3Psi2D K Qaa Ja ca z' y - i3Psi2D K Qbb Jb cb z' y) =
      ((i3Psi2Abar K Ja Qaa (z - y) - i3Psi2Abar K Jb Qbb (z - y)) -
        (i3Psi2Bz K Ja Qaa z y - i3Psi2Bz K Jb Qbb z y)) *
      ((i3Psi2Abar K Ja Qaa (z' - y) - i3Psi2Abar K Jb Qbb (z' - y)) -
        (i3Psi2Bz K Ja Qaa z' y - i3Psi2Bz K Jb Qbb z' y)) := fun y => by
    simp only [hDa, hDb]; ring
  have hbB : ∀ u y, |i3Psi2Bz K Ja Qaa u y - i3Psi2Bz K Jb Qbb u y| ≤
      i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u) y +
        i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u) y :=
    fun u y => abs_i3Psi2Bz_sub_le_pot hKi hJam hJbm hJab hJbb hQam hQbm hQab hQbb u y
  have iuu := (hu z z' hzz).1
  have bu := (hu z z' hzz).2
  have eu : (5 - (3 + (δ / 2 + θ)) - (3 + (δ / 2 + θ)) : ℝ) = -(1 + δ + 2 * θ) := by ring
  rw [eu] at bu
  obtain ⟨jx, kx⟩ := hcross hμ hKs hKm hJam hJbm hQam hQbm hK hJa hQa hQb hΔQ hΔJ hQae hQbe
    z z' hz hz' hz1 hz1'
  obtain ⟨jy, ky⟩ := hcross hμ hKs hKm hJam hJbm hQam hQbm hK hJa hQa hQb hΔQ hΔJ hQae hQbe
    z' z hz' hz hz1' hz1
  obtain ⟨jp, kp⟩ := hpp hμ hKs hKm hJam hJbm hQam hQbm hK hJa hQa hQb hΔQ hΔJ hQae hQbe
    z z' hz hz' hz1 hz1'
  have i₁ : Integrable (fun y => (C1 * μ * singularPow (3 + (δ / 2 + θ)) z y) *
      (C1 * μ * singularPow (3 + (δ / 2 + θ)) z' y)) :=
    (iuu.const_mul ((C1 * μ) * (C1 * μ))).congr (Filter.Eventually.of_forall fun y => by
      simp only; ring)
  have b₁ : ∫ y, (C1 * μ * singularPow (3 + (δ / 2 + θ)) z y) *
      (C1 * μ * singularPow (3 + (δ / 2 + θ)) z' y) ≤
      (C1 * μ) * (C1 * μ) * (Cu * torusParabolicSize (z - z') ^ (-(1 + δ + 2 * θ))) := by
    calc _ = ∫ y, (C1 * μ) * (C1 * μ) * (singularPow (3 + (δ / 2 + θ)) z y *
          singularPow (3 + (δ / 2 + θ)) z' y) :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
      _ = (C1 * μ) * (C1 * μ) * ∫ y, singularPow (3 + (δ / 2 + θ)) z y *
          singularPow (3 + (δ / 2 + θ)) z' y := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left bu (mul_nonneg (mul_nonneg hC1 hμ) (mul_nonneg hC1 hμ))
  have i₂ : Integrable (fun y => (C1 * μ * singularPow (3 + (δ / 2 + θ)) z y) *
      (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z') y +
        i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z') y)) :=
    (jx.const_mul (C1 * μ)).congr (Filter.Eventually.of_forall fun y => by simp only; ring)
  have b₂ : ∫ y, (C1 * μ * singularPow (3 + (δ / 2 + θ)) z y) *
      (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z') y +
        i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z') y) ≤
      C1 * μ * (μ * Cc * (torusParabolicSize z' ^ (-(1 + 2 * δ + 2 * θ)) +
        torusParabolicSize z ^ (-(1 + 2 * δ + 2 * θ)))) := by
    calc _ = ∫ y, C1 * μ * (singularPow (3 + (δ / 2 + θ)) z y *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z') y)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
      _ = C1 * μ * ∫ y, singularPow (3 + (δ / 2 + θ)) z y *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z') y) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left kx (mul_nonneg hC1 hμ)
  have i₃ : Integrable (fun y => (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z) y +
        i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z) y) *
      (C1 * μ * singularPow (3 + (δ / 2 + θ)) z' y)) :=
    (jy.const_mul (C1 * μ)).congr (Filter.Eventually.of_forall fun y => by simp only; ring)
  have b₃ : ∫ y, (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z) y +
        i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z) y) *
      (C1 * μ * singularPow (3 + (δ / 2 + θ)) z' y) ≤
      C1 * μ * (μ * Cc * (torusParabolicSize z ^ (-(1 + 2 * δ + 2 * θ)) +
        torusParabolicSize z' ^ (-(1 + 2 * δ + 2 * θ)))) := by
    calc _ = ∫ y, C1 * μ * (singularPow (3 + (δ / 2 + θ)) z' y *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z) y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z) y)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
      _ = C1 * μ * ∫ y, singularPow (3 + (δ / 2 + θ)) z' y *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z) y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z) y) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left ky (mul_nonneg hC1 hμ)
  obtain ⟨hFi, hbd⟩ := integrable_and_abs_integral_le_of_parts
    (F := fun y => (i3Psi2D K Qaa Ja ca z y - i3Psi2D K Qbb Jb cb z y) *
      (i3Psi2D K Qaa Ja ca z' y - i3Psi2D K Qbb Jb cb z' y))
    (a := fun y => i3Psi2Abar K Ja Qaa (z - y) - i3Psi2Abar K Jb Qbb (z - y))
    (a' := fun y => i3Psi2Abar K Ja Qaa (z' - y) - i3Psi2Abar K Jb Qbb (z' - y))
    (b := fun y => i3Psi2Bz K Ja Qaa z y - i3Psi2Bz K Jb Qbb z y)
    (b' := fun y => i3Psi2Bz K Ja Qaa z' y - i3Psi2Bz K Jb Qbb z' y)
    (ua := fun y => C1 * μ * singularPow (3 + (δ / 2 + θ)) z y)
    (ua' := fun y => C1 * μ * singularPow (3 + (δ / 2 + θ)) z' y)
    (ub := fun y => i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z) y +
      i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z) y)
    (ub' := fun y => i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z') y +
      i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z') y)
    hF hFm
    (by filter_upwards [ae_torusParabolicSize_sub_pos z] with y hy using hA' _ hy)
    (by filter_upwards [ae_torusParabolicSize_sub_pos z'] with y hy using hA' _ hy)
    (Filter.Eventually.of_forall fun y => hbB z y) (Filter.Eventually.of_forall fun y => hbB z' y)
    i₁ b₁ i₂ b₂ i₃ b₃ jp kp
  refine ⟨hFi, hbd.trans ?_⟩
  have t0 := far_le_diffTarget δ θ z z'
  have tz := left_le_diffTarget δ θ z z'
  have tz' := right_le_diffTarget δ θ z z'
  set S : ℝ := i3Psi2DiffTarget δ θ z z' with hS
  have hS1 : torusParabolicSize z' ^ (-(1 + 2 * δ + 2 * θ)) +
      torusParabolicSize z ^ (-(1 + 2 * δ + 2 * θ)) ≤ 2 * S := by linarith
  have hS1' : torusParabolicSize z ^ (-(1 + 2 * δ + 2 * θ)) +
      torusParabolicSize z' ^ (-(1 + 2 * δ + 2 * θ)) ≤ 2 * S := by linarith
  have hS2 : torusParabolicSize z ^ (-(1 + 2 * δ + 2 * θ)) +
      2 * torusParabolicSize z' ^ (-(1 + 2 * δ + 2 * θ)) ≤ 3 * S := by linarith
  have bI₁ := mul_le_mul_of_nonneg_left t0 (by positivity : 0 ≤ μ ^ 2 * (C1 ^ 2 * Cu))
  have bI₂ := mul_le_mul_of_nonneg_left hS1 (by positivity : 0 ≤ μ ^ 2 * (C1 * Cc))
  have bI₃ := mul_le_mul_of_nonneg_left hS1' (by positivity : 0 ≤ μ ^ 2 * (C1 * Cc))
  have bI₄ := mul_le_mul_of_nonneg_left hS2 (by positivity : 0 ≤ μ ^ 2 * Cq)
  linarith

end RegularityStructures

end
