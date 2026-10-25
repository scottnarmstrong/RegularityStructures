/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2PotPair
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOneBound

/-!
# The chaos-`1` part of the difference of `I(Ψ³)Ψ²`, for arbitrary `z, z'`

`i3Psi2Chaos1Diff_bound_global`: global version of `i3Psi2Chaos1Diff_bound`: for arbitrary `z, z'`
and `D` bounding `s(z - w)`, `s(z' - w)` for `|w.1| ≤ 1`,
`|∫ (D^a_z - D^b_z)(D^a_{z'} - D^b_{z'}) dy| ≤ C μ² (1 + D^δ)² treeTheta z z'`.
-/

public section

open MeasureTheory

namespace RegularityStructures

private theorem one_add_sq_aux {d : ℝ} (hd : 0 ≤ d) :
    d ≤ (1 + d) ^ 2 ∧ d ^ 2 ≤ (1 + d) ^ 2 ∧ 1 ≤ (1 + d) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

private theorem dterm_le {L d W x k Θ : ℝ} (hL : 0 ≤ L) (hd : 0 ≤ d) (hdW : d ≤ W) (hx0 : 0 ≤ x)
    (hx : x ≤ k * Θ) : L * (d * x) ≤ L * k * (W * Θ) := by
  have hW : 0 ≤ W := hd.trans hdW
  calc L * (d * x) ≤ L * (W * (k * Θ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hdW hx hx0 hW) hL
    _ = _ := by ring

/-- The final comparison of the singular terms with `treeTheta` for the chaos-`1` difference. -/
theorem chaos1Diff_numerics {δ θ μ C1 Cu Cc Cq D : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) (hμ : 0 ≤ μ) (hD0 : 0 ≤ D) (hC1 : 0 ≤ C1) (hCu : 0 ≤ Cu)
    (hCc : 0 ≤ Cc) (hCq : 0 ≤ Cq) {z z' : SpaceTime} (hz : 0 < torusParabolicSize z)
    (hz' : 0 < torusParabolicSize z') (hzz : 0 < torusParabolicSize (z - z')) :
    (C1 * μ) * (C1 * μ) * (Cu * torusParabolicSize (z - z') ^ (-(1 + δ + 2 * θ))) +
      C1 * μ * (μ * Cc * D ^ δ * (torusParabolicSize z' ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
            torusParabolicSize z ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
            (torusParabolicSize z' ^ (-(1 + δ + θ + (δ / 2 + θ))) +
              torusParabolicSize z ^ (-(1 + δ + θ + (δ / 2 + θ)))))) +
      C1 * μ * (μ * Cc * D ^ δ * (torusParabolicSize z ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
            torusParabolicSize z' ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
            (torusParabolicSize z ^ (-(1 + δ + θ + (δ / 2 + θ))) +
              torusParabolicSize z' ^ (-(1 + δ + θ + (δ / 2 + θ)))))) +
      μ ^ 2 * Cq * (D ^ δ) ^ 2 *
            ((torusParabolicSize z ^ (-(1 + (θ + δ) + 0 + 0)) * torusParabolicSize z' ^ (-(θ + δ)) +
                torusParabolicSize z' ^ (-(1 + (θ + δ) + 0 + 0 + (θ + δ)))) +
              (torusParabolicSize z ^ (-(1 + (θ + δ) + 0 + θ)) * torusParabolicSize z' ^ (-δ) +
                torusParabolicSize z' ^ (-(1 + (θ + δ) + 0 + θ + δ))) +
              (torusParabolicSize z ^ (-(1 + δ + θ + 0)) * torusParabolicSize z' ^ (-(θ + δ)) +
                torusParabolicSize z' ^ (-(1 + δ + θ + 0 + (θ + δ)))) +
              (torusParabolicSize z ^ (-(1 + δ + θ + θ)) * torusParabolicSize z' ^ (-δ) +
                torusParabolicSize z' ^ (-(1 + δ + θ + θ + δ)))) ≤
      (C1 ^ 2 * Cu + 8 * C1 * Cc + 12 * Cq) * μ ^ 2 * (1 + D ^ δ) ^ 2 * treeTheta z z' := by
  set Θ := treeTheta z z' with hΘ
  have hΘ0 : 0 ≤ Θ := treeTheta_nonneg z z'
  have hd0 : 0 ≤ D ^ δ := Real.rpow_nonneg hD0 _
  obtain ⟨hdW, hdW2, hW1⟩ := one_add_sq_aux hd0
  set W := (1 + D ^ δ) ^ 2 with hW
  have nn : ∀ (a : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize a ^ e := fun a e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  -- singular terms
  have sz : ∀ e : ℝ, 0 ≤ e → e ≤ 5 / 2 → torusParabolicSize z ^ (-e) ≤ Θ := fun e h0 h1 =>
    rpow_z_le_treeTheta hz h0 h1
  have sz' : ∀ e : ℝ, 0 ≤ e → e ≤ 5 / 2 → torusParabolicSize z' ^ (-e) ≤ Θ := fun e h0 h1 =>
    rpow_z'_le_treeTheta hz' h0 h1
  have X1 : torusParabolicSize z' ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
      torusParabolicSize z ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
      (torusParabolicSize z' ^ (-(1 + δ + θ + (δ / 2 + θ))) +
        torusParabolicSize z ^ (-(1 + δ + θ + (δ / 2 + θ)))) ≤ 4 * Θ := by
    have a1 := sz' (1 + (θ + δ) + 0 + (δ / 2 + θ)) (by linarith) (by linarith)
    have a2 := sz (1 + (θ + δ) + 0 + (δ / 2 + θ)) (by linarith) (by linarith)
    have a3 := sz' (1 + δ + θ + (δ / 2 + θ)) (by linarith) (by linarith)
    have a4 := sz (1 + δ + θ + (δ / 2 + θ)) (by linarith) (by linarith)
    linarith
  have X2 : torusParabolicSize z ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
      torusParabolicSize z' ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
      (torusParabolicSize z ^ (-(1 + δ + θ + (δ / 2 + θ))) +
        torusParabolicSize z' ^ (-(1 + δ + θ + (δ / 2 + θ)))) ≤ 4 * Θ := by
    linarith
  have Xn : ∀ x : ℝ, x = torusParabolicSize z' ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
      torusParabolicSize z ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
      (torusParabolicSize z' ^ (-(1 + δ + θ + (δ / 2 + θ))) +
        torusParabolicSize z ^ (-(1 + δ + θ + (δ / 2 + θ)))) → 0 ≤ x := fun x hx => by
    rw [hx]
    exact add_nonneg (add_nonneg (nn _ _) (nn _ _)) (add_nonneg (nn _ _) (nn _ _))
  have X1n := Xn _ rfl
  have X2n : 0 ≤ torusParabolicSize z ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
      torusParabolicSize z' ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
      (torusParabolicSize z ^ (-(1 + δ + θ + (δ / 2 + θ))) +
        torusParabolicSize z' ^ (-(1 + δ + θ + (δ / 2 + θ)))) :=
    add_nonneg (add_nonneg (nn _ _) (nn _ _)) (add_nonneg (nn _ _) (nn _ _))
  -- pairs
  have pr : ∀ a b : ℝ, 0 ≤ a → a ≤ 5 / 4 → 0 ≤ b → b ≤ 5 / 4 →
      torusParabolicSize z ^ (-a) * torusParabolicSize z' ^ (-b) ≤ 2 * Θ := fun a b h0 h1 h2 h3 =>
    rpow_z_mul_z'_le_treeTheta hz hz' h0 h1 h2 h3
  have P11 := pr (1 + (θ + δ) + 0 + 0) (θ + δ) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have P12 := pr (1 + (θ + δ) + 0 + θ) δ (by linarith) (by linarith) (by linarith) (by linarith)
  have P21 := pr (1 + δ + θ + 0) (θ + δ) (by linarith) (by linarith) (by linarith) (by linarith)
  have P22 := pr (1 + δ + θ + θ) δ (by linarith) (by linarith) (by linarith) (by linarith)
  have Q11 := sz' (1 + (θ + δ) + 0 + 0 + (θ + δ)) (by linarith) (by linarith)
  have Q12 := sz' (1 + (θ + δ) + 0 + θ + δ) (by linarith) (by linarith)
  have Q21 := sz' (1 + δ + θ + 0 + (θ + δ)) (by linarith) (by linarith)
  have Q22 := sz' (1 + δ + θ + θ + δ) (by linarith) (by linarith)
  have PP : (torusParabolicSize z ^ (-(1 + (θ + δ) + 0 + 0)) * torusParabolicSize z' ^ (-(θ + δ)) +
                torusParabolicSize z' ^ (-(1 + (θ + δ) + 0 + 0 + (θ + δ)))) +
              (torusParabolicSize z ^ (-(1 + (θ + δ) + 0 + θ)) * torusParabolicSize z' ^ (-δ) +
                torusParabolicSize z' ^ (-(1 + (θ + δ) + 0 + θ + δ))) +
              (torusParabolicSize z ^ (-(1 + δ + θ + 0)) * torusParabolicSize z' ^ (-(θ + δ)) +
                torusParabolicSize z' ^ (-(1 + δ + θ + 0 + (θ + δ)))) +
              (torusParabolicSize z ^ (-(1 + δ + θ + θ)) * torusParabolicSize z' ^ (-δ) +
                torusParabolicSize z' ^ (-(1 + δ + θ + θ + δ))) ≤ 12 * Θ := by linarith
  have PPn : 0 ≤ (torusParabolicSize z ^ (-(1 + (θ + δ) + 0 + 0)) * torusParabolicSize z' ^ (-(θ + δ)) +
                torusParabolicSize z' ^ (-(1 + (θ + δ) + 0 + 0 + (θ + δ)))) +
              (torusParabolicSize z ^ (-(1 + (θ + δ) + 0 + θ)) * torusParabolicSize z' ^ (-δ) +
                torusParabolicSize z' ^ (-(1 + (θ + δ) + 0 + θ + δ))) +
              (torusParabolicSize z ^ (-(1 + δ + θ + 0)) * torusParabolicSize z' ^ (-(θ + δ)) +
                torusParabolicSize z' ^ (-(1 + δ + θ + 0 + (θ + δ)))) +
              (torusParabolicSize z ^ (-(1 + δ + θ + θ)) * torusParabolicSize z' ^ (-δ) +
                torusParabolicSize z' ^ (-(1 + δ + θ + θ + δ))) := by
    have m := fun a b : ℝ => mul_nonneg (nn z (-a)) (nn z' (-b))
    have := m (1 + (θ + δ) + 0 + 0) (θ + δ)
    have := m (1 + (θ + δ) + 0 + θ) δ
    have := m (1 + δ + θ + 0) (θ + δ)
    have := m (1 + δ + θ + θ) δ
    have := nn z' (-(1 + (θ + δ) + 0 + 0 + (θ + δ)))
    have := nn z' (-(1 + (θ + δ) + 0 + θ + δ))
    have := nn z' (-(1 + δ + θ + 0 + (θ + δ)))
    have := nn z' (-(1 + δ + θ + θ + δ))
    linarith
  -- the four contributions
  have t1 : (C1 * μ) * (C1 * μ) * (Cu * torusParabolicSize (z - z') ^ (-(1 + δ + 2 * θ))) ≤
      μ ^ 2 * (C1 ^ 2 * Cu) * (W * Θ) := by
    have h := rpow_zz_le_treeTheta hzz (e := 1 + δ + 2 * θ) (by linarith) (by linarith)
    have h1 : torusParabolicSize (z - z') ^ (-(1 + δ + 2 * θ)) ≤ W * Θ := by
      have := mul_le_mul_of_nonneg_right hW1 hΘ0
      linarith
    calc _ = μ ^ 2 * (C1 ^ 2 * Cu) * torusParabolicSize (z - z') ^ (-(1 + δ + 2 * θ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  have t2 := dterm_le (L := C1 * μ * (μ * Cc)) (by positivity) hd0 hdW X1n X1
  have t3 := dterm_le (L := C1 * μ * (μ * Cc)) (by positivity) hd0 hdW X2n X2
  have t4 := dterm_le (L := μ ^ 2 * Cq) (d := (D ^ δ) ^ 2) (by positivity) (by positivity) hdW2
    PPn PP
  linarith only [t1, t2, t3, t4]

/-- **Bound for the chaos-`1` part of the difference, for arbitrary `z, z'`.** -/
theorem i3Psi2Chaos1Diff_bound_global {B δ θ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Ja Jb Qaa Qbb : SpaceTime → ℝ} {μ M MQ ca cb D : ℝ}, 0 ≤ μ → 0 ≤ D →
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
        0 < torusParabolicSize (z - z') →
        (∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (z - w) ≤ D) →
        (∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (z' - w) ≤ D) →
        Integrable (fun y => (i3Psi2D K Qaa Ja ca z y - i3Psi2D K Qbb Jb cb z y) *
          (i3Psi2D K Qaa Ja ca z' y - i3Psi2D K Qbb Jb cb z' y)) ∧
        |∫ y, (i3Psi2D K Qaa Ja ca z y - i3Psi2D K Qbb Jb cb z y) *
          (i3Psi2D K Qaa Ja ca z' y - i3Psi2D K Qbb Jb cb z' y)| ≤
          C * μ ^ 2 * (1 + D ^ δ) ^ 2 * treeTheta z z' := by
  have hν : 0 < δ / 2 := by linarith
  obtain ⟨C1, hC1, hA⟩ := abs_i3Psi2Abar_sub_le hB hδ hδ1 hθ hθ1
  obtain ⟨Cu, hCu, hu⟩ := integrable_and_integral_singularPow_mul_le (a := 3 + (δ / 2 + θ))
    (b := 3 + (δ / 2 + θ)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨Cc, hCc, hcross⟩ := chaosOne_diff_cross_bound_global hB hδ hδ1 hθ hθ1
  obtain ⟨Cq, hCq, hpp⟩ := chaosOne_diff_pp_bound_global hB hδ hδ1 hθ hθ1
  refine ⟨C1 ^ 2 * Cu + 8 * C1 * Cc + 12 * Cq, by positivity, ?_⟩
  intro K Ja Jb Qaa Qbb μ M MQ ca cb D hμ hD0 hKs hKi hKm hJam hJbm hQam hQbm hJab hJbb hJai hJbi
    hQab hQbb hK hJa hJainc hQa hQb hΔQ hΔJ hΔJinc hQJa hQJb hca hcb z z' hz hz' hzz hDz hDz'
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
  obtain ⟨jx, kx⟩ := hcross hμ hD0 hKs hKm hJam hJbm hQam hQbm hK hJa hQa hQb hΔQ hΔJ hQae hQbe
    z z' hz hz' hDz'
  obtain ⟨jy, ky⟩ := hcross hμ hD0 hKs hKm hJam hJbm hQam hQbm hK hJa hQa hQb hΔQ hΔJ hQae hQbe
    z' z hz' hz hDz
  obtain ⟨jp, kp⟩ := hpp hμ hD0 hKs hKm hJam hJbm hQam hQbm hK hJa hQa hQb hΔQ hΔJ hQae hQbe
    z z' hz hz' hDz hDz'
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
      C1 * μ * (μ * Cc * D ^ δ * (torusParabolicSize z' ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
            torusParabolicSize z ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
            (torusParabolicSize z' ^ (-(1 + δ + θ + (δ / 2 + θ))) +
              torusParabolicSize z ^ (-(1 + δ + θ + (δ / 2 + θ)))))) := by
    calc _ = ∫ y, C1 * μ * (singularPow (3 + (δ / 2 + θ)) z y *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z') y)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
      _ = C1 * μ * ∫ y, singularPow (3 + (δ / 2 + θ)) z y *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z') y) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (kx.trans (le_of_eq (by ring))) (mul_nonneg hC1 hμ)
  have i₃ : Integrable (fun y => (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z) y +
        i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z) y) *
      (C1 * μ * singularPow (3 + (δ / 2 + θ)) z' y)) :=
    (jy.const_mul (C1 * μ)).congr (Filter.Eventually.of_forall fun y => by simp only; ring)
  have b₃ : ∫ y, (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z) y +
        i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z) y) *
      (C1 * μ * singularPow (3 + (δ / 2 + θ)) z' y) ≤
      C1 * μ * (μ * Cc * D ^ δ * (torusParabolicSize z ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
            torusParabolicSize z' ^ (-(1 + (θ + δ) + 0 + (δ / 2 + θ))) +
            (torusParabolicSize z ^ (-(1 + δ + θ + (δ / 2 + θ))) +
              torusParabolicSize z' ^ (-(1 + δ + θ + (δ / 2 + θ)))))) := by
    calc _ = ∫ y, C1 * μ * (singularPow (3 + (δ / 2 + θ)) z' y *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z) y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z) y)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
      _ = C1 * μ * ∫ y, singularPow (3 + (δ / 2 + θ)) z' y *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb z) y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb z) y) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (ky.trans (le_of_eq (by ring))) (mul_nonneg hC1 hμ)
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
  exact chaos1Diff_numerics hδ hδ1 hθ hθ1 hμ hD0 hC1 hCu hCc hCq hz hz' hzz

end RegularityStructures

end
