/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOnePot

/-!
# Cross terms and pairings of potentials, general exponents

Generalisations of `chaosOne_cross_le` and `chaosOne_pp_le` to potentials of kernels of order
`3 + ε₂` against majorants `s(w)^(-3) s(z - w)^(-(2+ε₁))` of the weight `h`:

* `chaosOne_cross_gen`: `∫ s(z - y)^(-(3+ε₃)) Pot_J h (y) dy ≤ C (s(z')^(-η) + s(z)^(-η))`,
  `η = 1 + ε₁ + ε₂ + ε₃`;
* `chaosOne_pp_gen`: `∫ Pot_{J₁} h₁ Pot_{J₂} h₂ dy ≤ C (s(z)^(-η) s(z')^(-ε₁') + s(z')^(-(ε₁'+η)))`,
  `η = 1 + ε₁ + ε₂ + ε₂'`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- The cross term `∫ s(z - y)^(-(3+ε₃)) Pot_J h(y) dy`. -/
theorem chaosOne_cross_gen {ε₁ ε₂ ε₃ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hε₃ : 0 ≤ ε₃)
    (hs : ε₁ + ε₂ + ε₃ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J h : SpaceTime → ℝ} {BJ Hc : ℝ}, 0 ≤ BJ → 0 ≤ Hc → Measurable J →
      (∀ x, 0 < torusParabolicSize x → |J x| ≤ BJ * torusParabolicSize x ^ (-(3 + ε₂))) →
      Measurable h → (∀ w, 0 ≤ h w) → ∀ z z' : SpaceTime, 0 < torusParabolicSize z →
        0 < torusParabolicSize z' →
        (∀ᵐ w : SpaceTime ∂volume,
          h w ≤ Hc * (singularPow 3 0 w * singularPow (2 + ε₁) z' w)) →
          Integrable (fun y => singularPow (3 + ε₃) z y * i3Psi2Pot J h y) ∧
            ∫ y, singularPow (3 + ε₃) z y * i3Psi2Pot J h y ≤
              C * Hc * BJ * (torusParabolicSize z' ^ (-(1 + ε₁ + ε₂ + ε₃)) +
                torusParabolicSize z ^ (-(1 + ε₁ + ε₂ + ε₃))) := by
  obtain ⟨Cp, hCp, hp⟩ := power_mul_abs_J_le_gen (a := 3 + ε₃) (j := 3 + ε₂) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨Cl, hCl, hl⟩ := singularIntLe_mul_three (a := 2 + ε₁) (b := 1 + ε₂ + ε₃) (c := 3)
    (η := 1 + ε₁ + ε₂ + ε₃) (by linarith) (by linarith) (by linarith) (by norm_num)
    (by norm_num) (by linarith) (by ring)
  refine ⟨Cp * Cl, mul_nonneg hCp hCl, ?_⟩
  intro J h BJ Hc hBJ hHc hJm hJ hhm hh0 z z' hz hz' hH
  have pz : 0 < torusParabolicSize (z - 0) := by rwa [sub_zero]
  have pz' : 0 < torusParabolicSize (z' - 0) := by rwa [sub_zero]
  have hX : SingularIntLe (fun w => (Hc * (singularPow 3 0 w * singularPow (2 + ε₁) z' w)) *
      ((Cp * BJ) * singularPow (1 + ε₂ + ε₃) z w))
      (Cp * Cl * Hc * BJ * (torusParabolicSize z' ^ (-(1 + ε₁ + ε₂ + ε₃)) +
        torusParabolicSize z ^ (-(1 + ε₁ + ε₂ + ε₃)))) := by
    have := ((hl z' z 0 pz' pz).const_mul (c := Hc * (Cp * BJ))
      (mul_nonneg hHc (mul_nonneg hCp hBJ)))
    simp only [sub_zero] at this
    exact (this.congr_fun (g := fun w => (Hc * (singularPow 3 0 w * singularPow (2 + ε₁) z' w)) *
      ((Cp * BJ) * singularPow (1 + ε₂ + ε₃) z w)) (fun w => by ring)).mono_right
      (le_of_eq (by ring))
  refine integral_mul_pot_le (H := fun w => Hc * (singularPow 3 0 w *
    singularPow (2 + ε₁) z' w)) (U := fun w => (Cp * BJ) * singularPow (1 + ε₂ + ε₃) z w) hJm
    (fun y => singularPow_nonneg _ _ _) (measurable_singularPow _ _) hh0 hhm hH ?_ hX
  filter_upwards [ae_torusParabolicSize_sub_pos z] with w hw
  obtain ⟨i, b⟩ := hp hBJ hJm hJ z w hw
  have e : (5 - (3 + ε₃) - (3 + ε₂) : ℝ) = -(1 + ε₂ + ε₃) := by ring
  rw [e] at b
  refine ⟨i, ?_⟩
  simpa [singularPow, mul_assoc] using b

/-- The pairing `∫ Pot_{J₁} h₁ Pot_{J₂} h₂ dy`. -/
theorem chaosOne_pp_gen {ε₁ ε₁' ε₂ ε₂' : ℝ} (hε₁ : 0 ≤ ε₁) (hε₁' : 0 < ε₁') (hε₂ : 0 ≤ ε₂)
    (hε₂' : 0 ≤ ε₂') (hs : ε₁ + ε₁' + ε₂ + ε₂' ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J₁ J₂ h₁ h₂ : SpaceTime → ℝ} {B₁ B₂ Hc₁ Hc₂ : ℝ}, 0 ≤ B₁ → 0 ≤ B₂ →
      0 ≤ Hc₁ → 0 ≤ Hc₂ → Measurable J₁ → Measurable J₂ →
      (∀ x, 0 < torusParabolicSize x → |J₁ x| ≤ B₁ * torusParabolicSize x ^ (-(3 + ε₂))) →
      (∀ x, 0 < torusParabolicSize x → |J₂ x| ≤ B₂ * torusParabolicSize x ^ (-(3 + ε₂'))) →
      Measurable h₁ → Measurable h₂ → (∀ w, 0 ≤ h₁ w) → (∀ w, 0 ≤ h₂ w) →
      ∀ z z' : SpaceTime, 0 < torusParabolicSize z → 0 < torusParabolicSize z' →
        (∀ᵐ w : SpaceTime ∂volume,
          h₁ w ≤ Hc₁ * (singularPow 3 0 w * singularPow (2 + ε₁) z w)) →
        (∀ᵐ w : SpaceTime ∂volume,
          h₂ w ≤ Hc₂ * (singularPow 3 0 w * singularPow (2 + ε₁') z' w)) →
          Integrable (fun y => i3Psi2Pot J₁ h₁ y * i3Psi2Pot J₂ h₂ y) ∧
            ∫ y, i3Psi2Pot J₁ h₁ y * i3Psi2Pot J₂ h₂ y ≤
              C * Hc₁ * Hc₂ * B₁ * B₂ *
                (torusParabolicSize z ^ (-(1 + ε₁ + ε₂ + ε₂')) * torusParabolicSize z' ^ (-ε₁') +
                  torusParabolicSize z' ^ (-(1 + ε₁ + ε₂ + ε₂' + ε₁'))) := by
  obtain ⟨C0, hC0, h0⟩ := abs_J_mul_J_le_gen (j₁ := 3 + ε₂) (j₂ := 3 + ε₂') (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨Ci, hCi, hi⟩ := singularIntLe_mul_three (a := 2 + ε₁) (b := 1 + ε₂ + ε₂') (c := 3)
    (η := 1 + ε₁ + ε₂ + ε₂') (by linarith) (by linarith) (by linarith) (by norm_num)
    (by norm_num) (by linarith) (by ring)
  obtain ⟨Co1, hCo1, ho1⟩ := singularIntLe_mul_two (a := 2 + ε₁') (b := 3) (η := ε₁')
    (by linarith) (by linarith) (by norm_num) (by norm_num) hε₁' (by ring)
  obtain ⟨Co2, hCo2, ho2⟩ := singularIntLe_mul_two (a := 2 + ε₁') (b := 3 + (1 + ε₁ + ε₂ + ε₂'))
    (η := 1 + ε₁ + ε₂ + ε₂' + ε₁') (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by ring)
  have n2 : (0 : ℝ) ≤ 2 ^ (1 + ε₂ + ε₂') := Real.rpow_nonneg (by norm_num) _
  have n2' : (0 : ℝ) ≤ 2 ^ (1 + ε₁ + ε₂ + ε₂') := Real.rpow_nonneg (by norm_num) _
  refine ⟨2 ^ (1 + ε₂ + ε₂') * C0 * Ci * (Co1 + Co2 * 2 ^ (1 + ε₁ + ε₂ + ε₂')),
    by positivity, ?_⟩
  intro J₁ J₂ h₁ h₂ B₁ B₂ Hc₁ Hc₂ hB₁ hB₂ hHc₁ hHc₂ hJ₁m hJ₂m hJ₁ hJ₂ hh₁m hh₂m hh₁0 hh₂0 z z'
    hz hz' hH₁ hH₂
  have pz : 0 < torusParabolicSize (z - 0) := by rwa [sub_zero]
  have pz' : 0 < torusParabolicSize (z' - 0) := by rwa [sub_zero]
  set q : ℝ := 1 + ε₂ + ε₂' with hq
  set η : ℝ := 1 + ε₁ + ε₂ + ε₂' with hη
  have hΛ : ∀ w w' : SpaceTime, 0 < torusParabolicSize (w - w') →
      Integrable (fun y => |J₁ (w - y)| * |J₂ (w' - y)|) ∧
        ∫ y, |J₁ (w - y)| * |J₂ (w' - y)| ≤ 2 ^ q * (C0 * B₁ * B₂) * singularPow q w' w := by
    intro w w' hww
    obtain ⟨i, b⟩ := h0 hB₁ hB₂ hJ₁m hJ₂m hJ₁ hJ₂ w w' hww
    refine ⟨i, b.trans ?_⟩
    have f := rpow_neg_flip_singularPow (p := q) (by rw [hq]; linarith) (c := w') (w := w)
      (torusParabolicSize_sub_pos_symm hww)
    have e : (5 - (3 + ε₂) - (3 + ε₂') : ℝ) = -q := by rw [hq]; ring
    rw [e]
    have hc : 0 ≤ C0 * B₁ * B₂ := mul_nonneg (mul_nonneg hC0 hB₁) hB₂
    calc C0 * B₁ * B₂ * torusParabolicSize (w - w') ^ (-q) ≤
        C0 * B₁ * B₂ * (2 ^ q * singularPow q w' w) := mul_le_mul_of_nonneg_left f hc
      _ = _ := by ring
  let R : SpaceTime → ℝ := fun w' => Hc₁ * (2 ^ q * (C0 * B₁ * B₂)) * Ci *
    (torusParabolicSize z ^ (-η) + 2 ^ η * singularPow η 0 w')
  have hR : ∀ᵐ w' : SpaceTime ∂volume, SingularIntLe (fun w => (Hc₁ * (singularPow 3 0 w *
      singularPow (2 + ε₁) z w)) * (2 ^ q * (C0 * B₁ * B₂) * singularPow q w' w)) (R w') := by
    filter_upwards [ae_torusParabolicSize_sub_pos 0] with w' b
    have pw' : 0 < torusParabolicSize (w' - 0) := by
      have := torusParabolicSize_sub_pos_symm b
      exact this
    have := ((hi z w' 0 pz pw').const_mul (c := Hc₁ * (2 ^ q * (C0 * B₁ * B₂)))
      (by positivity))
    simp only [sub_zero] at this pw'
    refine (this.congr_fun (g := fun w => (Hc₁ * (singularPow 3 0 w *
      singularPow (2 + ε₁) z w)) * (2 ^ q * (C0 * B₁ * B₂) * singularPow q w' w))
      (fun w => by ring)).mono_right ?_
    have f := rpow_neg_flip_singularPow (p := η) (by rw [hη]; linarith) (c := 0) (w := w') b
    simp only [sub_zero] at f
    simp only [R]
    have hP : 0 ≤ Hc₁ * (2 ^ q * (C0 * B₁ * B₂)) * Ci := by positivity
    have := mul_le_mul_of_nonneg_left f hP
    linarith [this]
  have hX : SingularIntLe (fun w' => (Hc₂ * (singularPow 3 0 w' * singularPow (2 + ε₁') z' w')) *
      R w') (2 ^ q * C0 * Ci * (Co1 + Co2 * 2 ^ η) * Hc₁ * Hc₂ * B₁ * B₂ *
        (torusParabolicSize z ^ (-η) * torusParabolicSize z' ^ (-ε₁') +
          torusParabolicSize z' ^ (-(η + ε₁')))) := by
    have e1 := ho1 z' 0 pz'
    have e2 := (ho2 z' 0 pz').congr_ae (g := fun w => singularPow 3 0 w *
      singularPow (2 + ε₁') z' w * singularPow η 0 w) (by
        filter_upwards [ae_singularPow_mul_self (a := 3) (b := η) (e := 3 + η) (by ring)
          (0 : SpaceTime)] with w hw
        rw [← hw]
        ring)
    have e1' := e1.congr_fun (g := fun w => singularPow 3 0 w * singularPow (2 + ε₁') z' w)
      (fun w => by ring)
    have hz0 : 0 ≤ torusParabolicSize z ^ (-η) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have t1 := e1'.const_mul (c := torusParabolicSize z ^ (-η)) hz0
    have t2 := e2.const_mul (c := 2 ^ η) (Real.rpow_nonneg (by norm_num) _)
    have hP : 0 ≤ Hc₂ * (Hc₁ * (2 ^ q * (C0 * B₁ * B₂)) * Ci) := by positivity
    have := (t1.add t2).const_mul (c := Hc₂ * (Hc₁ * (2 ^ q * (C0 * B₁ * B₂)) * Ci)) hP
    simp only [sub_zero] at this
    refine (this.congr_fun (g := fun w' => (Hc₂ * (singularPow 3 0 w' *
      singularPow (2 + ε₁') z' w')) * R w') (fun w' => by simp only [R]; ring)).mono_right ?_
    have y0 : 0 ≤ torusParabolicSize z' ^ (-ε₁') := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have y1 : 0 ≤ torusParabolicSize z' ^ (-(η + ε₁')) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have x0 : 0 ≤ torusParabolicSize z ^ (-η) * torusParabolicSize z' ^ (-ε₁') := mul_nonneg hz0 y0
    have hQ : 0 ≤ 2 ^ q * C0 * Ci * Hc₁ * Hc₂ * B₁ * B₂ := by positivity
    have hη2 : (0 : ℝ) ≤ 2 ^ η := Real.rpow_nonneg (by norm_num) _
    have key : Hc₂ * (Hc₁ * (2 ^ q * (C0 * B₁ * B₂)) * Ci) *
        (torusParabolicSize z ^ (-η) * (Co1 * torusParabolicSize z' ^ (-ε₁')) +
          2 ^ η * (Co2 * torusParabolicSize z' ^ (-(η + ε₁')))) =
        (2 ^ q * C0 * Ci * Hc₁ * Hc₂ * B₁ * B₂) *
          (Co1 * (torusParabolicSize z ^ (-η) * torusParabolicSize z' ^ (-ε₁')) +
            Co2 * 2 ^ η * torusParabolicSize z' ^ (-(η + ε₁'))) := by ring
    rw [key]
    have : (2 ^ q * C0 * Ci * Hc₁ * Hc₂ * B₁ * B₂) *
          (Co1 * (torusParabolicSize z ^ (-η) * torusParabolicSize z' ^ (-ε₁')) +
            Co2 * 2 ^ η * torusParabolicSize z' ^ (-(η + ε₁'))) ≤
        (2 ^ q * C0 * Ci * Hc₁ * Hc₂ * B₁ * B₂) * ((Co1 + Co2 * 2 ^ η) *
          (torusParabolicSize z ^ (-η) * torusParabolicSize z' ^ (-ε₁') +
            torusParabolicSize z' ^ (-(η + ε₁')))) := by
      refine mul_le_mul_of_nonneg_left ?_ hQ
      linarith [mul_nonneg hCo1 y1, mul_nonneg (mul_nonneg hCo2 hη2) x0]
    refine this.trans (le_of_eq ?_)
    ring
  have hfin := integral_pot_mul_pot_le_pair (H₁ := fun w => Hc₁ * (singularPow 3 0 w *
    singularPow (2 + ε₁) z w)) (H₂ := fun w => Hc₂ * (singularPow 3 0 w *
    singularPow (2 + ε₁') z' w)) (Λ := fun w w' => 2 ^ q * (C0 * B₁ * B₂) * singularPow q w' w)
    hJ₁m hJ₂m hh₁0 hh₁m hh₂0 hh₂m hH₁ hH₂ hΛ hR hX
  refine ⟨hfin.1, hfin.2.trans (le_of_eq ?_)⟩
  ring

end RegularityStructures

end
