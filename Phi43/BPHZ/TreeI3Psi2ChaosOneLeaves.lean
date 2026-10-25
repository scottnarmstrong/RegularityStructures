/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2ChaosOnePotPair
public import Phi43.BPHZ.TreeI3Psi2DiagramLeaves
public import Phi43.BPHZ.TreeI3Psi2DiagramPointwise

/-!
# Leaves for the regular part `B_z` of the chaos-`1` kernel

Integral estimates for the products of the centred powers
`s(w)^(-3) s(z - w)^(-(2+δ))` (the majorant of `|K(-w)| Q(w - z)²`) with one further power, in
the sharp form (only the pairs of centres which actually occur, so that no mixed `s(z - z')`
terms appear).
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- Outer leaf for the cross terms: `s(w)^(-3) s(z' - w)^(-(2+δ)) s(z - w)^(-(1+δ'))`. -/
theorem chaosOne_leaf_cross {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') (hδ1 : δ ≤ 1 / 4)
    (hδ'1 : δ' ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z z' : SpaceTime}, 0 < torusParabolicSize (z' - 0) →
      0 < torusParabolicSize (z - 0) →
      SingularIntLe (fun w => singularPow 3 0 w * singularPow (2 + δ) z' w *
        singularPow (1 + δ') z w) (C * (torusParabolicSize (z' - 0) ^ (-(1 + δ + δ')) +
          torusParabolicSize (z - 0) ^ (-(1 + δ + δ')))) := by
  obtain ⟨C, hC, h⟩ := singularIntLe_mul_three (a := 2 + δ) (b := 1 + δ') (c := 3)
    (η := 1 + δ + δ') (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num)
    (by linarith) (by ring)
  refine ⟨C, hC, fun {z z'} h1 h2 => ?_⟩
  exact ((h z' z 0 h1 h2).congr_fun (g := fun w => singularPow 3 0 w *
    singularPow (2 + δ) z' w * singularPow (1 + δ') z w) (fun w => by ring))

/-- Inner leaf for the pair `B_z B_{z'}`: `s(w)^(-3) s(z - w)^(-(2+δ)) s(w' - w)^(-1)`. -/
theorem chaosOne_leaf_inner {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z w' : SpaceTime}, 0 < torusParabolicSize (z - 0) →
      0 < torusParabolicSize (w' - 0) →
      SingularIntLe (fun w => singularPow 3 0 w * singularPow (2 + δ) z w *
        singularPow 1 w' w) (C * (torusParabolicSize (z - 0) ^ (-(1 + δ)) +
          torusParabolicSize (w' - 0) ^ (-(1 + δ)))) := by
  obtain ⟨C, hC, h⟩ := singularIntLe_mul_three (a := 2 + δ) (b := 1) (c := 3)
    (η := 1 + δ) (by linarith) (by norm_num) (by linarith) (by norm_num) (by norm_num)
    (by linarith) (by ring)
  refine ⟨C, hC, fun {z w'} h1 h2 => ?_⟩
  exact ((h z w' 0 h1 h2).congr_fun (g := fun w => singularPow 3 0 w *
    singularPow (2 + δ) z w * singularPow 1 w' w) (fun w => by ring))

/-- Outer leaves for the pair `B_z B_{z'}`. -/
theorem chaosOne_leaf_outer {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z' : SpaceTime}, 0 < torusParabolicSize (z' - 0) →
      SingularIntLe (fun w => singularPow 3 0 w * singularPow (2 + δ) z' w)
        (C * torusParabolicSize (z' - 0) ^ (-δ)) ∧
      SingularIntLe (fun w => singularPow 3 0 w * singularPow (2 + δ) z' w *
        singularPow (1 + δ) 0 w) (C * torusParabolicSize (z' - 0) ^ (-(1 + 2 * δ))) := by
  obtain ⟨C1, hC1, h1⟩ := singularIntLe_mul_two (a := 2 + δ) (b := 3) (η := δ) (by linarith)
    (by linarith) (by norm_num) (by norm_num) hδ (by ring)
  obtain ⟨C2, hC2, h2⟩ := singularIntLe_mul_two (a := 2 + δ) (b := 4 + δ) (η := 1 + 2 * δ)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
  have n1 : ∀ z' : SpaceTime, 0 ≤ torusParabolicSize (z' - 0) ^ (-δ) :=
    fun z' => Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  refine ⟨C1 + C2, by positivity, fun {z'} hz' => ?_⟩
  have p0 : 0 < torusParabolicSize (z' - 0) := hz'
  have e1 := (h1 z' 0 hz').congr_fun (g := fun w => singularPow 3 0 w *
    singularPow (2 + δ) z' w) (fun w => by ring)
  have e2 := (h2 z' 0 hz').congr_ae (g := fun w => singularPow 3 0 w * singularPow (2 + δ) z' w *
    singularPow (1 + δ) 0 w) (by
      filter_upwards [ae_singularPow_mul_self (a := 3) (b := 1 + δ) (e := 4 + δ) (by ring)
        (0 : SpaceTime)] with w hw
      rw [← hw]
      ring)
  refine ⟨e1.mono_right (mul_le_mul_of_nonneg_right (by linarith) (n1 z')),
    e2.mono_right (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))⟩

end RegularityStructures

end
