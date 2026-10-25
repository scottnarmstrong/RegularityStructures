/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovNorm

/-!
# Pseudometric properties of the local model norms

The local model difference norm `Model.diffNormOn` is the best constant in a pair of explicit
bounds, so it is symmetric, vanishes on the diagonal and satisfies the triangle inequality, and
the model norm is controlled by the norm of another model plus the difference norm.

* `Model.diffNormOn_self`, `Model.diffNormOn_comm`, `Model.diffNormOn_triangle`;
* `Model.normOn_le_add_diffNormOn`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E} {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}
  {M₁ M₂ M₃ : Model 𝒯 K} {γ : ℝ} {S : Set E}

theorem PiDiffBoundOn.triangle {C₁ C₂ : ℝ} (h₁ : M₁.PiDiffBoundOn M₂ γ C₁ S)
    (h₂ : M₂.PiDiffBoundOn M₃ γ C₂ S) : M₁.PiDiffBoundOn M₃ γ (C₁ + C₂) S := by
  intro i hi t ht x hx
  have a := h₁ i hi t ht x hx
  have b := h₂ i hi t ht x hx
  calc _ ≤ |M₁.regPi x (Pi.single i 1) t x - M₂.regPi x (Pi.single i 1) t x| +
        |M₂.regPi x (Pi.single i 1) t x - M₃.regPi x (Pi.single i 1) t x| := abs_sub_le _ _ _
    _ ≤ _ := by rw [add_mul]; exact add_le_add a b

theorem GammaDiffBoundOn.triangle {C₁ C₂ : ℝ} (h₁ : M₁.GammaDiffBoundOn M₂ γ C₁ S)
    (h₂ : M₂.GammaDiffBoundOn M₃ γ C₂ S) : M₁.GammaDiffBoundOn M₃ γ (C₁ + C₂) S := by
  intro i j hi hj x hx y hy
  have a := h₁ i j hi hj x hx y hy
  have b := h₂ i j hi hj x hx y hy
  calc _ ≤ |M₁.gammaMap y x (Pi.single i 1) j - M₂.gammaMap y x (Pi.single i 1) j| +
        |M₂.gammaMap y x (Pi.single i 1) j - M₃.gammaMap y x (Pi.single i 1) j| := abs_sub_le _ _ _
    _ ≤ _ := by rw [add_mul]; exact add_le_add a b

theorem PiDiffBoundOn.symm {C : ℝ} (h : M₁.PiDiffBoundOn M₂ γ C S) :
    M₂.PiDiffBoundOn M₁ γ C S := fun i hi t ht x hx => by
  rw [abs_sub_comm]; exact h i hi t ht x hx

theorem GammaDiffBoundOn.symm {C : ℝ} (h : M₁.GammaDiffBoundOn M₂ γ C S) :
    M₂.GammaDiffBoundOn M₁ γ C S := fun i j hi hj x hx y hy => by
  rw [abs_sub_comm]; exact h i j hi hj x hx y hy

theorem PiDiffBoundOn.self : M₁.PiDiffBoundOn M₁ γ 0 S := fun i _ t _ x _ => by simp

theorem GammaDiffBoundOn.self : M₁.GammaDiffBoundOn M₁ γ 0 S := fun i j _ _ x _ y _ => by simp

theorem PiBoundOn.of_diff {C₁ C₂ : ℝ} (h₂ : M₂.PiBoundOn γ C₂ S)
    (h : M₁.PiDiffBoundOn M₂ γ C₁ S) : M₁.PiBoundOn γ (C₂ + C₁) S := by
  intro i hi t ht x hx
  have a := h₂ i hi t ht x hx
  have b := h i hi t ht x hx
  calc _ ≤ |M₂.regPi x (Pi.single i 1) t x| +
        |M₁.regPi x (Pi.single i 1) t x - M₂.regPi x (Pi.single i 1) t x| := by
        have := abs_sub_le (M₁.regPi x (Pi.single i 1) t x) (M₂.regPi x (Pi.single i 1) t x) 0
        simpa [abs_sub_comm, add_comm] using this
    _ ≤ _ := by rw [add_mul]; exact add_le_add a b

theorem GammaBoundOn.of_diff {C₁ C₂ : ℝ} (h₂ : M₂.GammaBoundOn γ C₂ S)
    (h : M₁.GammaDiffBoundOn M₂ γ C₁ S) : M₁.GammaBoundOn γ (C₂ + C₁) S := by
  intro i j hi hj x hx y hy
  have a := h₂ i j hi hj x hx y hy
  have b := h i j hi hj x hx y hy
  calc _ ≤ |M₂.gammaMap y x (Pi.single i 1) j| +
        |M₁.gammaMap y x (Pi.single i 1) j - M₂.gammaMap y x (Pi.single i 1) j| := by
        have := abs_sub_le (M₁.gammaMap y x (Pi.single i 1) j)
          (M₂.gammaMap y x (Pi.single i 1) j) 0
        simpa [abs_sub_comm, add_comm] using this
    _ ≤ _ := by rw [add_mul]; exact add_le_add a b

theorem piDiffNormOn_triangle :
    M₁.piDiffNormOn M₃ γ S ≤ M₁.piDiffNormOn M₂ γ S + M₂.piDiffNormOn M₃ γ S := by
  unfold piDiffNormOn
  simp only [ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun C₂ => le_iInf fun h₂ => le_iInf fun C₁ => le_iInf fun h₁ => ?_
  have := iInf₂_le (f := fun (C : ℝ≥0) (_ : M₁.PiDiffBoundOn M₃ γ C S) => (C : ℝ≥0∞))
    (C₁ + C₂) (by simpa using h₁.triangle h₂)
  simpa using this

theorem gammaDiffNormOn_triangle :
    M₁.gammaDiffNormOn M₃ γ S ≤ M₁.gammaDiffNormOn M₂ γ S + M₂.gammaDiffNormOn M₃ γ S := by
  unfold gammaDiffNormOn
  simp only [ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun C₂ => le_iInf fun h₂ => le_iInf fun C₁ => le_iInf fun h₁ => ?_
  have := iInf₂_le (f := fun (C : ℝ≥0) (_ : M₁.GammaDiffBoundOn M₃ γ C S) => (C : ℝ≥0∞))
    (C₁ + C₂) (by simpa using h₁.triangle h₂)
  simpa using this

/-- The triangle inequality for the local model difference norm. -/
theorem diffNormOn_triangle :
    M₁.diffNormOn M₃ γ S ≤ M₁.diffNormOn M₂ γ S + M₂.diffNormOn M₃ γ S := by
  unfold diffNormOn
  calc _ ≤ (M₁.piDiffNormOn M₂ γ S + M₂.piDiffNormOn M₃ γ S) +
        (M₁.gammaDiffNormOn M₂ γ S + M₂.gammaDiffNormOn M₃ γ S) :=
        add_le_add piDiffNormOn_triangle gammaDiffNormOn_triangle
    _ = _ := by ring

theorem piDiffNormOn_comm : M₁.piDiffNormOn M₂ γ S = M₂.piDiffNormOn M₁ γ S := by
  refine le_antisymm ?_ ?_ <;>
  exact le_iInf fun C => le_iInf fun h => iInf₂_le (f := fun (C : ℝ≥0) _ => (C : ℝ≥0∞)) C h.symm

theorem gammaDiffNormOn_comm : M₁.gammaDiffNormOn M₂ γ S = M₂.gammaDiffNormOn M₁ γ S := by
  refine le_antisymm ?_ ?_ <;>
  exact le_iInf fun C => le_iInf fun h => iInf₂_le (f := fun (C : ℝ≥0) _ => (C : ℝ≥0∞)) C h.symm

/-- The local model difference norm is symmetric. -/
theorem diffNormOn_comm : M₁.diffNormOn M₂ γ S = M₂.diffNormOn M₁ γ S := by
  unfold diffNormOn
  rw [piDiffNormOn_comm, gammaDiffNormOn_comm]

/-- The local model difference norm vanishes on the diagonal. -/
theorem diffNormOn_self : M₁.diffNormOn M₁ γ S = 0 := by
  unfold diffNormOn piDiffNormOn gammaDiffNormOn
  have h1 := iInf₂_le (f := fun (C : ℝ≥0) (_ : M₁.PiDiffBoundOn M₁ γ C S) => (C : ℝ≥0∞))
    0 (by simpa using PiDiffBoundOn.self (M₁ := M₁) (γ := γ) (S := S))
  have h2 := iInf₂_le (f := fun (C : ℝ≥0) (_ : M₁.GammaDiffBoundOn M₁ γ C S) => (C : ℝ≥0∞))
    0 (by simpa using GammaDiffBoundOn.self (M₁ := M₁) (γ := γ) (S := S))
  simp only [ENNReal.coe_zero, nonpos_iff_eq_zero] at h1 h2
  rw [h1, h2, add_zero]

theorem piNormOn_le_add_piDiffNormOn :
    M₁.piNormOn γ S ≤ M₂.piNormOn γ S + M₁.piDiffNormOn M₂ γ S := by
  unfold piNormOn piDiffNormOn
  simp only [ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun C₁ => le_iInf fun h₁ => le_iInf fun C₂ => le_iInf fun h₂ => ?_
  have := iInf₂_le (f := fun (C : ℝ≥0) (_ : M₁.PiBoundOn γ C S) => (C : ℝ≥0∞))
    (C₂ + C₁) (by simpa using PiBoundOn.of_diff (M₁ := M₁) (M₂ := M₂) h₂ h₁)
  simpa using this

theorem gammaNormOn_le_add_gammaDiffNormOn :
    M₁.gammaNormOn γ S ≤ M₂.gammaNormOn γ S + M₁.gammaDiffNormOn M₂ γ S := by
  unfold gammaNormOn gammaDiffNormOn
  simp only [ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun C₁ => le_iInf fun h₁ => le_iInf fun C₂ => le_iInf fun h₂ => ?_
  have := iInf₂_le (f := fun (C : ℝ≥0) (_ : M₁.GammaBoundOn γ C S) => (C : ℝ≥0∞))
    (C₂ + C₁) (by simpa using GammaBoundOn.of_diff (M₁ := M₁) (M₂ := M₂) h₂ h₁)
  simpa using this

/-- The model norm is controlled by the norm of another model plus the difference norm. -/
theorem normOn_le_add_diffNormOn :
    M₁.normOn γ S ≤ M₂.normOn γ S + M₁.diffNormOn M₂ γ S := by
  unfold normOn diffNormOn
  calc _ ≤ (M₂.piNormOn γ S + M₁.piDiffNormOn M₂ γ S) +
        (M₂.gammaNormOn γ S + M₁.gammaDiffNormOn M₂ γ S) :=
        add_le_add piNormOn_le_add_piDiffNormOn gammaNormOn_le_add_gammaDiffNormOn
    _ = _ := by ring

end Model

end RegularityStructures
