/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Inhomogeneity.DuhamelDeriv

/-!
# Linearity of the Duhamel field in the forcing, and the jet element `θ`

`duhamelField (g₁ - g₂) = duhamelField g₁ - duhamelField g₂` (`duhamelField_sub`), so the
comparison of the jets of two Duhamel fields reduces to `DerivBound` of the Duhamel field of the
difference of the forcings (`derivBound_duhamelField_sub`).
-/

open scoped ContDiff

public section

namespace RegularityStructures.Inhomogeneity

open RegularityStructures.PDE

variable {g₁ g₂ : ParabolicSpace → ℝ}

theorem PerSmooth.sub (h₁ : PerSmooth g₁) (h₂ : PerSmooth g₂) : PerSmooth (g₁ - g₂) where
  smooth := h₁.smooth.sub h₂.smooth
  periodic z c hc := by
    simp only [Pi.sub_apply]
    rw [h₁.periodic z c hc, h₂.periodic z c hc]

theorem forcePath_sub (h₁ : PerSmooth g₁) (h₂ : PerSmooth g₂) (s : ℝ) :
    forcePath (h₁.sub h₂) s = forcePath h₁ s - forcePath h₂ s := by
  ext x
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  simp [forcePath_apply]

theorem duhamelField_sub (h₁ : PerSmooth g₁) (h₂ : PerSmooth g₂) :
    duhamelField (h₁.sub h₂) = duhamelField h₁ - duhamelField h₂ := by
  funext z
  by_cases hz : 0 < z.1
  · rw [duhamelField_of_pos _ hz, Pi.sub_apply, duhamelField_of_pos _ hz,
      duhamelField_of_pos _ hz]
    have : forcePath (h₁.sub h₂) = fun s => forcePath h₁ s - forcePath h₂ s :=
      funext (forcePath_sub h₁ h₂)
    rw [this, duhamel_sub (continuous_forcePath h₁) (continuous_forcePath h₂)]
    rfl
  · simp [duhamelField_of_nonpos _ (not_lt.1 hz)]

end RegularityStructures.Inhomogeneity

end
