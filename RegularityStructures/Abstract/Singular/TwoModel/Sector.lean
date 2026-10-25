/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Model
public import RegularityStructures.Abstract.Model

/-!
# The polynomial sector `P⊕` of the difference model

The polynomial sector `polySectorSum P : PolynomialSector 𝒯⊕ N'` (`emb = inr ∘ P.emb`, see
`RegularityStructures.Abstract.Singular.TwoModel.Group`). The model `M⊕` is polynomial-compatible
with `P⊕` (`isPolyCompatible_modelSum`).
-/

public section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

theorem isPolyCompatible_modelSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P) :
    (modelSum (lam := lam) h₁ h₂).IsPolyCompatible (polySectorSum P) := by
  intro x k t z
  rw [regPi_modelSum]
  exact (coe_piSum_single_inr x (P.emb k) t z).trans (h₂ x k t z)

end TwoModel

end RegularityStructures

end
