/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.LayerSum
public import RegularityStructures.Abstract.Singular.TwoModel.IntegrationData
public import RegularityStructures.Abstract.Integration.Lipschitz.Coeff
public import RegularityStructures.Abstract.Model

/-!
# Reconstruction and pairings of the lift `f⊕` are differences

For polynomial-compatible `M₁, M₂`, `λ ≠ 0` and `f⊕ = liftSum P λ f₁ f₂`
(`Π⊕_x f⊕(x) = Π¹_x f₁(x) - Π²_x f₂(x)`):

* `latticeApprox_modelSum_liftSum`, `latticeRecon_modelSum_liftSum`: `S_n f⊕ ψ = S¹_n f₁ ψ - S²_n f₂ ψ`
  (`n ≥ 3`) and `⟨R f⊕, ψ⟩ = ⟨R¹ f₁, ψ⟩ - ⟨R² f₂, ψ⟩` when both approximations converge;
* `singShellPairing_modelSum`, `nCoeffS_modelSum`: the shell pairings and `N_γ` coefficients;
* `remPairing_modelSum`: the smooth-remainder pairings;
* `rightPart_nVecS_modelSum`, `rightPart_remVec_modelSum` and the vanishing of the left parts.
-/

public section

open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}
  {f₁ f₂ : ParabolicSpace → ι → ℝ} {γ η α C₁ C₂ CPi₁ CPi₂ CGam₁ CGam₂ T : ℝ}

theorem regPi_modelSum_liftSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : lam ≠ 0) (x : ParabolicSpace) :
    (modelSum (lam := lam) h₁ h₂).regPi x (liftSum P lam f₁ f₂ x) =
      fun t y => M₁.regPi x (f₁ x) t y - M₂.regPi x (f₂ x) t y := by
  funext t y
  rw [regPi_modelSum, piSum_liftSum h₁ h₂ hlam]
  simp [Model.regPi]

end TwoModel

end RegularityStructures

end
