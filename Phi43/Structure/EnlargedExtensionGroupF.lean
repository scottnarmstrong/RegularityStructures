/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedExtensionCommF

/-!
# Every old group action admits a finite planted extension

Hairer [Hai14, Theorem 5.14], algebraic part. The explicit linear map
with zero additional Taylor polynomial is graded-unipotent and hence
invertible. Its integration and noise identities give membership in
the extension group. This is not the analytic extension of a model.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The actual automorphism extending an old group element to the new plants. -/
def phi43PlantExtensionGroupElementF (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (hg : g ∈ (phi43RegularityStructure κ).group) :
    LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    (phi43LinearEquivOfGradedUnipotentF (phi43DegreeF κ) (phi43PlantExtensionLinearF g.val)
      (phi43PlantExtensionLinearF_unipotent κ g.val
        ((phi43RegularityStructure κ).isGradedUnipotent g hg)))

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem phi43PlantExtensionGroupElementF_mem (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (hg : g ∈ (phi43RegularityStructure κ).group) :
    phi43PlantExtensionGroupElementF κ g hg ∈ (phi43RegularityStructureF κ).group := by
  apply phi43ExtensionGroupF_mem_of_basis κ _
    (phi43PlantExtensionLinearF_unipotent κ g.val
      ((phi43RegularityStructure κ).isGradedUnipotent g hg)) g hg
  · exact phi43PlantExtensionLinearF_old g.val
  · intro τ
    change phi43IntegrationF (phi43PlantExtensionLinearF g.val (Pi.single τ 1)) -
      phi43PlantExtensionLinearF g.val (phi43IntegrationF (Pi.single τ 1)) ∈ _
    cases τ with
    | old τ => exact phi43PlantExtensionLinearF_comm_old κ g hg τ
    | planted τ =>
      rw [phi43PlantExtensionLinearF_comm_planted κ g hg τ]
      exact Submodule.zero_mem _
  · exact phi43PlantExtensionLinearF_noise_single κ g hg

end RegularityStructures.Phi43

end
