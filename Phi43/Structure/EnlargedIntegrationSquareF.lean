/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedIntegrationF

/-!
# The integration square on the finite planted completion

Hairer [Hai14, Definition 5.7, Theorem 5.14]. Integration vanishes on
the newly planted symbols. Its square on a general vector retains only
the raw-noise coefficient; hence it vanishes on the whole Xi-free space.
-/

public section

namespace RegularityStructures.Phi43

theorem phi43IntegrationF_sq (a : SymbolF → ℝ) :
    phi43IntegrationF (phi43IntegrationF a) =
      a (.old .noise) • Pi.single (.old .iPsi) 1 := by
  funext σ
  cases σ with
  | old σ => cases σ <;> simp [phi43IntegrationF]
  | planted σ => cases σ <;>
      simp [phi43IntegrationF, Phi43PlantSource.symbol]

theorem phi43IntegrationF_sq_eq_zero {a : SymbolF → ℝ} (ha : a (.old .noise) = 0) :
    phi43IntegrationF (phi43IntegrationF a) = 0 := by
  rw [phi43IntegrationF_sq, ha, zero_smul]

end RegularityStructures.Phi43

end
