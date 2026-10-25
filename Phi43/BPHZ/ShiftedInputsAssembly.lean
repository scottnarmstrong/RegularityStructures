/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSingleAll
public import Phi43.BPHZ.ShiftedPiSubAll
public import Phi43.BPHZ.ShiftedPiCubeSq
public import Phi43.BPHZ.ShiftedGamma

/-!
# The shifted moment package

`ShiftedBphzInputs N κ` (`ShiftedMomentDefs`) assembled from its four parts: the linear rows
(`shiftedBphzInputs_pi_of`, `shiftedBphzInputs_pi_sub_of`), the `I(Ψ³)²` square
(`regPi_iPsiCubeSq_shift_lintegral_enorm_pow_le` and its difference version) and the Γ shift
(`shiftedBphzInputs_gamma`). The only remaining hypothesis is `BphzCauchyMoments`, the product
moments of `I(Ψ)Ψ` and `I(Ψ)Ψ²`, which holds by `bphzCauchyMoments_holds`.
-/

public section

namespace RegularityStructures.Phi43

universe u

/-- The full shifted moment package, given the product moments `BphzCauchyMoments`. -/
theorem shiftedBphzInputs_of_bphzCauchyMoments
    (hmiss : ∀ (N : ℕ) (κ : Kappa), BphzCauchyMoments.{u} N κ) :
    ∀ (N : ℕ) (κ : Kappa), ShiftedBphzInputs.{u} N κ := fun N κ =>
  { pi := shiftedBphzInputs_pi_of (hmiss N κ)
      (fun hρ _ hκb0 hκb _ hq _ hB =>
        regPi_iPsiCubeSq_shift_lintegral_enorm_pow_le N hρ κ hκb0 hκb hq hB)
    pi_sub := shiftedBphzInputs_pi_sub_of (hmiss N κ)
      (fun hρ hρ' _ _ hκb0 hθ hκθ _ hq _ hB =>
        regPi_iPsiCubeSq_shift_sub_lintegral_enorm_pow_le N hρ hρ' κ hκb0 hθ hκθ hq hB)
    gamma := shiftedBphzInputs_gamma N κ }

end RegularityStructures.Phi43

end
