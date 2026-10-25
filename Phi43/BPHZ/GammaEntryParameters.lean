/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaEntryFormulas
import Mathlib.Tactic
public import Phi43.Structure.CanonicalModel

/-!
# The parameters of `canonicalGammaParameter`

For `D : CanonicalData κ` and `z z' : ParabolicSpace`, let `Ψ = D.localPsi` and let `T₀ f`,
`∂ᵢ f` denote `D.kernel.taylorConstant f`, `D.kernel.taylorSpatial f i`. Three of the parameters of
`g = D.canonicalGammaParameter z z' = f_z⁻¹ * f_{z'}` are

* `g.shift i = z_i - z'_i` (`canonicalGammaParameter_shift`);
* `g.cPsiGrad i = ∂ᵢΨ(z) - ∂ᵢΨ(z')` (`canonicalGammaParameter_cPsiGrad`);
* `g.cPsi = T₀Ψ(z) - T₀Ψ(z') + Σᵢ ∂ᵢΨ(z') (z' - z)_i` (`canonicalGammaParameter_cPsi`).

The remaining two are the differences `T₀(Ψ²)(z) - T₀(Ψ²)(z')` and `T₀(Ψ³)(z) - T₀(Ψ³)(z')`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

namespace CanonicalData

local notation "E" => ParabolicSpace

variable {κ : Kappa} (D : CanonicalData κ)

theorem canonicalGammaParameter_shift (z z' : E) (i : Fin 4) :
    (D.canonicalGammaParameter z z').shift i = parabolicCoords z i - parabolicCoords z' i := by
  simp [canonicalGammaParameter, structureGroupInv, canonicalCharacter, canonicalShift]
  ring

theorem canonicalGammaParameter_cPsiGrad (z z' : E) (i : Fin 3) :
    (D.canonicalGammaParameter z z').cPsiGrad i =
      D.kernel.taylorSpatial D.localPsi i z - D.kernel.taylorSpatial D.localPsi i z' := by
  simp [canonicalGammaParameter, structureGroupInv, canonicalCharacter, canonicalCPsiGrad]
  ring

theorem canonicalGammaParameter_cPsi (z z' : E) :
    (D.canonicalGammaParameter z z').cPsi =
      D.kernel.taylorConstant D.localPsi z - D.kernel.taylorConstant D.localPsi z' +
        ∑ i : Fin 3, D.kernel.taylorSpatial D.localPsi i z' * relCoord z z' i.succ := by
  simp only [canonicalGammaParameter, structureGroupMul_cPsi, structureGroupInv,
    canonicalCharacter, canonicalCPsi, canonicalCPsiGrad, canonicalShift, relCoord,
    Finset.sum_neg_distrib, Pi.neg_apply, neg_mul, mul_neg, neg_neg]
  rw [show (∑ i : Fin 3, D.kernel.taylorSpatial D.localPsi i z' *
      (parabolicCoords z' i.succ - parabolicCoords z i.succ)) =
      (∑ i : Fin 3, parabolicCoords z' i.succ * D.kernel.taylorSpatial D.localPsi i z') -
        ∑ i : Fin 3, parabolicCoords z i.succ * D.kernel.taylorSpatial D.localPsi i z' by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring]
  ring

end CanonicalData

end RegularityStructures.Phi43

end
