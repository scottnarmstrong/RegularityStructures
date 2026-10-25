/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaEntryParameters
public import Phi43.BPHZ.PositiveTreeFormulas
import Mathlib.Tactic
public import Phi43.Structure.CanonicalModel

/-!
# The parameter `cPsi` of `Γ_{zz'}` as a recentred convolution

Assume the Taylor constants of the kernel record are the convolutions
(`hT : ∀ f z, D.kernel.taylorConstant f z = CanonicalKernel.convolution D.kernel f z`; this holds by
`rfl` for `hairerCanonicalData`). With `⟦f⟧^r_z = D.integrate r f z`, so that
`(Π_z I(f))(y) = ⟦f⟧^r_z y` (compare [Hai14, Lemma 5.16] for the entries of `Γ`), the parameter
`cPsi` of `g = D.canonicalGammaParameter z z'` is

`g.cPsi = -(Π_z I(Ψ))(z') - Σᵢ g.cPsiGrad i (z' - z)ᵢ`

(`canonicalGammaParameter_cPsi_eq_neg_integrate`), where
`(Π_z I(Ψ))(z') = (K*Ψ)(z') - (K*Ψ)(z) - ∇(K*Ψ)(z)·(z' - z)`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

namespace CanonicalData

local notation "E" => ParabolicSpace

variable {κ : Kappa} (D : CanonicalData κ)

private theorem gammaRec_iPsi_gt_one : 1 < homogeneity κ .iPsi := by
  have := κ.2.2
  simp only [homogeneity]; linarith

variable (hT : ∀ f z, D.kernel.taylorConstant f z = CanonicalKernel.convolution D.kernel f z)
include hT

theorem canonicalGammaParameter_cPsi_eq_neg_integrate (z z' : E) :
    (D.canonicalGammaParameter z z').cPsi =
      -D.integrate (homogeneity κ .iPsi) D.localPsi z z' -
        ∑ i : Fin 3, (D.canonicalGammaParameter z z').cPsiGrad i * relCoord z z' i.succ := by
  rw [canonicalGammaParameter_cPsi, integrate_eq_of_one_lt D gammaRec_iPsi_gt_one,
    hT D.localPsi z']
  simp only [canonicalGammaParameter_cPsiGrad, sub_mul, Finset.sum_sub_distrib]
  have : ∀ i : Fin 3, D.kernel.taylorSpatial D.localPsi i z' * relCoord z z' i.succ =
      relCoord z z' i.succ * D.kernel.taylorSpatial D.localPsi i z' := fun i => mul_comm _ _
  ring

end CanonicalData

end RegularityStructures.Phi43

end
