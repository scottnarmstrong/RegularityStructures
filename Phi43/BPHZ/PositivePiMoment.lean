/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositivePiMomentSq
public import Phi43.BPHZ.PositivePiMomentCubeSq
public import Phi43.BPHZ.PositivePiMomentIPsiBound
public import Phi43.BPHZ.PositivePiMomentPsiX

/-!
# `q`-th moments of `Q_t Π_x τ (x)` of the canonical models on the positive-degree symbols

Facade for the Kolmogorov-form moment bounds (single model and two-model difference with the factor
`(ε ∨ ε')^θ`) for `canonicalModelOfLift N κ C (ξ ω)` on

* `I(Ψ)` (`regPi_iPsi_lintegral_enorm_pow_le`, `regPi_iPsi_sub_lintegral_enorm_pow_le`),
* `ΨXᵢ` (`regPi_psiX_lintegral_enorm_pow_le`, `regPi_psiX_sub_lintegral_enorm_pow_le`),
* `I(Ψ²)`, `I(Ψ³)` (`PositivePiMomentSq`),
* `I(Ψ³)²` (`PositivePiMomentCubeSq`).

The products `I(Ψ)Ψ`, `I(Ψ)Ψ²`, `I(Ψ²)Ψ` are not covered (see the status note).
-/
