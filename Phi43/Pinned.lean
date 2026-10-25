/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Pinned.GroupParameters
public import Phi43.Pinned.ModelAgreement
public import Phi43.Pinned.PinnedPi
public import Phi43.Pinned.PiPinned
public import Phi43.Pinned.GammaPinned
public import Phi43.Pinned.NormTransfer

/-!
# `Γ` and `Π` are pinned by `IsRenormalisedCanonicalModel` (aggregator)

* `regPi_eq_of_isRenormalisedCanonicalModel`: `Q_t Π_x e_τ` agrees for two models, for `τ` in
  `F₋`, `1`, `X_i`, `I(Ψ)`, `I(Ψ²)`, `I(Ψ³)`.
* `gammaMap_single_eq_of_isRenormalisedCanonicalModel`: `Γ_{xy} e_τ` agrees for every
  `τ ≠ X₀`.
* `gammaBoundOn_iff_of_isRenormalisedCanonicalModel`, `abs_regPi_diag_eq_of_pinned`: the
  `Γ`-bounds at the cutoff and the diagonal `Π`-bounds on pinned symbols agree.

**The exception `τ = X₀` is necessary.**  `Γ_{xy} X₀ = X₀ + shift₀(x,y) • 1` and the time shift
occurs in no other `Γ_{xy} e_τ`.  Given `Z`, set `Π'_x X₀ := Π_x X₀ + h(x) • 1` (`h` a measurable
function) and `shift₀' := shift₀ + h(y) - h(x)`, all other data unchanged: this is a model
(`Π'_x Γ'_{xy} X₀ = Π_x X₀ + h(x) + shift₀' = Π'_y X₀`; cocycle by additivity), satisfies
`IsRenormalisedCanonicalModel` (which constrains only `deg < γ`, and `deg X₀ = 2 > γ`), but has a
different `Γ_{xy} X₀` for non-constant `h`.
-/
