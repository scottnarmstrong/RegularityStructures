/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Commute.Lemma516

/-!
# Hairer's Lemma 5.16: `Γ` commutes with `I + J`

Aggregator for `RegularityStructures.Abstract.Integration.Commute`:
`kConv N Λ = ∑_n ⟨Λ, K_n(z - ·)⟩` and its growth (`KConv`, `KRegular`), linearity (`KConvLinear`),
the pairing split (`GermSplit`), the germ identity `realGerm = kConv - Taylor polynomial` (`Germ`),
`Q_t` on polynomially bounded functions (`Reg`), `Q_t Π_x (I + J(x)) e_i = Q_t (K ∗ Π_x e_i)`
(`Integral`) and the lemma `Γ_{xy} (I + J(y)) e_i = (I + J(x)) Γ_{xy} e_i` (`Lemma516`). Reference:
[Hai14, Lemma 5.16], arXiv:1303.5113v4.
-/
