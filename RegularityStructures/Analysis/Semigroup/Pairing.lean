/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Main

/-!
# Pairing of `Q`-distributions with test functions

Aggregator for `Analysis/Semigroup/Pairing/`: the pairing `⟨Λ, φ⟩ = lim_{s ↓ 0} ∫ Λ_s φ`
(`pairing`), its existence (`tendsto_integral_pairing`) and the bound
`|⟨Λ, φ⟩| ≤ C · pairingConst A · (B₀ + B₁) · λ^γ` (`abs_pairing_le`) for `Λ` of local order `γ`
at `x₀` and `φ` adapted to scale `λ` with `ψ = Lφ`; the increment identity
`LocalData.integral_sub_integral_eq_integral`. Reference: [Hai14, Theorem 3.10, (3.3)],
arXiv:1303.5113v4.
-/
