/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StationaryField

/-!
# Stochastic objects of Φ⁴₃

Aggregator for the Φ⁴₃-specific Gaussian computations (the remark after Definition 2.5 of the
statement): `StationaryField`, the field `Ψ_ε(z) = W(G_ε(z - ·))`, its covariance `Q_ε` and
`E[Ψ_ε(z)²] = C₁^ε`.
-/
