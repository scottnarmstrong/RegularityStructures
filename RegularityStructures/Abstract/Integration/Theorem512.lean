/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.Witness
public import RegularityStructures.Abstract.Integration.Sector

/-!
# Multilevel Schauder estimate, Hairer Theorem 5.12 (facade)

Aggregator for `RegularityStructures.Abstract.Integration.Theorem512`: the standing hypotheses
(`Setting`), sup bounds and support in `T_{<γ+2}` (`Sup`), the `D^{γ+2}` bound (`Increment`),
measurability of `𝒦_γ f` (`MeasPairing`, `MeasKGamma`) `𝒦_γ f ∈ D^{γ+2}` (`Main`), and
`R 𝒦_γ f = K ∗ Rf` (5.17) (`Helpers`, `KConvTaylor`, `ReconId`, `ReconMain`); `Witness` exhibits a
concrete instance of the standing hypotheses (non-vacuity). Reference: [Hai14, Theorem 5.12],
arXiv:1303.5113v4.
-/
