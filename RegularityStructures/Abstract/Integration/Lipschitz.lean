/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Lipschitz.Coeff

/-!
# Local Lipschitz continuity of the multilevel Schauder estimate (facade)

Aggregator for the local Lipschitz half of [Hai14, Theorem 5.12] (last statement),
`|||𝒦_γ f; 𝒦̄_γ f̄|||_{γ+2} ≲ |||f; f̄|||_γ + ‖Π − Π̄‖ + ‖Γ − Γ̄‖`, on a sector `V`.

* `Local`, `LocalPi`: the differences `(R¹f¹ − Π¹_x f¹(x)) − (R²f² − Π²_x f²(x))` and
  `Π¹_x e_i − Π²_x e_i` are of the right local order at `x` (sector exponents);
* `Setting`: the bundled hypotheses `LipModels`, `LipFunctions`;
* `Coeff`: Lipschitz bounds for `jCoeff` and `nCoeff`;
* `Sup`, `Increment`: sup values and non-polynomial increments of `𝒦¹f¹ − 𝒦²f²`;
* `Series`, `Large`, `PolyTerm`, `PolySum`, `PolySmall`, `PolySeries`, `Poly`: polynomial
  components of the increments (series bound for the difference of the two series);
* `Main`: `Model.kGamma_modelledDiffBound_in`; `Corollary`: `Model.kGamma_modelledDiffBound_in_le`.
-/
