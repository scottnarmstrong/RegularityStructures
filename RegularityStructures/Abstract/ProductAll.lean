/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ProductDefs
public import RegularityStructures.Abstract.ProductBounds
public import RegularityStructures.Abstract.ProductTheorem
public import RegularityStructures.Abstract.ProductCube
public import RegularityStructures.Abstract.ProductTwoModelsBounds
public import RegularityStructures.Abstract.ProductTwoModels
public import RegularityStructures.Abstract.WeightedSingularDefs
public import RegularityStructures.Abstract.WeightedSingularBounds
public import RegularityStructures.Abstract.WeightedSingularProduct
public import RegularityStructures.Abstract.WeightedSingularTwoModels
public import RegularityStructures.Abstract.WeightedSingularCube
public import RegularityStructures.Abstract.WeightedSingularCubeTwoModels

/-!
# Products of modelled distributions (aggregator)

[Hai14, §4 and §6.2] on the abstract layer:

* `ProductDefs`: products on a regularity structure (Definition 4.1), `γ`-regular pairs of
  sectors (Definition 4.6), the truncated product `f ⋆_γ g = Q_{<γ}(f ⋆ g)`;
* `ProductTheorem`: multiplication of modelled distributions (Theorem 4.7);
* `ProductNorm`: Theorem 4.7 in terms of the norms `modelledNormOn`, `gammaNormOn`;
* `ProductExamples`: the hypotheses of Theorem 4.7 are satisfiable (a unital product on the
  single-symbol structure and the constant model);
* `ProductLipschitz`: the local Lipschitz bound for one model;
* `ProductTwoModels`: products for two models (Proposition 4.10);
* `ProductCube`: triple products and the cube `U ↦ Q_{<γ}(U ⋆ U ⋆ U)` (Φ⁴₃ nonlinearity);
* `ProductCubeTwoModels`: continuity of the cube jointly in `U` and the model;
* `WeightedSingularDefs`: singular modelled distributions `D^{γ,η}_P` (Definition 6.2);
* `WeightedSingularProduct`: their multiplication (Proposition 6.12, with the necessary extra
  hypothesis `η ≤ γ`);
* `WeightedSingularTwoModels`: the two-model bound of Proposition 6.12;
* `WeightedSingularLipschitz`: the local Lipschitz bound on `D^{γ,η}_P` for one model;
* `WeightedSingularCube`: triple products and the cube on `D^{γ,η}_P`;
* `WeightedSingularCubeTwoModels`: the cube on `D^{γ,η}_P` for two models.
-/
