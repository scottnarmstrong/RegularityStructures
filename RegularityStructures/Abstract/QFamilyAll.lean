/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.QFamilyContinuousModel
public import RegularityStructures.Abstract.QFamilyR4Convolution
public import RegularityStructures.Abstract.QFamilyModelBound
public import RegularityStructures.Abstract.QFamilyR4ModelBound
public import RegularityStructures.Abstract.QFamilyR4KernelIncrement
public import RegularityStructures.Abstract.QFamilyR4ModelMollify

/-!
# `Q`-families, distributions and test functions (aggregator)

The link between the `Q`-family representation of distributions, `Λ_t = Q_t Λ` for the regularising
semigroup `Q`, and distributions tested against test functions:

* `QFamilyContinuousModel`: for a model realised by continuous functions, `Rf` is the function
  `x ↦ (Π_x f(x))(x)` ([Hai14, Remark 3.15]);
* `QFamilyR4Convolution`: on `ℝ⁴`, `∫ φ^λ_0(v) D_t(x + v) dv = ∫ q_t(x − w) ⟨D, φ^λ_w⟩ dw`;
* `QFamilyModelBound`, `QFamilyR4ModelBound`: the `Q`-form model bounds imply Hairer's
  test-function model bound [Hai14, (2.15)];
* `QFamilyR4KernelIncrement`, `QFamilyR4ModelMollify`: spatial increments of the parabolic kernel
  and the mollification of the model at positive time, ingredients of the converse implication.
-/
