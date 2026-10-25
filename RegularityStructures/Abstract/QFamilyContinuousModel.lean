/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Consistency

/-!
# Reconstruction for a model realised by continuous functions

[Hai14, Remark 3.15]: if every `Π_x τ` is a continuous function, then for `f ∈ D^γ`, `γ > 0`,
the reconstruction `Rf` is the continuous function `Rf(x) = (Π_x f(x))(x)`. ([Hai14,
Proposition 3.28] is the related statement for sectors `V ⊂ T̄ + T_{α+}`.)

Here a model is *realised by functions* (`IsFunctionModel M g`) when every `Π_x e_i` is the
`Q`-family `t ↦ Q_t g_{x,i}` of a bounded measurable function `g_{x,i}` that is continuous with
respect to `scaleDist`. For a conservative kernel:

* `diag_eq_zero_of_isFunctionModel`: `g_{y,i}(y) = 0` when `0 < deg i < γ` (the model bound
  `|(Q_t Π_y e_i)(y)| ≤ C_Π t^{deg i/ℓ}` and the approximate identity `Q_t g → g`);
* `sum_mul_eq_sum_gammaMap`: `(Π_x τ)(y) = (Π_y Γ_{yx} τ)(y)` pointwise;
* `pointwiseReconstruct g f x = ∑_i f(x)_i g_{x,i}(x) = (Π_x f(x))(x)`;
* `reconstruct_eq_ofFunction`: **`Rf = Q(R̃f)`**, the identity of `Q`-families, under the
  additional hypothesis that the diagonal values `g_{y,i}(y)` of the components of negative
  homogeneity are bounded (with the global norms of this layer, this replaces the local
  boundedness implicit in [Hai14]);
* `continuous_pointwiseReconstruct`: `R̃f` is continuous with respect to `scaleDist`;
* `pairing_reconstruct_eq_integral`: `⟨Rf, φ⟩ = ∫ R̃f φ` for every integrable `φ`.

Sources: [Hai14] = arXiv:1303.5113v4, Remark 3.15 and Proposition 3.28.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

/-- `R̃f(x) = (Π_x f(x))(x) = ∑_i f(x)_i g_{x,i}(x)`, the candidate reconstruction of
[Hai14, Remark 3.15] for a model realised by the functions `g`. -/
def pointwiseReconstruct (g : E → ι → E → ℝ) (f : E → ι → ℝ) (x : E) : ℝ :=
  ∑ i, f x i * g x i x

end RegularityStructures

end

