/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Decomposition
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The germ of a realised integral

For a model `M` and a basis index `i`, Hairer's Remark 5.10 expresses the integral `I e_i` through

  `(Π_x I e_i)(ψ) = ∑_n ∫ ψ(y) (Π_x e_i)(K^α_{n;xy}) dy`,  `α = deg i`,

with `K^α_{n;xy}(z) = K_n(y, z) - ∑_{|k|_𝔰 < α + 2} (y - x)^k/k! D₁^k K_n(x, z)`. The inner
function is `realGerm M N x i y = ∑_n ⟨Π_x e_i, K^{deg i}_{n;xy}⟩` (with `K_n = annShell N n`).
We show the series converges absolutely and
`|realGerm M N x i y| ≤ c C_Π max(C_Γ, 1) ‖y - x‖_𝔰^{deg i + 2}`
(`exists_abs_realGerm_le`), by the Taylor-remainder pairing bound
(`exists_tsum_abs_pairing_taylorKernel_le`) applied to `Π_x e_i`, which is of local order
`deg i` at `x` (`Model.isLocalOrder_regPi_single`).

Source: [Hai14] = arXiv:1303.5113v4, Definition 5.9, Remark 5.10, (5.14), Lemma 5.19.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- `Π_x e_i`, as a `Q`-family, lies in the distributions. -/
theorem regPi_single_mem_distributions (M : Model 𝒯 parabolicSemigroup) (x : ParabolicSpace)
    (i : ι) :
    (fun t z => M.regPi x (Pi.single i 1) t z) ∈ parabolicSemigroup.distributions :=
  (M.pi x (Pi.single i 1)).2

end RegularityStructures

end
