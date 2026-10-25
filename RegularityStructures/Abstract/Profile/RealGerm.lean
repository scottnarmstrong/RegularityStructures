/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Profile.Basic
public import RegularityStructures.Abstract.Integration.Realising.Measurable
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The germ of a realised integral, for a general shell profile

Profile-generic version of `RegularityStructures.Abstract.Integration.Realising.Germ` and of the
measurability part of `RegularityStructures.Abstract.Integration.Realising.Measurable`. For a model
`M`, a basis index `i` and a kernel profile `h` (`ShellProfile h N`), the germ is
`realGermP M h x i y = ∑_n ⟨Π_x e_i, K^{deg i}_{n;xy}⟩` with `K_n = scaledShell h n` [Hai14, Remark
5.10]. It converges absolutely with
`|realGermP M h x i y| ≤ c C_Π max(C_Γ, 1) ‖y - x‖_𝔰^{deg i + 2}` (`exists_abs_realGerm_leP`) and is
measurable (`measurable_realGermP`).

Source: [Hai14] = arXiv:1303.5113v4, Definition 5.9, Remark 5.10, (5.14), Lemma 5.19.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- `y ↦ ∑_n ⟨Π_x e_i, K^{deg i}_{n;xy}⟩` with `K_n = scaledShell h n`: the density of
`Π_x I e_i` against Lebesgue measure in Hairer's Remark 5.10. -/
def realGermP (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (i : ι) (y : ParabolicSpace) : ℝ :=
  ∑' n : ℕ, parabolicSemigroup.pairing (fun t z => M.regPi x (Pi.single i 1) t z)
    (taylorKernel h n (𝒯.deg i + 2) x y)

end RegularityStructures

end

