/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Realising.Measurable
public import RegularityStructures.Abstract.Polynomial.Model.Fubini

/-!
# The realised integral as a `Q`-distribution

A model realises the kernel for `I` when `(Q_t Π_x I e_i)(z) = ∫ Q_t(z, y) g_{x,i}(y) dy`,
`g_{x,i} = realGerm M N x i` [Hai14, Remark 5.10]. The germ has polynomial growth
`|g_{x,i}(y)| ≲ ‖y - x‖_𝔰^{deg i + 2}` (`polyBounded_realGerm`), so `Q_t g_{x,i}` is defined, and
`realReg M N x i t = Q_t g_{x,i}` (`0` for `t ≤ 0`) is a `Q`-distribution (`realReg_mem`)
by the semigroup property on polynomially bounded functions (`PolyBounded.apply_apply`).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- Generic fact: `t ↦ Q_t g` (zero for `t ≤ 0`) is a `Q`-distribution for polynomially bounded
`g`. -/
theorem mem_distributions_ite_apply {g : ParabolicSpace → ℝ} (hg : PolyBounded g) :
    (fun t z => if 0 < t then parabolicSemigroup.apply t g z else 0) ∈
      parabolicSemigroup.distributions := by
  refine ⟨fun t ht => ?_, fun s t hs ht y => ?_⟩
  · funext z
    simp [not_lt.2 ht]
  · simp only [ht, add_pos hs ht, ite_true]
    exact ⟨(hg.apply ht).integrable_parabolicKernel_mul hs y, hg.apply_apply hs ht y⟩

end RegularityStructures

end
