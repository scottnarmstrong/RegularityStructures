/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.TorusLittlewoodPaleyENorm
public import RegularityStructures.Torus.HolderBesov
public import Phi43.Steps.ClosureNormEquiv

/-!
# The heat-semigroup norm and the Littlewood–Paley norm

For `η < 0`, the norm `‖f‖_η = sup_{0 < s ≤ 1} s^{-η/2} ‖P_s f‖_∞` of the statement, equation
(2.3), and the Littlewood–Paley norm `sup_n 2^{nη} ‖Δ_n f‖_∞` of `B^η_{∞,∞}(T³)` are equivalent
on `C(T³)`. Hence the space `𝒞^η` of Theorem A, the completion of `C(T³)` for `‖·‖_η`, is the
closure of the continuous functions in the Hölder–Besov space `B^η_{∞,∞}(T³)` in which
[Hai14, Theorem 1.15] is stated. The statement records this equivalence in the remark after
Definition 2.1, outside the theorem itself.

The proof is `RegularityStructures.Phi43.closureNorm_equiv_littlewoodPaley`,
in the module `Phi43.Steps.ClosureNormEquiv`.

Source: the statement, Definition 2.1 and the remark after it.
-/

public section

namespace RegularityStructures.Phi43

/-- **Equivalence of norms.** For `η < 0` there is `C > 0` such that
`‖f‖_η ≤ C ‖f‖_{B^η_{∞,∞}}` and `‖f‖_{B^η_{∞,∞}} ≤ C ‖f‖_η` for every `f ∈ C(T³)`. Here `‖·‖_η` is
`holderBesovENorm η`, and the Littlewood–Paley norm is `torusLittlewoodPaleyENorm η`. -/
theorem Statements.closureNorm_equiv_littlewoodPaley (η : ℝ) (hη : η < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : C(RegularityStructures.Torus3, ℝ),
      RegularityStructures.holderBesovENorm η f ≤
          ENNReal.ofReal C * RegularityStructures.Phi43.Statements.torusLittlewoodPaleyENorm η f ∧
        RegularityStructures.Phi43.Statements.torusLittlewoodPaleyENorm η f ≤
          ENNReal.ofReal C * RegularityStructures.holderBesovENorm η f :=
  by exact RegularityStructures.Phi43.closureNorm_equiv_littlewoodPaley η hη

end RegularityStructures.Phi43

end
