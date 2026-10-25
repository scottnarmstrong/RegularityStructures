/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedPolynomialF
public import RegularityStructures.Analysis.Parabolic.SingularKernel
import RegularityStructures.Abstract.Integration.JMapLinear
import Mathlib.Tactic.Linarith

/-!
# Degree hypotheses for the enlarged Φ⁴₃ polynomial sector

Hairer [Hai14, Section 9.4, Proposition 9.8].  With
`γ₀ = 1 + 3κ` and `α = -1/2 - κ`, the polynomial degree required by the
fixed-point theorem is `γ₀ + 2α + 2 = 2 + κ < 3`.  Thus `PolyIndex 3`
contains every required monomial, including `X₀` and the symmetric spatial
quadratics.  This is only the algebraic degree input, not the fixed-point
theorem itself.
-/

public section

namespace RegularityStructures.Phi43

theorem phi43DegreeTwo_hNgamma (κ : Kappa) (l : Fin 4 →₀ ℕ)
    (h : (multiDeg l : ℝ) < gamma κ + (-1 / 2 - κ.1) + (-1 / 2 - κ.1) + 2) :
    multiDeg l < 3 := by
  have hk : κ.1 < 1 := by
    linarith [κ.2.2]
  have he : gamma κ + (-1 / 2 - κ.1) + (-1 / 2 - κ.1) + 2 = 2 + κ.1 := by
    dsimp [gamma]
    ring
  rw [he] at h
  have hreal : (multiDeg l : ℝ) < 3 := by
    linarith
  exact_mod_cast hreal

end RegularityStructures.Phi43

end
