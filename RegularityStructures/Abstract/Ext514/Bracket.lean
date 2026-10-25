/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Ext514.Decomp
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Schauder.Derivative
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The series for the polynomial components of `Γ_{yx} I e_i`

`extU M h x y i k n = ∑_{j : |k| < deg j + 2} τ_j ⟨Π_y e_j, D^k K_n(y − ·)⟩ −
 ∑_{|l| < σ} (y−x)^l/l! ⟨Π_x e_i, D^{k+l} K_n(x − ·)⟩`, `τ = Γ_{yx} e_i`, `σ = deg i + 2 − |k|`
(the `n`-th term of [Hai14, (5.38)], with the roles of `x, y` exchanged).
`Model.poly_bracket_ext`: `k! (Γ_{yx} I e_i)_{X^k} = ∑_n extU n` and the series is summable.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

open scoped Classical in
/-- The `n`-th term of the series for the `X^k` component of `Γ_{yx} I e_i`. -/
def extU (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (x y : ParabolicSpace) (i : ι)
    (k : Fin 4 →₀ ℕ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.univ.filter (fun j => (multiDeg k : ℝ) < 𝒯.deg j + 2),
    M.gammaMap y x (Pi.single i 1) j *
      derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k y n) -
  ∑ l ∈ taylorIdx (𝒯.deg i + 2 - multiDeg k), coeffT (parabolicCoords (y - x)) l *
    derivShellPairing (fun t z => M.regPi x (Pi.single i 1) t z) h (k + l) x n

end RegularityStructures

end

