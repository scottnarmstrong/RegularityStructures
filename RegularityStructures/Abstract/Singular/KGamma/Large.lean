/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.Bracket
public import RegularityStructures.Abstract.Singular.Kernel.Shell
public import RegularityStructures.Analysis.Heat.Schauder.DTaylorDeriv
public import RegularityStructures.Analysis.Heat.Schauder.TaylorSum
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Singular `𝒦_γ`: the large-scale form of the series

Singular analogue of the large-scale form of the series in the proof of [Hai14, Theorem 5.12]: for
every `n`,

  `polyUS n = ⟨Rf − Π_x f(x), K^{k,γ}_{n;yx}⟩ − ∑_{i : |k| ≥ deg i + 2} τ_i ⟨Π_y e_i, D^k K_n(y−·)⟩`,

where `⟨Rf − Π_x f(x), g⟩ = latticeRecon f g − ⟨Π_x f(x), g⟩`, `K^{k,γ}_{n;yx}` is
`dTaylorKernel h k n (γ + 2 − |k|) x y`, and `τ = f(y) − Γ_{yx} f(x)` ([Hai14, (5.48)]).
Linearity of the lattice reconstruction is used under the
hypothesis `hconv` that the lattice approximations converge on the shell derivatives.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace RegularityStructures

theorem dTaylorKernel_eq_sub_sum (h : ParabolicSpace → ℝ) (k : Fin 4 →₀ ℕ) (n : ℕ) (σ : ℝ)
    (x y : ParabolicSpace) :
    dTaylorKernel h k n σ x y = fun w =>
      lineIter (multiDirs k) (scaledShell h n) (y - w) - ∑ l ∈ taylorIdx σ,
        coeffT (parabolicCoords (y - x)) l *
          lineIter (multiDirs (k + l)) (scaledShell h n) (x - w) := by
  funext w
  simp only [dTaylorKernel, evalParabolic_monomial_div]

end RegularityStructures

end
