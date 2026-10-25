/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiCrossPointwise
public import Phi43.BPHZ.TreeI3PsiDifferenceChain
public import Phi43.BPHZ.TreeI3Psi2DifferenceTwoChaos

/-!
# The chain pieces of the cross-mollifier difference diagram of `I(Ψ³)Ψ`

With `K = hairerKernelTorus N`, `δK(z, w) = K(z - w) - K(-w)` and the second differences
`i3PsiDiffD1Cross`, `i3PsiDiffD2Cross`, `i3PsiDiffD3Cross` of the cross covariances of the two
mollifiers `ρ, ρ'` at scales `ε, ε'`, the three pieces of the second difference of the block kernels
are `δK(z,w) δK(z',v)` times these second differences, evaluated at the arguments of the diagram.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The first chain piece. -/
def i3PsiDiffPiece1Cross (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (ε ε' : ℝ)
    (z z' w v : SpaceTime) : ℝ :=
  (hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)) *
    (hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)) *
    i3PsiDiffD1Cross N ρ ρ' ε ε' (w - z) (w - v) (v - z')

/-- The third piece (secondary chain). -/
def i3PsiDiffPiece3Cross (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (ε ε' : ℝ)
    (z z' w v : SpaceTime) : ℝ :=
  (hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)) *
    (hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)) *
    i3PsiDiffD3Cross N ρ ρ' ε ε' (w - v) (w - z') (z - v)

/-- The principal piece. -/
def i3PsiDiffPiece2Cross (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (ε ε' : ℝ)
    (z z' w v : SpaceTime) : ℝ :=
  (hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)) *
    (hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)) *
    i3PsiDiffD2Cross N ρ ρ' ε ε' (w - v) (z - z')

end RegularityStructures.Phi43

end
