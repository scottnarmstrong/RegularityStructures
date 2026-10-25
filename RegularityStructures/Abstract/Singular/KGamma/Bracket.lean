/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Singular.KGamma.Defs
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Singular `𝒦_γ`: the series for the `X^k` component of the increment

Singular analogue of the series for the polynomial components in the proof of
[Hai14, Theorem 5.12]: with
`τ = f(y) − Γ_{yx} f(x)`,

  `polyUS n = ∑_{|k| < deg i + 2} τ_i ⟨Π_y e_i, D^k K_n(y−·)⟩ + ⟨Rf − Π_y f(y), D^k K_n(y−·)⟩
     − ∑_{|l| < γ+2−|k|} (y−x)^l/l! ⟨Rf − Π_x f(x), D^{k+l} K_n(x−·)⟩`

and `k! (𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x))_{X^k} = ∑ₙ polyUS n`, given summability of the shell
pairings `n ↦ ⟨Rf − Π_z f(z), D^k K_n(z−·)⟩` (an analytic fact, taken as a hypothesis here).

Source: [Hai14] = arXiv:1303.5113v4, proof of Theorem 5.12 / Proposition 6.16.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

open Classical in
/-- The `n`-th term of the series for `k! (𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x))_{X^k}` (singular case). -/
def polyUS (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (γ : ℝ)
    (f : ParabolicSpace → ι → ℝ) (x y : ParabolicSpace) (k : Fin 4 →₀ ℕ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2),
      (f y - M.gammaMap y x (f x)) i *
        parabolicSemigroup.pairing (fun t z => M.regPi y (Pi.single i 1) t z)
          (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w))) +
    M.singShellPairing h f y k n -
    ∑ l ∈ taylorIdx (γ + 2 - multiDeg k), coeffT (parabolicCoords (y - x)) l *
      M.singShellPairing h f x (k + l) n

end RegularityStructures

end

