/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Ext514.Bracket
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Schauder.Derivative

/-!
# The large-scale form of the series for `Γ_{yx} I e_i`

`extU_eq_large`: `extU n = ⟨Π_x e_i, K^{k,σ}_{n;xy}⟩ − extR n`, where `K^{k,σ}_{n;xy} =
D^k K_n(y − ·) − ∑_{|l|<σ} (y−x)^l/l! D^{k+l} K_n(x − ·)` (`dTaylorKernel`) and
`extR n = ∑_{j : |k| ≥ deg j + 2} τ_j ⟨Π_y e_j, D^k K_n(y − ·)⟩`.  This uses `Π_x e_i =
∑_j τ_j Π_y e_j` ([Hai14, proof of Lemma 5.21, (5.39)]).
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

open scoped Classical in
/-- The remainder `∑_{j : |k| ≥ deg j + 2} τ_j ⟨Π_y e_j, D^k K_n(y − ·)⟩` of the large-scale form. -/
def extR (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (x y : ParabolicSpace) (i : ι)
    (k : Fin 4 →₀ ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => ¬ (multiDeg k : ℝ) < 𝒯.deg j + 2),
    M.gammaMap y x (Pi.single i 1) j *
      derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k y n

end RegularityStructures

end

