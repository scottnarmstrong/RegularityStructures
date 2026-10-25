/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Ext514.Large
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Termwise bounds for the series of the polynomial components of `Γ_{yx} I e_i`

With `τ = Γ_{yx} e_i`, `d = ‖y − x‖_𝔰`, `X = max(C_Γ, 1) C_Π card ι` and `D_j =
derivShellConst h k (degreesBelowLeIn V γ (deg j))`:

* `abs_extR_le`: `|extR n| ≤ ∑_{j ∈ F₂} max(C_Γ, 1) d^{deg i − deg j} D_j X 2^{(|k| − deg j − 2) n}`;
* `abs_extU_le_small`: `|extU n| ≤ ∑_{j ∈ F₁} (same) + ∑_{|l|<σ} d^{|l|} D'_l X
  2^{(|k+l| − deg i − 2) n}`.

The index sets `F₁`, `F₂` (`extF₁`, `extF₂`) depend only on `𝒯, V, k, i` (and the set `S` of
indices whose pairings vanish), not on the model.
[Hai14, proof of Lemma 5.21, case `‖x − y‖ ≥ 2^{-n}`, and (5.40)].
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- The basis indices `j` with `|k| < deg j + 2`, `e_j ∈ V`, `deg j ≤ deg i`. -/
def extF₁ (𝒯 : RegularityStructure ι) (V : Submodule ℝ (ι → ℝ)) (k : Fin 4 →₀ ℕ) (i : ι) :
    Finset ι :=
  Finset.univ.filter (fun j => (multiDeg k : ℝ) < 𝒯.deg j + 2 ∧ (Pi.single j 1 : ι → ℝ) ∈ V ∧
    𝒯.deg j ≤ 𝒯.deg i)

open scoped Classical in
/-- The basis indices `j ∉ S` with `|k| ≥ deg j + 2`, `e_j ∈ V`, `deg j ≤ deg i`. -/
def extF₂ (𝒯 : RegularityStructure ι) (V : Submodule ℝ (ι → ℝ)) (k : Fin 4 →₀ ℕ) (i : ι)
    (S : Finset ι) : Finset ι :=
  Finset.univ.filter (fun j => ¬ (multiDeg k : ℝ) < 𝒯.deg j + 2 ∧ (Pi.single j 1 : ι → ℝ) ∈ V ∧
    𝒯.deg j ≤ 𝒯.deg i ∧ j ∉ S)

end RegularityStructures

end

