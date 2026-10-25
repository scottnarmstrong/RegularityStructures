/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Statements.Defs.ParabolicThickening
public import Phi43Statements.Defs.Phi43Box
public import Phi43Statements.Defs.Phi43NoiseDist
public import Phi43Statements.Defs.Phi43NoiseSize
public import RegularityStructures.Analysis.Parabolic.GeneratorScaling.Integral

/-!
# Elementary facts for the convergence of the G-models

The noise distance `phi43NoiseDist` is a pseudometric on potentials and dominates the difference of
noise sizes; the window `phi43Box` is compact, and so is the parabolic thickening of a compact set.
-/

public section

open scoped ENNReal

namespace RegularityStructures.Phi43

theorem phi43NoiseDist_self (η T : ℝ) (ψ : ℝ → C(Torus3, ℝ)) :
    Statements.phi43NoiseDist η T ψ ψ = 0 := by
  simp [Statements.phi43NoiseDist, holderBesovENorm_zero]

theorem phi43NoiseDist_comm (η T : ℝ) (ψ ψ' : ℝ → C(Torus3, ℝ)) :
    Statements.phi43NoiseDist η T ψ ψ' = Statements.phi43NoiseDist η T ψ' ψ := by
  unfold Statements.phi43NoiseDist
  refine iSup_congr fun t => iSup_congr fun _ => ?_
  rw [← holderBesovENorm_neg, neg_sub]

theorem phi43NoiseDist_triangle (η T : ℝ) (ψ ψ' ψ'' : ℝ → C(Torus3, ℝ)) :
    Statements.phi43NoiseDist η T ψ ψ'' ≤ Statements.phi43NoiseDist η T ψ ψ' + Statements.phi43NoiseDist η T ψ' ψ'' := by
  unfold Statements.phi43NoiseDist
  refine iSup₂_le fun t ht => ?_
  have h : ψ t - ψ'' t = (ψ t - ψ' t) + (ψ' t - ψ'' t) := by abel
  rw [h]
  refine (holderBesovENorm_add_le η _ _).trans (add_le_add ?_ ?_)
  · exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (-1 : ℝ) (T + 1)) =>
      holderBesovENorm η (ψ t - ψ' t)) t ht
  · exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (-1 : ℝ) (T + 1)) =>
      holderBesovENorm η (ψ' t - ψ'' t)) t ht

theorem phi43NoiseSize_le_add_dist (η T : ℝ) (ψ ψ' : ℝ → C(Torus3, ℝ)) :
    Statements.phi43NoiseSize η T ψ ≤ Statements.phi43NoiseSize η T ψ' + Statements.phi43NoiseDist η T ψ ψ' := by
  unfold Statements.phi43NoiseSize Statements.phi43NoiseDist
  refine iSup₂_le fun t ht => ?_
  have h : ψ t = ψ' t + (ψ t - ψ' t) := by abel
  rw [h]
  refine (holderBesovENorm_add_le η _ _).trans (add_le_add ?_ ?_)
  · have := le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (-1 : ℝ) (T + 1)) =>
      holderBesovENorm η (ψ' t)) t ht
    simpa using this
  · have := le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (-1 : ℝ) (T + 1)) =>
      holderBesovENorm η (ψ t - ψ' t)) t ht
    simpa using this

theorem isCompact_phi43Box (T : ℝ) : IsCompact (Statements.phi43Box T) :=
  isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)

end RegularityStructures.Phi43

end
