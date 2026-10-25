/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.Series
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The layer bound for the lattice reconstruction of a singular modelled distribution

Hairer, arXiv:1303.5113v4, Proposition 6.9 (in the lattice form of the proof of Proposition 7.2):
for `f ∈ D^{γ,η}_P` with values in a sector of regularity `α`, `α ∧ η > -2`, and a test function
`ψ = φ^λ_x` (for any `x`, in particular crossing `P = {t = 0}`) vanishing after time `T`, the
lattice approximations `S_n f ψ` converge and `|⟨R f, ψ⟩| ≤ C K₀ Cf λ^{α ∧ η}`.
-/

public section

open Filter Set Topology

namespace RegularityStructures.Layer

theorem exists_gamma_prime {γ η α : ℝ} (hγ : 0 < γ) (hαγ : α ≤ γ) (hαη : -2 < min α η) :
    ∃ g : ℝ, 0 < g ∧ g ≤ γ ∧ g < η + 2 ∧ min α η ≤ g := by
  have hη : -2 < η := lt_of_lt_of_le hαη (min_le_right _ _)
  set p : ℝ := min 1 ((η + 2) / 2) with hp
  have hp0 : 0 < p := lt_min one_pos (by linarith)
  have hp1 : p < η + 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨min γ (max (min α η) p), lt_min hγ (lt_max_of_lt_right hp0), min_le_left _ _, ?_, ?_⟩
  · refine lt_of_le_of_lt (min_le_right _ _) (max_lt ?_ hp1)
    linarith [min_le_right α η]
  · exact le_min ((min_le_left _ _).trans hαγ) (le_max_left _ _)

theorem rpow_inv_two_pow_add (n₀ j : ℕ) (a : ℝ) :
    (((2 : ℝ) ^ (j + n₀))⁻¹) ^ a = (((2 : ℝ) ^ n₀)⁻¹) ^ a * (((2 : ℝ)⁻¹) ^ a) ^ j := by
  have e : ((2 : ℝ) ^ (j + n₀))⁻¹ = ((2 : ℝ) ^ n₀)⁻¹ * ((2 : ℝ)⁻¹) ^ j := by
    rw [pow_add, mul_inv, mul_comm, inv_pow]
  rw [e, Real.mul_rpow (by positivity) (by positivity), Real.rpow_pow_comm (by positivity)]

end RegularityStructures.Layer

end

