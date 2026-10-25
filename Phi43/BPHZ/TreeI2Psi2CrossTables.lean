/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiCrossTables
public import Phi43.BPHZ.TreeI2Psi2DifferenceTables

/-!
# The `2 × 2` tables of cross covariances at two mollifiers: uniform bound data

Cross-mollifier version of `TreeI2Psi2DifferenceTables`: for `z ≠ 0` the three tables
`(a, b, c, d)`, `(a, a, d, d)`, `(a, d, a, d)` of cross covariances of `(ρ, ε)`, `(ρ', ε')`
(`hairerCrossCovarianceTwo`) satisfy the bound data `Bd μ (A' p) (2 q)` with `p = s(±z)^(-1)`,
`q = s(±z)^(-θ)`, `μ = (max ε ε')^θ`.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The three tables at a point `z` with `z ≠ 0`, in the form `Bd μ (A p) (2 q)` with
`p = s(z)^(-1)`, `q = s(z)^(-θ)`. -/
theorem i2Psi2CrossTwo_tables_bd_nat (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ z : SpaceTime, 0 < torusParabolicSize z →
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize z ^ (-(1 : ℝ)))
          (2 * torusParabolicSize z ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ ε ρ' ε' z,
            hairerCrossCovarianceTwo N ρ' ε' ρ ε z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z⟩ ∧
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize z ^ (-(1 : ℝ)))
          (2 * torusParabolicSize z ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ ε ρ ε z,
            hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z⟩ ∧
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize z ^ (-(1 : ℝ)))
          (2 * torusParabolicSize z ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z,
            hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z⟩ := by
  obtain ⟨A, hA, h⟩ := hairerCrossTwo_tables_bd_i3Psi N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨A, hA, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 z hz
  obtain ⟨b1, b2, b3⟩ := h hε hε1 hε' hε'1 z hz
  have hM : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.le) _
  have hq : 0 ≤ torusParabolicSize z ^ (-θ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hq2 : torusParabolicSize z ^ (-θ) ≤ 2 * torusParabolicSize z ^ (-θ) := by linarith
  exact ⟨i2Psi2DiffTableBd_mono hM hq le_rfl hq2 b1, i2Psi2DiffTableBd_mono hM hq le_rfl hq2 b2,
    i2Psi2DiffTableBd_mono hM hq le_rfl hq2 b3⟩

/-- The three tables at a point `z` with `z ≠ 0`, in the flipped form `Bd μ (A p) (2 q)` with
`p = s(-z)^(-1)`, `q = s(-z)^(-θ)`. -/
theorem i2Psi2CrossTwo_tables_bd_flip (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ')
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ z : SpaceTime, 0 < torusParabolicSize (-z) →
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize (-z) ^ (-(1 : ℝ)))
          (2 * torusParabolicSize (-z) ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ ε ρ' ε' z,
            hairerCrossCovarianceTwo N ρ' ε' ρ ε z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z⟩ ∧
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize (-z) ^ (-(1 : ℝ)))
          (2 * torusParabolicSize (-z) ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ ε ρ ε z,
            hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z⟩ ∧
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize (-z) ^ (-(1 : ℝ)))
          (2 * torusParabolicSize (-z) ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z,
            hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z⟩ := by
  obtain ⟨A, hA, h⟩ := hairerCrossTwo_tables_bd_i3Psi N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨2 * A, by positivity, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 z hz
  have hM : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.le) _
  have hq : 0 ≤ torusParabolicSize z ^ (-θ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hn : 0 ≤ torusParabolicSize (-z) ^ (-θ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hn1 : 0 ≤ torusParabolicSize (-z) ^ (-(1 : ℝ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hz' : 0 < torusParabolicSize z := by
    have := torusParabolicSize_neg_le_two_mul z
    linarith
  obtain ⟨b1, b2, b3⟩ := h hε hε1 hε' hε'1 z hz'
  have hpq := torusParabolicSize_rpow_neg_le_flip (e := 1) zero_le_one (u := z) hz
  have hpq' := torusParabolicSize_rpow_neg_le_flip (e := θ) hθ.le (u := z) hz
  have h21 : (2 : ℝ) ^ (1 : ℝ) = 2 := Real.rpow_one 2
  rw [h21] at hpq
  have h2 : (2 : ℝ) ^ θ ≤ 2 := by
    calc (2 : ℝ) ^ θ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
      _ = 2 := h21
  have hP : A * torusParabolicSize z ^ (-(1 : ℝ)) ≤ 2 * A * torusParabolicSize (-z) ^ (-(1 : ℝ)) :=
    calc A * torusParabolicSize z ^ (-(1 : ℝ)) ≤ A * (2 * torusParabolicSize (-z) ^ (-(1 : ℝ))) :=
          mul_le_mul_of_nonneg_left hpq hA
      _ = _ := by ring
  have hQ : torusParabolicSize z ^ (-θ) ≤ 2 * torusParabolicSize (-z) ^ (-θ) :=
    hpq'.trans (mul_le_mul_of_nonneg_right h2 hn)
  exact ⟨i2Psi2DiffTableBd_mono hM hq hP hQ b1, i2Psi2DiffTableBd_mono hM hq hP hQ b2,
    i2Psi2DiffTableBd_mono hM hq hP hQ b3⟩

/-- The three tables with a common constant, for both orientations. -/
theorem i2Psi2CrossTwo_tables_bd (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      (∀ z : SpaceTime, 0 < torusParabolicSize z →
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize z ^ (-(1 : ℝ)))
          (2 * torusParabolicSize z ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ ε ρ' ε' z,
            hairerCrossCovarianceTwo N ρ' ε' ρ ε z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z⟩ ∧
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize z ^ (-(1 : ℝ)))
          (2 * torusParabolicSize z ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ ε ρ ε z,
            hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z⟩ ∧
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize z ^ (-(1 : ℝ)))
          (2 * torusParabolicSize z ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z,
            hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z⟩) ∧
      (∀ z : SpaceTime, 0 < torusParabolicSize (-z) →
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize (-z) ^ (-(1 : ℝ)))
          (2 * torusParabolicSize (-z) ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ ε ρ' ε' z,
            hairerCrossCovarianceTwo N ρ' ε' ρ ε z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z⟩ ∧
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize (-z) ^ (-(1 : ℝ)))
          (2 * torusParabolicSize (-z) ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ ε ρ ε z,
            hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z⟩ ∧
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize (-z) ^ (-(1 : ℝ)))
          (2 * torusParabolicSize (-z) ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z,
            hairerCrossCovarianceTwo N ρ ε ρ ε z, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z⟩) := by
  obtain ⟨A₁, hA₁, h₁⟩ := i2Psi2CrossTwo_tables_bd_nat N ρ ρ' hρ hρ' hθ hθ1
  obtain ⟨A₂, hA₂, h₂⟩ := i2Psi2CrossTwo_tables_bd_flip N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨A₁ + A₂, add_nonneg hA₁ hA₂, ?_⟩
  intro ε ε' hε hε1 hε' hε'1
  have hM : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.le) _
  have nz : ∀ u : SpaceTime, 0 ≤ torusParabolicSize u ^ (-θ) := fun u =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have np : ∀ u : SpaceTime, 0 ≤ torusParabolicSize u ^ (-(1 : ℝ)) := fun u =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have key : ∀ (u : SpaceTime) (t : I3PsiDiffTable) (C₁ C₂ : ℝ), C₁ ≤ C₂ →
      I3PsiDiffTable.Bd ((max ε ε') ^ θ) (C₁ * torusParabolicSize u ^ (-(1 : ℝ)))
        (2 * torusParabolicSize u ^ (-θ)) t →
      I3PsiDiffTable.Bd ((max ε ε') ^ θ) (C₂ * torusParabolicSize u ^ (-(1 : ℝ)))
        (2 * torusParabolicSize u ^ (-θ)) t := fun u t C₁ C₂ hC h =>
    i2Psi2DiffTableBd_mono hM (by have := nz u; positivity)
      (mul_le_mul_of_nonneg_right hC (np u)) le_rfl h
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨b1, b2, b3⟩ := h₁ hε hε1 hε' hε'1 z hz
    exact ⟨key _ _ _ _ (by linarith) b1, key _ _ _ _ (by linarith) b2,
      key _ _ _ _ (by linarith) b3⟩
  · obtain ⟨b1, b2, b3⟩ := h₂ hε hε1 hε' hε'1 z hz
    exact ⟨key _ _ _ _ (by linarith) b1, key _ _ _ _ (by linarith) b2,
      key _ _ _ _ (by linarith) b3⟩

end RegularityStructures.Phi43

end
