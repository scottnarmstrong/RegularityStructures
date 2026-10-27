/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-! Numerical pieces of `s.local.insertion`, `s.local.chain`, and
`s.local.maxrow`. Local seminorm and PDE attachments remain separate obligations. -/
public section

namespace GlobalPhi43.Local

/-- Defect half of the augmented contradiction predicate, for a *given* common `c`.
No per-datum existential choice of `c` is hidden here. -/
@[expose] def DefectSmall (c M E₁ E₂ E₃ : ℝ) : Prop :=
  E₁ + E₃ ≤ c * M ^ 3 ∧ E₂ ≤ c * M ^ 2

/-- The three smooth defects have precisely the combined bound used in (4.8′). -/
theorem defect_forcing_le {c M E₁ E₂ E₃ : ℝ}
    (hM : 0 ≤ M) (h : DefectSmall c M E₁ E₂ E₃) :
    E₁ + E₃ + 3 * M * E₂ ≤ 4 * c * M ^ 3 := by
  obtain ⟨h₁₃, h₂⟩ := h
  nlinarith [mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 3 * M by positivity)]

/-- At the natural radius `d₀ = M⁻¹`, the insertion is bounded by `4CcM`.
This is slightly sharper than the exported `5CcM` allowance. -/
theorem defect_insertion_at_natural_radius {C c M E₁ E₂ E₃ : ℝ}
    (hC : 0 ≤ C) (hM : 0 < M) (h : DefectSmall c M E₁ E₂ E₃) :
    C * (M⁻¹) ^ 2 * (E₁ + E₃ + 3 * M * E₂) ≤ 4 * C * c * M := by
  calc
    _ ≤ C * (M⁻¹) ^ 2 * (4 * c * M ^ 3) :=
      mul_le_mul_of_nonneg_left (defect_forcing_le hM.le h) (by positivity)
    _ = _ := by field_simp

/-- The maximum-row defect contributes `c^(1/3) M`, with the same `c`. -/
theorem defect_cube_root_le {c M E₁ E₂ E₃ : ℝ}
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hE₁ : 0 ≤ E₁) (hE₃ : 0 ≤ E₃)
    (h : DefectSmall c M E₁ E₂ E₃) :
    E₁ ^ (1 / 3 : ℝ) ≤ c ^ (1 / 3 : ℝ) * M := by
  have hbound : E₁ ≤ c * M ^ 3 := by have := h.1; linarith
  calc
    _ ≤ (c * M ^ 3) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow hE₁ hbound (by norm_num)
    _ = c ^ (1 / 3 : ℝ) * M := by
      rw [Real.mul_rpow hc (by positivity), ← Real.rpow_natCast M 3,
        ← Real.rpow_mul hM]
      norm_num

end GlobalPhi43.Local
