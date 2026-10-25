/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Inhomogeneity.DuhamelBounds
public import RegularityStructures.Abstract.Datum.Bound

/-!
# `DerivBound` of the Duhamel field

If `g` is smooth, spatially periodic, and `|ddA l g| ≤ Gc L · B` on `[0, 1] × ℝ³` for all words `l`
of length `≤ L` (for every `L`), then the Duhamel field `θ` of `g` satisfies the derivative bounds
`DerivBound η B Kc θ` of `Datum` with `Kc k = duhCst (k 0) · Gc (2 k₀ + k₁ + k₂ + k₃)`, for every
`η ≤ 0`.  Since `t ≤ 1`, the singular weights `t^{(η - |k|_𝔰)/2} ≥ 1`, so the bound is a plain sup
bound.
-/

open scoped ContDiff

public section

namespace RegularityStructures.Inhomogeneity

open RegularityStructures.PDE Set

variable {g : ParabolicSpace → ℝ}

theorem D_eq_pdIter_pdWord (F : ParabolicSpace → ℝ) (k : Fin 4 → ℕ) :
    Datum.D k F = Datum.pdIter 0 (k 0) (Datum.pdWord
      (List.replicate (k 1) 0 ++ List.replicate (k 2) 1 ++ List.replicate (k 3) 2) F) := by
  rw [Datum.pdWord_append, Datum.pdWord_append, Datum.pdWord_replicate, Datum.pdWord_replicate,
    Datum.pdWord_replicate]
  rfl

theorem derivBound_duhamelField (hg : PerSmooth g) {η B : ℝ} (hη : η ≤ 0) (hB : 0 ≤ B)
    (Gc : ℕ → ℝ) (hGc : ∀ L, 0 ≤ Gc L) (hG : ∀ L, DerivHyp g (Gc L * B) L) :
    Datum.DerivBound η B (fun k => duhCst (k 0) * Gc (2 * k 0 + k 1 + k 2 + k 3))
      (duhamelField hg) := by
  refine ⟨smoothPos_duhamelField hg, fun k z hz hz1 => ?_⟩
  obtain ⟨t, y⟩ := z
  rw [D_eq_pdIter_pdWord]
  have h := abs_pdIter_pdWord_duhamelField_le hg (k 0) (hG (2 * k 0 + k 1 + k 2 + k 3))
    (List.replicate (k 1) 0 ++ List.replicate (k 2) 1 ++ List.replicate (k 3) 2)
    (by simp; omega) hz hz1 y
  refine h.trans ?_
  have hK : 0 ≤ duhCst (k 0) * Gc (2 * k 0 + k 1 + k 2 + k 3) * B :=
    mul_nonneg (mul_nonneg (duhCst_nonneg _) (hGc _)) hB
  have hw : 1 ≤ t ^ ((η - (Datum.wt k : ℝ)) / 2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hz hz1
      (by have : (0 : ℝ) ≤ Datum.wt k := Nat.cast_nonneg _
          linarith)
  calc duhCst (k 0) * (Gc (2 * k 0 + k 1 + k 2 + k 3) * B)
      = duhCst (k 0) * Gc (2 * k 0 + k 1 + k 2 + k 3) * B := by ring
    _ ≤ duhCst (k 0) * Gc (2 * k 0 + k 1 + k 2 + k 3) * B * t ^ ((η - (Datum.wt k : ℝ)) / 2) :=
        le_mul_of_one_le_right hK hw

end RegularityStructures.Inhomogeneity

end
