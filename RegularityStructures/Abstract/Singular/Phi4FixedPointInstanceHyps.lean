/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Phi4FixedPointInstanceStructure
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# The numerical hypotheses of the `Φ⁴₃` fixed point, on the instance

The parameters are `γ₀ = 5/4`, `α = 0`, `η₀ = η' = η'' = 0`, `ζ = -1/2`, `N = N' = 4`.  This file
discharges the scalar and non-integrality hypotheses of
`Model.exists_unique_phi4_fixedPoint_causal_win_near` (`hnat`, `hni`, `hNγ`, `hdeg`, `hAζ`, ...).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi4Inst

/-- `γ₀ = 5/4`. -/
abbrev gam₀ : ℝ := 5 / 4

/-- `α = 0`, the regularity of `V`. -/
abbrev alpha : ℝ := 0

/-- `ζ = -1/2`, the regularity of the block. -/
abbrev zeta : ℝ := -1 / 2

end RegularityStructures.Phi4Inst

end

public section

namespace RegularityStructures.Phi4Inst

theorem deg_inr_zero : («structure» 4).deg (Sum.inr 0) = -1 / 2 := structure_deg_tau

theorem deg_inr_one : («structure» 4).deg (Sum.inr 1) = 3 / 2 := structure_deg_sigma

theorem hyp_hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < gam₀ + alpha + alpha + 2 →
    ∀ i, i ∉ Set.range (polySector 4).emb → zeta ≤ («structure» 4).deg i →
      («structure» 4).deg i < gam₀ + alpha + alpha →
        (multiDeg k : ℝ) ≠ («structure» 4).deg i + 2 := by
  intro k _ i hi _ hlt
  cases i with
  | inl j => exact absurd ⟨j, rfl⟩ hi
  | inr e =>
    by_cases he : e = 0
    · subst he
      intro h
      rw [deg_inr_zero] at h
      have h2 : (2 : ℝ) * (multiDeg k : ℝ) = 3 := by linarith
      have h3 : ((2 * multiDeg k : ℕ) : ℝ) = 3 := by push_cast; exact h2
      have := (by exact_mod_cast h3 : 2 * multiDeg k = 3)
      omega
    · exfalso
      have h1 : e = 1 := by fin_cases e <;> simp_all
      subst h1
      rw [deg_inr_one] at hlt
      norm_num at hlt

end RegularityStructures.Phi4Inst

end
