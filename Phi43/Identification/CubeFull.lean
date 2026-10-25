/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Identification.CubeExpansion
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

/-!
# The truncated cube of the full ansatz, and Hairer's display

`lowerProj_cube_ansatz`: for `u = phi43AnsatzF a φ c₃ c₂ ψ + r` with `r` supported in degrees
`≥ γ = 1 + 3κ`, `Q_{<κ}(u ⋆ (u ⋆ u)) = phi43CubeLowF a φ c₃ c₂ ψ`.  The specialisation
`a = 1`, `c₃ = -1`, `c₂ = -3φ` is `neg_lowerProj_cube_eq_oldEmb`, the display of
[Hai14, p. 147] minus `Ξ`, as old symbols via `phi43OldEmbF`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- Hairer's display `F(u) - Ξ` as a vector of the old coordinate space:
`-Ψ³ - 3φΨ² + 3Ψ²I(Ψ³) - 3φ²Ψ + 6φΨI(Ψ³) + 9φΨ²I(Ψ²) - 3φᵢΨ²Xᵢ - φ³·1`. -/
def phi43FDisplayOld (φ : ℝ) (ψ : Fin 3 → ℝ) : Symbol → ℝ :=
  -(Pi.single .psiCube 1 : Symbol → ℝ) - (3 * φ) • (Pi.single .psiSq 1 : Symbol → ℝ) +
    (3 : ℝ) • (Pi.single .iPsiCubePsiSq 1 : Symbol → ℝ) -
    (3 * φ ^ 2) • (Pi.single .psi 1 : Symbol → ℝ) +
    (6 * φ) • (Pi.single .iPsiCubePsi 1 : Symbol → ℝ) +
    (9 * φ) • (Pi.single .iPsiSqPsiSq 1 : Symbol → ℝ) -
    (∑ i, (3 * ψ i) • (Pi.single (.psiSqX i) 1 : Symbol → ℝ)) -
    (φ ^ 3) • (Pi.single .one 1 : Symbol → ℝ)

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

private theorem suppGe_sum (κ : Kappa) {α : ℝ} {ι : Type*} (s : Finset ι) (f : ι → SymbolF → ℝ)
    (h : ∀ i ∈ s, Phi43SuppGe κ α (f i)) : Phi43SuppGe κ α (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using phi43SuppGe_zero κ α
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact phi43SuppGe_add κ (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

private theorem suppGe_EF (κ : Kappa) {α : ℝ} {τ : Symbol} (h : α ≤ homogeneity κ τ) :
    Phi43SuppGe κ α (phi43EF τ) :=
  phi43SuppGe_single κ (τ := .old τ) h

theorem phi43AnsatzF_suppGe (κ : Kappa) (a φ c₃ c₂ : ℝ) (ψ : Fin 3 → ℝ) :
    Phi43SuppGe κ (-1 / 2 - κ.1) (phi43AnsatzF a φ c₃ c₂ ψ) := by
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  unfold phi43AnsatzF
  refine phi43SuppGe_add κ (phi43SuppGe_add κ (phi43SuppGe_add κ (phi43SuppGe_add κ
    (phi43SuppGe_smul κ _ (suppGe_EF κ ?_)) (phi43SuppGe_smul κ _ (suppGe_EF κ ?_)))
    (phi43SuppGe_smul κ _ (suppGe_EF κ ?_))) (phi43SuppGe_smul κ _ (suppGe_EF κ ?_)))
    (suppGe_sum κ _ _ fun i _ => phi43SuppGe_smul κ _ (suppGe_EF κ ?_))
  all_goals simp only [homogeneity]
  all_goals linarith

theorem phi43SqXF_suppGe (κ : Kappa) (ψ : Fin 3 → ℝ) : Phi43SuppGe κ 2 (phi43SqXF ψ) := by
  unfold phi43SqXF
  exact suppGe_sum κ _ _ fun i _ => suppGe_sum κ _ _ fun j _ =>
    phi43SuppGe_smul κ _ (suppGe_EF κ (by simp [homogeneity]))

private theorem mixed (κ : Kappa) {x y z : SymbolF → ℝ} (hx : Phi43SuppGe κ (-1 / 2 - κ.1) x)
    (hy : Phi43SuppGe κ (-1 / 2 - κ.1) y) (hz : Phi43SuppGe κ (-1 / 2 - κ.1) z)
    (h : Phi43SuppGe κ (gamma κ) x ∨ Phi43SuppGe κ (gamma κ) y ∨ Phi43SuppGe κ (gamma κ) z) :
    RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg κ.1
      (phi43ProductLinearF x (phi43ProductLinearF y z)) = 0 := by
  have hg : -1 / 2 - κ.1 ≤ gamma κ := by
    unfold gamma; linarith [κ.2.1]
  have e : gamma κ + (-1 / 2 - κ.1 + (-1 / 2 - κ.1)) = κ.1 := by unfold gamma; ring
  refine lowerProj_eq_zero_of_suppGe κ ?_
  rcases h with h | h | h
  · have := phi43ProductLinearF_suppGe κ h (phi43ProductLinearF_suppGe κ hy hz)
    exact phi43SuppGe_mono κ (by unfold gamma at *; linarith) this
  · have := phi43ProductLinearF_suppGe κ hx (phi43ProductLinearF_suppGe κ h hz)
    exact phi43SuppGe_mono κ (by unfold gamma at *; linarith) this
  · have := phi43ProductLinearF_suppGe κ hx (phi43ProductLinearF_suppGe κ hy h)
    exact phi43SuppGe_mono κ (by unfold gamma at *; linarith) this

/-- **The truncated cube of the ansatz** ([Hai14, p. 147]). -/
theorem lowerProj_cube_ansatz (κ : Kappa) (a φ c₃ c₂ : ℝ) (ψ : Fin 3 → ℝ) (r : SymbolF → ℝ)
    (hr : Phi43SuppGe κ (gamma κ) r) :
    RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg κ.1
      ((phi43ProductF κ).mul (phi43AnsatzF a φ c₃ c₂ ψ + r)
        ((phi43ProductF κ).mul (phi43AnsatzF a φ c₃ c₂ ψ + r)
          (phi43AnsatzF a φ c₃ c₂ ψ + r))) = phi43CubeLowF a φ c₃ c₂ ψ := by
  have hg : -1 / 2 - κ.1 ≤ gamma κ := by
    unfold gamma; linarith [κ.2.1]
  have hU := phi43AnsatzF_suppGe κ a φ c₃ c₂ ψ
  have hr' := phi43SuppGe_mono κ hg hr
  have hX := phi43SqXF_suppGe κ ψ
  rw [phi43ProductF_mul]
  set U := phi43AnsatzF a φ c₃ c₂ ψ
  simp only [map_add, LinearMap.add_apply]
  have h1 := mixed κ hr' hU hU (Or.inl hr)
  have h2 := mixed κ hU hr' hU (Or.inr (Or.inl hr))
  have h3 := mixed κ hU hU hr' (Or.inr (Or.inr hr))
  have h4 := mixed κ hr' hr' hU (Or.inl hr)
  have h5 := mixed κ hr' hU hr' (Or.inl hr)
  have h6 := mixed κ hU hr' hr' (Or.inr (Or.inl hr))
  have h7 := mixed κ hr' hr' hr' (Or.inl hr)
  have h8 : RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg κ.1
      (phi43ProductLinearF U (phi43SqXF ψ)) = 0 := by
    refine lowerProj_eq_zero_of_suppGe κ (phi43SuppGe_mono κ ?_
      (phi43ProductLinearF_suppGe κ hU hX))
    linarith [κ.2.1, κ.2.2]
  have h0 := lowerProj_mul_ansatz_sqMain κ a φ c₃ c₂ ψ
  have hs := phi43SqF_eq a φ c₃ c₂ ψ
  simp only [h1, h2, h3, h4, h5, h6, h7, add_zero]
  rw [hs]
  simp only [map_add, h8, add_zero]
  exact h0

theorem neg_lowerProj_cube_eq_oldEmb (κ : Kappa) (φ : ℝ) (ψ : Fin 3 → ℝ) (r : SymbolF → ℝ)
    (hr : Phi43SuppGe κ (gamma κ) r) :
    -RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg κ.1
      ((phi43ProductF κ).mul (phi43AnsatzF 1 φ (-1) (-3 * φ) ψ + r)
        ((phi43ProductF κ).mul (phi43AnsatzF 1 φ (-1) (-3 * φ) ψ + r)
          (phi43AnsatzF 1 φ (-1) (-3 * φ) ψ + r))) =
      phi43OldEmbF (phi43FDisplayOld φ ψ) := by
  rw [lowerProj_cube_ansatz κ _ _ _ _ _ r hr]
  simp only [phi43CubeLowF, phi43FDisplayOld, phi43EF_eq, map_add, map_sub, map_neg, map_smul,
    map_sum]
  simp only [one_pow, mul_one]
  module

end RegularityStructures.Phi43

end
