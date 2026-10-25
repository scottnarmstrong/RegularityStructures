/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.BphzCauchyPiSingle
public import Phi43.BPHZ.BphzCauchyPiSub
import Mathlib.Tactic

/-!
# The `Π`-moment hypotheses of the Kolmogorov bound, uniform over the symbols

Case analysis over the twenty symbols: `exists_piSingleBound_of_lt`, `exists_piSubBound_of_lt` for
a symbol `i ∉ Dπ` below `γ = 1 + 3κ`, and the constants uniform over the finitely many symbols
(`exists_piSingleBound_all`, `exists_piSubBound_all`).
-/

public section

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar θ : ℝ} {q : ℕ}

private theorem one_mem_piDeterministic : Symbol.one ∈ piDeterministic :=
  ⟨⟨0, by simp [weight_parabolicWeight]⟩, by simp [phi43PolyEmb]⟩

private theorem x_mem_piDeterministic (k : Fin 3) : Symbol.x k ∈ piDeterministic := by
  fin_cases k
  · exact ⟨⟨Finsupp.single (1 : Fin 4) 1, by simp [weight_parabolicWeight]⟩,
      phi43PolyEmb_eq_x0 rfl⟩
  · exact ⟨⟨Finsupp.single (2 : Fin 4) 1, by simp [weight_parabolicWeight]⟩,
      phi43PolyEmb_eq_x1 rfl⟩
  · exact ⟨⟨Finsupp.single (3 : Fin 4) 1, by simp [weight_parabolicWeight]⟩,
      phi43PolyEmb_eq_x2 rfl⟩

private theorem false_of_deg_ge {i : Symbol} (hlt : (phi43RegularityStructure κ).deg i < gamma κ)
    (h : gamma κ ≤ homogeneity κ i) : False := by
  have : homogeneity κ i < gamma κ := hlt
  linarith

private theorem gamma_le_iPsi : gamma κ ≤ homogeneity κ Symbol.iPsi := by
  have := κ.2.2
  simp only [homogeneity, gamma]
  linarith

private theorem gamma_le_x0 : gamma κ ≤ homogeneity κ Symbol.x0 := by
  have := κ.2.2
  simp only [homogeneity, gamma]
  linarith

private theorem gamma_le_xMul (p : Sym2 (Fin 3)) : gamma κ ≤ homogeneity κ (Symbol.xMul p) := by
  have := κ.2.2
  simp only [homogeneity, gamma]
  linarith

/-- Every symbol off `Dπ` and below `γ` has a uniform single `Π`-bound. -/
theorem exists_piSingleBound_of_lt (hmiss : BphzCauchyMoments.{u} N κ) (hρ : IsMollifier ρ)
    (hκ0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2) (hq : 1 ≤ q) {i : Symbol}
    (hi : i ∉ piDeterministic) (hlt : (phi43RegularityStructure κ).deg i < gamma κ) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q i C := by
  cases i with
  | one => exact absurd one_mem_piDeterministic hi
  | x k => exact absurd (x_mem_piDeterministic k) hi
  | x0 => exact (false_of_deg_ge hlt gamma_le_x0).elim
  | xMul p => exact (false_of_deg_ge hlt (gamma_le_xMul p)).elim
  | iPsi => exact (false_of_deg_ge hlt gamma_le_iPsi).elim
  | noise => exact exists_piSingleBound_noise hρ hκb hq
  | psi => exact exists_piSingleBound_psi hρ hκb hq
  | psiSq => exact exists_piSingleBound_psiSq hρ hκb hq
  | psiCube => exact exists_piSingleBound_psiCube hρ hκb hq
  | psiX k => exact exists_piSingleBound_psiX hρ hκb hq k
  | psiSqX k => exact exists_piSingleBound_psiSqX hρ hκb hq k
  | iPsiSq => exact exists_piSingleBound_iPsiSq hρ hκb hq hκ0
  | iPsiCube => exact exists_piSingleBound_iPsiCube hρ hκb hq hκ0
  | iPsiCubeSq => exact exists_piSingleBound_iPsiCubeSq hρ hκb hq hκ0
  | iPsiCubePsi => exact exists_piSingleBound_iPsiCubePsi hρ hκb hq
  | iPsiSqPsiSq => exact exists_piSingleBound_iPsiSqPsiSq hρ hκb hq
  | iPsiCubePsiSq => exact exists_piSingleBound_iPsiCubePsiSq hρ hκb hq
  | iPsiPsi => exact exists_piSingleBound_of_canonical (hmiss.iPsiPsi hρ hκ0 hκb hq)
  | iPsiPsiSq => exact exists_piSingleBound_of_canonical (hmiss.iPsiPsiSq hρ hκ0 hκb hq)
  | iPsiSqPsi => exact exists_piSingleBound_of_canonical (hmiss.iPsiSqPsi hρ hκ0 hκb hq)

/-- Every symbol off `Dπ` and below `γ` has a uniform difference `Π`-bound. -/
theorem exists_piSubBound_of_lt (hmiss : BphzCauchyMoments.{u} N κ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') (hκ0 : 0 ≤ κbar) (hθ : 0 < θ) (hκθ : κbar + θ ≤ κ.1 / 2)
    (hq : 1 ≤ q) {i : Symbol} (hi : i ∉ piDeterministic)
    (hlt : (phi43RegularityStructure κ).deg i < gamma κ) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSubBound.{u} N ρ ρ' κ κbar θ q i C := by
  cases i with
  | one => exact absurd one_mem_piDeterministic hi
  | x k => exact absurd (x_mem_piDeterministic k) hi
  | x0 => exact (false_of_deg_ge hlt gamma_le_x0).elim
  | xMul p => exact (false_of_deg_ge hlt (gamma_le_xMul p)).elim
  | iPsi => exact (false_of_deg_ge hlt gamma_le_iPsi).elim
  | noise => exact exists_piSubBound_noise hρ hρ' hκ0 hθ hκθ hq
  | psi => exact exists_piSubBound_psi hρ hρ' hκ0 hθ hκθ hq
  | psiSq => exact exists_piSubBound_psiSq hρ hρ' hκ0 hθ hκθ hq
  | psiCube => exact exists_piSubBound_psiCube hρ hρ' hκ0 hθ hκθ hq
  | psiX k => exact exists_piSubBound_psiX hρ hρ' hκ0 hθ hκθ hq k
  | psiSqX k => exact exists_piSubBound_psiSqX hρ hρ' hκ0 hθ hκθ hq k
  | iPsiSq => exact exists_piSubBound_iPsiSq hρ hρ' hκ0 hθ hκθ hq
  | iPsiCube => exact exists_piSubBound_iPsiCube hρ hρ' hκ0 hθ hκθ hq
  | iPsiCubeSq => exact exists_piSubBound_iPsiCubeSq hρ hρ' hκ0 hθ hκθ hq
  | iPsiCubePsi =>
    exact exists_piSubBound_of_model (hmiss.iPsiCubePsi_sub hρ hρ' hκ0 hθ hκθ hq)
  | iPsiSqPsiSq =>
    exact exists_piSubBound_of_model (hmiss.iPsiSqPsiSq_sub hρ hρ' hκ0 hθ hκθ hq)
  | iPsiCubePsiSq =>
    exact exists_piSubBound_of_model (hmiss.iPsiCubePsiSq_sub hρ hρ' hκ0 hθ hκθ hq)
  | iPsiPsi => exact exists_piSubBound_of_canonical (hmiss.iPsiPsi_sub hρ hρ' hκ0 hθ hκθ hq)
  | iPsiPsiSq => exact exists_piSubBound_of_canonical (hmiss.iPsiPsiSq_sub hρ hρ' hκ0 hθ hκθ hq)
  | iPsiSqPsi => exact exists_piSubBound_of_canonical (hmiss.iPsiSqPsi_sub hρ hρ' hκ0 hθ hκθ hq)

/-- One constant for all symbols: single bounds. -/
theorem exists_piSingleBound_all (hmiss : BphzCauchyMoments.{u} N κ) (hρ : IsMollifier ρ)
    (hκ0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2) (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ i, i ∉ piDeterministic → (phi43RegularityStructure κ).deg i < gamma κ →
      PiSingleBound.{u} N ρ κ κbar q i C₀ := by
  classical
  have h : ∀ i : Symbol, ∃ C : ℝ, 0 ≤ C ∧ (i ∉ piDeterministic →
      (phi43RegularityStructure κ).deg i < gamma κ → PiSingleBound.{u} N ρ κ κbar q i C) := by
    intro i
    by_cases H : i ∉ piDeterministic ∧ (phi43RegularityStructure κ).deg i < gamma κ
    · obtain ⟨C, hC, hb⟩ := exists_piSingleBound_of_lt hmiss hρ hκ0 hκb hq H.1 H.2
      exact ⟨C, hC, fun _ _ => hb⟩
    · exact ⟨0, le_rfl, fun a b => absurd ⟨a, b⟩ H⟩
  choose C hC hb using h
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC i, fun i hi hlt => PiSingleBound.mono (hb i hi hlt)
    (Finset.single_le_sum (f := C) (fun j _ => hC j) (Finset.mem_univ i))⟩

/-- One constant for all symbols: difference bounds. -/
theorem exists_piSubBound_all (hmiss : BphzCauchyMoments.{u} N κ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') (hκ0 : 0 ≤ κbar) (hθ : 0 < θ) (hκθ : κbar + θ ≤ κ.1 / 2)
    (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ i, i ∉ piDeterministic → (phi43RegularityStructure κ).deg i < gamma κ →
      PiSubBound.{u} N ρ ρ' κ κbar θ q i C₀ := by
  classical
  have h : ∀ i : Symbol, ∃ C : ℝ, 0 ≤ C ∧ (i ∉ piDeterministic →
      (phi43RegularityStructure κ).deg i < gamma κ →
        PiSubBound.{u} N ρ ρ' κ κbar θ q i C) := by
    intro i
    by_cases H : i ∉ piDeterministic ∧ (phi43RegularityStructure κ).deg i < gamma κ
    · obtain ⟨C, hC, hb⟩ := exists_piSubBound_of_lt hmiss hρ hρ' hκ0 hθ hκθ hq H.1 H.2
      exact ⟨C, hC, fun _ _ => hb⟩
    · exact ⟨0, le_rfl, fun a b => absurd ⟨a, b⟩ H⟩
  choose C hC hb using h
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC i, fun i hi hlt => PiSubBound.mono (hb i hi hlt)
    (Finset.single_le_sum (f := C) (fun j _ => hC j) (Finset.mem_univ i))⟩

end RegularityStructures.Phi43

end
