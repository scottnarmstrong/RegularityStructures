/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSingleTrees
import Mathlib.Tactic

/-!
# The `pi` field of `ShiftedBphzInputs`

Case analysis over the twenty symbols and the constant uniform over them.  The row of `I(Ψ³)²`
(the square of the shifted potential) is a hypothesis `hsq`, proved separately.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar : ℝ} {q : ℕ} {B C C' C1 C2 Ci Cg : ℝ}
  {i : Symbol}

theorem PiShiftSingleBound.mono (h : PiShiftSingleBound.{u} N ρ κ κbar q i B C) (hC : C ≤ C') :
    PiShiftSingleBound.{u} N ρ κ κbar q i B C' := by
  intro Ω _ P W ε ξ c hc hW hε hξ hgr t ht x
  refine le_ofReal_pow_mono (h c hc hW hε hξ hgr t ht x) ?_
  exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg ht.1.le _)

private theorem shifted_one_mem : Symbol.one ∈ piDeterministic :=
  ⟨⟨0, by simp [weight_parabolicWeight]⟩, by simp [phi43PolyEmb]⟩

private theorem shifted_x_mem (k : Fin 3) : Symbol.x k ∈ piDeterministic := by
  fin_cases k
  · exact ⟨⟨Finsupp.single (1 : Fin 4) 1, by simp [weight_parabolicWeight]⟩,
      phi43PolyEmb_eq_x0 rfl⟩
  · exact ⟨⟨Finsupp.single (2 : Fin 4) 1, by simp [weight_parabolicWeight]⟩,
      phi43PolyEmb_eq_x1 rfl⟩
  · exact ⟨⟨Finsupp.single (3 : Fin 4) 1, by simp [weight_parabolicWeight]⟩,
      phi43PolyEmb_eq_x2 rfl⟩

private theorem shifted_false_of_deg_ge (hlt : (phi43RegularityStructure κ).deg i < gamma κ)
    (h : gamma κ ≤ homogeneity κ i) : False := by
  have : homogeneity κ i < gamma κ := hlt
  linarith

/-- Every symbol off `Dπ` and below `γ` has a shifted single bound. -/
theorem exists_piShiftSingleBound_of_lt (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg)
    (hq : 1 ≤ q) (hκb : κbar ≤ κ.1 / 2) (hB : 0 ≤ B)
    (hsq : ∃ C : ℝ, 0 ≤ C ∧ PiShiftSingleBound.{u} N ρ κ κbar q Symbol.iPsiCubeSq B C)
    (hi : i ∉ piDeterministic) (hlt : (phi43RegularityStructure κ).deg i < gamma κ) :
    ∃ C : ℝ, 0 ≤ C ∧ PiShiftSingleBound.{u} N ρ κ κbar q i B C := by
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  obtain ⟨hC1, hC2, hCi, hCg⟩ := A.nonneg
  have hM0 := parabolicSemigroup.momentConst_nonneg 0
  have hM1 := parabolicSemigroup.momentConst_nonneg 1
  cases i with
  | one => exact absurd shifted_one_mem hi
  | x k => exact absurd (shifted_x_mem k) hi
  | x0 => exact (shifted_false_of_deg_ge hlt (by simp only [homogeneity, gamma]; linarith)).elim
  | xMul p => exact (shifted_false_of_deg_ge hlt (by simp only [homogeneity, gamma]; linarith)).elim
  | iPsi => exact (shifted_false_of_deg_ge hlt (by simp only [homogeneity, gamma]; linarith)).elim
  | noise => exact ⟨C1, hC1, shiftedPi_single_noise A B⟩
  | psi => exact ⟨C1, hC1, shiftedPi_single_psi A B⟩
  | psiSq => exact ⟨_, by positivity, shiftedPi_single_psiSq A hq hκb hB⟩
  | psiCube => exact ⟨_, by positivity, shiftedPi_single_psiCube A hq hB⟩
  | psiX k => exact ⟨C1, hC1, shiftedPi_single_psiX A k B⟩
  | psiSqX k => exact ⟨_, by positivity, shiftedPi_single_psiSqX A hq hκb hB k⟩
  | iPsiSq => exact ⟨C1, hC1, shiftedPi_single_iPsiSq A B⟩
  | iPsiCube => exact ⟨_, by positivity, shiftedPi_single_iPsiCube A hq hκb hB⟩
  | iPsiCubeSq => exact hsq
  | iPsiCubePsi => exact ⟨_, by positivity, shiftedPi_single_iPsiCubePsi A hq hB⟩
  | iPsiSqPsiSq => exact ⟨_, by positivity, shiftedPi_single_iPsiSqPsiSq A hq hκb hB⟩
  | iPsiCubePsiSq => exact ⟨_, by positivity, shiftedPi_single_iPsiCubePsiSq A hq hκb hB⟩
  | iPsiPsi => exact ⟨C1, hC1, shiftedPi_single_iPsiPsi A B⟩
  | iPsiPsiSq => exact ⟨_, by positivity, shiftedPi_single_iPsiPsiSq A hq hB⟩
  | iPsiSqPsi => exact ⟨C1, hC1, shiftedPi_single_iPsiSqPsi A B⟩

/-- One constant for all symbols. -/
theorem exists_piShiftSingleBound_all (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg)
    (hq : 1 ≤ q) (hκb : κbar ≤ κ.1 / 2) (hB : 0 ≤ B)
    (hsq : ∃ C : ℝ, 0 ≤ C ∧ PiShiftSingleBound.{u} N ρ κ κbar q Symbol.iPsiCubeSq B C) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ i, i ∉ piDeterministic →
      (phi43RegularityStructure κ).deg i < gamma κ → PiShiftSingleBound.{u} N ρ κ κbar q i B C₀ := by
  classical
  have h : ∀ i : Symbol, ∃ C : ℝ, 0 ≤ C ∧ (i ∉ piDeterministic →
      (phi43RegularityStructure κ).deg i < gamma κ → PiShiftSingleBound.{u} N ρ κ κbar q i B C) := by
    intro i
    by_cases H : i ∉ piDeterministic ∧ (phi43RegularityStructure κ).deg i < gamma κ
    · obtain ⟨C, hC, hb⟩ := exists_piShiftSingleBound_of_lt A hq hκb hB hsq H.1 H.2
      exact ⟨C, hC, fun _ _ => hb⟩
    · exact ⟨0, le_rfl, fun a b => absurd ⟨a, b⟩ H⟩
  choose C hC hb using h
  exact ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC i, fun i hi hlt =>
    PiShiftSingleBound.mono (hb i hi hlt)
      (Finset.single_le_sum (f := C) (fun j _ => hC j) (Finset.mem_univ i))⟩

/-- **The `pi` field of `ShiftedBphzInputs`**, conditionally on the missing unshifted moments and
on the bound for the row of `I(Ψ³)²`. -/
theorem shiftedBphzInputs_pi_of (hmiss : BphzCauchyMoments.{u} N κ)
    (hsq : ∀ {ρ : ℝ × (Fin 3 → ℝ) → ℝ}, IsMollifier ρ → ∀ {κbar : ℝ}, 0 ≤ κbar →
      κbar ≤ κ.1 / 2 → ∀ {q : ℕ}, 1 ≤ q → ∀ {B : ℝ}, 0 ≤ B →
      ∃ C : ℝ, 0 ≤ C ∧ PiShiftSingleBound.{u} N ρ κ κbar q Symbol.iPsiCubeSq B C) :
    ∀ {ρ : ℝ × (Fin 3 → ℝ) → ℝ}, IsMollifier ρ → ∀ {κbar : ℝ}, 0 ≤ κbar → κbar ≤ κ.1 / 2 →
      ∀ {q : ℕ}, 1 ≤ q → ∀ {B : ℝ}, 0 ≤ B →
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ i, i ∉ piDeterministic →
        (phi43RegularityStructure κ).deg i < gamma κ → PiShiftSingleBound.{u} N ρ κ κbar q i B C₀ := by
  intro ρ hρ κbar hκ0 hκb q hq B hB
  obtain ⟨C1, C2, Ci, Cg, A⟩ := shiftedPiAtoms_exists hmiss hρ hκ0 hκb hq
  exact exists_piShiftSingleBound_all A hq hκb hB (hsq hρ hκ0 hκb hq hB)

end RegularityStructures.Phi43

end
