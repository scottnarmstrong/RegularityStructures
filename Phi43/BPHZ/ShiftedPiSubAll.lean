/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSubCubePsiSq
import Mathlib.Tactic

/-!
# The `pi_sub` field of `ShiftedBphzInputs`

Case analysis over the twenty symbols and the constant uniform over them.  The row of `I(Ψ³)²`
is a hypothesis `hsqs`, proved separately.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar θ : ℝ} {q : ℕ}
  {B C C' C1 C2 Ci Cg S1 S2 Si Sg : ℝ} {i : Symbol}

theorem PiShiftSubBound.mono (h : PiShiftSubBound.{u} N ρ ρ' κ κbar θ q i B C) (hC : C ≤ C') :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q i B C' := by
  intro Ω _ P W ε ε' ξ ξ' c c' hc hc' hW hε hε' hξ hξ' hgr hgr' t ht x
  refine le_ofReal_pow_mono (h c c' hc hc' hW hε hε' hξ hξ' hgr hgr' t ht x) ?_
  have h0 : 0 ≤ (max ε ε') ^ θ + ‖c - c'‖ :=
    add_nonneg (Real.rpow_nonneg (le_max_of_le_left hε.1.le) _) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC h0)
    (Real.rpow_nonneg ht.1.le _)

private theorem shifted_sub_one_mem : Symbol.one ∈ piDeterministic :=
  ⟨⟨0, by simp [weight_parabolicWeight]⟩, by simp [phi43PolyEmb]⟩

private theorem shifted_sub_x_mem (k : Fin 3) : Symbol.x k ∈ piDeterministic := by
  fin_cases k
  · exact ⟨⟨Finsupp.single (1 : Fin 4) 1, by simp [weight_parabolicWeight]⟩,
      phi43PolyEmb_eq_x0 rfl⟩
  · exact ⟨⟨Finsupp.single (2 : Fin 4) 1, by simp [weight_parabolicWeight]⟩,
      phi43PolyEmb_eq_x1 rfl⟩
  · exact ⟨⟨Finsupp.single (3 : Fin 4) 1, by simp [weight_parabolicWeight]⟩,
      phi43PolyEmb_eq_x2 rfl⟩

private theorem shifted_sub_false_of_deg_ge
    (hlt : (phi43RegularityStructure κ).deg i < gamma κ) (h : gamma κ ≤ homogeneity κ i) :
    False := by
  have : homogeneity κ i < gamma κ := hlt
  linarith

/-- Every symbol off `Dπ` and below `γ` has a shifted difference bound. -/
theorem exists_piShiftSubBound_of_lt
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg)
    (hq : 1 ≤ q) (hκb : κbar ≤ κ.1 / 2) (hB : 0 ≤ B)
    (hsq : ∃ C : ℝ, 0 ≤ C ∧ PiShiftSubBound.{u} N ρ ρ' κ κbar θ q Symbol.iPsiCubeSq B C)
    (hi : i ∉ piDeterministic) (hlt : (phi43RegularityStructure κ).deg i < gamma κ) :
    ∃ C : ℝ, 0 ≤ C ∧ PiShiftSubBound.{u} N ρ ρ' κ κbar θ q i B C := by
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  obtain ⟨hS1, hS2, hSi, hSg⟩ := SA.nonneg
  obtain ⟨hC1, hC2, hCi, hCg⟩ := SA.left.nonneg
  have hM0 := parabolicSemigroup.momentConst_nonneg 0
  have hM1 := parabolicSemigroup.momentConst_nonneg 1
  cases i with
  | one => exact absurd shifted_sub_one_mem hi
  | x k => exact absurd (shifted_sub_x_mem k) hi
  | x0 => exact (shifted_sub_false_of_deg_ge hlt (by simp only [homogeneity, gamma]; linarith)).elim
  | xMul p =>
    exact (shifted_sub_false_of_deg_ge hlt (by simp only [homogeneity, gamma]; linarith)).elim
  | iPsi => exact (shifted_sub_false_of_deg_ge hlt (by simp only [homogeneity, gamma]; linarith)).elim
  | noise => exact ⟨S1, hS1, shiftedPi_sub_noise SA B⟩
  | psi => exact ⟨S1, hS1, shiftedPi_sub_psi SA B⟩
  | psiSq => exact ⟨_, by positivity, shiftedPi_sub_psiSq SA hq hκb⟩
  | psiCube => exact ⟨_, by positivity, shiftedPi_sub_psiCube SA hq hB⟩
  | psiX k => exact ⟨S1, hS1, shiftedPi_sub_psiX SA k B⟩
  | psiSqX k => exact ⟨_, by positivity, shiftedPi_sub_psiSqX SA hq hκb k⟩
  | iPsiSq => exact ⟨S1, hS1, shiftedPi_sub_iPsiSq SA B⟩
  | iPsiCube => exact ⟨_, by positivity, shiftedPi_sub_iPsiCube SA hq hκb hB⟩
  | iPsiCubeSq => exact hsq
  | iPsiCubePsi => exact ⟨_, by positivity, shiftedPi_sub_iPsiCubePsi SA hq hB⟩
  | iPsiSqPsiSq => exact ⟨_, by positivity, shiftedPi_sub_iPsiSqPsiSq SA hq hκb hB⟩
  | iPsiCubePsiSq => exact ⟨_, by positivity, shiftedPi_sub_iPsiCubePsiSq SA hq hκb hB⟩
  | iPsiPsi => exact ⟨S1, hS1, shiftedPi_sub_iPsiPsi SA B⟩
  | iPsiPsiSq => exact ⟨_, by positivity, shiftedPi_sub_iPsiPsiSq SA hq hB⟩
  | iPsiSqPsi => exact ⟨S1, hS1, shiftedPi_sub_iPsiSqPsi SA B⟩

/-- One constant for all symbols. -/
theorem exists_piShiftSubBound_all
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg)
    (hq : 1 ≤ q) (hκb : κbar ≤ κ.1 / 2) (hB : 0 ≤ B)
    (hsq : ∃ C : ℝ, 0 ≤ C ∧ PiShiftSubBound.{u} N ρ ρ' κ κbar θ q Symbol.iPsiCubeSq B C) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ i, i ∉ piDeterministic →
      (phi43RegularityStructure κ).deg i < gamma κ →
        PiShiftSubBound.{u} N ρ ρ' κ κbar θ q i B C₀ := by
  classical
  have h : ∀ i : Symbol, ∃ C : ℝ, 0 ≤ C ∧ (i ∉ piDeterministic →
      (phi43RegularityStructure κ).deg i < gamma κ →
        PiShiftSubBound.{u} N ρ ρ' κ κbar θ q i B C) := by
    intro i
    by_cases H : i ∉ piDeterministic ∧ (phi43RegularityStructure κ).deg i < gamma κ
    · obtain ⟨C, hC, hb⟩ := exists_piShiftSubBound_of_lt SA hq hκb hB hsq H.1 H.2
      exact ⟨C, hC, fun _ _ => hb⟩
    · exact ⟨0, le_rfl, fun a b => absurd ⟨a, b⟩ H⟩
  choose C hC hb using h
  exact ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC i, fun i hi hlt =>
    PiShiftSubBound.mono (hb i hi hlt)
      (Finset.single_le_sum (f := C) (fun j _ => hC j) (Finset.mem_univ i))⟩

/-- **The `pi_sub` field of `ShiftedBphzInputs`**, conditionally on the missing unshifted moments
and on the difference bound for the row of `I(Ψ³)²`. -/
theorem shiftedBphzInputs_pi_sub_of (hmiss : BphzCauchyMoments.{u} N κ)
    (hsqs : ∀ {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}, IsMollifier ρ → IsMollifier ρ' → ∀ {κbar θ : ℝ},
      0 ≤ κbar → 0 < θ → κbar + θ ≤ κ.1 / 2 → ∀ {q : ℕ}, 1 ≤ q → ∀ {B : ℝ}, 0 ≤ B →
      ∃ C : ℝ, 0 ≤ C ∧ PiShiftSubBound.{u} N ρ ρ' κ κbar θ q Symbol.iPsiCubeSq B C) :
    ∀ {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}, IsMollifier ρ → IsMollifier ρ' → ∀ {κbar θ : ℝ},
      0 ≤ κbar → 0 < θ → κbar + θ ≤ κ.1 / 2 → ∀ {q : ℕ}, 1 ≤ q → ∀ {B : ℝ}, 0 ≤ B →
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ i, i ∉ piDeterministic →
        (phi43RegularityStructure κ).deg i < gamma κ →
          PiShiftSubBound.{u} N ρ ρ' κ κbar θ q i B C₀ := by
  intro ρ ρ' hρ hρ' κbar θ hκ0 hθ hκθ q hq B hB
  obtain ⟨C1, C2, Ci, Cg, S1, S2, Si, Sg, SA⟩ :=
    shiftedPiSubAtoms_exists hmiss hρ hρ' hκ0 hθ hκθ hq
  have hk0 := κ.2.1
  exact exists_piShiftSubBound_all SA hq (by linarith) hB (hsqs hρ hρ' hκ0 hθ hκθ hq hB)

end RegularityStructures.Phi43

end
