/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSubShifted
import Mathlib.Tactic

/-!
# Shifted difference bounds: the rows `I(Ψ)Ψ²` and `I(Ψ²)Ψ²`
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar θ : ℝ} {q : ℕ}
  {C1 C2 Ci Cg S1 S2 Si Sg : ℝ}

theorem shiftedPi_sub_iPsiPsiSq
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (hq : 1 ≤ q)
    {B : ℝ} (hB : 0 ≤ B) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q .iPsiPsiSq B (S1 + Ci + B * Si) := by
  refine PiShiftSubBound.of_shiftMom ?_
  intro Ω _ P W ε ε' ξ ξ' c c' hc hc' hW hε hε' hξ hξ' hgr hgr' t ht x
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hS1 := SA.nonneg.1
  have hSi := SA.nonneg.2.2.1
  have hCi := SA.left.nonneg.2.2.1
  have hmx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  set D := (max ε ε') ^ θ + ‖c - c'‖ with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hDm : (max ε ε') ^ θ ≤ D := le_add_of_nonneg_right (norm_nonneg _)
  have key : ∀ ω, shiftedPiReg N κ (shiftConst N ρ ε c) (ξ ω) x t .iPsiPsiSq -
      shiftedPiReg N κ (shiftConst N ρ' ε' c') (ξ' ω) x t .iPsiPsiSq =
      (shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t .iPsiPsiSq -
        shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t .iPsiPsiSq) -
        (c.1 * shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t .iPsi -
          c'.1 * shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t .iPsi) :=
    fun ω => by
    rw [shiftedPi_reg_iPsiPsiSq (C := shiftedPiHairerConst N ρ ε) (C' := shiftConst N ρ ε c) x
        (hξ.1 ω) (hgr ω) ht.1 rfl,
      shiftedPi_reg_iPsiPsiSq (C := shiftedPiHairerConst N ρ' ε') (C' := shiftConst N ρ' ε' c') x
        (hξ'.1 ω) (hgr' ω) ht.1 rfl]
    ring
  refine ShiftMom.congr key ?_
  have e : (homogeneity κ .iPsiPsiSq + κbar) / 4 ≤ (homogeneity κ .iPsi + κbar) / 4 := by
    simp only [homogeneity]; linarith
  have a1 := SA.momSub (σ := .iPsiPsiSq) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hε' hξ hξ' hgr hgr' ht x D hDm
  have a2 := (SA.left.momIPsi hW hε hξ hgr ht x).tpow hCi ht e
  have a3 := (SA.momSubIPsi hW hε hε' hξ hξ' hgr hgr' ht x D hDm).tpow
    (mul_nonneg hSi hD0) ht e
  have a4 := ShiftMom.cdiff hq (measurable_shiftedPiReg hξ hgr _ x ht.1 _)
    (measurable_shiftedPiReg hξ' hgr' _ x ht.1 _) c.1 c'.1 a2 a3
    (B' := B) (d := D) (abs_fst_le_of_norm_le hc')
    ((abs_fst_sub_le_norm c c').trans (le_add_of_nonneg_left (by positivity)))
    (by positivity) (by positivity) (by positivity) hB
  have := a1.sub hq ((measurable_shiftedPiReg hξ hgr _ x ht.1 _).sub
    (measurable_shiftedPiReg hξ' hgr' _ x ht.1 _))
    (((measurable_shiftedPiReg hξ hgr _ x ht.1 _).const_mul _).sub
      ((measurable_shiftedPiReg hξ' hgr' _ x ht.1 _).const_mul _)) a4
    (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))

theorem shiftedPi_sub_iPsiSqPsiSq
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (hq : 1 ≤ q)
    (hκb : κbar ≤ κ.1 / 2) {B : ℝ} (hB : 0 ≤ B) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q .iPsiSqPsiSq B
      (S1 + C1 + B * S1 + parabolicSemigroup.momentConst 0) := by
  refine PiShiftSubBound.of_shiftMom ?_
  intro Ω _ P W ε ε' ξ ξ' c c' hc hc' hW hε hε' hξ hξ' hgr hgr' t ht x
  have := hW.isProbabilityMeasure
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hM0 := parabolicSemigroup.momentConst_nonneg 0
  have hS1 := SA.nonneg.1
  have hC1 := SA.left.nonneg.1
  have hmx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  set D := (max ε ε') ^ θ + ‖c - c'‖ with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hDm : (max ε ε') ^ θ ≤ D := le_add_of_nonneg_right (norm_nonneg _)
  have key : ∀ ω, shiftedPiReg N κ (shiftConst N ρ ε c) (ξ ω) x t .iPsiSqPsiSq -
      shiftedPiReg N κ (shiftConst N ρ' ε' c') (ξ' ω) x t .iPsiSqPsiSq =
      ((shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t .iPsiSqPsiSq -
        shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t .iPsiSqPsiSq) -
        (c.1 * shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t .iPsiSq -
          c'.1 * shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t .iPsiSq)) -
        (c.2 - c'.2) * shiftedPiMass t x := fun ω => by
    rw [shiftedPi_reg_iPsiSqPsiSq (C := shiftedPiHairerConst N ρ ε) (C' := shiftConst N ρ ε c) x
        (hξ.1 ω) (hgr ω) ht.1 rfl rfl,
      shiftedPi_reg_iPsiSqPsiSq (C := shiftedPiHairerConst N ρ' ε') (C' := shiftConst N ρ' ε' c') x
        (hξ'.1 ω) (hgr' ω) ht.1 rfl rfl]
    ring
  refine ShiftMom.congr key ?_
  have e : (homogeneity κ .iPsiSqPsiSq + κbar) / 4 ≤ (homogeneity κ .iPsiSq + κbar) / 4 := by
    simp only [homogeneity]; linarith
  have a1 := SA.momSub (σ := .iPsiSqPsiSq) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hε' hξ hξ' hgr hgr' ht x D hDm
  have a2 := (SA.left.mom (σ := .iPsiSq) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x).tpow hC1 ht e
  have a3 := (SA.momSub (σ := .iPsiSq) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hε' hξ hξ' hgr hgr' ht x D hDm).tpow
    (mul_nonneg hS1 hD0) ht e
  have a4 := ShiftMom.cdiff hq (measurable_shiftedPiReg hξ hgr _ x ht.1 _)
    (measurable_shiftedPiReg hξ' hgr' _ x ht.1 _) c.1 c'.1 a2 a3
    (B' := B) (d := D) (abs_fst_le_of_norm_le hc')
    ((abs_fst_sub_le_norm c c').trans (le_add_of_nonneg_left (by positivity)))
    (by positivity) (by positivity) (by positivity) hB
  have a5 : ShiftMom P q (fun _ => (c.2 - c'.2) * shiftedPiMass t x)
      (parabolicSemigroup.momentConst 0 * D * t ^ ((homogeneity κ .iPsiSqPsiSq + κbar) / 4)) := by
    refine (ShiftMom.const (P := P) _ (A := parabolicSemigroup.momentConst 0 * D) ?_).mono ?_
    · rw [abs_mul, mul_comm]
      exact mul_le_mul (abs_shiftedPiMass_le ht.1 x)
        ((abs_snd_sub_le_norm c c').trans (le_add_of_nonneg_left (by positivity)))
        (abs_nonneg _) hM0
    · have := one_le_tpow ht (e := (homogeneity κ .iPsiSqPsiSq + κbar) / 4)
        (by simp only [homogeneity]; linarith)
      nlinarith [mul_nonneg hM0 hD0]
  have h12 := a1.sub hq ((measurable_shiftedPiReg hξ hgr _ x ht.1 _).sub
    (measurable_shiftedPiReg hξ' hgr' _ x ht.1 _))
    (((measurable_shiftedPiReg hξ hgr _ x ht.1 _).const_mul _).sub
      ((measurable_shiftedPiReg hξ' hgr' _ x ht.1 _).const_mul _)) a4
    (by positivity) (by positivity)
  have := h12.sub hq (((measurable_shiftedPiReg hξ hgr _ x ht.1 _).sub
    (measurable_shiftedPiReg hξ' hgr' _ x ht.1 _)).sub
    (((measurable_shiftedPiReg hξ hgr _ x ht.1 _).const_mul _).sub
      ((measurable_shiftedPiReg hξ' hgr' _ x ht.1 _).const_mul _))) measurable_const a5
    (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))

end RegularityStructures.Phi43

end
