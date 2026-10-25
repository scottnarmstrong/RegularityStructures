/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSubRows
import Mathlib.Tactic

/-!
# Shifted difference bounds: the rows `Ψ², Ψ³, Ψ²Xᵢ, I(Ψ)Ψ², I(Ψ²)Ψ²`
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar θ : ℝ} {q : ℕ}
  {C1 C2 Ci Cg S1 S2 Si Sg : ℝ}

theorem shiftedPi_sub_psiSq
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (hq : 1 ≤ q)
    (hκb : κbar ≤ κ.1 / 2) {B : ℝ} :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q .psiSq B (S1 + parabolicSemigroup.momentConst 0) := by
  refine PiShiftSubBound.of_shiftMom ?_
  intro Ω _ P W ε ε' ξ ξ' c c' hc hc' hW hε hε' hξ hξ' hgr hgr' t ht x
  have := hW.isProbabilityMeasure
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hM0 := parabolicSemigroup.momentConst_nonneg 0
  have hS1 := SA.nonneg.1
  have hε0 : 0 < ε := hε.1
  have hmx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  set D := (max ε ε') ^ θ + ‖c - c'‖ with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hDm : (max ε ε') ^ θ ≤ D := le_add_of_nonneg_right (norm_nonneg _)
  have key : ∀ ω, shiftedPiReg N κ (shiftConst N ρ ε c) (ξ ω) x t .psiSq -
      shiftedPiReg N κ (shiftConst N ρ' ε' c') (ξ' ω) x t .psiSq =
      (shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t .psiSq -
        shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t .psiSq) -
        (c.1 - c'.1) * shiftedPiMass t x := fun ω => by
    rw [shiftedPi_reg_psiSq (C := shiftedPiHairerConst N ρ ε) (C' := shiftConst N ρ ε c) x
        (hξ.1 ω) (hgr ω) ht.1 rfl,
      shiftedPi_reg_psiSq (C := shiftedPiHairerConst N ρ' ε') (C' := shiftConst N ρ' ε' c') x
        (hξ'.1 ω) (hgr' ω) ht.1 rfl]
    ring
  refine ShiftMom.congr key ?_
  have a1 := SA.momSub (σ := .psiSq) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hε' hξ hξ' hgr hgr' ht x D hDm
  have a2 : ShiftMom P q (fun _ => (c.1 - c'.1) * shiftedPiMass t x)
      (parabolicSemigroup.momentConst 0 * D * t ^ ((homogeneity κ .psiSq + κbar) / 4)) := by
    refine (ShiftMom.const (P := P) _ (A := parabolicSemigroup.momentConst 0 * D) ?_).mono ?_
    · rw [abs_mul, mul_comm]
      exact mul_le_mul (abs_shiftedPiMass_le ht.1 x)
        ((abs_fst_sub_le_norm c c').trans (le_add_of_nonneg_left (by positivity)))
        (abs_nonneg _) hM0
    · have := one_le_tpow ht (e := (homogeneity κ .psiSq + κbar) / 4)
        (by simp only [homogeneity]; linarith)
      nlinarith [mul_nonneg hM0 hD0]
  have := a1.sub hq ((measurable_shiftedPiReg hξ hgr _ x ht.1 _).sub
    (measurable_shiftedPiReg hξ' hgr' _ x ht.1 _)) measurable_const a2
    (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))

theorem shiftedPi_sub_psiCube
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (hq : 1 ≤ q)
    {B : ℝ} (hB : 0 ≤ B) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q .psiCube B (S1 + 3 * C1 + 3 * B * S1) := by
  refine PiShiftSubBound.of_shiftMom ?_
  intro Ω _ P W ε ε' ξ ξ' c c' hc hc' hW hε hε' hξ hξ' hgr hgr' t ht x
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hS1 := SA.nonneg.1
  have hC1 := SA.left.nonneg.1
  have hmx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  set D := (max ε ε') ^ θ + ‖c - c'‖ with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hDm : (max ε ε') ^ θ ≤ D := le_add_of_nonneg_right (norm_nonneg _)
  have key : ∀ ω, shiftedPiReg N κ (shiftConst N ρ ε c) (ξ ω) x t .psiCube -
      shiftedPiReg N κ (shiftConst N ρ' ε' c') (ξ' ω) x t .psiCube =
      (shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t .psiCube -
        shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t .psiCube) -
        ((3 * c.1) * shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t .psi -
          (3 * c'.1) * shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t .psi) :=
    fun ω => by
    rw [shiftedPi_reg_psiCube (C := shiftedPiHairerConst N ρ ε) (C' := shiftConst N ρ ε c) x
        (hξ.1 ω) (hgr ω) ht.1 rfl,
      shiftedPi_reg_psiCube (C := shiftedPiHairerConst N ρ' ε') (C' := shiftConst N ρ' ε' c') x
        (hξ'.1 ω) (hgr' ω) ht.1 rfl]
    ring
  refine ShiftMom.congr key ?_
  have e : (homogeneity κ .psiCube + κbar) / 4 ≤ (homogeneity κ .psi + κbar) / 4 := by
    simp only [homogeneity]; linarith
  have a1 := SA.momSub (σ := .psiCube) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hε' hξ hξ' hgr hgr' ht x D hDm
  have a2 := (SA.left.mom (σ := .psi) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x).tpow hC1 ht e
  have a3 := (SA.momSub (σ := .psi) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hε' hξ hξ' hgr hgr' ht x D hDm).tpow
    (mul_nonneg hS1 hD0) ht e
  have a4 := ShiftMom.cdiff hq (measurable_shiftedPiReg hξ hgr _ x ht.1 _)
    (measurable_shiftedPiReg hξ' hgr' _ x ht.1 _) (3 * c.1) (3 * c'.1) a2 a3
    (B' := 3 * B) (d := 3 * D)
    (by rw [abs_mul]; norm_num; linarith [abs_fst_le_of_norm_le hc'])
    (by
      rw [← mul_sub, abs_mul]
      norm_num
      linarith [abs_fst_sub_le_norm c c', le_add_of_nonneg_left (norm_nonneg (c - c')) (a := (max ε ε') ^ θ), hmx])
    (by positivity) (by positivity) (by positivity) (by positivity)
  have := a1.sub hq ((measurable_shiftedPiReg hξ hgr _ x ht.1 _).sub
    (measurable_shiftedPiReg hξ' hgr' _ x ht.1 _))
    (((measurable_shiftedPiReg hξ hgr _ x ht.1 _).const_mul _).sub
      ((measurable_shiftedPiReg hξ' hgr' _ x ht.1 _).const_mul _)) a4
    (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))

theorem shiftedPi_sub_psiSqX
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (hq : 1 ≤ q)
    (hκb : κbar ≤ κ.1 / 2) {B : ℝ} (k : Fin 3) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q (.psiSqX k) B
      (S1 + parabolicSemigroup.momentConst 1) := by
  refine PiShiftSubBound.of_shiftMom ?_
  intro Ω _ P W ε ε' ξ ξ' c c' hc hc' hW hε hε' hξ hξ' hgr hgr' t ht x
  have := hW.isProbabilityMeasure
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hM1 := parabolicSemigroup.momentConst_nonneg 1
  have hS1 := SA.nonneg.1
  have hmx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  set D := (max ε ε') ^ θ + ‖c - c'‖ with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hDm : (max ε ε') ^ θ ≤ D := le_add_of_nonneg_right (norm_nonneg _)
  have key : ∀ ω, shiftedPiReg N κ (shiftConst N ρ ε c) (ξ ω) x t (.psiSqX k) -
      shiftedPiReg N κ (shiftConst N ρ' ε' c') (ξ' ω) x t (.psiSqX k) =
      (shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t (.psiSqX k) -
        shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t (.psiSqX k)) -
        (c.1 - c'.1) * shiftedPiMoment t x k := fun ω => by
    rw [shiftedPi_reg_psiSqX (C := shiftedPiHairerConst N ρ ε) (C' := shiftConst N ρ ε c) x
        (hξ.1 ω) (hgr ω) ht.1 rfl k,
      shiftedPi_reg_psiSqX (C := shiftedPiHairerConst N ρ' ε') (C' := shiftConst N ρ' ε' c') x
        (hξ'.1 ω) (hgr' ω) ht.1 rfl k]
    ring
  refine ShiftMom.congr key ?_
  have a1 := SA.momSub (σ := .psiSqX k) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hε' hξ hξ' hgr hgr' ht x D hDm
  have a2 : ShiftMom P q (fun _ => (c.1 - c'.1) * shiftedPiMoment t x k)
      (parabolicSemigroup.momentConst 1 * D * t ^ ((homogeneity κ (.psiSqX k) + κbar) / 4)) := by
    have h0 : ShiftMom P q (fun _ => (c.1 - c'.1) * shiftedPiMoment t x k)
        (parabolicSemigroup.momentConst 1 * D * t ^ (1 / 4 : ℝ)) := by
      refine ShiftMom.const (P := P) _ ?_
      rw [abs_mul]
      calc |c.1 - c'.1| * |shiftedPiMoment t x k|
          ≤ D * (parabolicSemigroup.momentConst 1 * t ^ (1 / 4 : ℝ)) :=
            mul_le_mul ((abs_fst_sub_le_norm c c').trans (le_add_of_nonneg_left (by positivity)))
              (abs_shiftedPiMoment_le ht.1 x k) (abs_nonneg _) hD0
        _ = parabolicSemigroup.momentConst 1 * D * t ^ (1 / 4 : ℝ) := by ring
    refine h0.tpow (by positivity) ht ?_
    simp only [homogeneity]; linarith
  have := a1.sub hq ((measurable_shiftedPiReg hξ hgr _ x ht.1 _).sub
    (measurable_shiftedPiReg hξ' hgr' _ x ht.1 _)) measurable_const a2
    (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))

end RegularityStructures.Phi43

end
