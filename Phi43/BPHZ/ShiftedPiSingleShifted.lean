/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSingleRows
import Mathlib.Tactic

/-!
# Single shifted bounds: the rows `Ψ², Ψ³, Ψ²Xᵢ, I(Ψ)Ψ², I(Ψ²)Ψ²`

By the shift identities of `ShiftedPiRegPi`, these rows are the unshifted rows plus a multiple
(`-a`, `-3a`, bounded by `3B`) of one row of higher degree, or of the deterministic mass and first
moment of the kernel.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar : ℝ} {q : ℕ} {C1 C2 Ci Cg : ℝ}

theorem abs_fst_le_of_norm_le {c : RenormalisationConstants} {B : ℝ} (h : ‖c‖ ≤ B) : |c.1| ≤ B :=
  (norm_fst_le c).trans' (le_of_eq (Real.norm_eq_abs _).symm) |>.trans h

theorem abs_snd_le_of_norm_le {c : RenormalisationConstants} {B : ℝ} (h : ‖c‖ ≤ B) : |c.2| ≤ B :=
  (norm_snd_le c).trans' (le_of_eq (Real.norm_eq_abs _).symm) |>.trans h

theorem one_le_tpow {t e : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (he : e ≤ 0) : 1 ≤ t ^ e :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2 he

theorem shiftedPi_single_psiSq (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) (hq : 1 ≤ q)
    (hκb : κbar ≤ κ.1 / 2) {B : ℝ} (hB : 0 ≤ B) :
    PiShiftSingleBound.{u} N ρ κ κbar q .psiSq B (C1 + B * parabolicSemigroup.momentConst 0) := by
  refine PiShiftSingleBound.of_shiftMom ?_
  intro Ω _ P W ε ξ c hc hW hε hξ hgr t ht x
  have := hW.isProbabilityMeasure
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hM0 := parabolicSemigroup.momentConst_nonneg 0
  have hC1 := A.nonneg.1
  refine ShiftMom.congr (fun ω => shiftedPi_reg_psiSq x (hξ.1 ω) (hgr ω) ht.1 rfl) ?_
  have a1 := A.mom (σ := .psiSq) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x
  have a2 : ShiftMom P q (fun _ => c.1 * shiftedPiMass t x)
      (B * parabolicSemigroup.momentConst 0 * t ^ ((homogeneity κ .psiSq + κbar) / 4)) := by
    refine (ShiftMom.const (P := P) (c.1 * shiftedPiMass t x) (A := B * parabolicSemigroup.momentConst 0)
      ?_).mono ?_
    · rw [abs_mul]
      exact mul_le_mul (abs_fst_le_of_norm_le hc) (abs_shiftedPiMass_le ht.1 x)
        (abs_nonneg _) hB
    · have := one_le_tpow ht (e := (homogeneity κ .psiSq + κbar) / 4)
        (by simp only [homogeneity]; linarith)
      nlinarith [mul_nonneg hB hM0]
  have := a1.sub hq (measurable_shiftedPiReg hξ hgr _ x ht.1 _) measurable_const a2
    (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))

theorem shiftedPi_single_psiCube (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) (hq : 1 ≤ q)
    {B : ℝ} (hB : 0 ≤ B) :
    PiShiftSingleBound.{u} N ρ κ κbar q .psiCube B (C1 * (1 + 3 * B)) := by
  refine PiShiftSingleBound.of_shiftMom ?_
  intro Ω _ P W ε ξ c hc hW hε hξ hgr t ht x
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hC1 := A.nonneg.1
  refine ShiftMom.congr (fun ω => shiftedPi_reg_psiCube x (hξ.1 ω) (hgr ω) ht.1 rfl) ?_
  have a1 := A.mom (σ := .psiCube) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x
  have a2 := (A.mom (σ := .psi) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x).tpow hC1 ht
    (e₁ := (homogeneity κ .psiCube + κbar) / 4) (by simp only [homogeneity]; linarith)
  have a3 := a2.const_mul (3 * c.1) (B := 3 * B)
    (by rw [abs_mul]; norm_num; linarith [abs_fst_le_of_norm_le hc]) (by positivity)
  have := a1.sub hq (measurable_shiftedPiReg hξ hgr _ x ht.1 _)
    (((measurable_shiftedPiReg hξ hgr _ x ht.1 _)).const_mul _) a3 (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))

theorem shiftedPi_single_psiSqX (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) (hq : 1 ≤ q)
    (hκb : κbar ≤ κ.1 / 2) {B : ℝ} (hB : 0 ≤ B) (k : Fin 3) :
    PiShiftSingleBound.{u} N ρ κ κbar q (.psiSqX k) B
      (C1 + B * parabolicSemigroup.momentConst 1) := by
  refine PiShiftSingleBound.of_shiftMom ?_
  intro Ω _ P W ε ξ c hc hW hε hξ hgr t ht x
  have := hW.isProbabilityMeasure
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hM1 := parabolicSemigroup.momentConst_nonneg 1
  have hC1 := A.nonneg.1
  refine ShiftMom.congr (fun ω => shiftedPi_reg_psiSqX x (hξ.1 ω) (hgr ω) ht.1 rfl k) ?_
  have a1 := A.mom (σ := .psiSqX k) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x
  have a2 : ShiftMom P q (fun _ => c.1 * shiftedPiMoment t x k)
      (B * parabolicSemigroup.momentConst 1 * t ^ ((homogeneity κ (.psiSqX k) + κbar) / 4)) := by
    have h0 : ShiftMom P q (fun _ => c.1 * shiftedPiMoment t x k)
        (B * parabolicSemigroup.momentConst 1 * t ^ (1 / 4 : ℝ)) := by
      refine ShiftMom.const (P := P) _ ?_
      rw [abs_mul, mul_assoc]
      exact mul_le_mul (abs_fst_le_of_norm_le hc) (abs_shiftedPiMoment_le ht.1 x k)
        (abs_nonneg _) hB
    refine h0.tpow (by positivity) ht ?_
    simp only [homogeneity]; linarith
  have := a1.sub hq (measurable_shiftedPiReg hξ hgr _ x ht.1 _) measurable_const a2
    (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))

theorem shiftedPi_single_iPsiPsiSq (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) (hq : 1 ≤ q)
    {B : ℝ} (hB : 0 ≤ B) :
    PiShiftSingleBound.{u} N ρ κ κbar q .iPsiPsiSq B (C1 + B * Ci) := by
  refine PiShiftSingleBound.of_shiftMom ?_
  intro Ω _ P W ε ξ c hc hW hε hξ hgr t ht x
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hC1 := A.nonneg.1
  have hCi := A.nonneg.2.2.1
  refine ShiftMom.congr (fun ω => shiftedPi_reg_iPsiPsiSq x (hξ.1 ω) (hgr ω) ht.1 rfl) ?_
  have a1 := A.mom (σ := .iPsiPsiSq) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x
  have a2 := (A.momIPsi hW hε hξ hgr ht x).tpow hCi ht
    (e₁ := (homogeneity κ .iPsiPsiSq + κbar) / 4) (by simp only [homogeneity]; linarith)
  have a3 := a2.const_mul c.1 (B := B) (abs_fst_le_of_norm_le hc) (by positivity)
  have := a1.sub hq (measurable_shiftedPiReg hξ hgr _ x ht.1 _)
    (((measurable_shiftedPiReg hξ hgr _ x ht.1 _)).const_mul _) a3 (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))

theorem shiftedPi_single_iPsiSqPsiSq (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg)
    (hq : 1 ≤ q) (hκb : κbar ≤ κ.1 / 2) {B : ℝ} (hB : 0 ≤ B) :
    PiShiftSingleBound.{u} N ρ κ κbar q .iPsiSqPsiSq B
      (C1 + B * C1 + B * parabolicSemigroup.momentConst 0) := by
  refine PiShiftSingleBound.of_shiftMom ?_
  intro Ω _ P W ε ξ c hc hW hε hξ hgr t ht x
  have := hW.isProbabilityMeasure
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hM0 := parabolicSemigroup.momentConst_nonneg 0
  have hC1 := A.nonneg.1
  refine ShiftMom.congr
    (fun ω => shiftedPi_reg_iPsiSqPsiSq x (hξ.1 ω) (hgr ω) ht.1 rfl rfl) ?_
  have a1 := A.mom (σ := .iPsiSqPsiSq) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x
  have a2 := (A.mom (σ := .iPsiSq) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x).tpow hC1 ht
    (e₁ := (homogeneity κ .iPsiSqPsiSq + κbar) / 4) (by simp only [homogeneity]; linarith)
  have a3 := a2.const_mul c.1 (B := B) (abs_fst_le_of_norm_le hc) (by positivity)
  have a4 : ShiftMom P q (fun _ => c.2 * shiftedPiMass t x)
      (B * parabolicSemigroup.momentConst 0 * t ^ ((homogeneity κ .iPsiSqPsiSq + κbar) / 4)) := by
    refine (ShiftMom.const (P := P) (c.2 * shiftedPiMass t x) (A := B * parabolicSemigroup.momentConst 0)
      ?_).mono ?_
    · rw [abs_mul]
      exact mul_le_mul (abs_snd_le_of_norm_le hc) (abs_shiftedPiMass_le ht.1 x)
        (abs_nonneg _) hB
    · have := one_le_tpow ht (e := (homogeneity κ .iPsiSqPsiSq + κbar) / 4)
        (by simp only [homogeneity]; linarith)
      nlinarith [mul_nonneg hB hM0]
  have h12 := a1.sub hq (measurable_shiftedPiReg hξ hgr _ x ht.1 _)
    (((measurable_shiftedPiReg hξ hgr _ x ht.1 _)).const_mul _) a3 (by positivity) (by positivity)
  have := h12.sub hq ((measurable_shiftedPiReg hξ hgr _ x ht.1 _).sub
    ((measurable_shiftedPiReg hξ hgr _ x ht.1 _).const_mul _)) measurable_const a4
    (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))

end RegularityStructures.Phi43

end
