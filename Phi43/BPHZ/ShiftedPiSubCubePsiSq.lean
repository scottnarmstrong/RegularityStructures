/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSubGH
import Mathlib.Tactic

/-!
# Shifted difference bound: the row `I(Ψ³)Ψ²`
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar θ : ℝ} {q : ℕ}
  {C1 C2 Ci Cg S1 S2 Si Sg : ℝ}

theorem shiftedPi_sub_iPsiCubePsiSq
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (hq : 1 ≤ q)
    (hκb : κbar ≤ κ.1 / 2) {B : ℝ} (hB : 0 ≤ B) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q .iPsiCubePsiSq B
      (S1 + (C1 + B * S1) + (3 * C1 + 3 * B * S1) +
        (9 * (Cg * C2) + 3 * B * (3 * (Sg * C2 + Cg * S2))) +
        (6 * B * (Ci + 3 * (Cg * parabolicSemigroup.momentConst 1)) +
          3 * B ^ 2 * (Si + 3 * (Sg * parabolicSemigroup.momentConst 1))) +
        (3 * C1 + 3 * B * S1)) := by
  refine PiShiftSubBound.of_shiftMom ?_
  intro Ω _ P W ε ε' ξ ξ' c c' hc hc' hW hε hε' hξ hξ' hgr hgr' t ht x
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hM1 := parabolicSemigroup.momentConst_nonneg 1
  have hS1 := SA.nonneg.1
  have hS2 := SA.nonneg.2.1
  have hSi := SA.nonneg.2.2.1
  have hSg := SA.nonneg.2.2.2
  have hC1 := SA.left.nonneg.1
  have hC2 := SA.left.nonneg.2.1
  have hCi := SA.left.nonneg.2.2.1
  have hCg := SA.left.nonneg.2.2.2
  have hc1 := abs_fst_le_of_norm_le hc
  have hc1' := abs_fst_le_of_norm_le hc'
  have hmx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  set D := (max ε ε') ^ θ + ‖c - c'‖ with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hDm : (max ε ε') ^ θ ≤ D := le_add_of_nonneg_right (norm_nonneg _)
  have hdc1 : |c.1 - c'.1| ≤ D := (abs_fst_sub_le_norm c c').trans (le_add_of_nonneg_left hmx)
  have hdc2 : |c.2 - c'.2| ≤ D := (abs_snd_sub_le_norm c c').trans (le_add_of_nonneg_left hmx)
  set R : Symbol → Ω → ℝ := fun σ ω =>
    shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t σ with hR
  set R' : Symbol → Ω → ℝ := fun σ ω =>
    shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t σ with hR'
  set G := shiftedPiGsum N κ (shiftedPiHairerConst N ρ ε) ξ x t with hG
  set G' := shiftedPiGsum N κ (shiftedPiHairerConst N ρ' ε') ξ' x t with hG'
  set H := shiftedPiHsum N κ (shiftedPiHairerConst N ρ ε) ξ x t with hH
  set H' := shiftedPiHsum N κ (shiftedPiHairerConst N ρ' ε') ξ' x t with hH'
  have key : ∀ ω, shiftedPiReg N κ (shiftConst N ρ ε c) (ξ ω) x t .iPsiCubePsiSq -
      shiftedPiReg N κ (shiftConst N ρ' ε' c') (ξ' ω) x t .iPsiCubePsiSq =
      (R .iPsiCubePsiSq ω - R' .iPsiCubePsiSq ω) -
        (c.1 * R .iPsiCube ω - c'.1 * R' .iPsiCube ω) -
        ((3 * c.1) * R .iPsiPsiSq ω - (3 * c'.1) * R' .iPsiPsiSq ω) -
        ((3 * c.1) * G ω - (3 * c'.1) * G' ω) +
        ((3 * c.1 ^ 2) * H ω - (3 * c'.1 ^ 2) * H' ω) -
        ((3 * c.2) * R .psi ω - (3 * c'.2) * R' .psi ω) := fun ω => by
    rw [shiftedPi_reg_iPsiCubePsiSq_GH (C := shiftedPiHairerConst N ρ ε)
        (C' := shiftConst N ρ ε c) x (hξ.1 ω) (hgr ω) ht.1 rfl rfl,
      shiftedPi_reg_iPsiCubePsiSq_GH (C := shiftedPiHairerConst N ρ' ε')
        (C' := shiftConst N ρ' ε' c') x (hξ'.1 ω) (hgr' ω) ht.1 rfl rfl]
    ring
  refine ShiftMom.congr key ?_
  have mR : ∀ σ, Measurable (R σ) := fun σ => measurable_shiftedPiReg hξ hgr _ x ht.1 σ
  have mR' : ∀ σ, Measurable (R' σ) := fun σ => measurable_shiftedPiReg hξ' hgr' _ x ht.1 σ
  have mg : ∀ k : Fin 3, Measurable fun ω => shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k :=
    fun k => (measurable_shiftedPiGrad hξ x k).mul_const _
  have mg' : ∀ k : Fin 3, Measurable fun ω => shiftedPiGrad N ξ' ω x k * shiftedPiMoment t x k :=
    fun k => (measurable_shiftedPiGrad hξ' x k).mul_const _
  have mgd : ∀ k : Fin 3, Measurable fun ω => (shiftedPiGrad N ξ ω x k -
      shiftedPiGrad N ξ' ω x k) * shiftedPiMoment t x k :=
    fun k => ((measurable_shiftedPiGrad hξ x k).sub (measurable_shiftedPiGrad hξ' x k)).mul_const _
  have mgR : ∀ k : Fin 3, Measurable fun ω => shiftedPiGrad N ξ ω x k * R (.psiSqX k) ω :=
    fun k => (measurable_shiftedPiGrad hξ x k).mul (mR _)
  have mgR' : ∀ k : Fin 3, Measurable fun ω => shiftedPiGrad N ξ' ω x k * R' (.psiSqX k) ω :=
    fun k => (measurable_shiftedPiGrad hξ' x k).mul (mR' _)
  have mG : Measurable G := measurable_shiftedPiGsum hξ hgr x ht.1
  have mG' : Measurable G' := measurable_shiftedPiGsum hξ' hgr' x ht.1
  have mH : Measurable H := measurable_shiftedPiHsum hξ hgr x ht.1
  have mH' : Measurable H' := measurable_shiftedPiHsum hξ' hgr' x ht.1
  -- the rows of higher degree
  have lift : ∀ {σ : Symbol} (h1 : σ ≠ .one) (hx : ∀ j, σ ≠ .x j)
      (hlt : homogeneity κ σ < gamma κ),
      (homogeneity κ .iPsiCubePsiSq + κbar) / 4 ≤ (homogeneity κ σ + κbar) / 4 →
      ShiftMom P q (R σ) (C1 * t ^ ((homogeneity κ .iPsiCubePsiSq + κbar) / 4)) ∧
      ShiftMom P q (fun ω => R σ ω - R' σ ω)
        (S1 * D * t ^ ((homogeneity κ .iPsiCubePsiSq + κbar) / 4)) :=
    fun h1 hx hlt he => ⟨(SA.left.mom h1 hx hlt hW hε hξ hgr ht x).tpow hC1 ht he,
      (SA.momSub h1 hx hlt hW hε hε' hξ hξ' hgr hgr' ht x D hDm).tpow (mul_nonneg hS1 hD0) ht he⟩
  obtain ⟨b2, d2⟩ := lift (σ := .iPsiCube) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) (by simp only [homogeneity]; linarith)
  obtain ⟨b3, d3⟩ := lift (σ := .iPsiPsiSq) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) (by simp only [homogeneity]; linarith)
  obtain ⟨b6, d6⟩ := lift (σ := .psi) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) (by simp only [homogeneity]; linarith)
  have e1 : (homogeneity κ .iPsiCubePsiSq + κbar) / 4 ≤ (homogeneity κ .iPsi + κbar) / 4 := by
    simp only [homogeneity]; linarith
  have e2 : (homogeneity κ .iPsiCubePsiSq + κbar) / 4 ≤ 1 / 4 := by
    simp only [homogeneity]; linarith
  have e3 : (homogeneity κ .iPsiCubePsiSq + κbar) / 4 ≤ (homogeneity κ (.psiSqX 0) + κbar) / 4 := by
    simp only [homogeneity]; linarith
  have bG := SA.left.momGsum hq hW hε hξ hgr ht x e3
  have dG := SA.momGsumSub hq hW hε hε' hξ hξ' hgr hgr' ht x D hDm e3
  have bH := SA.left.momHsum hq hW hε hξ hgr ht x e1 e2
  have dH := SA.momHsumSub hq hW hε hε' hξ hξ' hgr hgr' ht x D hDm e1 e2
  -- the six terms
  have t2 := ShiftMom.cdiff hq (mR _) (mR' _) c.1 c'.1 b2 d2 (B' := B) (d := D) hc1' hdc1
    (by positivity) (by positivity) hD0 hB
  have t3 := ShiftMom.cdiff hq (mR _) (mR' _) (3 * c.1) (3 * c'.1) b3 d3 (B' := 3 * B)
    (d := 3 * D) (by rw [abs_mul]; norm_num; linarith)
    (by rw [← mul_sub, abs_mul]; norm_num; linarith) (by positivity) (by positivity)
    (by positivity) (by positivity)
  have t4 := ShiftMom.cdiff hq mG mG' (3 * c.1) (3 * c'.1) bG dG (B' := 3 * B)
    (d := 3 * D) (by rw [abs_mul]; norm_num; linarith)
    (by rw [← mul_sub, abs_mul]; norm_num; linarith) (by positivity) (by positivity)
    (by positivity) (by positivity)
  have t5 := ShiftMom.cdiff hq mH mH' (3 * c.1 ^ 2) (3 * c'.1 ^ 2) bH dH (B' := 3 * B ^ 2)
    (d := 6 * B * D)
    (by
      rw [abs_mul, abs_pow]
      norm_num
      have := sq_abs c'.1
      nlinarith [abs_nonneg c'.1])
    (by
      have e : 3 * c.1 ^ 2 - 3 * c'.1 ^ 2 = 3 * ((c.1 - c'.1) * (c.1 + c'.1)) := by ring
      rw [e, abs_mul, abs_mul]
      norm_num
      have h1 : |c.1 + c'.1| ≤ 2 * B := (abs_add_le _ _).trans (by linarith)
      linarith [mul_le_mul hdc1 h1 (abs_nonneg _) hD0, abs_nonneg (c.1 - c'.1),
        abs_nonneg (c.1 + c'.1)])
    (by positivity) (by positivity) (by positivity) (by positivity)
  have t6 := ShiftMom.cdiff hq (mR _) (mR' _) (3 * c.2) (3 * c'.2) b6 d6 (B' := 3 * B)
    (d := 3 * D) (by rw [abs_mul]; norm_num; linarith [abs_snd_le_of_norm_le hc'])
    (by rw [← mul_sub, abs_mul]; norm_num; linarith) (by positivity) (by positivity)
    (by positivity) (by positivity)
  have a1 := SA.momSub (σ := .iPsiCubePsiSq) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hε' hξ hξ' hgr hgr' ht x D hDm
  have := ShiftMom.assemble6 hq ((mR _).sub (mR' _))
    (((mR _).const_mul _).sub ((mR' _).const_mul _))
    (((mR _).const_mul _).sub ((mR' _).const_mul _))
    ((mG.const_mul _).sub (mG'.const_mul _)) ((mH.const_mul _).sub (mH'.const_mul _))
    (((mR _).const_mul _).sub ((mR' _).const_mul _)) a1 t2 t3 t4 t5 t6
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity)
  exact this.mono (le_of_eq (by ring))

end RegularityStructures.Phi43

end
