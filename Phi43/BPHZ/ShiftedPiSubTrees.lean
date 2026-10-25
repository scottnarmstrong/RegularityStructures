/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSubGrad
import Mathlib.Tactic

/-!
# Shifted difference bounds: the rows `I(Ψ³)` and `I(Ψ³)Ψ`

For two models the shift terms are `3 c F - 3 c' F'` with `F = R_{I(Ψ)} + ∑ₖ gₖ Mₖ` (respectively
`F = R_{I(Ψ)Ψ} + ∑ₖ gₖ R_{ΨXₖ}`), which is `3 (c - c') F + 3 c' (F - F')`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar θ : ℝ} {q : ℕ}
  {C1 C2 Ci Cg S1 S2 Si Sg : ℝ}

theorem shiftedPi_sub_iPsiCube
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (hq : 1 ≤ q)
    (hκb : κbar ≤ κ.1 / 2) {B : ℝ} (hB : 0 ≤ B) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q .iPsiCube B
      (S1 + 3 * (Ci + 3 * (Cg * parabolicSemigroup.momentConst 1)) +
        3 * B * (Si + 3 * (Sg * parabolicSemigroup.momentConst 1))) := by
  refine PiShiftSubBound.of_shiftMom ?_
  intro Ω _ P W ε ε' ξ ξ' c c' hc hc' hW hε hε' hξ hξ' hgr hgr' t ht x
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hM1 := parabolicSemigroup.momentConst_nonneg 1
  have hS1 := SA.nonneg.1
  have hSi := SA.nonneg.2.2.1
  have hSg := SA.nonneg.2.2.2
  have hCi := SA.left.nonneg.2.2.1
  have hCg := SA.left.nonneg.2.2.2
  have hmx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  set D := (max ε ε') ^ θ + ‖c - c'‖ with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hDm : (max ε ε') ^ θ ≤ D := le_add_of_nonneg_right (norm_nonneg _)
  set R : Symbol → Ω → ℝ := fun σ ω =>
    shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t σ with hR
  set R' : Symbol → Ω → ℝ := fun σ ω =>
    shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t σ with hR'
  set F : Ω → ℝ := fun ω => R .iPsi ω + (shiftedPiGrad N ξ ω x 0 * shiftedPiMoment t x 0 +
    shiftedPiGrad N ξ ω x 1 * shiftedPiMoment t x 1 +
    shiftedPiGrad N ξ ω x 2 * shiftedPiMoment t x 2) with hF
  set F' : Ω → ℝ := fun ω => R' .iPsi ω + (shiftedPiGrad N ξ' ω x 0 * shiftedPiMoment t x 0 +
    shiftedPiGrad N ξ' ω x 1 * shiftedPiMoment t x 1 +
    shiftedPiGrad N ξ' ω x 2 * shiftedPiMoment t x 2) with hF'
  have key : ∀ ω, shiftedPiReg N κ (shiftConst N ρ ε c) (ξ ω) x t .iPsiCube -
      shiftedPiReg N κ (shiftConst N ρ' ε' c') (ξ' ω) x t .iPsiCube =
      (R .iPsiCube ω - R' .iPsiCube ω) - ((3 * c.1) * F ω - (3 * c'.1) * F' ω) := fun ω => by
    rw [shiftedPi_reg_iPsiCube (C := shiftedPiHairerConst N ρ ε) (C' := shiftConst N ρ ε c) x
        (hξ.1 ω) (hgr ω) ht.1 rfl,
      shiftedPi_reg_iPsiCube (C := shiftedPiHairerConst N ρ' ε') (C' := shiftConst N ρ' ε' c') x
        (hξ'.1 ω) (hgr' ω) ht.1 rfl, Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [hF, hF']
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
  have mF : Measurable F := (mR _).add (((mg 0).add (mg 1)).add (mg 2))
  have mF' : Measurable F' := (mR' _).add (((mg' 0).add (mg' 1)).add (mg' 2))
  have e1 : (homogeneity κ .iPsiCube + κbar) / 4 ≤ (homogeneity κ .iPsi + κbar) / 4 := by
    simp only [homogeneity]; linarith
  have e2 : (homogeneity κ .iPsiCube + κbar) / 4 ≤ 1 / 4 := by
    simp only [homogeneity]; linarith
  -- single bound for F
  have gm : ∀ k : Fin 3, ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k)
      (Cg * parabolicSemigroup.momentConst 1 * t ^ ((homogeneity κ .iPsiCube + κbar) / 4)) :=
    fun k => SA.left.momGradMoment hW hε hξ ht x k e2
  have sg := ((gm 0).add hq (mg 0) (mg 1) (gm 1) (by positivity) (by positivity)).add hq
    ((mg 0).add (mg 1)) (mg 2) (gm 2) (by positivity) (by positivity)
  have a2 := (SA.left.momIPsi hW hε hξ hgr ht x).tpow hCi ht e1
  have hFb := a2.add hq (mR _) (((mg 0).add (mg 1)).add (mg 2)) sg (by positivity)
    (by positivity)
  -- difference bound for F
  have gd : ∀ k : Fin 3, ShiftMom P q (fun ω => (shiftedPiGrad N ξ ω x k -
      shiftedPiGrad N ξ' ω x k) * shiftedPiMoment t x k)
      (Sg * parabolicSemigroup.momentConst 1 * D * t ^ ((homogeneity κ .iPsiCube + κbar) / 4)) :=
    fun k => SA.momGradMomentSub hW hε hε' hξ hξ' ht x k D hDm e2
  have sgd := ((gd 0).add hq (mgd 0) (mgd 1) (gd 1) (by positivity) (by positivity)).add hq
    ((mgd 0).add (mgd 1)) (mgd 2) (gd 2) (by positivity) (by positivity)
  have b2 := (SA.momSubIPsi hW hε hε' hξ hξ' hgr hgr' ht x D hDm).tpow (mul_nonneg hSi hD0) ht e1
  have hFd0 := b2.add hq ((mR _).sub (mR' _)) (((mgd 0).add (mgd 1)).add (mgd 2)) sgd
    (by positivity) (by positivity)
  have hFd : ShiftMom P q (fun ω => F ω - F' ω) _ :=
    ShiftMom.congr (fun ω => by simp only [hF, hF', Pi.sub_apply, Pi.add_apply]; ring) hFd0
  have a4 := ShiftMom.cdiff hq mF mF' (3 * c.1) (3 * c'.1) hFb hFd
    (B' := 3 * B) (d := 3 * D)
    (by rw [abs_mul]; norm_num; linarith [abs_fst_le_of_norm_le hc'])
    (by
      rw [← mul_sub, abs_mul]
      norm_num
      linarith [abs_fst_sub_le_norm c c', le_add_of_nonneg_left (norm_nonneg (c - c'))
        (a := (max ε ε') ^ θ)])
    (by positivity) (by positivity) (by positivity) (by positivity)
  have a1 := SA.momSub (σ := .iPsiCube) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hε' hξ hξ' hgr hgr' ht x D hDm
  have := a1.sub hq ((mR _).sub (mR' _))
    (((mF.const_mul _).sub (mF'.const_mul _))) a4 (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))

theorem shiftedPi_sub_iPsiCubePsi
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (hq : 1 ≤ q)
    {B : ℝ} (hB : 0 ≤ B) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q .iPsiCubePsi B
      (S1 + 3 * (C1 + 3 * (Cg * C2)) + 3 * B * (S1 + 3 * (Sg * C2 + Cg * S2))) := by
  refine PiShiftSubBound.of_shiftMom ?_
  intro Ω _ P W ε ε' ξ ξ' c c' hc hc' hW hε hε' hξ hξ' hgr hgr' t ht x
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hS1 := SA.nonneg.1
  have hS2 := SA.nonneg.2.1
  have hSg := SA.nonneg.2.2.2
  have hC1 := SA.left.nonneg.1
  have hC2 := SA.left.nonneg.2.1
  have hCg := SA.left.nonneg.2.2.2
  have hmx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  set D := (max ε ε') ^ θ + ‖c - c'‖ with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hDm : (max ε ε') ^ θ ≤ D := le_add_of_nonneg_right (norm_nonneg _)
  set R : Symbol → Ω → ℝ := fun σ ω =>
    shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t σ with hR
  set R' : Symbol → Ω → ℝ := fun σ ω =>
    shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t σ with hR'
  set F : Ω → ℝ := fun ω => R .iPsiPsi ω + (shiftedPiGrad N ξ ω x 0 * R (.psiX 0) ω +
    shiftedPiGrad N ξ ω x 1 * R (.psiX 1) ω + shiftedPiGrad N ξ ω x 2 * R (.psiX 2) ω) with hF
  set F' : Ω → ℝ := fun ω => R' .iPsiPsi ω + (shiftedPiGrad N ξ' ω x 0 * R' (.psiX 0) ω +
    shiftedPiGrad N ξ' ω x 1 * R' (.psiX 1) ω + shiftedPiGrad N ξ' ω x 2 * R' (.psiX 2) ω)
    with hF'
  have key : ∀ ω, shiftedPiReg N κ (shiftConst N ρ ε c) (ξ ω) x t .iPsiCubePsi -
      shiftedPiReg N κ (shiftConst N ρ' ε' c') (ξ' ω) x t .iPsiCubePsi =
      (R .iPsiCubePsi ω - R' .iPsiCubePsi ω) - ((3 * c.1) * F ω - (3 * c'.1) * F' ω) :=
    fun ω => by
    rw [shiftedPi_reg_iPsiCubePsi (C := shiftedPiHairerConst N ρ ε) (C' := shiftConst N ρ ε c) x
        (hξ.1 ω) (hgr ω) ht.1 rfl,
      shiftedPi_reg_iPsiCubePsi (C := shiftedPiHairerConst N ρ' ε') (C' := shiftConst N ρ' ε' c') x
        (hξ'.1 ω) (hgr' ω) ht.1 rfl, Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [hF, hF']
    ring
  refine ShiftMom.congr key ?_
  have mR : ∀ σ, Measurable (R σ) := fun σ => measurable_shiftedPiReg hξ hgr _ x ht.1 σ
  have mR' : ∀ σ, Measurable (R' σ) := fun σ => measurable_shiftedPiReg hξ' hgr' _ x ht.1 σ
  have mgR : ∀ k : Fin 3, Measurable fun ω => shiftedPiGrad N ξ ω x k * R (.psiX k) ω :=
    fun k => (measurable_shiftedPiGrad hξ x k).mul (mR _)
  have mgR' : ∀ k : Fin 3, Measurable fun ω => shiftedPiGrad N ξ' ω x k * R' (.psiX k) ω :=
    fun k => (measurable_shiftedPiGrad hξ' x k).mul (mR' _)
  have mF : Measurable F := (mR _).add (((mgR 0).add (mgR 1)).add (mgR 2))
  have mF' : Measurable F' := (mR' _).add (((mgR' 0).add (mgR' 1)).add (mgR' 2))
  have e1 : (homogeneity κ .iPsiCubePsi + κbar) / 4 ≤ (homogeneity κ .iPsiPsi + κbar) / 4 := by
    simp only [homogeneity]; linarith
  have e2 : (homogeneity κ .iPsiCubePsi + κbar) / 4 ≤ (homogeneity κ (.psiX 0) + κbar) / 4 := by
    simp only [homogeneity]; linarith
  have gm : ∀ k : Fin 3, ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k * R (.psiX k) ω)
      (Cg * C2 * t ^ ((homogeneity κ .iPsiCubePsi + κbar) / 4)) :=
    fun k => SA.left.momGradReg (σ := .psiX k) (by simp) (by simp)
      (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x k
      (by simp only [homogeneity]; linarith)
  have sg := ((gm 0).add hq (mgR 0) (mgR 1) (gm 1) (by positivity) (by positivity)).add hq
    ((mgR 0).add (mgR 1)) (mgR 2) (gm 2) (by positivity) (by positivity)
  have a2 := (SA.left.mom (σ := .iPsiPsi) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x).tpow hC1 ht e1
  have hFb := a2.add hq (mR _) (((mgR 0).add (mgR 1)).add (mgR 2)) sg (by positivity)
    (by positivity)
  have gd : ∀ k : Fin 3, ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k * R (.psiX k) ω -
      shiftedPiGrad N ξ' ω x k * R' (.psiX k) ω)
      ((Sg * C2 + Cg * S2) * D * t ^ ((homogeneity κ .iPsiCubePsi + κbar) / 4)) :=
    fun k => SA.momGradRegSub hq (σ := .psiX k) (by simp) (by simp)
      (by simp only [homogeneity, gamma]; linarith) hW hε hε' hξ hξ' hgr hgr' ht x k D hDm
      (by simp only [homogeneity]; linarith)
  have sgd := ((gd 0).add hq ((mgR 0).sub (mgR' 0)) ((mgR 1).sub (mgR' 1)) (gd 1)
      (by positivity) (by positivity)).add hq (((mgR 0).sub (mgR' 0)).add ((mgR 1).sub (mgR' 1)))
    ((mgR 2).sub (mgR' 2)) (gd 2) (by positivity) (by positivity)
  have b2 := (SA.momSub (σ := .iPsiPsi) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hε' hξ hξ' hgr hgr' ht x D hDm).tpow
    (mul_nonneg hS1 hD0) ht e1
  have hFd0 := b2.add hq ((mR _).sub (mR' _))
    ((((mgR 0).sub (mgR' 0)).add ((mgR 1).sub (mgR' 1))).add ((mgR 2).sub (mgR' 2))) sgd
    (by positivity) (by positivity)
  have hFd : ShiftMom P q (fun ω => F ω - F' ω) _ :=
    ShiftMom.congr (fun ω => by simp only [hF, hF', Pi.sub_apply, Pi.add_apply]; ring) hFd0
  have a4 := ShiftMom.cdiff hq mF mF' (3 * c.1) (3 * c'.1) hFb hFd
    (B' := 3 * B) (d := 3 * D)
    (by rw [abs_mul]; norm_num; linarith [abs_fst_le_of_norm_le hc'])
    (by
      rw [← mul_sub, abs_mul]
      norm_num
      linarith [abs_fst_sub_le_norm c c', le_add_of_nonneg_left (norm_nonneg (c - c'))
        (a := (max ε ε') ^ θ)])
    (by positivity) (by positivity) (by positivity) (by positivity)
  have a1 := SA.momSub (σ := .iPsiCubePsi) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hε' hξ hξ' hgr hgr' ht x D hDm
  have := a1.sub hq ((mR _).sub (mR' _))
    (((mF.const_mul _).sub (mF'.const_mul _))) a4 (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))

end RegularityStructures.Phi43

end
