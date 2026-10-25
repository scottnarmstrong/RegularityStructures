/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSingleShifted
import Mathlib.Tactic

/-!
# Single shifted bounds: the rows containing `I(Ψ³)`

`I(Ψ³)`, `I(Ψ³)Ψ` and `I(Ψ³)Ψ²` shift by multiples of rows of higher degree with the random
coefficients `gₖ = ∂ₖ(K ∗ Ψ)(x)`; their `L^(2q)` moments are uniform (`ShiftedPiAtoms.grad`), so
Hölder's inequality closes the bounds.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar : ℝ} {q : ℕ} {C1 C2 Ci Cg : ℝ}

theorem shiftedPi_single_iPsiCube (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) (hq : 1 ≤ q)
    (hκb : κbar ≤ κ.1 / 2) {B : ℝ} (hB : 0 ≤ B) :
    PiShiftSingleBound.{u} N ρ κ κbar q .iPsiCube B
      (C1 + 3 * B * (Ci + 3 * (Cg * parabolicSemigroup.momentConst 1))) := by
  refine PiShiftSingleBound.of_shiftMom ?_
  intro Ω _ P W ε ξ c hc hW hε hξ hgr t ht x
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hM1 := parabolicSemigroup.momentConst_nonneg 1
  have hC1 := A.nonneg.1
  have hCi := A.nonneg.2.2.1
  have hCg := A.nonneg.2.2.2
  have key : ∀ ω, shiftedPiReg N κ (shiftConst N ρ ε c) (ξ ω) x t .iPsiCube =
      shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t .iPsiCube -
        (3 * c.1) * (shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t .iPsi +
          (shiftedPiGrad N ξ ω x 0 * shiftedPiMoment t x 0 +
            shiftedPiGrad N ξ ω x 1 * shiftedPiMoment t x 1 +
            shiftedPiGrad N ξ ω x 2 * shiftedPiMoment t x 2)) := fun ω => by
    rw [shiftedPi_reg_iPsiCube x (hξ.1 ω) (hgr ω) ht.1 rfl, Fin.sum_univ_three]
  refine ShiftMom.congr key ?_
  have a1 := A.mom (σ := .iPsiCube) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x
  have a2 := (A.momIPsi hW hε hξ hgr ht x).tpow hCi ht
    (e₁ := (homogeneity κ .iPsiCube + κbar) / 4) (by simp only [homogeneity]; linarith)
  have gm : ∀ k : Fin 3, ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k)
      (Cg * parabolicSemigroup.momentConst 1 * t ^ ((homogeneity κ .iPsiCube + κbar) / 4)) := by
    intro k
    have h0 := ShiftMom.mul_const (P := P) (shiftedPiMoment t x k) (A.grad1 hW hε hξ x k)
      (abs_shiftedPiMoment_le ht.1 x k) hCg
    have h1 : ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k)
        (Cg * parabolicSemigroup.momentConst 1 * t ^ (1 / 4 : ℝ)) :=
      h0.mono (le_of_eq (by ring))
    exact h1.tpow (by positivity) ht (by simp only [homogeneity]; linarith)
  have mg : ∀ k : Fin 3, Measurable fun ω => shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k :=
    fun k => (measurable_shiftedPiGrad hξ x k).mul_const _
  have s01 := (gm 0).add hq (mg 0) (mg 1) (gm 1) (by positivity) (by positivity)
  have s012 := s01.add hq ((mg 0).add (mg 1)) (mg 2) (gm 2) (by positivity) (by positivity)
  have s := a2.add hq (measurable_shiftedPiReg hξ hgr _ x ht.1 _)
    (((mg 0).add (mg 1)).add (mg 2)) s012 (by positivity) (by positivity)
  have s' := s.const_mul (3 * c.1) (B := 3 * B)
    (by rw [abs_mul]; norm_num; linarith [abs_fst_le_of_norm_le hc]) (by positivity)
  have := a1.sub hq (measurable_shiftedPiReg hξ hgr _ x ht.1 _)
    ((((measurable_shiftedPiReg hξ hgr _ x ht.1 _)).add (((mg 0).add (mg 1)).add (mg 2))).const_mul _)
    s' (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))

theorem shiftedPi_single_iPsiCubePsi (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg)
    (hq : 1 ≤ q) {B : ℝ} (hB : 0 ≤ B) :
    PiShiftSingleBound.{u} N ρ κ κbar q .iPsiCubePsi B (C1 + 3 * B * (C1 + 3 * (Cg * C2))) := by
  refine PiShiftSingleBound.of_shiftMom ?_
  intro Ω _ P W ε ξ c hc hW hε hξ hgr t ht x
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hC1 := A.nonneg.1
  have hC2 := A.nonneg.2.1
  have hCg := A.nonneg.2.2.2
  have key : ∀ ω, shiftedPiReg N κ (shiftConst N ρ ε c) (ξ ω) x t .iPsiCubePsi =
      shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t .iPsiCubePsi -
        (3 * c.1) * (shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t .iPsiPsi +
          (shiftedPiGrad N ξ ω x 0 *
              shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t (.psiX 0) +
            shiftedPiGrad N ξ ω x 1 *
              shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t (.psiX 1) +
            shiftedPiGrad N ξ ω x 2 *
              shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t (.psiX 2))) :=
    fun ω => by
    rw [shiftedPi_reg_iPsiCubePsi x (hξ.1 ω) (hgr ω) ht.1 rfl, Fin.sum_univ_three]
  refine ShiftMom.congr key ?_
  have a1 := A.mom (σ := .iPsiCubePsi) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x
  have a2 := (A.mom (σ := .iPsiPsi) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x).tpow hC1 ht
    (e₁ := (homogeneity κ .iPsiCubePsi + κbar) / 4) (by simp only [homogeneity]; linarith)
  have gm : ∀ k : Fin 3, ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k *
      shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t (.psiX k))
      (Cg * C2 * t ^ ((homogeneity κ .iPsiCubePsi + κbar) / 4)) := by
    intro k
    have hp := (A.mom2 (σ := .psiX k) (by simp) (by simp)
      (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x).tpow hC2 ht
      (e₁ := (homogeneity κ .iPsiCubePsi + κbar) / 4) (by simp only [homogeneity]; linarith)
    have h0 := ShiftMom.mul (measurable_shiftedPiGrad hξ x k)
      (measurable_shiftedPiReg hξ hgr _ x ht.1 _) (A.grad hW hε hξ x k) hp hCg
    exact h0.mono (le_of_eq (by ring))
  have mg : ∀ k : Fin 3, Measurable fun ω => shiftedPiGrad N ξ ω x k *
      shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t (.psiX k) :=
    fun k => (measurable_shiftedPiGrad hξ x k).mul (measurable_shiftedPiReg hξ hgr _ x ht.1 _)
  have s01 := (gm 0).add hq (mg 0) (mg 1) (gm 1) (by positivity) (by positivity)
  have s012 := s01.add hq ((mg 0).add (mg 1)) (mg 2) (gm 2) (by positivity) (by positivity)
  have s := a2.add hq (measurable_shiftedPiReg hξ hgr _ x ht.1 _)
    (((mg 0).add (mg 1)).add (mg 2)) s012 (by positivity) (by positivity)
  have s' := s.const_mul (3 * c.1) (B := 3 * B)
    (by rw [abs_mul]; norm_num; linarith [abs_fst_le_of_norm_le hc]) (by positivity)
  have := a1.sub hq (measurable_shiftedPiReg hξ hgr _ x ht.1 _)
    ((((measurable_shiftedPiReg hξ hgr _ x ht.1 _)).add (((mg 0).add (mg 1)).add (mg 2))).const_mul _)
    s' (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))


theorem shiftedPi_single_iPsiCubePsiSq (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg)
    (hq : 1 ≤ q) (hκb : κbar ≤ κ.1 / 2) {B : ℝ} (hB : 0 ≤ B) :
    PiShiftSingleBound.{u} N ρ κ κbar q .iPsiCubePsiSq B
      (C1 + B * C1 + 3 * B * C1 + 3 * B * (3 * (Cg * C2)) +
        3 * B ^ 2 * (Ci + 3 * (Cg * parabolicSemigroup.momentConst 1)) + 3 * B * C1) := by
  refine PiShiftSingleBound.of_shiftMom ?_
  intro Ω _ P W ε ξ c hc hW hε hξ hgr t ht x
  have ht0 : 0 < t := ht.1
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hM1 := parabolicSemigroup.momentConst_nonneg 1
  have hC1 := A.nonneg.1
  have hC2 := A.nonneg.2.1
  have hCi := A.nonneg.2.2.1
  have hCg := A.nonneg.2.2.2
  have hc1 := abs_fst_le_of_norm_le hc
  have hc2 := abs_snd_le_of_norm_le hc
  set R : Symbol → Ω → ℝ := fun σ ω =>
    shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t σ with hR
  have key : ∀ ω, shiftedPiReg N κ (shiftConst N ρ ε c) (ξ ω) x t .iPsiCubePsiSq =
      R .iPsiCubePsiSq ω - c.1 * R .iPsiCube ω - (3 * c.1) * R .iPsiPsiSq ω -
        (3 * c.1) * (shiftedPiGrad N ξ ω x 0 * R (.psiSqX 0) ω +
          shiftedPiGrad N ξ ω x 1 * R (.psiSqX 1) ω + shiftedPiGrad N ξ ω x 2 * R (.psiSqX 2) ω) +
        (3 * c.1 ^ 2) * (R .iPsi ω + (shiftedPiGrad N ξ ω x 0 * shiftedPiMoment t x 0 +
            shiftedPiGrad N ξ ω x 1 * shiftedPiMoment t x 1 +
            shiftedPiGrad N ξ ω x 2 * shiftedPiMoment t x 2)) -
        (3 * c.2) * R .psi ω := fun ω => by
    rw [shiftedPi_reg_iPsiCubePsiSq x (hξ.1 ω) (hgr ω) ht.1 rfl rfl, Fin.sum_univ_three,
      Fin.sum_univ_three]
  refine ShiftMom.congr key ?_
  have mR : ∀ σ, Measurable (R σ) := fun σ => measurable_shiftedPiReg hξ hgr _ x ht.1 σ
  have mg : ∀ k : Fin 3, Measurable fun ω => shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k :=
    fun k => (measurable_shiftedPiGrad hξ x k).mul_const _
  have mgR : ∀ k : Fin 3, Measurable fun ω => shiftedPiGrad N ξ ω x k * R (.psiSqX k) ω :=
    fun k => (measurable_shiftedPiGrad hξ x k).mul (mR _)
  have a1 := A.mom (σ := .iPsiCubePsiSq) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x
  have lift : ∀ {σ : Symbol} (h1 : σ ≠ .one) (hx : ∀ j, σ ≠ .x j)
      (hlt : homogeneity κ σ < gamma κ),
      (homogeneity κ .iPsiCubePsiSq + κbar) / 4 ≤ (homogeneity κ σ + κbar) / 4 →
      ShiftMom P q (R σ) (C1 * t ^ ((homogeneity κ .iPsiCubePsiSq + κbar) / 4)) :=
    fun h1 hx hlt he => (A.mom h1 hx hlt hW hε hξ hgr ht x).tpow hC1 ht he
  have b2 := lift (σ := .iPsiCube) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) (by simp only [homogeneity]; linarith)
  have b3 := lift (σ := .iPsiPsiSq) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) (by simp only [homogeneity]; linarith)
  have b6 := lift (σ := .psi) (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith) (by simp only [homogeneity]; linarith)
  have b5 := (A.momIPsi hW hε hξ hgr ht x).tpow hCi ht
    (e₁ := (homogeneity κ .iPsiCubePsiSq + κbar) / 4) (by simp only [homogeneity]; linarith)
  have gm : ∀ k : Fin 3, ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k)
      (Cg * parabolicSemigroup.momentConst 1 * t ^ ((homogeneity κ .iPsiCubePsiSq + κbar) / 4)) := by
    intro k
    have h0 := ShiftMom.mul_const (P := P) (shiftedPiMoment t x k) (A.grad1 hW hε hξ x k)
      (abs_shiftedPiMoment_le ht.1 x k) hCg
    have h1 : ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k)
        (Cg * parabolicSemigroup.momentConst 1 * t ^ (1 / 4 : ℝ)) :=
      h0.mono (le_of_eq (by ring))
    exact h1.tpow (by positivity) ht (by simp only [homogeneity]; linarith)
  have gr : ∀ k : Fin 3, ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k * R (.psiSqX k) ω)
      (Cg * C2 * t ^ ((homogeneity κ .iPsiCubePsiSq + κbar) / 4)) := by
    intro k
    have hp := (A.mom2 (σ := .psiSqX k) (by simp) (by simp)
      (by simp only [homogeneity, gamma]; linarith) hW hε hξ hgr ht x).tpow hC2 ht
      (e₁ := (homogeneity κ .iPsiCubePsiSq + κbar) / 4) (by simp only [homogeneity]; linarith)
    have h0 := ShiftMom.mul (measurable_shiftedPiGrad hξ x k) (mR _) (A.grad hW hε hξ x k) hp hCg
    exact h0.mono (le_of_eq (by ring))
  -- the three-term sums
  have sg01 := (gm 0).add hq (mg 0) (mg 1) (gm 1) (by positivity) (by positivity)
  have sg := sg01.add hq ((mg 0).add (mg 1)) (mg 2) (gm 2) (by positivity) (by positivity)
  have sr01 := (gr 0).add hq (mgR 0) (mgR 1) (gr 1) (by positivity) (by positivity)
  have sr := sr01.add hq ((mgR 0).add (mgR 1)) (mgR 2) (gr 2) (by positivity) (by positivity)
  -- the terms
  have t2 := b2.const_mul c.1 (B := B) hc1 (by positivity)
  have t3 := b3.const_mul (3 * c.1) (B := 3 * B)
    (by rw [abs_mul]; norm_num; linarith) (by positivity)
  have t4 := sr.const_mul (3 * c.1) (B := 3 * B)
    (by rw [abs_mul]; norm_num; linarith) (by positivity)
  have t5in := b5.add hq (mR _) (((mg 0).add (mg 1)).add (mg 2)) sg (by positivity) (by positivity)
  have t5 := t5in.const_mul (3 * c.1 ^ 2) (B := 3 * B ^ 2)
    (by
      rw [abs_mul, abs_pow]
      norm_num
      have h := sq_abs c.1
      nlinarith [abs_nonneg c.1, hc1]) (by positivity)
  have t6 := b6.const_mul (3 * c.2) (B := 3 * B)
    (by rw [abs_mul]; norm_num; linarith) (by positivity)
  have s1 := a1.sub hq (mR _) ((mR _).const_mul _) t2 (by positivity) (by positivity)
  have s2 := s1.sub hq ((mR _).sub ((mR _).const_mul _)) ((mR _).const_mul _) t3
    (by positivity) (by positivity)
  have s3 := s2.sub hq (((mR _).sub ((mR _).const_mul _)).sub ((mR _).const_mul _))
    ((((mgR 0).add (mgR 1)).add (mgR 2)).const_mul _) t4 (by positivity) (by positivity)
  have s4 := s3.add hq ((((mR _).sub ((mR _).const_mul _)).sub ((mR _).const_mul _)).sub
    ((((mgR 0).add (mgR 1)).add (mgR 2)).const_mul _))
    (((mR _).add (((mg 0).add (mg 1)).add (mg 2))).const_mul _) t5 (by positivity) (by positivity)
  have s5 := s4.sub hq (((((mR _).sub ((mR _).const_mul _)).sub ((mR _).const_mul _)).sub
    ((((mgR 0).add (mgR 1)).add (mgR 2)).const_mul _)).add
    (((mR _).add (((mg 0).add (mg 1)).add (mg 2))).const_mul _))
    ((mR _).const_mul _) t6 (by positivity) (by positivity)
  exact s5.mono (le_of_eq (by ring))

end RegularityStructures.Phi43

end
