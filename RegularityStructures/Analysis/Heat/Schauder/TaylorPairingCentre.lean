/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorPairing
public import RegularityStructures.Analysis.Semigroup.Pairing.General
public import RegularityStructures.Analysis.Heat.Schauder.DerivativeReflect

/-!
# Pairing bound for reflected functions at the centre

`abs_pairing_reflect_le_centre`: the pairing bound for a function supported near the base point.

Source: [Hai14, proof of Lemma 5.19].
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem tendsto_and_abs_pairing_reflect_le_centre {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {x c : ParabolicSpace} {γ C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ) (hC : 0 ≤ C)
    (hloc : parabolicSemigroup.IsLocalOrder Λ x γ A C)
    {h : ParabolicSpace → ℝ} (hh : ContDiff ℝ ∞ h) {lam B₀ B₁ : ℝ} (hlam : 0 < lam)
    (hlam2 : lam ≤ 2) (hs : ∀ w, lam < parabolicNorm w → h w = 0)
    (h0 : ∫ w, |h w| ≤ B₀) (h1 : ∫ w, |parabolicGenerator h w| ≤ B₁ * lam ^ (-(4 : ℝ))) :
    Filter.Tendsto (fun s => ∫ y, Λ s y * h (c - y)) (nhdsWithin 0 (Ioi 0))
        (nhds (parabolicSemigroup.pairing Λ (fun z => h (c - z)))) ∧
      |parabolicSemigroup.pairing Λ (fun z => h (c - z))| ≤
        C * (∑ a ∈ A, pairingWeight a * (lam ^ a * (lam + parabolicNorm (c - x)) ^ (γ - a))) *
          (B₀ + B₁) := by
  set d := parabolicNorm (c - x) with hd
  have hd0 : 0 ≤ d := parabolicNorm_nonneg _
  set R := lam + d with hR
  have hR0 : 0 < R := by linarith
  have hB₀ : 0 ≤ B₀ := (integral_nonneg fun _ => abs_nonneg _).trans h0
  have hB₁ : 0 ≤ B₁ := by
    have h2 : 0 ≤ B₁ * lam ^ (-(4 : ℝ)) := (integral_nonneg fun _ => abs_nonneg _).trans h1
    exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hlam _)).1 h2
  have hφ : ContDiff ℝ ∞ (fun y => h (c - y)) := hh.comp (contDiff_const.sub contDiff_id)
  have hcs : ∀ g : ParabolicSpace → ℝ, (∀ w, lam < parabolicNorm w → g w = 0) →
      ∀ y, R < parabolicNorm (y - x) → g (c - y) = 0 := by
    intro g hg y hy
    refine hg _ ?_
    have h3 : parabolicNorm (y - x) ≤ parabolicNorm (y - c) + parabolicNorm (c - x) := by
      simpa using parabolicNorm_add_le (y - c) (c - x)
    rw [parabolicNorm_sub_comm]
    linarith
  have hcsup : HasCompactSupport (fun y => h (c - y)) :=
    hasCompactSupport_of_eq_zero hR0 x (hcs h hs)
  have hLcont : Continuous (parabolicGenerator (fun y => h (c - y))) :=
    continuous_parabolicGenerator hφ
  have hLeq : parabolicGenerator (fun y => h (c - y)) =
      fun y => parabolicGenerator h (c - y) := funext (parabolicGenerator_sub_left hh c)
  have hLs : ∀ y, R < parabolicNorm (y - x) →
      parabolicGenerator (fun y => h (c - y)) y = 0 := by
    intro y hy
    rw [hLeq]
    exact hcs (parabolicGenerator h) (fun w hw => parabolicGenerator_eq_zero_of_lt hs hw) y hy
  have hLsup : HasCompactSupport (parabolicGenerator (fun y => h (c - y))) :=
    hasCompactSupport_of_eq_zero hR0 x hLs
  have hgen := parabolicSemigroup_isGeneratorPair hφ hcsup
  have hA' : ∀ a ∈ A, -parabolicSemigroup.order < a := fun a ha => by
    simpa [parabolicSemigroup] using (hA a ha).1
  set B₁' := B₁ * lam ^ (-(4 : ℝ)) * R ^ (4 : ℝ) with hB₁'
  have hB₁'0 : 0 ≤ B₁' := by
    exact mul_nonneg (mul_nonneg hB₁ (Real.rpow_nonneg hlam.le (-(4 : ℝ))))
      (Real.rpow_nonneg hR0.le (4 : ℝ))
  have hRR : R ^ (4 : ℝ) * R ^ (-(4 : ℝ)) = 1 := by
    rw [← Real.rpow_add hR0]; simp
  set T : ℝ := (lam / 2) ^ (4 : ℝ) with hT
  have hT0 : 0 < T := Real.rpow_pos_of_pos (by positivity) _
  have hT1 : T ≤ 1 := Real.rpow_le_one (by positivity) (by linarith) (by norm_num)
  obtain ⟨L, hL, key⟩ := RegularisingSemigroup.LocalData.exists_tendsto_abs_le_of_time
    (K := parabolicSemigroup) parabolicSemigroup_isSymmetric
    parabolicSemigroup_isMetricScale parabolicSemigroup_isJointMeasurable
    (RegularisingSemigroup.LocalData.mk hΛ hΛm hC (fun a ha => (hA a ha).2) hloc) hA'
    (φ := fun y => h (c - y)) (ψ := parabolicGenerator (fun y => h (c - y))) (R := R)
    (B₀ := B₀) (B₁ := B₁') (T := T) hR0 hB₁'0
    ⟨hφ.continuous.measurable, hφ.continuous.integrable_of_hasCompactSupport hcsup,
      hcs h hs⟩
    ⟨hLcont.measurable, hLcont.integrable_of_hasCompactSupport hLsup, hLs⟩
    (by rw [integral_abs_sub_left]; exact h0)
    (by
      rw [hLeq]
      have := integral_abs_sub_left (parabolicGenerator h) c
      simp only [parabolicSemigroup]
      rw [this]
      refine h1.trans (le_of_eq ?_)
      rw [hB₁', mul_assoc (B₁ * lam ^ (-(4 : ℝ))), hRR, mul_one])
    hgen hT0 hT1
  have hpair : parabolicSemigroup.pairing Λ (fun z => h (c - z)) = L :=
    parabolicSemigroup.pairing_eq_of_tendsto hL
  rw [hpair]
  refine ⟨hL, key.trans ?_⟩
  have hord : parabolicSemigroup.order = 4 := rfl
  simp only [hord, RegularisingSemigroup.incrBound]
  have hβ : C * (B₁' * R ^ (-(4 : ℝ))) = C * (B₁ * lam ^ (-(4 : ℝ))) := by
    rw [hB₁', mul_assoc (B₁ * lam ^ (-(4 : ℝ))), hRR, mul_one]
  rw [hβ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    Finset.sum_mul]
  refine Finset.sum_le_sum fun a ha => ?_
  have hlt : -4 < a := (hA a ha).1
  have h1' : T ^ (a / 4) = (lam / 2) ^ a := timeTerm_eq hlam
  have h2' := incrTerm_eq hlam hlt
  have hrw : C * (B₁ * lam ^ (-(4 : ℝ))) * (T ^ (a / 4 + 1) / (a / 4 + 1) * R ^ (γ - a)) =
      C * B₁ * ((lam / 2) ^ a * R ^ (γ - a) * ((1 / 16) * (4 / (a + 4)))) := by
    have : C * (B₁ * lam ^ (-(4 : ℝ))) * (T ^ (a / 4 + 1) / (a / 4 + 1) * R ^ (γ - a)) =
        C * B₁ * ((T ^ (a / 4 + 1) / (a / 4 + 1) * lam ^ (-(4 : ℝ))) * R ^ (γ - a)) := by ring
    rw [this, hT, h2']
    ring
  have hpw : pairingWeight a * (lam ^ a * R ^ (γ - a)) = (1 + 4 / (a + 4)) *
      ((lam / 2) ^ a * R ^ (γ - a)) := by
    rw [pairingWeight, Real.div_rpow hlam.le (by norm_num), Real.rpow_neg (by norm_num)]
    have : (2 : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) a).ne'
    field_simp
  rw [hrw, hpw, h1']
  have hP : 0 ≤ (lam / 2) ^ a * R ^ (γ - a) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hR0.le _)
  have hv : 0 ≤ 4 / (a + 4) := div_nonneg (by norm_num) (by linarith)
  have := alg_term_le hC hP hB₀ hB₁ hv
  refine le_trans (le_of_eq ?_) this
  ring

theorem abs_pairing_reflect_le_centre {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {x c : ParabolicSpace} {γ C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ) (hC : 0 ≤ C)
    (hloc : parabolicSemigroup.IsLocalOrder Λ x γ A C)
    {h : ParabolicSpace → ℝ} (hh : ContDiff ℝ ∞ h) {lam B₀ B₁ : ℝ} (hlam : 0 < lam)
    (hlam2 : lam ≤ 2) (hs : ∀ w, lam < parabolicNorm w → h w = 0)
    (h0 : ∫ w, |h w| ≤ B₀) (h1 : ∫ w, |parabolicGenerator h w| ≤ B₁ * lam ^ (-(4 : ℝ))) :
    |parabolicSemigroup.pairing Λ (fun z => h (c - z))| ≤
      C * (∑ a ∈ A, pairingWeight a * (lam ^ a * (lam + parabolicNorm (c - x)) ^ (γ - a))) *
        (B₀ + B₁) :=
  (tendsto_and_abs_pairing_reflect_le_centre hΛ hΛm hA hC hloc hh hlam hlam2 hs h0 h1).2

end RegularityStructures

end
