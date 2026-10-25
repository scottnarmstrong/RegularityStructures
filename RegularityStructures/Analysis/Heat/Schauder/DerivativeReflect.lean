/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.Reflect
public import RegularityStructures.Analysis.Heat.Schauder.ReflectPairing
public import RegularityStructures.Analysis.Parabolic.TestFunctionExists

/-!
# Pairing bound for a reflected supported function, general local order

Version of `tendsto_and_abs_pairing_reflect_le` for `Λ` with `IsLocalOrder Λ x γ A C` (exponent set `A`,
order `γ`) instead of a single global exponent.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem abs_pairing_reflect_le_of_localOrder {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {x : ParabolicSpace} {γ C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ) (hC : 0 ≤ C)
    (hloc : parabolicSemigroup.IsLocalOrder Λ x γ A C)
    {h : ParabolicSpace → ℝ} (hh : ContDiff ℝ ∞ h) {lam B₀ B₁ : ℝ} (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hs : ∀ w, lam < parabolicNorm w → h w = 0)
    (h0 : ∫ w, |h w| ≤ B₀) (h1 : ∫ w, |parabolicGenerator h w| ≤ B₁ * lam ^ (-(4 : ℝ))) :
    |parabolicSemigroup.pairing Λ (fun y => h (x - y))| ≤
      C * parabolicSemigroup.pairingConst A * (B₀ + B₁) * lam ^ γ := by
  have hφ : ContDiff ℝ ∞ (fun y => h (x - y)) := hh.comp (contDiff_const.sub contDiff_id)
  have hcs : ∀ g : ParabolicSpace → ℝ, (∀ w, lam < parabolicNorm w → g w = 0) →
      ∀ y, lam < parabolicNorm (y - x) → g (x - y) = 0 := fun g hg y hy => by
    refine hg _ ?_
    rwa [parabolicNorm_sub_comm]
  have hcsup : HasCompactSupport (fun y => h (x - y)) :=
    hasCompactSupport_of_eq_zero hlam x (hcs h hs)
  have hLcont : Continuous (parabolicGenerator (fun y => h (x - y))) :=
    continuous_parabolicGenerator hφ
  have hLeq : parabolicGenerator (fun y => h (x - y)) =
      fun y => parabolicGenerator h (x - y) := funext (parabolicGenerator_sub_left hh x)
  have hLs : ∀ y, lam < parabolicNorm (y - x) → parabolicGenerator (fun y => h (x - y)) y = 0 := by
    intro y hy
    rw [hLeq]
    exact parabolicGenerator_eq_zero_of_lt hs (by rwa [parabolicNorm_sub_comm])
  have hLsup : HasCompactSupport (parabolicGenerator (fun y => h (x - y))) :=
    hasCompactSupport_of_eq_zero hlam x hLs
  have hgen := parabolicSemigroup_isGeneratorPair hφ hcsup
  have hA' : ∀ a ∈ A, -parabolicSemigroup.order < a ∧ a ≤ γ := fun a ha => by
    refine ⟨?_, (hA a ha).2⟩
    simpa [parabolicSemigroup] using (hA a ha).1
  exact parabolicSemigroup.abs_pairing_le parabolicSemigroup_isSymmetric
    parabolicSemigroup_isMetricScale parabolicSemigroup_isJointMeasurable hΛ hΛm hA' hC hloc
    (φ := fun y => h (x - y)) (ψ := parabolicGenerator (fun y => h (x - y))) (lam := lam)
    (B₀ := B₀) (B₁ := B₁) hlam hlam1 hφ.continuous.measurable hLcont.measurable
    (hφ.continuous.integrable_of_hasCompactSupport hcsup)
    (hLcont.integrable_of_hasCompactSupport hLsup) (fun y hy => hcs h hs y hy) hLs
    (by rw [integral_abs_sub_left]; exact h0)
    (by
      rw [hLeq]
      have := integral_abs_sub_left (parabolicGenerator h) x
      simp only [parabolicSemigroup]
      rw [this]; exact h1)
    hgen

end RegularityStructures

end
