/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.Reflect
public import RegularityStructures.Analysis.Parabolic.GeneratorScaling
public import RegularityStructures.Analysis.Kernel.GeneratorIdentity
public import RegularityStructures.Analysis.Semigroup.Pairing.Main
public import RegularityStructures.Analysis.Semigroup.Pairing.Limit
public import RegularityStructures.Analysis.Parabolic.TestFunctionExists

/-!
# Pairing bound for reflected supported functions

`tendsto_and_abs_pairing_reflect_le`: existence and bound of the pairing of a `Q`-distribution with a
smooth function supported in a small parabolic ball.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

/-- **Pairing bound for a reflected supported function.** `h` is smooth, vanishes outside the
parabolic ball of radius `lam ≤ 1`, `∫ |h| ≤ B₀`, `∫ |L h| ≤ B₁ lam^{-4}`; `Λ` is a distribution
of global order `α`. -/
theorem tendsto_and_abs_pairing_reflect_le {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {α C : ℝ} (hα : -4 < α) (hC : 0 ≤ C)
    (hloc : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / 4))
    {h : ParabolicSpace → ℝ} (hh : ContDiff ℝ ∞ h) {lam B₀ B₁ : ℝ} (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hs : ∀ w, lam < parabolicNorm w → h w = 0)
    (h0 : ∫ w, |h w| ≤ B₀) (h1 : ∫ w, |parabolicGenerator h w| ≤ B₁ * lam ^ (-(4 : ℝ)))
    (x : ParabolicSpace) :
    Filter.Tendsto (fun s => ∫ y, Λ s y * h (x - y)) (nhdsWithin 0 (Ioi 0))
        (nhds (parabolicSemigroup.pairing Λ (fun y => h (x - y)))) ∧
      |parabolicSemigroup.pairing Λ (fun y => h (x - y))| ≤
        C * (1 + 4 / (α + 4)) * (B₀ + B₁) * lam ^ α := by
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
  have hA : ∀ a ∈ ({α} : Finset ℝ), -parabolicSemigroup.order < a ∧ a ≤ α := by
    intro a ha
    rw [Finset.mem_singleton] at ha
    subst ha
    exact ⟨by simpa [parabolicSemigroup] using hα, le_rfl⟩
  have hlocal : parabolicSemigroup.IsLocalOrder Λ x α {α} C := by
    intro u hu y
    simp only [Finset.sum_singleton, sub_self, Real.rpow_zero, mul_one]
    simpa [parabolicSemigroup] using hloc u hu y
  have key := parabolicSemigroup.abs_pairing_le parabolicSemigroup_isSymmetric
    parabolicSemigroup_isMetricScale parabolicSemigroup_isJointMeasurable hΛ hΛm hA hC hlocal
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
  have key2 := parabolicSemigroup.tendsto_integral_pairing parabolicSemigroup_isSymmetric
    parabolicSemigroup_isMetricScale parabolicSemigroup_isJointMeasurable hΛ hΛm hA hC hlocal
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
  refine ⟨?_, ?_⟩
  · exact key2
  · simpa [RegularisingSemigroup.pairingConst, parabolicSemigroup] using key

end RegularityStructures

end
