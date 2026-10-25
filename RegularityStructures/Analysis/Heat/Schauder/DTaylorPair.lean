/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.DTaylorLinear
public import RegularityStructures.Analysis.Heat.Schauder.DTaylorLimit

/-!
# The pairing with `dTaylorKernel` splits

`pairing_dTaylorKernel_eq`: for `Λ` of local order `γ` at `x`,
`⟨Λ, K^{k,σ}_{n;xy}⟩ = ⟨Λ, D^k K_n(y - ·)⟩ - ∑_{l} c_l ⟨Λ, D^{k+l} K_n(x - ·)⟩`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace RegularityStructures

theorem pairing_dTaylorKernel_eq {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    {x y : ParabolicSpace} {γ C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ) (hC : 0 ≤ C)
    (hloc : parabolicSemigroup.IsLocalOrder Λ x γ A C) (k : Fin 4 →₀ ℕ) (n : ℕ) (σ : ℝ) :
    parabolicSemigroup.pairing Λ (dTaylorKernel h k n σ x y) =
      parabolicSemigroup.pairing Λ (fun z => lineIter (multiDirs k) (scaledShell h n) (y - z)) -
        ∑ l ∈ taylorIdx σ, coeffT (parabolicCoords (y - x)) l *
          parabolicSemigroup.pairing Λ
            (fun z => lineIter (multiDirs (k + l)) (scaledShell h n) (x - z)) := by
  classical
  have hLD : parabolicSemigroup.LocalData Λ x γ A C :=
    ⟨hΛ, hΛm, hC, fun a ha => (hA a ha).2, hloc⟩
  have hg := contDiff_scaledShell h0 n
  have hker : dTaylorKernel h k n σ x y = fun w =>
      lineIter (multiDirs k) (scaledShell h n) (y - w) - ∑ l ∈ taylorIdx σ,
        coeffT (parabolicCoords (y - x)) l *
          lineIter (multiDirs (k + l)) (scaledShell h n) (x - w) := by
    funext w
    simp only [dTaylorKernel, evalParabolic_monomial_div]
  have hcs : ∀ L : List ParabolicSpace, ∀ c : ParabolicSpace,
      Continuous (fun w => lineIter L (scaledShell h n) (c - w)) ∧
        HasCompactSupport (fun w => lineIter L (scaledShell h n) (c - w)) := fun L c =>
    ⟨(contDiff_lineIter hg L).continuous.comp (continuous_const.sub continuous_id),
      hasCompactSupport_reflect (hasCompactSupport_lineIter (hasCompactSupport_scaledShell
        (fun z hz => hs z hz) n) L) c⟩
  have hT0 := tendsto_dShell_centre hΛ hΛm h0 hs (y := y) hA hC hloc k n
  have hTl : ∀ l ∈ taylorIdx σ, Tendsto (fun s => ∫ z, Λ s z *
      lineIter (multiDirs (k + l)) (scaledShell h n) (x - z)) (nhdsWithin 0 (Ioi 0))
      (nhds (parabolicSemigroup.pairing Λ
        (fun z => lineIter (multiDirs (k + l)) (scaledShell h n) (x - z)))) := fun l _ =>
    (tendsto_and_abs_pairing_word_scaledShell_le hΛ hΛm h0 hs hA hC hloc
      ((Finsupp.toMultiset (k + l)).toList) n).1
  have hlim := tendsto_integral_sub_sum_right (F := taylorIdx σ)
    (fun l => coeffT (parabolicCoords (y - x)) l) hT0 hTl
    (fun s hs' => integrable_mul_of_hasCompactSupport hLD hs' (hcs _ _).1 (hcs _ _).2)
    (fun l _ s hs' => integrable_mul_of_hasCompactSupport hLD hs' (hcs _ _).1 (hcs _ _).2)
  rw [hker, parabolicSemigroup.pairing_eq_of_tendsto hlim]

end RegularityStructures

end
