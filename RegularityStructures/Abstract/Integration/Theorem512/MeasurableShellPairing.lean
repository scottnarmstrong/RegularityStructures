/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.MeasPairing
public import RegularityStructures.Abstract.Integration.Theorem512.Sup
public import RegularityStructures.Abstract.Integration.Theorem512.SupBound
public import RegularityStructures.Analysis.Heat.Schauder.TaylorSplit
public import RegularityStructures.Analysis.Heat.Schauder.Derivative
public import RegularityStructures.Analysis.Heat.Schauder.DerivativePairing

/-!
# Measurability of the shell pairings

`measurable_derivShellPairing`: the pairing of a jointly measurable family with the derivatives of the
shells is measurable in the base point.

Source: [Hai14, Theorem 5.12].
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace RegularityStructures

theorem measurable_derivShellPairing {Λ : ParabolicSpace → ℝ → ParabolicSpace → ℝ}
    (hΛ : ∀ x, Λ x ∈ parabolicSemigroup.distributions)
    (hΛm : ∀ s, 0 < s → Measurable fun p : ParabolicSpace × ParabolicSpace => Λ p.1 s p.2)
    {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    {γ C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ) (hC : 0 ≤ C)
    (hloc : ∀ x, parabolicSemigroup.IsLocalOrder (Λ x) x γ A C) (k : Fin 4 →₀ ℕ) (n : ℕ) :
    Measurable fun x => derivShellPairing (Λ x) h k x n := by
  have hg : ContDiff ℝ ∞ (lineIter (multiDirs k) (scaledShell h n)) :=
    contDiff_lineIter (contDiff_scaledShell h0 n) _
  have hF : ∀ m : ℕ, Measurable fun x => ∫ z, Λ x (1 / ((m : ℝ) + 1)) z *
      lineIter (multiDirs k) (scaledShell h n) (x - z) := by
    intro m
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hm : Measurable fun p : ParabolicSpace × ParabolicSpace =>
        Λ p.1 (1 / ((m : ℝ) + 1)) p.2 *
          lineIter (multiDirs k) (scaledShell h n) (p.1 - p.2) :=
      (hΛm _ hpos).mul (hg.continuous.comp (continuous_fst.sub continuous_snd)).measurable
    exact (hm.stronglyMeasurable.integral_prod_right (ν := volume)).measurable
  refine measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.2 fun x => ?_)
  have key := (tendsto_and_abs_pairing_word_scaledShell_le (hΛ x)
    (fun u hu => (hΛm u hu).comp measurable_prodMk_left) h0 hs hA hC (hloc x)
    (Finsupp.toMultiset k).toList n).1
  have hseq : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun m => by
        show (0 : ℝ) < 1 / ((m : ℝ) + 1)
        positivity⟩
  exact key.comp hseq

end RegularityStructures

end
