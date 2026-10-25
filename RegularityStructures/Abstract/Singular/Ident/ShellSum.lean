/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Profile.Basic
public import RegularityStructures.Analysis.Heat.Schauder.DerivativeScaling
public import RegularityStructures.Abstract.Singular.Ident.LatticeLimit

/-!
# Summability of the shell integrals `∑_n ∫ |R̃f K_n(x − ·)|`

For a shell profile `h` supported in the unit ball and a point `x` with `x₀ > 0`:

* `R̃f` is bounded near `x` (`exists_abs_pointwiseReconstruct_le_near`);
* `∫ |K_n(x − y)| dy = (2^n)^{-2} ∫ |h|`, hence `∫ |R̃f(y) K_n(x − y)| dy ≤ B (2^n)^{-2} ∫ |h|` for
  large `n`, and the series of these integrals converges
  (`summable_integral_abs_pointwiseReconstruct_mul_shell`);
* for a causal `h` and every `y`, `n ↦ K_n(x − y)` is summable (`summable_scaledShell_of_causal`).
-/

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures

theorem summable_scaledShell_of_causal {h : ParabolicSpace → ℝ}
    (hs : ∀ z, 1 < parabolicNorm z → h z = 0) (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (z : ParabolicSpace) : Summable fun n : ℕ => scaledShell h n z := by
  by_cases hz : z.1 ≤ 0
  · have : (fun n : ℕ => scaledShell h n z) = fun _ => 0 := by
      funext n
      have h2 : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
      have : (parabolicDilate (2 ^ n) z).1 ≤ 0 := by
        simp only [parabolicDilate]
        have : (0 : ℝ) ≤ ((2 : ℝ) ^ n) ^ 2 := by positivity
        nlinarith
      simp [scaledShell, hc _ this]
    rw [this]; exact summable_zero
  · have hzpos : 0 < parabolicNorm z := by
      have h0 : 0 < z.1 := not_le.1 hz
      unfold parabolicNorm
      have : 0 < Real.sqrt |z.1| := Real.sqrt_pos.2 (abs_pos.2 h0.ne')
      have : 0 ≤ ∑ i, |z.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_inv_two_pow_lt hzpos)
    refine summable_of_ne_finset_zero (s := Finset.range N) fun n hn => ?_
    have hn' : N ≤ n := by simpa using hn
    refine scaledShell_eq_zero hs ?_
    have := hN n hn'
    simpa [inv_pow] using this

end RegularityStructures
