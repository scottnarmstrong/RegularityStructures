/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateModulusAll
public import Phi43.Stochastic.ConstantsRateMemLp
public import Phi43.Stochastic.ConstantsRateMassiveIncrement
public import Phi43.Stochastic.ConstantsRateHairerTorus
public import Phi43.Stochastic.ConstantsComparisonKernelLp

/-!
# `L^{3/2}` translation moduli of the massive and Hairer kernels

Both kernels satisfy `|f| ≲ size⁻³` and `|f(· - h) - f| ≲ size(h) size⁻⁴` away from the origin, so
their `L^{3/2}` translation modulus has exponent `1/2` for `∫ ‖f(· - h) - f‖^{3/2}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

theorem constantsRate_massive_memLp :
    MemLp massiveHeatKernel (ENNReal.ofReal (3 / 2)) := by
  obtain ⟨C, hC, hG⟩ := massiveHeatKernel_global_singular_bound
  refine constantsRate_memLp_of_bound measurable_massiveHeatKernel (q := 3 / 2) (a := 3)
    (A := C) (by norm_num) hC (by norm_num) (by norm_num) ?_
  filter_upwards [] with z hz
  rw [abs_of_nonneg (massiveHeatKernel_nonneg z)]
  exact hG z hz

theorem constantsRate_hairer_memLp (N : ℕ) :
    MemLp (hairerKernelTorus N) (ENNReal.ofReal (3 / 2)) := by
  obtain ⟨C, hC, hK⟩ := constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  refine constantsRate_memLp_of_bound (measurable_constantsComparison_hairerKernelTorus N)
    (q := 3 / 2) (a := 3) (A := C) (by norm_num) hC (by norm_num) (by norm_num) ?_
  filter_upwards [] with z hz
  exact hK hz

theorem constantsRate_massive_modulus :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : SpaceTime, 0 < torusParabolicSize h →
      ∫⁻ z, ‖massiveHeatKernel (z - h) - massiveHeatKernel z‖ₑ ^ (3 / 2 : ℝ) ≤
        ENNReal.ofReal (C * torusParabolicSize h ^ (1 / 2 : ℝ)) := by
  obtain ⟨A, hA, hG⟩ := massiveHeatKernel_global_singular_bound
  obtain ⟨B, hB, hinc⟩ := constantsRate_massive_increment
  have hmod := constantsRate_translation_modulus (f := massiveHeatKernel)
    measurable_massiveHeatKernel (q := 3 / 2) (a := 3) (A := A) (c := 4) (B := B) (θ := 1)
    (κ := 64) (r₀ := 1 / 16) (by norm_num) (by norm_num) (by norm_num) hA (by norm_num) hB
    (by norm_num) (by norm_num)
    (by
      filter_upwards [constantsRate_ae_size_pos] with z hz
      intro _
      rw [abs_of_nonneg (massiveHeatKernel_nonneg z)]
      exact hG z hz)
    (by
      intro h hh
      filter_upwards [constantsRate_ae_size_pos] with z hz hzh
      simpa [Real.rpow_one] using hinc z h hz hzh hh)
  obtain ⟨C, hC, hC'⟩ := hmod
  have hmem := constantsRate_massive_memLp
  have hall := constantsRate_modulus_all (f := massiveHeatKernel) measurable_massiveHeatKernel
    (q := 3 / 2) (by norm_num) hmem (C := C) (γ := min (5 - 3 * (3 / 2)) (1 * (3 / 2) + 5 - 4 * (3 / 2)))
    (r₀ := 1 / 16) hC (by norm_num) (by norm_num) hC'
  obtain ⟨C', hC'0, hC''⟩ := hall
  refine ⟨C', hC'0, fun h hh => ?_⟩
  have := hC'' h hh
  have hγ : min (5 - 3 * (3 / 2) : ℝ) (1 * (3 / 2) + 5 - 4 * (3 / 2)) = 1 / 2 := by norm_num
  rwa [hγ] at this

theorem constantsRate_hairer_modulus (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : SpaceTime, 0 < torusParabolicSize h →
      ∫⁻ z, ‖hairerKernelTorus N (z - h) - hairerKernelTorus N z‖ₑ ^ (3 / 2 : ℝ) ≤
        ENNReal.ofReal (C * torusParabolicSize h ^ (1 / 2 : ℝ)) := by
  obtain ⟨A, hA, hK⟩ := constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  obtain ⟨B, hB, hinc⟩ := constantsRate_hairerKernelTorus_increment N
  have hmod := constantsRate_translation_modulus (f := hairerKernelTorus N)
    (measurable_constantsComparison_hairerKernelTorus N) (q := 3 / 2) (a := 3) (A := A)
    (c := 4) (B := B) (θ := 1) (κ := 64) (r₀ := 1 / 16) (by norm_num) (by norm_num)
    (by norm_num) hA (by norm_num) hB (by norm_num) (by norm_num)
    (by
      filter_upwards [constantsRate_ae_size_pos] with z hz
      intro _
      exact hK hz)
    (by
      intro h hh
      filter_upwards [constantsRate_ae_size_pos] with z hz hzh
      have hr0 : 0 ≤ torusParabolicSize h := torusParabolicSize_nonneg h
      simpa [Real.rpow_one] using hinc z h hz (by linarith))
  obtain ⟨C, hC, hC'⟩ := hmod
  have hmem := constantsRate_hairer_memLp N
  have hall := constantsRate_modulus_all (f := hairerKernelTorus N)
    (measurable_constantsComparison_hairerKernelTorus N)
    (q := 3 / 2) (by norm_num) hmem (C := C)
    (γ := min (5 - 3 * (3 / 2)) (1 * (3 / 2) + 5 - 4 * (3 / 2)))
    (r₀ := 1 / 16) hC (by norm_num) (by norm_num) hC'
  obtain ⟨C', hC'0, hC''⟩ := hall
  refine ⟨C', hC'0, fun h hh => ?_⟩
  have := hC'' h hh
  have hγ : min (5 - 3 * (3 / 2) : ℝ) (1 * (3 / 2) + 5 - 4 * (3 / 2)) = 1 / 2 := by norm_num
  rwa [hγ] at this

end RegularityStructures.Phi43

end
