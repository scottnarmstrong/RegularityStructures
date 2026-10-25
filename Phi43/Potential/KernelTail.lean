/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.PairingGeneric
public import Phi43.Structure.CanonicalKernelHairer
public import RegularityStructures.Analysis.Heat.Kernel

/-!
# The kernel `K` away from small lags is a smooth kernel of range `1`

With the lag cutoff `potCutoff` (`= 1` on `t ≤ 1/8`, `= 0` on `t ≥ 1/4`), the kernel
`(1 - potCutoff t) K_N(t, x)` of `hairerKernel N = ∑ₙ annShellC N n` is smooth (the singularity of
`K_N` sits at the origin, where the factor vanishes) and vanishes outside the unit parabolic ball
(`isUnitKernel_potTail`).  By `abs_potConv_le` the convolution of the noise with it is bounded by
the model constants: the "smooth part" of the decomposition of `K ∗ f`.
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Potential

/-- The smooth lag cutoff: `1` for `t ≤ 1/8`, `0` for `t ≥ 1/4`. -/
def potCutoff (t : ℝ) : ℝ := Real.smoothTransition (2 - 8 * t)

/-- The large-lag part `(1 - χ(t)) K_N(t, x)` of the kernel. -/
def potTail (N : ℕ) (z : ParabolicSpace) : ℝ :=
  (1 - potCutoff z.1) * Phi43.hairerKernel N z

end RegularityStructures.Potential

end

public section

open Filter Topology Set

namespace RegularityStructures.Potential

theorem contDiff_potCutoff : ContDiff ℝ ∞ potCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))

theorem potCutoff_eq_one {t : ℝ} (ht : t ≤ 1 / 8) : potCutoff t = 1 :=
  by unfold potCutoff; exact Real.smoothTransition.one_of_one_le (by linarith)

theorem potCutoff_eq_zero {t : ℝ} (ht : 1 / 4 ≤ t) : potCutoff t = 0 :=
  by unfold potCutoff; exact Real.smoothTransition.zero_of_nonpos (by linarith)

theorem potCutoff_nonneg (t : ℝ) : 0 ≤ potCutoff t := Real.smoothTransition.nonneg _

theorem potCutoff_le_one (t : ℝ) : potCutoff t ≤ 1 := Real.smoothTransition.le_one _

theorem hairerKernel_eq_zero_of_one_lt (N : ℕ) {z : ParabolicSpace} (hz : 1 < parabolicNorm z) :
    Phi43.hairerKernel N z = 0 := by
  unfold Phi43.hairerKernel
  refine (tsum_congr fun n => annShellC_eq_zero (N := N) (n := n) ?_).trans tsum_zero
  exact lt_of_le_of_lt (pow_le_one₀ (by norm_num) (by norm_num)) hz

theorem contDiffAt_hairerKernel_of_pos (N : ℕ) {z : ParabolicSpace} (hz : 0 < z.1) :
    ContDiffAt ℝ ∞ (Phi43.hairerKernel N) z := by
  have hev : Phi43.hairerKernel N =ᶠ[𝓝 z] fun w => heatKernelR4 w - annRemainderC N w := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz] with w hw
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact lt_irrefl _ hw
    exact Phi43.hairerKernel_eq_heat_sub_remainder hw0
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (contDiffAt_heatKernelR4_of_pos hz).sub (contDiff_annRemainderC N).contDiffAt

theorem contDiff_potTail (N : ℕ) : ContDiff ℝ ∞ (potTail N) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.1 < 1 / 8
  · have hev : potTail N =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with w hw
      simp [potTail, potCutoff_eq_one hw.le]
    exact (contDiffAt_const).congr_of_eventuallyEq hev
  · have hz' : 0 < z.1 := by linarith [not_lt.1 hz]
    exact ((contDiff_const.sub (contDiff_potCutoff.comp contDiff_fst)).contDiffAt).mul
      (contDiffAt_hairerKernel_of_pos N hz')

/-- The large-lag part of `K_N` is a smooth kernel supported in the unit parabolic ball. -/
theorem isUnitKernel_potTail (N : ℕ) : IsUnitKernel (potTail N) where
  smooth := contDiff_potTail N
  supp w hw := by rw [potTail, hairerKernel_eq_zero_of_one_lt N hw, mul_zero]

end RegularityStructures.Potential

end
