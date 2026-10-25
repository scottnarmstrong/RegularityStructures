/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.TaylorQuant
public import RegularityStructures.Abstract.Singular.Remainder.RemKernelG

/-!
# Lipschitz dependence of `⟨R f, D^k R(x − ·)⟩` on `x`

For `x₀, x₀' ≤ T ≤ 1` with `‖x − x'‖ ≤ 1`,
`|⟨R f, D^k R(x − ·)⟩ − ⟨R f, D^k R(x' − ·)⟩| ≤ C K₀ Cf ‖x − x'‖`
(`exists_abs_remPairing_sub_le_growth`).  The difference of the two test functions is the kernel
`u ↦ D^k R(u + (x − x')) − D^k R(u)` at `x' − ·`, whose derivatives are `≲ ‖x − x'‖` times the
spatial decay by the mean value inequality.
-/

public section

open scoped ContDiff
open Filter Topology

namespace RegularityStructures

theorem RemKernel.exists_isRemKernel_sub_shift {r : ParabolicSpace → ℝ} (hr : RemKernel r)
    (k : Fin 4 →₀ ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ δ : ParabolicSpace, ‖δ‖ ≤ 1 →
      IsRemKernel (fun u => lineIter (multiDirs k) r (u + δ) -
        lineIter (multiDirs k) r u) (c * ‖δ‖) := by
  obtain ⟨BG, hBG0, hBG⟩ := hr.exists_remDecay_lineIter k 5 4
  set G : ParabolicSpace → ℝ := lineIter (multiDirs k) r with hG
  have hGs : ContDiff ℝ ∞ G := contDiff_lineIter hr.contDiff _
  refine ⟨(2 + 6 * (1 : ℝ) ^ 2) ^ 3 * BG, by positivity, fun δ hδ => ⟨?_, by positivity,
    fun i hi u hu => ?_⟩⟩
  · exact (hGs.comp (contDiff_id.add contDiff_const)).sub hGs
  · have hsh : ContDiff ℝ ∞ (fun u => G (u + δ)) := hGs.comp (contDiff_id.add contDiff_const)
    have e : iteratedFDeriv ℝ i (fun u => G (u + δ) - G u) u =
        iteratedFDeriv ℝ i G (u + δ) - iteratedFDeriv ℝ i G u := by
      have := iteratedFDeriv_sub_apply (x := u) (i := i) (f := fun u => G (u + δ)) (g := G)
        (hsh.contDiffAt.of_le (by exact_mod_cast le_top))
        (hGs.contDiffAt.of_le (by exact_mod_cast le_top))
      rw [show (fun u => G (u + δ) - G u) = (fun u => G (u + δ)) - G from rfl, this,
        iteratedFDeriv_comp_add_right]
    rw [e]
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ i G) :=
      hGs.differentiable_iteratedFDeriv (m := i) (by exact_mod_cast ENat.natCast_lt_top _)
    have hb : ∀ w ∈ Metric.closedBall u 1,
        ‖fderiv ℝ (iteratedFDeriv ℝ i G) w‖ ≤ (2 + 6 * (1 : ℝ) ^ 2) ^ 3 * BG * remWt u.2 := by
      intro w hw
      rw [norm_fderiv_iteratedFDeriv]
      have hw1 : ‖w - u‖ ≤ 1 := by simpa [dist_eq_norm] using hw
      have hwt : w.1 ≤ 4 := by
        have := (abs_le.1 ((abs_fst_sub_le_norm w u).trans hw1)).2
        linarith
      refine (hBG (i + 1) (by omega) w hwt).trans ?_
      have hrw : remWt w.2 ≤ (2 + 6 * (1 : ℝ) ^ 2) ^ 3 * remWt u.2 :=
        remWt_le_mul_remWt fun j => (abs_snd_sub_le_norm u w j).trans (by rw [norm_sub_rev]; exact hw1)
      calc BG * remWt w.2 ≤ BG * ((2 + 6 * (1 : ℝ) ^ 2) ^ 3 * remWt u.2) :=
            mul_le_mul_of_nonneg_left hrw hBG0
        _ = _ := by ring
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := iteratedFDeriv ℝ i G) (s := Metric.closedBall u 1) (x := u) (y := u + δ)
      (fun w _ => hdiff w) hb (convex_closedBall u 1) (Metric.mem_closedBall_self zero_le_one)
      (by simpa [dist_eq_norm] using hδ)
    refine this.trans (le_of_eq ?_)
    rw [add_sub_cancel_left]
    ring

end RegularityStructures

end
