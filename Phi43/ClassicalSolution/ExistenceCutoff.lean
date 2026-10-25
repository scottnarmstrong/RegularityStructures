/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution
public import RegularityStructures.PDE.MildSmooth
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The truncated cubic nonlinearity

For `K > 0` let `χ_K` be a smooth bump on `ℝ` with `χ_K = 1` on `[-K, K]` and `χ_K = 0` outside
`(-K-1, K+1)`. The truncated nonlinearity
`G(t, x, v) = χ_K(v) (-v³ + c v) + f(t, x)`
is smooth and globally Lipschitz in `v`, and coincides with `-v³ + c v + f(t, x)` for `|v| ≤ K`.
Mild solutions for `G` exist on every bounded time interval; the maximum principle shows that they
never leave the region where the truncation is inactive.
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures.PDE

/-- A smooth bump on `ℝ` equal to one on `[-K, K]` and supported in `(-K-1, K+1)`. -/
def cubicCutoff (K : ℝ) (hK : 0 < K) : ContDiffBump (0 : ℝ) :=
  ⟨K, K + 1, hK, by linarith⟩

/-- The truncated cubic `v ↦ χ_K(v) (-v³ + c v)`. -/
def truncCubic (c K : ℝ) (hK : 0 < K) (v : ℝ) : ℝ :=
  cubicCutoff K hK v * (-v ^ 3 + c * v)

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

open RegularityStructures.PDE Set Filter Topology

theorem truncCubic_eq {c K : ℝ} (hK : 0 < K) {v : ℝ} (hv : |v| ≤ K) :
    truncCubic c K hK v = -v ^ 3 + c * v := by
  rw [truncCubic, (cubicCutoff K hK).one_of_mem_closedBall, one_mul]
  rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero]

theorem truncCubic_eq_mul (c K : ℝ) (hK : 0 < K) :
    truncCubic c K hK = ⇑(cubicCutoff K hK) * fun v => -v ^ 3 + c * v := rfl

theorem contDiff_truncCubic (c K : ℝ) (hK : 0 < K) : ContDiff ℝ ∞ (truncCubic c K hK) := by
  rw [truncCubic_eq_mul]
  exact (cubicCutoff K hK).contDiff.mul ((contDiff_id.pow 3).neg.add (contDiff_const.mul contDiff_id))

theorem exists_lipschitzWith_truncCubic (c K : ℝ) (hK : 0 < K) :
    ∃ L, LipschitzWith L (truncCubic c K hK) := by
  have hsupp : HasCompactSupport (truncCubic c K hK) := by
    rw [truncCubic_eq_mul]
    exact (cubicCutoff K hK).hasCompactSupport.mul_right
  exact (contDiff_truncCubic c K hK).lipschitzWith_of_hasCompactSupport hsupp (by simp)

/-- A function on `ℝ × T³` with a smooth (hence continuous) lift is continuous. -/
theorem continuous_of_isSmoothOnSpaceTime {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) :
    Continuous f := by
  have hq : IsOpenQuotientMap (Prod.map (id : ℝ → ℝ) torusProj) :=
    IsOpenQuotientMap.id.prodMap isOpenQuotientMap_torusProj
  rw [hq.isQuotientMap.continuous_iff]
  exact hf.continuous

end RegularityStructures.Phi43

end

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures.PDE

/-- The truncated nonlinearity `(t, x, v) ↦ χ_K(v) (-v³ + c v) + f(t, x)`. -/
def cutoffNonlin (c K : ℝ) (hK : 0 < K) {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) :
    C(ℝ × Torus3 × ℝ, ℝ) :=
  ⟨fun p => truncCubic c K hK p.2.2 + f (p.1, p.2.1),
    ((contDiff_truncCubic c K hK).continuous.comp (continuous_snd.comp continuous_snd)).add
      ((continuous_of_isSmoothOnSpaceTime hf).comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))⟩

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

open RegularityStructures.PDE Set Filter Topology
open scoped NNReal

theorem cutoffNonlin_apply (c K : ℝ) (hK : 0 < K) {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (s : ℝ) (x : Torus3) (v : ℝ) :
    cutoffNonlin c K hK hf (s, x, v) = truncCubic c K hK v + f (s, x) := rfl

theorem contDiff_nonlinLift_cutoffNonlin (c K : ℝ) (hK : 0 < K) {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) : ContDiff ℝ ∞ (nonlinLift (cutoffNonlin c K hK hf)) := by
  have h : nonlinLift (cutoffNonlin c K hK hf) = fun p : ℝ × (Fin 3 → ℝ) × ℝ =>
      truncCubic c K hK p.2.2 + (fun q : ℝ × (Fin 3 → ℝ) => f (q.1, torusProj q.2)) (p.1, p.2.1) :=
    rfl
  rw [h]
  exact ((contDiff_truncCubic c K hK).comp (contDiff_snd.comp contDiff_snd)).add
    (hf.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)))

theorem exists_lipschitzWith_cutoffNonlin (c K : ℝ) (hK : 0 < K) {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) :
    ∃ L : ℝ≥0, ∀ s x, LipschitzWith L fun v => cutoffNonlin c K hK hf (s, x, v) := by
  obtain ⟨L, hL⟩ := exists_lipschitzWith_truncCubic c K hK
  refine ⟨L, fun s x => LipschitzWith.of_dist_le_mul fun v v' => ?_⟩
  simp only [cutoffNonlin_apply, dist_add_right]
  exact hL.dist_le_mul v v'

/-- The cubic dominates bounded forcing at large amplitude: if `R = |c| + B + 1` and
`|φ| ≤ B`, then `-v³ + c v + φ < 0` for `v ≥ R`. -/
theorem cubic_add_neg {c B φ v : ℝ} (hφ : |φ| ≤ B) (hv : |c| + B + 1 ≤ v) :
    -v ^ 3 + c * v + φ < 0 := by
  have hB : 0 ≤ B := (abs_nonneg φ).trans hφ
  have hv1 : 1 ≤ v := by linarith [abs_nonneg c]
  have hc : c * v ≤ |c| * v := mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith)
  have hφ' : φ ≤ B := (le_abs_self φ).trans hφ
  have hvv : v ≤ v ^ 2 := by nlinarith
  have h1 : v * (B + 1) ≤ v * (v - |c|) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : B + 1 ≤ v * (B + 1) := by nlinarith
  nlinarith

/-- The mirror statement: `-v³ + c v + φ > 0` for `v ≤ -R`. -/
theorem cubic_add_pos {c B φ v : ℝ} (hφ : |φ| ≤ B) (hv : v ≤ -(|c| + B + 1)) :
    0 < -v ^ 3 + c * v + φ := by
  have h := cubic_add_neg (c := c) (B := B) (φ := -φ) (v := -v) (by rwa [abs_neg]) (by linarith)
  linarith [show (-v) ^ 3 = -v ^ 3 by ring]

end RegularityStructures.Phi43

end
