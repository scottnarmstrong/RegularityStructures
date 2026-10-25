/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Consistency

/-!
# The auxiliary semigroup on `ℝ⁴` is conservative

* `parabolicSemigroup_isConservative`: `∫ q_t(x - y) dy = 1`
  ([Hos25, Definition 2.6 (ii)], arXiv:2310.07396v2);
* `exists_dist_lt_of_parabolicNorm_lt`: the parabolic size controls the Euclidean-type distance;
* `pairing_ofFunction_parabolicSemigroup`: for bounded continuous `g` and integrable `φ`, the
  pairing of the `Q`-distribution of `g` with `φ` is `∫ g φ`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem parabolicSemigroup_isConservative : parabolicSemigroup.IsConservative := by
  intro t ht x
  have h : ∀ y : ParabolicSpace, parabolicSemigroup.kernel t x y = parabolicKernel t (y - x) := by
    intro y
    show parabolicKernel t (x - y) = _
    rw [← parabolicKernel_neg t (y - x), neg_sub]
  simp_rw [h]
  rw [Measure.volume_eq_prod]
  rw [integral_sub_right_eq_self (fun w : ParabolicSpace => parabolicKernel t w) x]
  rw [← Measure.volume_eq_prod]
  exact integral_parabolicKernel ht

/-- A small parabolic size forces a small distance in `ℝ × (Fin 3 → ℝ)`. -/
theorem parabolicNorm_lt_imp_dist_lt {z : ParabolicSpace} {η : ℝ} (hη : 0 < η)
    (hz : parabolicNorm z < min η 1) : ‖z‖ < η := by
  have h1 : Real.sqrt |z.1| < min η 1 := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (z.2 i))
    unfold parabolicNorm at hz
    linarith
  have hm : min η 1 ≤ 1 := min_le_right _ _
  have hmη : min η 1 ≤ η := min_le_left _ _
  have hz1 : |z.1| < η := by
    have h2 : |z.1| < (min η 1) ^ 2 := by
      have := Real.sq_sqrt (abs_nonneg z.1)
      nlinarith [Real.sqrt_nonneg |z.1|]
    nlinarith [lt_min hη one_pos]
  have hz2 : ∀ i, |z.2 i| < η := by
    intro i
    have := Finset.single_le_sum (f := fun i => |z.2 i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
    have := Real.sqrt_nonneg |z.1|
    unfold parabolicNorm at hz
    linarith
  rw [Prod.norm_def, max_lt_iff]
  refine ⟨by simpa using hz1, (pi_norm_lt_iff hη).2 fun i => by simpa using hz2 i⟩

theorem parabolicSemigroup_continuity {g : ParabolicSpace → ℝ} (hg : Continuous g)
    (x : ParabolicSpace) :
    ∀ ε > 0, ∃ δ > 0, ∀ y, parabolicSemigroup.scaleDist y x < δ → |g y - g x| < ε := by
  intro ε hε
  obtain ⟨η, hη, h⟩ := Metric.continuousAt_iff.1 hg.continuousAt ε hε
  refine ⟨min η 1, lt_min hη one_pos, fun y hy => ?_⟩
  have := parabolicNorm_lt_imp_dist_lt hη hy
  have hd : dist y x < η := by rw [dist_eq_norm]; exact this
  simpa [Real.dist_eq] using h hd

end RegularityStructures

end
