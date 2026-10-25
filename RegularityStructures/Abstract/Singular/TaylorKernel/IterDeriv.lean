/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition.LineIter
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Norms of iterated derivatives via directional derivatives

For smooth `f : ParabolicSpace → ℝ`, `iteratedFDeriv ℝ j f u (m)` is the iterated directional
derivative `lineIter (List.ofFn m) f u`. Consequently `‖iteratedFDeriv ℝ j f u‖` is controlled by
the sup of `|lineIter L f u|` over lists `L` of `j` directions of norm `≤ 1`
(`norm_iteratedFDeriv_le_of_lineIter`), and conversely
(`abs_lineIter_le_norm_iteratedFDeriv`).

Source: [Hai14] = arXiv:1303.5113v4, §2 (scaled derivative bounds).
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem iteratedFDeriv_apply_eq_lineIter {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) {j : ℕ}
    (m : Fin j → ParabolicSpace) (u : ParabolicSpace) :
    iteratedFDeriv ℝ j f u m = lineIter (List.ofFn m) f u := by
  have h := congrFun (iteratedFDeriv_get_eq_lineIter hf (List.ofFn m)) u
  rw [← h]
  have key : ∀ (j' : ℕ) (hj : j' = j) (g : Fin j' → ParabolicSpace),
      iteratedFDeriv ℝ j' f u g = iteratedFDeriv ℝ j f u (g ∘ Fin.cast hj.symm) := by
    intro j' hj g
    subst hj
    rfl
  rw [key _ (List.length_ofFn)]
  congr 1
  funext i
  simp

theorem abs_lineIter_le_norm_iteratedFDeriv {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : List ParabolicSpace) (hL : ∀ d ∈ L, ‖d‖ ≤ 1) (u : ParabolicSpace) :
    |lineIter L f u| ≤ ‖iteratedFDeriv ℝ L.length f u‖ := by
  rw [← congrFun (iteratedFDeriv_get_eq_lineIter hf L) u]
  rw [← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have hp : ∏ i : Fin L.length, ‖L.get i‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hL _ (List.get_mem _ _)
  exact mul_le_of_le_one_right (norm_nonneg _) hp

theorem norm_iteratedFDeriv_le_of_lineIter {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ)
    (u : ParabolicSpace) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ L : List ParabolicSpace, L.length = j → (∀ d ∈ L, ‖d‖ ≤ 1) → |lineIter L f u| ≤ C) :
    ‖iteratedFDeriv ℝ j f u‖ ≤ C := by
  refine ContinuousMultilinearMap.opNorm_le_bound hC fun m => ?_
  by_cases hm : ∀ i, m i ≠ 0
  · set m' : Fin j → ParabolicSpace := fun i => (‖m i‖)⁻¹ • m i with hm'
    have hn : ∀ i, ‖m i‖ ≠ 0 := fun i => norm_ne_zero_iff.2 (hm i)
    have hm1 : ∀ i, ‖m' i‖ ≤ 1 := fun i => by
      simp only [hm', norm_smul, norm_inv, norm_norm]
      exact (inv_mul_cancel₀ (hn i)).le
    have e : m = fun i => ‖m i‖ • m' i := by
      funext i
      simp only [hm', smul_smul, mul_inv_cancel₀ (hn i), one_smul]
    have hb : |iteratedFDeriv ℝ j f u m'| ≤ C := by
      rw [iteratedFDeriv_apply_eq_lineIter hf]
      refine h _ (List.length_ofFn) fun d hd => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hd
      exact hm1 i
    conv_lhs => rw [e]
    rw [(iteratedFDeriv ℝ j f u).map_smul_univ, smul_eq_mul, Real.norm_eq_abs, abs_mul]
    have : |∏ i, ‖m i‖| = ∏ i, ‖m i‖ := abs_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    rw [this, mul_comm]
    exact mul_le_mul_of_nonneg_right hb (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  · push Not at hm
    obtain ⟨i, hi⟩ := hm
    rw [(iteratedFDeriv ℝ j f u).map_coord_zero i hi, norm_zero]
    exact mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _)

end RegularityStructures

end
