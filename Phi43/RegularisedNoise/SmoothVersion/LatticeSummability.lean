/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# Polynomial weights on the integer frequency lattice

The Fourier series construction uses polynomial decay on `Fin d → ℤ`.  This file packages the
elementary lattice summability estimate needed for the four-dimensional finite-window torus.
The proof follows the standard comparison with the full integer lattice inside the real
finite-dimensional space.
-/

@[expose] public section

open Filter

namespace RegularityStructures.Phi43

private noncomputable def smoothVersionLatticePoint {d : ℕ} (n : Fin d → ℤ) :
    Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d))) :=
  ⟨fun i => (n i : ℝ), by
    have hcoord : (fun i => (n i : ℝ)) = ∑ i, n i • Pi.basisFun ℝ (Fin d) i := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hcoord]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))⟩

private theorem smoothVersionLatticePoint_injective {d : ℕ} :
    Function.Injective (smoothVersionLatticePoint (d := d)) := by
  intro n m h
  have h' : (fun i => (n i : ℝ)) = fun i => (m i : ℝ) := congrArg Subtype.val h
  ext i
  exact Int.cast_injective (congrFun h' i)

private theorem smoothVersionLatticePoint_norm_sq_le {d : ℕ} (n : Fin d → ℤ) :
    ‖smoothVersionLatticePoint n‖ ^ 2 ≤ 1 + ∑ i, ((n i : ℝ)) ^ 2 := by
  have hsum : 0 ≤ ∑ i, ((n i : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS : 0 ≤ 1 + ∑ i, ((n i : ℝ)) ^ 2 := by linarith
  have hnorm : ‖smoothVersionLatticePoint n‖ ≤
      Real.sqrt (1 + ∑ i, ((n i : ℝ)) ^ 2) := by
    change ‖(fun i => (n i : ℝ))‖ ≤ Real.sqrt (1 + ∑ i, ((n i : ℝ)) ^ 2)
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs, Real.le_sqrt (abs_nonneg _) hS, sq_abs]
    calc
      ((n i : ℝ)) ^ 2 ≤ ∑ j, ((n j : ℝ)) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg ((n j : ℝ))) (Finset.mem_univ i)
      _ ≤ 1 + ∑ j, ((n j : ℝ)) ^ 2 := by linarith
  calc
    ‖smoothVersionLatticePoint n‖ ^ 2 ≤
        Real.sqrt (1 + ∑ i, ((n i : ℝ)) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = 1 + ∑ i, ((n i : ℝ)) ^ 2 := Real.sq_sqrt hS

theorem summable_smoothVersion_inv_one_add_normSq_pow {d r : ℕ} (hr : d < 2 * r) :
    Summable (fun n : Fin d → ℤ =>
      (((1 : ℝ) + ∑ i, ((n i : ℝ)) ^ 2) ^ r)⁻¹) := by
  let L := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))
  have hrank : Module.finrank ℤ L = d := by
    rw [Module.finrank_eq_card_basis ((Pi.basisFun ℝ (Fin d)).restrictScalars ℤ), Fintype.card_fin]
  have hL : Summable (fun z : L => ‖z‖⁻¹ ^ (2 * r)) :=
    ZLattice.summable_norm_pow_inv L (2 * r) (by rw [hrank]; exact hr)
  refine Summable.of_norm_bounded_eventually
    (hL.comp_injective (smoothVersionLatticePoint_injective (d := d))) ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : Fin d → ℤ)).subset fun n hn => ?_
  by_contra hn0
  apply hn
  have hne : smoothVersionLatticePoint n ≠ 0 := fun h =>
    hn0 (smoothVersionLatticePoint_injective (d := d)
      (h.trans (by ext i; simp [smoothVersionLatticePoint])))
  have hpos : 0 < ‖smoothVersionLatticePoint n‖ := norm_pos_iff.mpr hne
  have hsum : 0 ≤ ∑ i, ((n i : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS : 0 < (1 : ℝ) + ∑ i, ((n i : ℝ)) ^ 2 := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Function.comp_apply, inv_pow]
  apply inv_anti₀ (by positivity)
  rw [pow_mul]
  exact pow_le_pow_left₀ (sq_nonneg _) (smoothVersionLatticePoint_norm_sq_le n) r

end RegularityStructures.Phi43

end
