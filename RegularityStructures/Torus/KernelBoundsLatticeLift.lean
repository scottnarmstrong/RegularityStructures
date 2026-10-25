/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsGaussian
public import RegularityStructures.Analysis.Parabolic.Basic

/-!
# Comparing the torus size with every lattice lift

The centred representative minimizes the Euclidean square norm over all integer lifts. Consequently
the torus parabolic size is at most the L1-based parabolic size of every lift. This transfers the
dyadic support from [Hai14, Assumption 5.1, (5.3)] to the periodised causal shells used in the
convergence of the mollified noise.
-/

public section

open Real Set

namespace RegularityStructures

theorem torusSpatialNorm_le_periodicLift (x : Torus3) (k : Fin 3 → ℤ) :
    torusSpatialNorm x ≤ √(sqNorm3 (torusRep x + fun i => (k i : ℝ))) := by
  obtain ⟨m, hm⟩ := torusRep_eq_centered_add_int x
  have hcoord (i : Fin 3) : (torusCenteredRep x i) ^ 2 ≤
      (torusRep x i + (k i : ℝ)) ^ 2 := by
    have hsq := sq_centered_add_int_ge (torusCenteredRep_mem_Icc x i) (m i + k i)
    have hi : torusRep x i + (k i : ℝ) =
        torusCenteredRep x i + ((m i + k i : ℤ) : ℝ) := by
      rw [hm]
      simp only [Pi.add_apply, Int.cast_add]
      ring
    rwa [← hi] at hsq
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum fun i _ => hcoord i

theorem torusParabolicSize_le_periodicLift (z : SpaceTime) (k : Fin 3 → ℤ) :
    torusParabolicSize z ≤
      parabolicNorm (z.1, torusRep z.2 + fun i => (k i : ℝ)) := by
  have hsp := torusSpatialNorm_le_periodicLift z.2 k
  have hroot : √(sqNorm3 (torusRep z.2 + fun i => (k i : ℝ))) ≤
      ∑ i, |(torusRep z.2 + fun i => (k i : ℝ)) i| := by
    rw [Real.sqrt_le_left (by positivity)]
    unfold sqNorm3
    simpa only [sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (f := fun i : Fin 3 => |(torusRep z.2 + fun i => (k i : ℝ)) i|)
        (fun i _ => abs_nonneg _))
  exact add_le_add le_rfl (hsp.trans hroot)

end RegularityStructures

end
