/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.HeatOperatorSlices

/-! Reflection converts the adjoint test generator to the actual heat
operator. Only past times occur in the subsequent kernel representation. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20
open scoped ContDiff

 theorem compact_time_reflection {u : ParabolicSpace → ℝ} (hu : HasCompactSupport u) (t₀ : ℝ) :
    HasCompactSupport (fun p : ParabolicSpace => u (t₀ - p.1, p.2)) := by
  have hc : Continuous (fun p : ParabolicSpace => (t₀ - p.1, p.2)) := by fun_prop
  apply HasCompactSupport.of_support_subset_isCompact (hu.isCompact.image hc)
  intro p hp
  refine ⟨(t₀ - p.1, p.2), subset_tsupport u hp, ?_⟩
  dsimp only
  ext <;> simp

 theorem heatTestGenerator_time_reflection {u : ParabolicSpace → ℝ} (hu : ContDiff ℝ ∞ u)
    (t₀ : ℝ) (p : ParabolicSpace) :
    heatTestGenerator (fun q : ParabolicSpace => u (t₀ - q.1, q.2)) p =
      -sourceHeat u (t₀ - p.1, p.2) := by
  let f : ParabolicSpace → ℝ := fun q => u (t₀ - q.1, q.2)
  have hf : ContDiff ℝ ∞ f := hu.comp (by fun_prop)
  have htime : fderiv ℝ f p (1, 0) = -fderiv ℝ u (t₀ - p.1, p.2) (1, 0) := by
    have hcurve : HasDerivAt (fun s : ℝ => (t₀ - s, p.2)) (-1, 0) p.1 := by
      exact ((hasDerivAt_id p.1).const_sub t₀).prodMk (hasDerivAt_const p.1 p.2)
    have hh := ((hu.differentiable (by simp) (t₀ - p.1, p.2)).hasFDerivAt.comp_hasDerivAt p.1 hcurve).deriv
    change deriv (fun s => f (s, p.2)) p.1 = _ at hh
    rw [source_time_deriv_eq_fderiv f p (hf.differentiable (by simp) p)] at hh
    rw [show ((-1 : ℝ), (0 : Fin 3 → ℝ)) = -((1 : ℝ), (0 : Fin 3 → ℝ)) by simp, map_neg] at hh
    exact hh
  have hspace (i : Fin 3) :
      fderiv ℝ (fun q : ParabolicSpace => fderiv ℝ f q (0, Pi.single i 1)) p (0, Pi.single i 1) =
      fderiv ℝ (fderiv ℝ (fun w : Fin 3 → ℝ => u (t₀ - p.1, w))) p.2 (Pi.single i 1) (Pi.single i 1) := by
    exact (spatial_slice_second_apply hf p.1 p.2 (Pi.single i 1) (Pi.single i 1)).symm
  change heatTestGenerator f p = _
  unfold heatTestGenerator
  rw [htime, sourceHeat_eq_spatial_slices hu]
  have heq : (∑ i : Fin 3, fderiv ℝ (fun q : ParabolicSpace => fderiv ℝ f q (0, Pi.single i 1)) p (0, Pi.single i 1)) =
      ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (fun w : Fin 3 → ℝ => u (t₀ - p.1, w))) p.2 (Pi.single i 1) (Pi.single i 1) :=
    Finset.sum_congr rfl (fun i _ => hspace i)
  rw [heq]
  ring

end GlobalPhi43.Local
