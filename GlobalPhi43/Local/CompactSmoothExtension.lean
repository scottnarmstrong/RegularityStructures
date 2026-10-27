/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Topology.Separation.Regular

/-! Qualitative compact extension for local smooth germs. Its cutoff
bounds are never introduced as quantitative source data. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Filter Topology
open scoped ContDiff

/-- Local smoothness near a compact carrier gives a compact global smooth
extension agreeing on a neighbourhood of each carrier point. -/
theorem exists_compact_smooth_extension {h : ParabolicSpace → ℝ} {K O : Set ParabolicSpace}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) (hh : ContDiffOn ℝ ∞ h O) :
    ∃ g : ParabolicSpace → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∀ x ∈ K, g =ᶠ[𝓝 x] h := by
  obtain ⟨V, hV, hKV, hcV⟩ := exists_isOpen_superset_and_isCompact_closure hK
  have hKOV : K ⊆ O ∩ V := fun x hx => ⟨hKO hx, hKV hx⟩
  obtain ⟨W, hW, hKW, hcW⟩ := hK.exists_isOpen_closure_subset ((hO.inter hV).mem_nhdsSet.mpr hKOV)
  obtain ⟨A, hA, hKA, hcA⟩ := hK.exists_isOpen_closure_subset (hW.mem_nhdsSet.mpr hKW)
  obtain ⟨χ, hχ, _, hsχ, hχone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hW isClosed_closure hcA
  have htχ : tsupport χ = closure W := by rw [tsupport, hsχ]
  have hcχ : HasCompactSupport χ := by
    rw [HasCompactSupport, htχ]
    exact hcV.of_isClosed_subset isClosed_closure (fun x hx => subset_closure (hcW hx).2)
  refine ⟨fun x => χ x * h x, ?_, hcχ.mul_right, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport χ
    · have hxO : x ∈ O := (hcW (htχ ▸ hx)).1
      exact hχ.contDiffAt.mul (hh.contDiffAt (hO.mem_nhds hxO))
    · have hev : (fun x => χ x * h x) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with z hz
        simp [image_eq_zero_of_notMem_tsupport hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro x hx
    filter_upwards [hA.mem_nhds (hKA hx)] with z hz
    rw [(hχone z).1 (subset_closure hz), one_mul]

end GlobalPhi43.Local
