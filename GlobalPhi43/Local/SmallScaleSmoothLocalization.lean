module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

public section

open Set Filter
open scoped ContDiff Topology

namespace GlobalPhi43.Local

/-- A locally smooth function near a compact set has a global smooth representative
agreeing on an open neighbourhood of that set. No bound on the extension is used. -/
theorem exists_smooth_representative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K O : Set E} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (u : E → ℝ) (hu : ContDiffOn ℝ ∞ u O) :
    ∃ (v : E → ℝ) (W : Set E), ContDiff ℝ ∞ v ∧ IsOpen W ∧ K ⊆ W ∧
      W ⊆ O ∧ EqOn v u W ∧ HasCompactSupport v ∧ tsupport v ⊆ O := by
  obtain ⟨B, hB, hKB, hBc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨N, hN, hKN, hNc⟩ := hK.exists_isOpen_closure_subset
    ((hO.inter hB).mem_nhdsSet.mpr (subset_inter hKO hKB))
  obtain ⟨W, hW, hKW, hWc⟩ := hK.exists_isOpen_closure_subset
    (hN.mem_nhdsSet.mpr hKN)
  obtain ⟨χ, hχ, _, hχs, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hN isClosed_closure hWc
  have hχc : tsupport χ ⊆ O := by
    rw [tsupport, hχs]
    exact hNc.trans inter_subset_left
  have hχcompact : HasCompactSupport χ := by
    change IsCompact (closure (Function.support χ))
    rw [hχs]
    exact hBc.of_isClosed_subset isClosed_closure
      (hNc.trans (inter_subset_right.trans subset_closure))
  refine ⟨fun x => χ x * u x, W, contDiff_iff_contDiffAt.mpr ?_, hW, hKW,
    (subset_closure.trans hWc).trans (subset_closure.trans (hNc.trans inter_subset_left)), ?_, hχcompact.mul_right,
    tsupport_mul_subset_left.trans hχc⟩
  · intro x
    by_cases hx : x ∈ O
    · exact hχ.contDiffAt.mul ((hu x hx).contDiffAt (hO.mem_nhds hx))
    · have hz : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp
        (fun h => hx (hχc h))
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp [hy]
  · intro x hx
    change χ x * u x = u x
    rw [(hχone x).mp (subset_closure hx), one_mul]

end GlobalPhi43.Local
