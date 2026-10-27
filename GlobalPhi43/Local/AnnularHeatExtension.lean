/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CompactSmoothExtension
public import GlobalPhi43.Local.CompactKernelTaylor
public import RegularityStructures.Analysis.Heat.Kernel

/-! The ordinary heat kernel has a global compact smooth extension from
any fixed compact annulus. Choices precede the field and all Taylor data. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Filter Topology
open scoped ContDiff

 theorem annular_heat_kernel_taylor_extension {K : Set ParabolicSpace}
    (hK : IsCompact K) (hzero : (0 : ParabolicSpace) ∉ K) :
    ∃ k : ParabolicSpace → ℝ, ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧
      (∀ p ∈ K, k =ᶠ[𝓝 p] heatKernelR4) ∧
      ∃ S ≥ 0, ∀ (x y : ParabolicSpace) (R : ℝ), 0 ≤ R → y ∈ pastBall x R →
        |k y - k x - fderiv ℝ (fun w : Fin 3 → ℝ => k (x.1, w)) x.2 (y.2 - x.2)| ≤
          2 * S * R ^ 2 := by
  have hO : IsOpen ({(0 : ParabolicSpace)}ᶜ) := isClosed_singleton.isOpen_compl
  have hKO : K ⊆ {(0 : ParabolicSpace)}ᶜ := by
    intro p hp
    simpa only [mem_compl_iff, mem_singleton_iff] using (show p ≠ 0 from fun he => hzero (he ▸ hp))
  have hheat : ContDiffOn ℝ ∞ heatKernelR4 ({(0 : ParabolicSpace)}ᶜ) := by
    intro p hp
    exact (contDiffAt_heatKernelR4 (by simpa only [mem_compl_iff, mem_singleton_iff] using hp)).contDiffWithinAt
  obtain ⟨k, hk, hck, he⟩ := exists_compact_smooth_extension hK hO hKO hheat
  exact ⟨k, hk, hck, he, exists_compact_kernel_taylor_bound hk hck⟩

end GlobalPhi43.Local
