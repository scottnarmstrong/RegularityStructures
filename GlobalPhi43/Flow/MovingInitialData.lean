module

public import GlobalPhi43.Flow.ClassicalApproximation
public import Mathlib.Topology.UniformSpace.UniformApproximation

public noncomputable section

open Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow.FiniteLimitSystem

variable {N : ℕ} {κ : Kappa} {η : NegExponent} {A : ℕ → LiftData N κ}

theorem continuous_data (sys : FiniteLimitSystem η A) (s q : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q) :
    Continuous (fun x : HolderBesov η => sys.value s q x) := by
  exact (sys.continuous_on s hs).comp_continuous (continuous_const.prodMk continuous_id)
    (fun _ => ⟨hq, mem_univ _⟩)

/-- Passing through a varying restart datum. A containing radius is derived
from convergence of the datum, not supplied as an additional state bound. -/
theorem tendsto_moving_data (sys : FiniteLimitSystem η A) (s q : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q)
    (y : ℕ → HolderBesov η) (z : HolderBesov η) (hy : Tendsto y atTop (𝓝 z)) :
    Tendsto (fun n => sys.approximant n s q (y n)) atTop (𝓝 (sys.value s q z)) := by
  let L := ‖z‖ + 1
  have hu : TendstoUniformlyOn (fun n x => sys.approximant n s q x)
      (fun x => sys.value s q x) atTop (closedBall (0 : HolderBesov η) L) := by
    apply ((sys.uniform_on_box s q L).comp (fun x : HolderBesov η => (s, q, x))).mono
    intro x hx
    exact ⟨⟨hs, le_rfl⟩, ⟨hq, le_rfl⟩,
      by simpa only [mem_closedBall, dist_zero_right] using hx⟩
  have he : ∀ᶠ n in atTop, y n ∈ closedBall (0 : HolderBesov η) L := by
    have hn := ((continuous_norm.tendsto z).comp hy).eventually
      (gt_mem_nhds (show ‖z‖ < L by dsimp [L]; linarith))
    filter_upwards [hn] with n hn
    simpa only [mem_closedBall, dist_zero_right, Function.comp_def] using hn.le
  exact hu.tendsto_comp (sys.continuous_data s q hs hq).continuousAt.continuousWithinAt
    (tendsto_nhdsWithin_iff.mpr ⟨hy, he⟩)

end GlobalPhi43.Flow.FiniteLimitSystem
