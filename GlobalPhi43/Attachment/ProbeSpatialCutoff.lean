module

public import GlobalPhi43.Attachment.ProbeTimeCutoff
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Fixed smooth spatial core and annular profiles for Gaussian localization.
All support and derivative bounds come from the constructed profiles. -/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace GlobalPhi43.Attachment

abbrev ProbeSpace := Fin 3 → ℝ

def probeSpaceBump : ContDiffBump (0 : ProbeSpace) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The fixed core profile. -/
def probeSpaceCore (y : ProbeSpace) : ℝ := probeSpaceBump y

/-- The fixed annular profile; its inner half-ball vanishes exactly. -/
def probeSpaceAnnulus (y : ProbeSpace) : ℝ := probeSpaceCore y - probeSpaceCore ((2 : ℝ) • y)

theorem probeSpaceCore_smooth : ContDiff ℝ ∞ probeSpaceCore := probeSpaceBump.contDiff

theorem probeSpaceAnnulus_smooth : ContDiff ℝ ∞ probeSpaceAnnulus := by
  unfold probeSpaceAnnulus
  exact probeSpaceCore_smooth.sub (probeSpaceCore_smooth.comp (by fun_prop))

theorem probeSpaceCore_support : tsupport probeSpaceCore ⊆ closedBall 0 2 := by
  rw [show probeSpaceCore = (probeSpaceBump : ProbeSpace → ℝ) from rfl,
    probeSpaceBump.tsupport_eq]
  exact Subset.rfl

theorem probeSpaceCore_one {y : ProbeSpace} (hy : ‖y‖ ≤ 1) : probeSpaceCore y = 1 :=
  probeSpaceBump.one_of_mem_closedBall (by simpa only [mem_closedBall, dist_zero_right, probeSpaceBump] using hy)

theorem probeSpaceCore_zero {y : ProbeSpace} (hy : 2 ≤ ‖y‖) : probeSpaceCore y = 0 := by
  apply probeSpaceBump.zero_of_le_dist
  simpa only [dist_zero_right, probeSpaceBump] using hy

theorem probeSpaceAnnulus_zero_inner {y : ProbeSpace} (hy : ‖y‖ ≤ 1 / 2) :
    probeSpaceAnnulus y = 0 := by
  have h2 : ‖(2 : ℝ) • y‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  rw [probeSpaceAnnulus, probeSpaceCore_one (by linarith), probeSpaceCore_one h2, sub_self]

theorem probeSpaceAnnulus_support : tsupport probeSpaceAnnulus ⊆
    {y : ProbeSpace | 1 / 2 ≤ ‖y‖ ∧ ‖y‖ ≤ 2} := by
  apply closure_minimal _ ((isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const))
  intro y hy
  constructor
  · by_contra hn
    exact hy (probeSpaceAnnulus_zero_inner (le_of_not_ge hn))
  · by_contra hn
    have h2 : 2 ≤ ‖(2 : ℝ) • y‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith [lt_of_not_ge hn]
    exact hy (by rw [probeSpaceAnnulus, probeSpaceCore_zero (le_of_not_ge hn),
      probeSpaceCore_zero h2, sub_self])

theorem probeSpaceCore_compact : HasCompactSupport probeSpaceCore :=
  (isCompact_closedBall (0 : ProbeSpace) 2).of_isClosed_subset
    (isClosed_tsupport _) probeSpaceCore_support

theorem probeSpaceAnnulus_compact : HasCompactSupport probeSpaceAnnulus :=
  (isCompact_closedBall (0 : ProbeSpace) 2).of_isClosed_subset (isClosed_tsupport _)
    (fun y hy => by simpa only [mem_closedBall, dist_zero_right] using
      (probeSpaceAnnulus_support hy).2)

/-- Both actual fixed profiles have a common finite C4 allowance. -/
theorem probeSpaceProfiles_derivative_bounds :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ≤ 4, ∀ y : ProbeSpace,
      ‖iteratedFDeriv ℝ k probeSpaceCore y‖ ≤ B ∧
      ‖iteratedFDeriv ℝ k probeSpaceAnnulus y‖ ≤ B := by
  obtain ⟨A, hA, ha⟩ := probeSpaceCore_compact.exists_bound_iteratedFDeriv probeSpaceCore_smooth 4
  obtain ⟨D, hD, hd⟩ := probeSpaceAnnulus_compact.exists_bound_iteratedFDeriv probeSpaceAnnulus_smooth 4
  refine ⟨A + D, add_nonneg hA hD, ?_⟩
  intro k hk y
  exact ⟨(ha k hk y).trans (le_add_of_nonneg_right hD),
    (hd k hk y).trans (le_add_of_nonneg_left hA)⟩

end GlobalPhi43.Attachment
