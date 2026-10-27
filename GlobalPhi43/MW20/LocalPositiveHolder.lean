module

public import GlobalPhi43.Local.SmallScaleLocalData
public import GlobalPhi43.MW20.SourceHolderBridges
public import GlobalPhi43.MW20.SourceNormDomains
public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.Setting.ParabolicHolderSeminorm

/-! Increment bounds from the local positive-tree norm. Both endpoints
remain in the specified domain, so the estimates require no extension or global norm. -/

@[expose] public noncomputable section

namespace GlobalPhi43.MW20

open RegularityStructures Set

theorem scalarHolderSeminorm_eq_parabolicHolderSeminorm (f : ParabolicSpace → ℝ)
    (D : Set ParabolicSpace) (α : ℝ) :
    scalarHolderSeminorm f D α = parabolicHolderSeminorm α D f := by
  simp only [scalarHolderSeminorm, parabolicHolderSeminorm, parabolicDist, Local.pdist,
    abs_sub_comm, ne_comm]

theorem radiusHolderSeminorm_le_parabolicHolderSeminorm (f : ParabolicSpace → ℝ)
    {D E : Set ParabolicSpace} (hDE : D ⊆ E) (α L : ℝ) :
    radiusHolderSeminorm f D α L ≤ parabolicHolderSeminorm α E f := by
  rw [← scalarHolderSeminorm_eq_parabolicHolderSeminorm]
  apply le_trans _ (scalarHolderSeminorm_mono_domain f hDE α)
  simp only [radiusHolderSeminorm, scalarHolderSeminorm, iSup_le_iff]
  intro x hx y hy hcut
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y
    (le_iSup_of_le hy (le_iSup_of_le hcut.2 le_rfl))))

theorem sourceCylinder_subset_positive {r : ℝ} (hr : 0 ≤ r) :
    sourceCylinder r ⊆ parabolicClosedNbhd mwCylinder 1 := by
  intro z hz
  refine ⟨z, ?_, ?_⟩
  · rw [Local.mwCylinder_eq_sourceCylinder]
    exact sourceCylinder_antitone (le_refl 0) hr hz
  · simp only [parabolicDist, sub_self, abs_zero, Real.sqrt_zero, norm_zero, max_self]
    norm_num

theorem mixedInterior_subset_positive {r d : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d) :
    Local.cylinderInterior r d ⊆ parabolicClosedNbhd mwCylinder 1 :=
  (mixedInterior_subset_base hd).trans (sourceCylinder_subset_positive hr)

/-- A source increment with explicit proofs for both original endpoints. -/
theorem abs_sub_le_of_parabolicHolderSeminorm_le {f : ParabolicSpace → ℝ} {α B : ℝ}
    (hB : 0 ≤ B)
    (hb : parabolicHolderSeminorm α (parabolicClosedNbhd mwCylinder 1) f ≤ ENNReal.ofReal B)
    {x y : ParabolicSpace} (hx : x ∈ parabolicClosedNbhd mwCylinder 1)
    (hy : y ∈ parabolicClosedNbhd mwCylinder 1) :
    |f y-f x| ≤ B*Local.pdist x y^α := by
  apply scalarHolderSeminorm_increment_bound f _ α hB _ hx hy
  rwa [scalarHolderSeminorm_eq_parabolicHolderSeminorm]

end GlobalPhi43.MW20
