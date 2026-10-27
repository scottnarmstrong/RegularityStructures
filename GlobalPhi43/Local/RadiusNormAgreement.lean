/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AugmentedLocalPDE
public import GlobalPhi43.Local.RadiusNormAssembly

/-! Local equality preserves the actual radius-truncated affine norm;
the constructed smooth representative carries no new norm or mass cost. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set

 theorem radiusAffineSeminorm_eqOn {U V : (ParabolicSpace × ParabolicSpace) → ℝ} {D : Set ParabolicSpace}
    (he : EqOn U V (D ×ˢ D)) (γ L : ℝ) :
    radiusAffineSeminorm U D γ L = radiusAffineSeminorm V D γ L := by
  unfold radiusAffineSeminorm
  apply iSup_congr
  intro x
  apply iSup_congr
  intro hx
  apply iInf_congr
  intro ν
  unfold radiusAffineRemainderSeminorm affineRemainderSeminorm
  apply iSup_congr
  intro y
  apply iSup_congr
  intro hy
  rw [he ⟨hx, hy.1⟩]

 theorem weightedRadiusAffineSeminorm_eqOn {U V : (ParabolicSpace × ParabolicSpace) → ℝ} {r d₀ γ : ℝ}
    (hr : 0 ≤ r) (he : EqOn U V (mwCylinder ×ˢ mwCylinder)) :
    weightedRadiusAffineSeminorm U r d₀ γ = weightedRadiusAffineSeminorm V r d₀ γ := by
  unfold weightedRadiusAffineSeminorm
  apply iSup_congr
  intro d
  apply iSup_congr
  intro hd
  congr 1
  apply radiusAffineSeminorm_eqOn
  have hD : cylinderInterior r d ⊆ mwCylinder := by
    intro z hz
    rw [mwCylinder_eq_sourceCylinder]
    exact sourceCylinder_antitone (by norm_num : (0 : ℝ) ≤ 0) hr
      (cylinderInterior_mem_domain hd.1.le hz)
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact he ⟨hD hx, hD hy⟩

 theorem weightedRadiusAffineSeminorm_remainder_representative
    {u J v Y Z : ParabolicSpace → ℝ} {W : Set ParabolicSpace} {r d₀ γ : ℝ}
    (hr : 0 ≤ r) (hKW : closure mwCylinder ⊆ W)
    (he : EqOn v (fun z => u z - J z) W) :
    weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ γ =
      weightedRadiusAffineSeminorm (sourceExpansion (fun z => u z - J z) Y Z) r d₀ γ := by
  apply weightedRadiusAffineSeminorm_eqOn hr
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact sourceExpansion_eqOn he ⟨hKW (subset_closure hx), hKW (subset_closure hy)⟩

end GlobalPhi43.Local
