module

public import GlobalPhi43.Attachment.MassivePDE
public import Phi43.Potential.ZetaDiff

/-! The actual J-minus-massive-potential equation in slice Step 1. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 RegularityStructures.PDE
open RegularityStructures.Inhomogeneity RegularityStructures.Potential
open scoped ContDiff

/-- The actual full-space difference used in the source Duhamel argument. -/
def sliceDifference (N : ℕ) (f : SpaceTime → ℝ) (ψ : ℝ → C(Torus3, ℝ)) : ParabolicSpace → ℝ :=
  fun z => treeJ N f (spaceTimeProj z) - ψ z.1 (torusProj z.2)

theorem sliceDifference_smooth {N : ℕ} {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) {ψ : ℝ → C(Torus3, ℝ)}
    (hψ : IsMassivePotential f ψ) : ContDiff ℝ ∞ (sliceDifference N f ψ) := by
  have hJ : ContDiff ℝ ∞ (fun z => treeJ N f (spaceTimeProj z)) :=
    defectPrimitive_smooth (N := N) hf 0 0
  have hP : ContDiff ℝ ∞ (fun z : ParabolicSpace => ψ z.1 (torusProj z.2)) := by
    exact (massivePotential_regular hf hg hψ).1
  exact hJ.sub hP

/-- Source Step 1, with the signed actual first defect and no assumed PDE. -/
theorem sliceDifference_pde {N : ℕ} {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) {ψ : ℝ → C(Torus3, ℝ)}
    (hψ : IsMassivePotential f ψ) (C : RenormalisationConstants) (z : ParabolicSpace) :
    ddv 0 (sliceDifference N f ψ) z -
      ∑ j : Fin 3, ddv j.succ (ddv j.succ (sliceDifference N f ψ)) z =
        ψ z.1 (torusProj z.2) + defectField N f C 0 z := by
  let J := fun z => treeJ N f (spaceTimeProj z)
  let P := fun z : ParabolicSpace => ψ z.1 (torusProj z.2)
  have hJ : ContDiff ℝ ∞ J := defectPrimitive_smooth (N := N) hf C 0
  have hP : ContDiff ℝ ∞ P := by
    exact (massivePotential_regular hf hg hψ).1
  have hdJ := defect_pde (N := N) hf C 0 z
  have hdP := massivePotential_pde hf hg hψ z
  have h0 := congrFun (RegularityStructures.Phi43.Potential.ddA_sub hJ hP [0]) z
  have h2 (j : Fin 3) := congrFun
    (RegularityStructures.Phi43.Potential.ddA_sub hJ hP [j.succ,j.succ]) z
  simp only [ddA] at h0 h2
  change ddv 0 (J-P) z - ∑ j : Fin 3, ddv j.succ (ddv j.succ (J-P)) z = _
  rw [h0]
  simp_rw [h2]
  simp only [Pi.sub_apply]
  rw [Finset.sum_sub_distrib]
  change ddv 0 J z - ∑ j : Fin 3, ddv j.succ (ddv j.succ J) z =
    f (spaceTimeProj z) + defectField N f C 0 z at hdJ
  change ddv 0 P z - ∑ j : Fin 3, ddv j.succ (ddv j.succ P) z + P z =
    f (spaceTimeProj z) at hdP
  change _ = P z + defectField N f C 0 z
  linarith only [hdJ,hdP]

end GlobalPhi43.Attachment
