module

public import GlobalPhi43.Attachment.DefectFields
public import Phi43.Reconstruction.PsiPDE
public import Phi43.BPHZ.GammaMomentGradBridgeIncrements

/-! The actual three kernel-defect PDE identities consumed by cover and time slices. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43
open RegularityStructures.Potential RegularityStructures.Inhomogeneity
open scoped ContDiff

/-- The three actual source primitives J,Y,Z, with arbitrary renormalisation constants. -/
def defectPrimitive (N : ℕ) (f : SpaceTime → ℝ) (C : RenormalisationConstants)
    (i : Fin 3) : SpaceTime → ℝ := ![treeJ N f, treeY N f (C₁ C), treeZ N f (C₁ C)] i

/-- The torus convolution formula for each of J,Y,Z. -/
theorem defectPrimitive_eq_torusIntegral (N : ℕ) (f : SpaceTime → ℝ)
    (C : RenormalisationConstants) (i : Fin 3) (z : SpaceTime) :
    defectPrimitive N f C i z = ∫ w, hairerKernelTorus N (z - w) *
      (![f, treeV N f (C₁ C), treeW N f (C₁ C)] i) w := by
  fin_cases i <;> rfl

/-- The source inputs noise,V,W are smooth at every outcome, without a growth premise. -/
theorem defectInput_smooth {N : ℕ} {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (C : RenormalisationConstants) (i : Fin 3) :
    IsSmoothOnSpaceTime (![f, treeV N f (C₁ C), treeW N f (C₁ C)] i) := by
  have hJ : IsSmoothOnSpaceTime (treeJ N f) :=
    isSmoothOnSpaceTime_hairerPsiField N (ξ := fun _ : Unit => f) (ωx := ()) hf
  fin_cases i
  · exact hf
  · exact (hJ.pow 2).sub contDiff_const
  · exact (hJ.pow 3).sub (contDiff_const.mul hJ)

/-- The actual primitives agree with the whole-space truncated convolution. -/
theorem defectPrimitive_eq_hairerConvolution {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants) (i : Fin 3) :
    (fun z : ParabolicSpace => defectPrimitive N f C i (spaceTimeProj z)) =
      hairerConvolution N (defectInput N f C i) := by
  funext z
  have h := hairerConvolution_comp_proj_eq N
    (IsSmoothOnSpaceTime.continuous (defectInput_smooth (N := N) hf C i)) z
  fin_cases i
  · exact h.symm
  · exact h.symm
  · exact h.symm

/-- All three actual primitives are smooth on the full smooth-noise space. -/
theorem defectPrimitive_smooth {N : ℕ} {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (C : RenormalisationConstants) (i : Fin 3) : IsSmoothOnSpaceTime (defectPrimitive N f C i) := by
  change ContDiff ℝ ∞ (fun z : ParabolicSpace => defectPrimitive N f C i (spaceTimeProj z))
  rw [defectPrimitive_eq_hairerConvolution hf C i]
  exact contDiff_hairerConvolution N (defectInput_smooth (N := N) hf C i)

/-- The defect equations for all three fields and every smooth forcing.
No growth, model, time cutoff or norm bound is assumed. -/
theorem defect_pde {N : ℕ} {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (C : RenormalisationConstants) (i : Fin 3) (z : ParabolicSpace) :
    ddv 0 (fun w => defectPrimitive N f C i (spaceTimeProj w)) z -
        ∑ j : Fin 3, ddv j.succ (ddv j.succ
          (fun w => defectPrimitive N f C i (spaceTimeProj w))) z =
      defectInput N f C i z + defectField N f C i z := by
  let g : SpaceTime → ℝ := ![f, treeV N f (C₁ C), treeW N f (C₁ C)] i
  let hg : IsSmoothOnSpaceTime g := defectInput_smooth (N := N) hf C i
  have h := psi_pde N (canonicalNoiseOfSpaceTime g hg) z
  rw [defectPrimitive_eq_hairerConvolution hf C i]
  change ddv 0 (hairerConvolution N (defectInput N f C i)) z -
      ∑ j : Fin 3, ddv j.succ (ddv j.succ (hairerConvolution N (defectInput N f C i))) z =
    defectInput N f C i z - potConv (defectInput N f C i) (potQ N) z
  exact h

end GlobalPhi43.Attachment
