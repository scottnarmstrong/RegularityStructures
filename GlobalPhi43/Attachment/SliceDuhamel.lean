module

public import GlobalPhi43.Attachment.HeatTimeTranslation

/-! The actual arbitrary-start Duhamel identity for J minus its massive potential. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 RegularityStructures.PDE
open RegularityStructures.Inhomogeneity Set
open scoped ContDiff

theorem sliceDifference_perSmooth {N : ℕ} {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) {ψ : ℝ → C(Torus3, ℝ)}
    (hψ : IsMassivePotential f ψ) : PerSmooth (sliceDifference N f ψ) where
  smooth := sliceDifference_smooth hf hg hψ
  periodic z c hc := by
    simp only [sliceDifference, spaceTimeProj, torusProj_add, hc, add_zero]

/-- Translation of a genuine periodic smooth field, at every real start time. -/
theorem attachment_perSmooth_translate {F : ParabolicSpace → ℝ} (hF : PerSmooth F)
    (v : ParabolicSpace) : PerSmooth (fun z => F (v+z)) where
  smooth := hF.smooth.comp (contDiff_const.add contDiff_id)
  periodic z c hc := by
    have he : v + (z.1,z.2+c) = ((v+z).1,(v+z).2+c) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add, add_assoc]
    rw [he]
    exact hF.periodic (v+z) c hc

theorem attachmentHeatOperator_translate (F : ParabolicSpace → ℝ) (v : ParabolicSpace) :
    attachmentHeatOperator (fun z => F (v+z)) = fun z => attachmentHeatOperator F (v+z) := by
  funext z
  simp only [attachmentHeatOperator]
  simp_rw [attachment_ddv_translate]

/-- The actual torus difference path, with periodic descent. -/
def sliceDifferencePath {N : ℕ} {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) {ψ : ℝ → C(Torus3, ℝ)}
    (hψ : IsMassivePotential f ψ) : ℝ → C(Torus3, ℝ) :=
  forcePath (sliceDifference_perSmooth (N := N) hf hg hψ)

theorem sliceDifferencePath_apply {N : ℕ} {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) {ψ : ℝ → C(Torus3, ℝ)}
    (hψ : IsMassivePotential f ψ) (r : ℝ) (y : Fin 3 → ℝ) :
    sliceDifferencePath (N := N) hf hg hψ r (torusProj y) =
      treeJ N f (r,torusProj y) - ψ r (torusProj y) := by
  rw [sliceDifferencePath, forcePath_apply]
  rfl

/-- A continuous forcing path; its evaluation theorem identifies exactly psi plus e1. -/
def sliceDuhamelForcing {N : ℕ} {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) {ψ : ℝ → C(Torus3, ℝ)}
    (hψ : IsMassivePotential f ψ) (a : ℝ) : ℝ → C(Torus3, ℝ) :=
  forcePath (attachmentHeatOperator_perSmooth
    (attachment_perSmooth_translate (sliceDifference_perSmooth (N := N) hf hg hψ) (a,0)))

theorem sliceDuhamelForcing_apply {N : ℕ} {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) {ψ : ℝ → C(Torus3, ℝ)}
    (hψ : IsMassivePotential f ψ) (C : RenormalisationConstants) (a r : ℝ) (y : Fin 3 → ℝ) :
    sliceDuhamelForcing (N := N) hf hg hψ a r (torusProj y) =
      ψ (a+r) (torusProj y) + defectField N f C 0 (a+r,y) := by
  rw [sliceDuhamelForcing, forcePath_apply, attachmentHeatOperator_translate]
  have h := sliceDifference_pde (N := N) hf hg hψ C ((a,0)+(r,y))
  simpa only [attachmentHeatOperator, Prod.mk_add_mk, zero_add] using h

/-- The Duhamel identity at arbitrary real starting times, derived from the evolution equation. -/
theorem sliceDifference_duhamel {N : ℕ} {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) {ψ : ℝ → C(Torus3, ℝ)}
    (hψ : IsMassivePotential f ψ) (a r : ℝ) (hr : 0 ≤ r) :
    sliceDifferencePath (N := N) hf hg hψ (a+r) =
      heatOp r (sliceDifferencePath (N := N) hf hg hψ a) +
        duhamel (sliceDuhamelForcing (N := N) hf hg hψ a) r := by
  let hA := attachment_perSmooth_translate (sliceDifference_perSmooth (N := N) hf hg hψ) (a,0)
  have h := duhamel_principle hA (attachmentHeatOperator_perSmooth hA) (fun _ => rfl) hr
  have he (s : ℝ) : forcePath hA s = sliceDifferencePath (N := N) hf hg hψ (a+s) := by
    ext x
    obtain ⟨y, rfl⟩ := torusProj_surjective x
    rw [forcePath_apply, sliceDifferencePath_apply]
    simp only [sliceDifference, Prod.mk_add_mk, zero_add, spaceTimeProj]
  rw [he r, he 0, add_zero] at h
  exact h

end GlobalPhi43.Attachment
