module

public import GlobalPhi43.Attachment.MassiveTimeShift
public import Phi43.Reconstruction.DuhamelPrinciple

/-! The actual exponentially weighted potential is a classical heat solution.
No classical PDE is assumed: its mild identity supplies the hypothesis. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 RegularityStructures.PDE
open RegularityStructures.Potential RegularityStructures.Inhomogeneity Set
open scoped ContDiff

/-- The actual smooth weighted source, shifted by an arbitrary start time. -/
def massiveWeightedLift {f : SpaceTime → ℝ} (a : ℝ) (z : ParabolicSpace) : ℝ :=
  Real.exp (a+z.1) * f (a+z.1, torusProj z.2)

theorem massiveWeightedLift_perSmooth {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (a : ℝ) : PerSmooth (massiveWeightedLift (f := f) a) where
  smooth := by
    have hs : ContDiff ℝ ∞ (fun z : ParabolicSpace => ((a+z.1,z.2) : ParabolicSpace)) :=
      (contDiff_const.add contDiff_fst).prodMk contDiff_snd
    exact (contDiff_const.add contDiff_fst).exp.mul (hf.comp hs)
  periodic z c hc := by
    simp only [massiveWeightedLift, torusProj_add, hc, add_zero]

/-- The smooth periodic forcing path is exactly the source weighted forcing path. -/
theorem massiveWeightedForcing_eq_forcePath {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) (a : ℝ) :
    massiveWeightedForcing hf hg a = forcePath (massiveWeightedLift_perSmooth hf a) := by
  funext r
  ext x
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  rw [forcePath_apply]
  rfl

/-- The classical forcing is exactly the reweighted source noise. -/
theorem massiveWeighted_forcing_apply {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (a r : ℝ) (x : Torus3) (v : ℝ) :
    forcing (massiveWeightedLift_perSmooth hf a) (r,x,v) = Real.exp (a+r) * f (a+r,x) := by
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  rw [forcing_apply]
  simp only [massiveWeightedLift, torusProj_torusRep]

/-- Every actual potential, reweighted and shifted, satisfies the mild-solution predicate. -/
theorem massivePotential_weighted_isMild {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    {ψ : ℝ → C(Torus3, ℝ)} (hψ : IsMassivePotential f ψ) (a T : ℝ) :
    IsMildSolution (forcing (massiveWeightedLift_perSmooth hf a))
      (Real.exp a • ψ a) T (fun r => Real.exp (a+r) • ψ (a+r)) := by
  intro r hr
  have h := massivePotential_shifted_weighted_identity hf hg hψ a r hr.1
  rw [massiveWeightedForcing_eq_forcePath] at h
  have he : (fun s => nemytskii (forcing (massiveWeightedLift_perSmooth hf a)) s
      (Real.exp (a+s) • ψ (a+s))) = forcePath (massiveWeightedLift_perSmooth hf a) := by
    funext s
    ext x
    rfl
  rw [he]
  exact h

/-- Actual classical jets and time derivative for the reweighted potential, derived from the integral. -/
theorem massivePotential_weighted_classical {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    {ψ : ℝ → C(Torus3, ℝ)} (hψ : IsMassivePotential f ψ) (a : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ (w : ℝ → C(Torus3, Fin 3 → ℝ)) (w2 : ℝ → C(Torus3, Fin 3 → Fin 3 → ℝ)),
      Continuous w ∧ Continuous w2 ∧
      (∀ r ∈ Icc 0 T, HasTorusDeriv (Real.exp (a+r) • ψ (a+r)) (w r)) ∧
      (∀ r ∈ Icc 0 T, HasTorusDeriv (w r) (w2 r)) ∧
      ∀ r ∈ Ioo 0 T, ∀ x : Torus3,
        HasDerivAt (fun s => (Real.exp (a+s) • ψ (a+s)) x)
          (torusLap (w2 r) x + forcing (massiveWeightedLift_perSmooth hf a)
            (r,x,(Real.exp (a+r) • ψ (a+r)) x)) r := by
  obtain ⟨hs, hc⟩ := massivePotential_regular hf hg hψ
  have hinit : ContDiff ℝ ∞ (fun y : Fin 3 → ℝ => (Real.exp a • ψ a) (torusProj y)) := by
    have hslice : ContDiff ℝ ∞ (fun y : Fin 3 → ℝ => ψ a (torusProj y)) :=
      hs.comp (contDiff_const.prodMk contDiff_id)
    exact contDiff_const.mul hslice
  have hcont : Continuous (fun r => Real.exp (a+r) • ψ (a+r)) :=
    (Real.continuous_exp.comp (continuous_const.add continuous_id)).smul (hc.comp (continuous_const.add continuous_id))
  exact hasDerivAt_of_isMildSolution
    (contDiff_nonlinLift_forcing (massiveWeightedLift_perSmooth hf a)) hinit hT hcont
    (massivePotential_weighted_isMild hf hg hψ a T)

end GlobalPhi43.Attachment
