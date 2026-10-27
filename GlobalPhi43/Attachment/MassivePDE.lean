module

public import GlobalPhi43.Attachment.MassiveWeightedClassical
public import GlobalPhi43.Attachment.TorusScaledJets

/-! Classical massive PDE for any actual potential, derived from its integral. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 RegularityStructures.PDE
open RegularityStructures.Inhomogeneity Set
open scoped ContDiff

/-- The full-space lift is smooth and periodic, without an extra periodicity assumption. -/
theorem attachment_perSmooth {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) :
    PerSmooth (fun z : ParabolicSpace => f (spaceTimeProj z)) :=
  RegularityStructures.Phi43.Potential.perSmooth_noise_zeta (canonicalNoiseOfSpaceTime f hf)

/-- Source (L+1)psi=f at every point, for any supplied massive potential.
No PDE, jet, boundedness, or slice estimate is an additional hypothesis. -/
theorem massivePotential_pde {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) {ψ : ℝ → C(Torus3, ℝ)}
    (hψ : IsMassivePotential f ψ) (z : ParabolicSpace) :
    ddv 0 (fun w => ψ w.1 (torusProj w.2)) z -
      ∑ j : Fin 3, ddv j.succ (ddv j.succ (fun w => ψ w.1 (torusProj w.2))) z +
        ψ z.1 (torusProj z.2) = f (spaceTimeProj z) := by
  let t := z.1
  let y := z.2
  let a := t-1
  obtain ⟨hs, hc⟩ := massivePotential_regular hf hg hψ
  let hp := attachment_perSmooth hs
  have he (r : ℝ) : forcePath hp r = ψ r := by
    ext x
    obtain ⟨v, rfl⟩ := torusProj_surjective x
    rw [forcePath_apply]
    rfl
  obtain ⟨D2, hD2, hlap⟩ := exists_hasTorusDeriv₂_forcePath hp t
  have hD := hasTorusDeriv_forcePath hp t
  rw [he] at hD
  obtain ⟨w,w2,hw,hw2,hDw,hDw2,hdt⟩ := massivePotential_weighted_classical hf hg hψ a
    (T := 2) (by norm_num)
  have h1 : (1 : ℝ) ∈ Icc 0 2 := by constructor <;> norm_num
  have h2 : (1 : ℝ) ∈ Ioo 0 2 := by constructor <;> norm_num
  have hDw1 := hDw 1 h1
  have ha1 : a+1=t := by dsimp [a]; ring
  rw [ha1] at hDw1
  have hweq : w 1 = Real.exp t • forceVec hp t :=
    hDw1.unique (attachment_hasTorusDeriv_smul hD (Real.exp t))
  have hDw21 := hDw2 1 h1
  rw [hweq] at hDw21
  have hw2eq : w2 1 = Real.exp t • D2 :=
    hDw21.unique (attachment_hasTorusDeriv_smul hD2 (Real.exp t))
  have hdψ := hasDerivAt_forcePath_apply hp t y
  simp only [he] at hdψ
  have hshift : HasDerivAt (fun s => ψ (a+s) (torusProj y))
      (ddv 0 (fun u => ψ u.1 (torusProj u.2)) (t,y)) 1 := by
    have hb := hdψ
    rw [← ha1] at hb
    have h := hb.comp 1 ((hasDerivAt_id 1).const_add a)
    simpa only [Function.comp_def, ha1, mul_one, spaceTimeProj] using h
  have hexp : HasDerivAt (fun s => Real.exp (a+s)) (Real.exp t) 1 := by
    have h := (Real.hasDerivAt_exp (a+1)).comp 1 ((hasDerivAt_id 1).const_add a)
    simpa only [Function.comp_def, ha1, mul_one, spaceTimeProj] using h
  have hprod := hexp.mul hshift
  have hdW := hdt 1 h2 (torusProj y)
  rw [massiveWeighted_forcing_apply hf a 1 (torusProj y)] at hdW
  simp only [ha1, hw2eq, attachment_torusLap_smul,
    ContinuousMap.smul_apply, smul_eq_mul] at hdW
  have heq := hprod.unique hdW
  simp only [ha1] at heq
  have hmul : Real.exp t * (ψ t (torusProj y) +
      ddv 0 (fun u => ψ u.1 (torusProj u.2)) (t,y)) =
      Real.exp t * (torusLap D2 (torusProj y) + f (t,torusProj y)) := by
    nlinarith only [heq]
  have hcancel := mul_left_cancel₀ (Real.exp_ne_zero t) hmul
  rw [hlap] at hcancel
  change ψ t (torusProj y) + ddv 0 (fun u => ψ u.1 (torusProj u.2)) (t,y) =
    (∑ j : Fin 3, ddv j.succ (ddv j.succ (fun u => ψ u.1 (torusProj u.2))) (t,y)) +
      f (t,torusProj y) at hcancel
  change ddv 0 (fun u => ψ u.1 (torusProj u.2)) (t,y) -
    ∑ j : Fin 3, ddv j.succ (ddv j.succ (fun u => ψ u.1 (torusProj u.2))) (t,y) +
      ψ t (torusProj y) = f (t,torusProj y)
  linarith only [hcancel]

end GlobalPhi43.Attachment
