/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Inhomogeneity.DuhamelField
public import RegularityStructures.Abstract.Datum.HeatField

/-!
# Spatial derivatives of the Duhamel field

For `g` smooth and spatially periodic, `∂_j (duhamelField g) = duhamelField (∂_j g)` on `{t > 0}`
(`pd_succ_duhamelField`): the spatial derivative falls on the forcing
(`hasTorusDeriv_duhamel`).  Iterating, every spatial derivative of the Duhamel field is the
Duhamel field of the corresponding derivative of the forcing (`pdWord_duhamelField`), and so is
bounded by `t` times the corresponding sup norm of the derivative of the forcing
(`abs_duhamelField_le`).
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Inhomogeneity

open RegularityStructures.PDE

/-- The derivative of `g` in the `j`-th coordinate direction of space-time (everywhere, not only
for `t > 0`). -/
def ddv (j : Fin 4) (g : ParabolicSpace → ℝ) : ParabolicSpace → ℝ :=
  fun z => fderiv ℝ g z (Datum.stBasis j)

variable {g : ParabolicSpace → ℝ}

theorem PerSmooth.ddv (hg : PerSmooth g) (j : Fin 4) : PerSmooth (Inhomogeneity.ddv j g) where
  smooth := (hg.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  periodic z c hc := by
    have h2 : (fun w : ParabolicSpace => g (w + (0, c))) = g :=
      funext fun w => by
        have e : w + (0, c) = (w.1, w.2 + c) := Prod.ext (by simp) rfl
        rw [e]
        exact hg.periodic w c hc
    have h3 := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := z) ((0, c) : ParabolicSpace)
    rw [h2] at h3
    simp only [Inhomogeneity.ddv]
    have : ((z.1, z.2 + c) : ParabolicSpace) = z + (0, c) := Prod.ext (by simp) rfl
    rw [this, ← h3]

/-- The vector forcing `(∂_1 g, ∂_2 g, ∂_3 g)`. -/
def forcingVec (hg : PerSmooth g) : C(ℝ × Torus3 × (Fin 3 → ℝ), Fin 3 → ℝ) :=
  descend3 (fun p : ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ) => fun j : Fin 3 => Inhomogeneity.ddv j.succ g (p.1, p.2.1))
    (continuous_pi fun j => ((hg.ddv j.succ).smooth.continuous.comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))))
    (fun s _ _ _ hab => funext fun j => (hg.ddv j.succ).eq_of_torusProj_eq s hab)

/-- The path `s ↦ (∂_j g(s, ·))_j ∈ C(T³, ℝ³)`. -/
def forceVec (hg : PerSmooth g) (s : ℝ) : C(Torus3, Fin 3 → ℝ) :=
  nemytskii (forcingVec hg) s 0

theorem continuous_forceVec (hg : PerSmooth g) : Continuous (forceVec hg) :=
  continuous_nemytskii_comp (forcingVec hg) (u := fun _ => (0 : C(Torus3, Fin 3 → ℝ)))
    continuous_const

theorem forceVec_apply (hg : PerSmooth g) (s : ℝ) (y : Fin 3 → ℝ) (j : Fin 3) :
    forceVec hg s (torusProj y) j = Inhomogeneity.ddv j.succ g (s, y) := by
  change Inhomogeneity.ddv j.succ g (s, torusRep (torusProj y)) = _
  exact (hg.ddv j.succ).eq_of_torusProj_eq s (torusProj_torusRep _)

theorem comp_forceVec (hg : PerSmooth g) (s : ℝ) (j : Fin 3) :
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).compLeftContinuous ℝ Torus3
        (forceVec hg s) = forcePath (hg.ddv j.succ) s := by
  ext x
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  rw [compLeftContinuous_apply_apply, ContinuousLinearMap.proj_apply, forceVec_apply,
    forcePath_apply]

theorem hasTorusDeriv_forcePath (hg : PerSmooth g) (s : ℝ) :
    HasTorusDeriv (forcePath hg s) (forceVec hg s) := by
  intro y
  have hlift : (fun y => forcePath hg s (torusProj y)) = fun y => g (s, y) :=
    funext fun y => forcePath_apply hg s y
  rw [hlift]
  have hι : HasFDerivAt (fun y' : Fin 3 → ℝ => ((s, y') : ParabolicSpace))
      (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ)) y :=
    (hasFDerivAt_const s y).prodMk (hasFDerivAt_id y)
  have hd : DifferentiableAt ℝ g (s, y) :=
    (hg.smooth.differentiable (by simp)) (s, y)
  have h : HasFDerivAt (fun y' : Fin 3 → ℝ => g (s, y'))
      ((fderiv ℝ g (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ))) y :=
    hd.hasFDerivAt.comp y hι
  have e : ofPartials (forceVec hg s (torusProj y)) =
      (fderiv ℝ g (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ)) := by
    rw [← ofPartials_apply_single ((fderiv ℝ g (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ _))]
    congr 1
    funext j
    rw [forceVec_apply]
    simp only [Inhomogeneity.ddv, ContinuousLinearMap.comp_apply, Datum.stBasis_succ]
    rfl
  rw [e]
  exact h

/-- **The spatial derivative falls on the forcing**: `∂_j (duhamelField g) = duhamelField (∂_j g)`
on `{t > 0}`. -/
theorem pd_succ_duhamelField (hg : PerSmooth g) (j : Fin 3) {z : ParabolicSpace} (hz : 0 < z.1) :
    Datum.pd j.succ (duhamelField hg) z = duhamelField (hg.ddv j.succ) z := by
  have hF : DifferentiableAt ℝ (duhamelField hg) (z.1, z.2) :=
    Datum.SmoothPos.differentiableAt (smoothPos_duhamelField hg) hz
  have hdh := hasTorusDeriv_duhamel (E := ℝ) (continuous_forcePath hg) (continuous_forceVec hg)
    hz.le (fun s _ => hasTorusDeriv_forcePath hg s)
  have e1 : (fun y' : Fin 3 → ℝ => duhamelField hg (z.1, y')) =
      fun y' => duhamel (forcePath hg) z.1 (torusProj y') :=
    funext fun y' => duhamelField_of_pos hg hz
  have e2 := Datum.sdLift_slice hF j
  rw [Datum.sdLift, e1, (hdh z.2).fderiv, ofPartials_single] at e2
  have e3 : Datum.pd j.succ (duhamelField hg) z = fderiv ℝ (duhamelField hg) (z.1, z.2)
      (Datum.stBasis j.succ) := Datum.pdv_of_pos hz
  rw [e3, ← e2, duhamelField_of_pos _ hz]
  have e4 := duhamel_compLeftContinuous (continuous_forceVec hg)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j) z.1
  simp_rw [comp_forceVec] at e4
  have e5 := congrArg (fun F : C(Torus3, ℝ) => F (torusProj z.2)) e4
  simpa using e5.symm

/-- The iterated spatial derivative of `g` along a word (global, not truncated at `t = 0`). -/
def ddWord : List (Fin 3) → (ParabolicSpace → ℝ) → ParabolicSpace → ℝ
  | [], g => g
  | j :: w, g => Inhomogeneity.ddv j.succ (ddWord w g)

theorem PerSmooth.ddWord (hg : PerSmooth g) :
    ∀ w : List (Fin 3), PerSmooth (Inhomogeneity.ddWord w g)
  | [] => hg
  | j :: w => (PerSmooth.ddWord hg w).ddv j.succ

/-- **Every spatial derivative of the Duhamel field is the Duhamel field of the derivative of the
forcing.** -/
theorem pdWord_duhamelField (hg : PerSmooth g) (w : List (Fin 3)) {z : ParabolicSpace}
    (hz : 0 < z.1) :
    Datum.pdWord w (duhamelField hg) z = duhamelField (hg.ddWord w) z := by
  induction w generalizing z with
  | nil => rfl
  | cons j w ih =>
    have h1 : Datum.pdWord (j :: w) (duhamelField hg) z =
        Datum.pd j.succ (Datum.pdWord w (duhamelField hg)) z := rfl
    have h2 : Datum.pd j.succ (Datum.pdWord w (duhamelField hg)) =
        Datum.pd j.succ (duhamelField (hg.ddWord w)) :=
      Datum.pdv_congr fun z hz => ih hz
    rw [h1, h2]
    exact pd_succ_duhamelField (hg.ddWord w) j hz

theorem norm_forcePath_le (hg : PerSmooth g) {t M : ℝ}
    (hM : ∀ s ∈ Set.Icc 0 t, ∀ y, |g (s, y)| ≤ M) (ht : 0 ≤ t) :
    ∀ s ∈ Set.Icc 0 t, ‖forcePath hg s‖ ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t ⟨ht, le_rfl⟩ 0)
  intro s hs
  refine (ContinuousMap.norm_le _ hM0).2 fun x => ?_
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  rw [forcePath_apply, Real.norm_eq_abs]
  exact hM s hs y

/-- **Sup bound of the Duhamel field**: `|duhamelField g (t, y)| ≤ M t` if `|g| ≤ M` on
`[0, t] × ℝ³`. -/
theorem abs_duhamelField_le (hg : PerSmooth g) {t M : ℝ}
    (hM : ∀ s ∈ Set.Icc 0 t, ∀ y, |g (s, y)| ≤ M) (ht : 0 < t) (y : Fin 3 → ℝ) :
    |duhamelField hg (t, y)| ≤ M * t := by
  rw [duhamelField_of_pos hg ht]
  have h := norm_duhamel_le_mul (continuous_forcePath hg) ht.le (norm_forcePath_le hg hM ht.le)
  exact (Real.norm_eq_abs _ ▸ (ContinuousMap.norm_coe_le_norm _ (torusProj y))).trans h

end RegularityStructures.Inhomogeneity
