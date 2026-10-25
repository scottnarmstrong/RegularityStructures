/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Inhomogeneity.DuhamelSpatial

/-!
# The heat equation with forcing for the Duhamel field

For `g` smooth and spatially periodic, the Duhamel field `θ = duhamelField g` satisfies
`∂_t θ = g + Δθ` on `{t > 0}` (`pd_zero_duhamelField`), where `Δ = ∑ⱼ ∂ⱼ∂ⱼ` is the spatial
Laplacian; as functions on all of space-time (`pd_zero_duhamelField_fun`) with `g` replaced by its
truncation `g⁺ = g · 1_{t>0}`. This is the mild-solution theory of
`RegularityStructures.PDE.MildTime` (`hasDerivAt_of_isMildSolution`) read through `Datum.pd`.
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Inhomogeneity

/-- `g` truncated to `{t > 0}`. -/
def posPart (g : ParabolicSpace → ℝ) : ParabolicSpace → ℝ :=
  fun z => if 0 < z.1 then g z else 0

end RegularityStructures.Inhomogeneity

end

public section

namespace RegularityStructures.Inhomogeneity

open RegularityStructures.PDE Set Filter Topology

variable {g : ParabolicSpace → ℝ}

theorem posPart_of_pos (g : ParabolicSpace → ℝ) {z : ParabolicSpace} (hz : 0 < z.1) :
    posPart g z = g z := by simp [posPart, hz]

theorem posPart_of_nonpos (g : ParabolicSpace → ℝ) {z : ParabolicSpace} (hz : z.1 ≤ 0) :
    posPart g z = 0 := by simp [posPart, not_lt.2 hz]

theorem PerSmooth.smoothPos_posPart (hg : PerSmooth g) : Datum.SmoothPos (posPart g) :=
  hg.smooth.contDiffOn.congr fun _ hz => posPart_of_pos g hz

/-- First spatial derivatives of the Duhamel field through the mild-solution jet. -/
private theorem pd_succ_eq_of_hasTorusDeriv (hg : PerSmooth g) {t : ℝ} (ht : 0 < t)
    {w : C(Torus3, Fin 3 → ℝ)} (hw : HasTorusDeriv (duhamel (forcePath hg) t) w)
    (j : Fin 3) (y : Fin 3 → ℝ) :
    Datum.pd j.succ (duhamelField hg) (t, y) = w (torusProj y) j := by
  have hF : DifferentiableAt ℝ (duhamelField hg) (t, y) :=
    Datum.SmoothPos.differentiableAt (smoothPos_duhamelField hg) ht
  have e1 : (fun y' : Fin 3 → ℝ => duhamelField hg (t, y')) =
      fun y' => duhamel (forcePath hg) t (torusProj y') :=
    funext fun y' => duhamelField_of_pos hg ht
  have e2 := Datum.sdLift_slice hF j
  rw [Datum.sdLift, e1, (hw y).fderiv, ofPartials_single] at e2
  exact (Datum.pdv_of_pos (v := Datum.stBasis j.succ) (F := duhamelField hg) (z := (t, y)) ht).trans
    e2.symm

private theorem pd_succ_pd_succ_eq (hg : PerSmooth g) {t : ℝ} (ht : 0 < t)
    {w : C(Torus3, Fin 3 → ℝ)} {w2 : C(Torus3, Fin 3 → Fin 3 → ℝ)}
    (hw : HasTorusDeriv (duhamel (forcePath hg) t) w)
    (hw2 : HasTorusDeriv (E := Fin 3 → ℝ) w w2) (i j : Fin 3) (y : Fin 3 → ℝ) :
    Datum.pd i.succ (Datum.pd j.succ (duhamelField hg)) (t, y) = w2 (torusProj y) i j := by
  have hF : DifferentiableAt ℝ (Datum.pd j.succ (duhamelField hg)) (t, y) :=
    Datum.SmoothPos.differentiableAt ((smoothPos_duhamelField hg).pd _) ht
  have e1 : (fun y' : Fin 3 → ℝ => Datum.pd j.succ (duhamelField hg) (t, y')) =
      fun y' => w (torusProj y') j :=
    funext fun y' => pd_succ_eq_of_hasTorusDeriv hg ht hw j y'
  have e2 := Datum.sdLift_slice hF i
  have h3 : HasFDerivAt (fun y' : Fin 3 → ℝ => w (torusProj y') j)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).comp
        (ofPartials (w2 (torusProj y)))) y :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).hasFDerivAt.comp y (hw2 y)
  rw [Datum.sdLift, e1, h3.fderiv] at e2
  rw [Datum.pd, Datum.pdv_of_pos ht, ← e2]
  simp [ofPartials_single]

theorem exists_duhamel_jet (hg : PerSmooth g) {t : ℝ} (ht : 0 < t) :
    ∃ (w : C(Torus3, Fin 3 → ℝ)) (w2 : C(Torus3, Fin 3 → Fin 3 → ℝ)),
      HasTorusDeriv (duhamel (forcePath hg) t) w ∧ HasTorusDeriv (E := Fin 3 → ℝ) w w2 ∧
      ∀ x, HasDerivAt (fun s => duhamel (forcePath hg) s x)
        (torusLap w2 x + forcing hg (t, x, duhamel (forcePath hg) t x)) t := by
  obtain ⟨w, w2, -, -, hw, hw2, hder⟩ := hasDerivAt_of_isMildSolution
    (contDiff_nonlinLift_forcing hg)
    (by simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Fin 3 → ℝ => (0 : ℝ)))
    (T := t + 1) (by linarith) (continuous_duhamelPath hg) (isMildSolution_duhamelPath hg (t + 1))
  exact ⟨w t, w2 t, hw t ⟨ht.le, by linarith⟩, hw2 t ⟨ht.le, by linarith⟩,
    fun x => hder t ⟨ht, by linarith⟩ x⟩

theorem hasDerivAt_duhamelField_time (hg : PerSmooth g) {t : ℝ} (ht : 0 < t) (y : Fin 3 → ℝ)
    {v : ℝ} (hd : HasDerivAt (fun s => duhamel (forcePath hg) s (torusProj y)) v t) :
    Datum.pd 0 (duhamelField hg) (t, y) = v := by
  have hF : DifferentiableAt ℝ (duhamelField hg) (t, y) :=
    Datum.SmoothPos.differentiableAt (smoothPos_duhamelField hg) ht
  have hι : HasDerivAt (fun s : ℝ => ((s, y) : ParabolicSpace)) ((1, 0) : ParabolicSpace) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  have hcomp := hF.hasFDerivAt.comp_hasDerivAt t hι
  have hloc : (fun s : ℝ => duhamel (forcePath hg) s (torusProj y)) =ᶠ[𝓝 t]
      (duhamelField hg ∘ fun s : ℝ => ((s, y) : ParabolicSpace)) :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht) fun s hs =>
      (duhamelField_of_pos hg (z := (s, y)) hs).symm
  have e0 := (hcomp.congr_of_eventuallyEq hloc).unique hd
  rw [Datum.pd, Datum.pdv_of_pos ht, Datum.stBasis_zero, e0]

/-- **`∂_t θ = g + Δθ`** on `{t > 0}` for the Duhamel field. -/
theorem pd_zero_duhamelField (hg : PerSmooth g) {z : ParabolicSpace} (hz : 0 < z.1) :
    Datum.pd 0 (duhamelField hg) z =
      g z + ∑ j : Fin 3, Datum.pd j.succ (Datum.pd j.succ (duhamelField hg)) z := by
  obtain ⟨t, y⟩ := z
  have ht : 0 < t := hz
  obtain ⟨w, w2, hw, hw2, hd⟩ := exists_duhamel_jet hg ht
  rw [hasDerivAt_duhamelField_time hg ht y (hd (torusProj y))]
  have hG : forcing hg (t, torusProj y, duhamel (forcePath hg) t (torusProj y)) = g (t, y) := by
    rw [forcing_apply]
    exact hg.eq_of_torusProj_eq t (torusProj_torusRep _)
  rw [hG, add_comm, torusLap_apply]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (pd_succ_pd_succ_eq hg ht hw hw2 i i y).symm

end RegularityStructures.Inhomogeneity

end
