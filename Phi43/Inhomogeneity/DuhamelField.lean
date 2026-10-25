/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.MildSmooth
public import RegularityStructures.PDE.MildTime
public import RegularityStructures.PDE.SpatialDeriv
public import RegularityStructures.Abstract.Datum.Deriv

/-!
# The Duhamel field of a smooth periodic forcing

For a smooth spatially periodic `g : ℝ × ℝ³ → ℝ` (`PerSmooth g`), the Duhamel field
`duhamelField hg (t, y) = ∫₀ᵗ P_{t-r} g(r, ·) dr (y)` for `t > 0` (and `0` for `t ≤ 0`) is the mild
solution of `∂_t u = Δu + g`, `u(0) = 0` (`isMildSolution_duhamelPath`).  By the mild-solution
theory of `PDE/` it is smooth on `{t > 0}` (`smoothPos_duhamelField`).

This is the function `θ_s(t) = ∫_s^t P_{t-r} ζ(r) dr` of the restart datum of the `Φ⁴₃` fixed point
(with the time `t - s` as the first coordinate).
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Inhomogeneity

open RegularityStructures.PDE

/-- A smooth function on `ℝ × ℝ³`, periodic in the space variables (the lift of a smooth function
on `ℝ × T³`). -/
structure PerSmooth (g : ParabolicSpace → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ g
  periodic : ∀ (z : ParabolicSpace) (c : Fin 3 → ℝ), torusProj c = 0 → g (z.1, z.2 + c) = g z

variable {g : ParabolicSpace → ℝ}

/-- The forcing `G(t, x, v) = g(t, x)` as a continuous function on `ℝ × T³ × ℝ`. -/
def forcing (hg : PerSmooth g) : C(ℝ × Torus3 × ℝ, ℝ) :=
  descend3 (fun p : ℝ × (Fin 3 → ℝ) × ℝ => g (p.1, p.2.1))
    (hg.smooth.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
    (fun s a b v hab => by
      have hc : torusProj (b - a) = 0 := (torusProj_eq_iff_sub b a).1 hab.symm
      have := hg.periodic (s, a) (b - a) hc
      simpa using this.symm)

/-- The path `s ↦ g(s, ·) ∈ C(T³)`. -/
def forcePath (hg : PerSmooth g) (s : ℝ) : C(Torus3, ℝ) :=
  nemytskii (forcing hg) s 0

/-- The Duhamel field `(t, y) ↦ ∫₀ᵗ P_{t-r} g(r, ·) dr (y)` for `t > 0`, and `0` for `t ≤ 0`. -/
def duhamelField (hg : PerSmooth g) : ParabolicSpace → ℝ :=
  fun z => if 0 < z.1 then duhamel (forcePath hg) z.1 (torusProj z.2) else 0

end RegularityStructures.Inhomogeneity

end

public section

open scoped ContDiff

namespace RegularityStructures.Inhomogeneity

open RegularityStructures.PDE Set Filter Topology

variable {g : ParabolicSpace → ℝ}

theorem PerSmooth.eq_of_torusProj_eq (hg : PerSmooth g) (s : ℝ) {a b : Fin 3 → ℝ}
    (hab : torusProj a = torusProj b) : g (s, a) = g (s, b) := by
  have hc : torusProj (b - a) = 0 := (torusProj_eq_iff_sub b a).1 hab.symm
  have := hg.periodic (s, a) (b - a) hc
  simpa using this.symm

theorem forcing_apply (hg : PerSmooth g) (s : ℝ) (x : Torus3) (v : ℝ) :
    forcing hg (s, x, v) = g (s, torusRep x) := rfl

theorem forcePath_apply (hg : PerSmooth g) (s : ℝ) (y : Fin 3 → ℝ) :
    forcePath hg s (torusProj y) = g (s, y) := by
  change g (s, torusRep (torusProj y)) = g (s, y)
  exact hg.eq_of_torusProj_eq s (torusProj_torusRep _)

theorem continuous_forcePath (hg : PerSmooth g) : Continuous (forcePath hg) :=
  continuous_nemytskii_comp (forcing hg) (u := fun _ => (0 : C(Torus3, ℝ))) continuous_const

theorem nonlinLift_forcing (hg : PerSmooth g) :
    nonlinLift (forcing hg) = fun p : ℝ × (Fin 3 → ℝ) × ℝ => g (p.1, p.2.1) := by
  funext p
  change g (p.1, torusRep (torusProj p.2.1)) = g (p.1, p.2.1)
  exact hg.eq_of_torusProj_eq _ (torusProj_torusRep _)

theorem contDiff_nonlinLift_forcing (hg : PerSmooth g) :
    ContDiff ℝ ∞ (nonlinLift (forcing hg)) := by
  rw [nonlinLift_forcing]
  exact hg.smooth.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))

theorem continuous_duhamelPath (hg : PerSmooth g) : Continuous (duhamel (forcePath hg)) :=
  continuous_duhamel (continuous_forcePath hg)

/-- The Duhamel path is the mild solution of `∂_t u = Δu + g`, `u(0) = 0`. -/
theorem isMildSolution_duhamelPath (hg : PerSmooth g) (T : ℝ) :
    IsMildSolution (forcing hg) 0 T (duhamel (forcePath hg)) := by
  intro t _
  have h : (fun s => nemytskii (forcing hg) s (duhamel (forcePath hg) s)) = forcePath hg := by
    funext s
    ext x
    rfl
  rw [h, heatOp_zero_right, zero_add]

theorem contDiffOn_duhamelPath (hg : PerSmooth g) {T : ℝ} (hT : 0 ≤ T) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => duhamel (forcePath hg) p.1 (torusProj p.2))
      (Ioo 0 T ×ˢ (univ : Set (Fin 3 → ℝ))) :=
  contDiffOn_of_isMildSolution (contDiff_nonlinLift_forcing hg)
    (by simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Fin 3 → ℝ => (0 : ℝ)))
    hT (continuous_duhamelPath hg) (isMildSolution_duhamelPath hg T)

theorem duhamelField_of_pos (hg : PerSmooth g) {z : ParabolicSpace} (hz : 0 < z.1) :
    duhamelField hg z = duhamel (forcePath hg) z.1 (torusProj z.2) := by
  simp [duhamelField, hz]

theorem duhamelField_of_nonpos (hg : PerSmooth g) {z : ParabolicSpace} (hz : z.1 ≤ 0) :
    duhamelField hg z = 0 := by
  simp [duhamelField, not_lt.2 hz]

theorem smoothPos_duhamelField (hg : PerSmooth g) : Datum.SmoothPos (duhamelField hg) := by
  refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
  have hz0 : 0 < z.1 := hz
  refine ⟨Ioo 0 (z.1 + 1) ×ˢ univ, isOpen_Ioo.prod isOpen_univ, ⟨⟨hz0, by linarith⟩, trivial⟩, ?_⟩
  refine ((contDiffOn_duhamelPath hg (T := z.1 + 1) (by linarith)).mono
    inter_subset_right).congr fun w hw => ?_
  exact duhamelField_of_pos hg hw.2.1.1

end RegularityStructures.Inhomogeneity

end
