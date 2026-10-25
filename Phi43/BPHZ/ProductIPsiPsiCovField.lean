/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiField
public import Phi43.BPHZ.GammaMomentGradBridgeIncrements
public import Phi43.BPHZ.GammaMomentLp
public import Phi43.BPHZ.TreePsiMoment
public import Phi43.BPHZ.NoiseTreeUnfold

/-!
# The field `v₁(x, y) Ψ(proj y)` as a Wiener integral

`ipsiTaylorKernel N x y w` is the Taylor remainder kernel of `v₁(x, y) = ∫ T_{x,y}(w) Ψ(w) dw`
(`hairerIPsiRecentred_eq_integral`).  The pair `(ω, y) ↦ v₁(x, y)(ω)` and the field
`hairerIPsiPsiField N ξ x ω y` are jointly measurable.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The Taylor remainder kernel of `v₁(x, y)`: `T_{x,y}(w) = hairerTaylorKernel (proj x) (y - x) w`. -/
def ipsiTaylorKernel (N : ℕ) (x y : ParabolicSpace) (w : SpaceTime) : ℝ :=
  hairerTaylorKernel N (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) w

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*}

theorem integrable_ipsiTaylorKernel (N : ℕ) (x y : ParabolicSpace) :
    Integrable (ipsiTaylorKernel N x y) :=
  integrable_hairerTaylorKernel N _ _ _

theorem measurable_ipsiTaylorKernel_uncurry (N : ℕ) (x : ParabolicSpace) :
    Measurable (fun q : ParabolicSpace × SpaceTime => ipsiTaylorKernel N x q.1 q.2) := by
  unfold ipsiTaylorKernel hairerTaylorKernel
  have hK := measurable_constantsComparison_hairerKernelTorus N
  have hy1 : Measurable (fun q : ParabolicSpace × SpaceTime => q.1.1 - x.1) :=
    (measurable_fst.comp measurable_fst).sub_const _
  have hy2 : Measurable (fun q : ParabolicSpace × SpaceTime => q.1.2 - x.2) :=
    (measurable_snd.comp measurable_fst).sub_const _
  have hv : Measurable (fun q : ParabolicSpace × SpaceTime =>
      spaceTimeProj x + (q.1.1 - x.1, torusProj (q.1.2 - x.2)) - q.2) :=
    (measurable_const.add (hy1.prodMk (measurable_torusProj'.comp hy2))).sub measurable_snd
  refine ((hK.comp hv).sub (hK.comp (measurable_const.sub measurable_snd))).sub ?_
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_hairerKernelTorusGrad N i).comp (measurable_const.sub measurable_snd)).mul
    ((measurable_pi_apply i).comp hy2)

/-- `v₁(x, y) = ∫ T_{x,y}(w) Ψ(w) dw` for smooth noise. -/
theorem hairerIPsiRecentred_eq_integral (N : ℕ) {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
    (hξ : IsSmoothOnSpaceTime (ξ ω)) (x y : ParabolicSpace) :
    hairerIPsiRecentred N ξ ω x y = ∫ w, ipsiTaylorKernel N x y w * hairerPsiField N ξ ω w :=
  hairerIPsiRecentred_eq_gammaPsiTaylor N hξ x y

variable [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}

theorem measurable_hairerIPsiRecentred_prod_uncurry (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (x : ParabolicSpace) :
    Measurable (fun q : Ω × ParabolicSpace => hairerIPsiRecentred N ξ q.1 x q.2) := by
  have hY := measurable_hairerPsiField_uncurry N hξ
  have hg : Measurable (fun p : (Ω × ParabolicSpace) × SpaceTime => (p.1.2, p.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hg' : Measurable (fun p : (Ω × ParabolicSpace) × SpaceTime => (p.1.1, p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have h1 : Measurable (fun p : (Ω × ParabolicSpace) × SpaceTime =>
      ipsiTaylorKernel N x p.1.2 p.2) := by
    exact Measurable.comp (g := fun q : ParabolicSpace × SpaceTime => ipsiTaylorKernel N x q.1 q.2)
      (f := fun p : (Ω × ParabolicSpace) × SpaceTime => (p.1.2, p.2))
      (measurable_ipsiTaylorKernel_uncurry N x) hg
  have h2 : Measurable (fun p : (Ω × ParabolicSpace) × SpaceTime =>
      hairerPsiField N ξ p.1.1 p.2) := by
    exact Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiField N ξ q.1 q.2)
      (f := fun p : (Ω × ParabolicSpace) × SpaceTime => (p.1.1, p.2)) hY hg'
  have hm : Measurable (fun p : (Ω × ParabolicSpace) × SpaceTime =>
      ipsiTaylorKernel N x p.1.2 p.2 * hairerPsiField N ξ p.1.1 p.2) := h1.mul h2
  have h := (hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure SpaceTime))).measurable
  have e : (fun q : Ω × ParabolicSpace => hairerIPsiRecentred N ξ q.1 x q.2) =
      fun q => ∫ w, ipsiTaylorKernel N x q.2 w * hairerPsiField N ξ q.1 w :=
    funext fun q => hairerIPsiRecentred_eq_integral N (hξ.1 q.1) x q.2
  rw [e]
  exact h

theorem measurable_hairerIPsiPsiField_uncurry_cov (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (x : ParabolicSpace) :
    Measurable (fun q : Ω × ParabolicSpace => hairerIPsiPsiField N ξ x q.1 q.2) := by
  have h1 := measurable_hairerIPsiRecentred_prod_uncurry N hξ x
  have hg : Measurable (fun q : Ω × ParabolicSpace => (q.1, spaceTimeProj q.2)) :=
    measurable_fst.prodMk (continuous_spaceTimeProj.measurable.comp measurable_snd)
  have h2 : Measurable (fun q : Ω × ParabolicSpace =>
      hairerPsiField N ξ q.1 (spaceTimeProj q.2)) :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiField N ξ q.1 q.2)
      (f := fun q : Ω × ParabolicSpace => (q.1, spaceTimeProj q.2))
      (measurable_hairerPsiField_uncurry N hξ) hg
  exact h1.mul h2

end RegularityStructures.Phi43

end
