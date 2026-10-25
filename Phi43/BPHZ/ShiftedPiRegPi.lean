/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiShift
public import Phi43.BPHZ.GammaFullParam
import Mathlib.Tactic

/-!
# The shift identities for `Q_t Π_x τ (x)` of the canonical models

The semigroup average `F ↦ ∫ Q_t(x, y) F(y) dy` is a linear functional on the submodule of
functions that are integrable against the kernel (`shiftedPiKernelInt`).  Together with the
pointwise identities of `ShiftedPiShift`, this gives for constants `C' = C + (a, b)`

`Q_t Π^{C'}_x τ (x) = Q_t Π^{C}_x τ (x) + ∑ (coefficient) * Q_t Π^{C}_x σ (x)`

with the rows `σ` of degree at least `deg τ`; the coefficients are polynomials in `a, b` and in the
gradients `gₖ = shiftedPiGrad`.  The deterministic rows are the kernel mass
`shiftedPiMass t x = ∫ Q_t(x, y) dy` and `shiftedPiMoment t x k = ∫ Q_t(x, y) (yₖ - xₖ) dy`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The functions integrable against the kernel `Q_t(x, ·)`. -/
def shiftedPiKernelSub (t : ℝ) (x : ParabolicSpace) : Submodule ℝ (ParabolicSpace → ℝ) where
  carrier := {F | Integrable (fun y => parabolicSemigroup.kernel t x y * F y)}
  add_mem' := by
    intro F G hF hG
    have hF' : Integrable (fun y => parabolicSemigroup.kernel t x y * F y) := hF
    have hG' : Integrable (fun y => parabolicSemigroup.kernel t x y * G y) := hG
    show Integrable (fun y => parabolicSemigroup.kernel t x y * (F + G) y)
    simp only [Pi.add_apply, mul_add]
    exact hF'.add hG'
  zero_mem' := by simp
  smul_mem' := by
    intro c F hF
    have hF' : Integrable (fun y => parabolicSemigroup.kernel t x y * F y) := hF
    have := hF'.const_mul c
    show Integrable (fun y => parabolicSemigroup.kernel t x y * (c • F) y)
    simpa only [Pi.smul_apply, smul_eq_mul, mul_left_comm] using this

/-- The semigroup average `F ↦ ∫ Q_t(x, y) F(y) dy`, linear on `shiftedPiKernelSub`. -/
def shiftedPiKernelInt (t : ℝ) (x : ParabolicSpace) : shiftedPiKernelSub t x →ₗ[ℝ] ℝ where
  toFun F := ∫ y, parabolicSemigroup.kernel t x y * (F : ParabolicSpace → ℝ) y
  map_add' F G := by
    have hF : Integrable (fun y => parabolicSemigroup.kernel t x y * (F : ParabolicSpace → ℝ) y) volume :=
      F.2
    have hG : Integrable (fun y => parabolicSemigroup.kernel t x y * (G : ParabolicSpace → ℝ) y) volume :=
      G.2
    simp only [Submodule.coe_add, Pi.add_apply, mul_add]
    exact integral_add hF hG
  map_smul' c F := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ c]
    exact integral_const_mul _ _

/-- The mass `∫ Q_t(x, y) dy`. -/
def shiftedPiMass (t : ℝ) (x : ParabolicSpace) : ℝ :=
  ∫ y, parabolicSemigroup.kernel t x y

/-- The first moment `∫ Q_t(x, y) (yₖ - xₖ) dy`. -/
def shiftedPiMoment (t : ℝ) (x : ParabolicSpace) (k : Fin 3) : ℝ :=
  ∫ y, parabolicSemigroup.kernel t x y * (y.2 k - x.2 k)

/-- The `Q_t Π_x τ (x)` of the canonical model of the lift of `f`. -/
abbrev shiftedPiReg (N : ℕ) (κ : Kappa) (C : RenormalisationConstants) (f : SpaceTime → ℝ)
    (x : ParabolicSpace) (t : ℝ) (τ : Symbol) : ℝ :=
  (canonicalModelOfLift N κ C f).regPi x (Pi.single τ (1 : ℝ) : Symbol → ℝ) t x


end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
  {C C' : RenormalisationConstants} {a b : ℝ} {t : ℝ} (x : ParabolicSpace)

theorem integrable_kernel_one (ht : 0 < t) :
    Integrable (fun y => parabolicSemigroup.kernel t x y * (1 : ℝ)) := by
  have := parabolicSemigroup.integrable_moment ht (le_refl (0 : ℝ)) x
  simp only [Real.rpow_zero, mul_one] at this ⊢
  exact (integrable_norm_iff (measurable_parabolicSemigroup_kernel t x).aestronglyMeasurable).1
    (by simpa using this)

theorem abs_coord_sub_le (y : ParabolicSpace) (k : Fin 3) :
    |y.2 k - x.2 k| ≤ parabolicSemigroup.scaleDist y x := by
  have h := abs_relCoord_succ_le y x k
  have e : CanonicalData.relCoord y x k.succ = x.2 k - y.2 k := by
    have hc4 : ∀ (z : ParabolicSpace) (j : Fin 3), parabolicCoords z j.succ = z.2 j := by
      intro z j
      fin_cases j <;> rfl
    simp [CanonicalData.relCoord, hc4]
  rw [e, abs_sub_comm] at h
  exact h

theorem integrable_kernel_coord (ht : 0 < t) (k : Fin 3) :
    Integrable (fun y => parabolicSemigroup.kernel t x y * (y.2 k - x.2 k)) := by
  have h := parabolicSemigroup.integrable_moment ht (zero_le_one : (0 : ℝ) ≤ 1) x
  refine h.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact ((measurable_parabolicSemigroup_kernel t x).mul
      ((measurable_pi_apply k).comp measurable_snd |>.sub measurable_const)).aestronglyMeasurable
  · rw [norm_mul, Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_coord_sub_le x y k) (abs_nonneg _)


variable (hf : IsSmoothOnSpaceTime (ξ ω)) (hg : Statements.HasPhi43NoiseGrowth (ξ ω))

include hf hg

/-- The extension row of `τ` as an element of the space of kernel-integrable functions. -/
@[expose] noncomputable def shiftedPiVec (ht : 0 < t) (C : RenormalisationConstants) (τ : Symbol) :
    shiftedPiKernelSub t x :=
  ⟨(hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
      C x (basis τ), integrable_kernel_mul_extensionPi hf hg τ ht x⟩

/-- The constant function `1`. -/
@[expose] noncomputable def shiftedPiVecOne (ht : 0 < t) : shiftedPiKernelSub t x :=
  ⟨fun _ => 1, integrable_kernel_one x ht⟩

/-- The coordinate function `y ↦ yₖ - xₖ`. -/
@[expose] noncomputable def shiftedPiVecCoord (ht : 0 < t) (k : Fin 3) : shiftedPiKernelSub t x :=
  ⟨fun y => y.2 k - x.2 k, integrable_kernel_coord x ht k⟩

theorem shiftedPi_reg_eq (ht : 0 < t) (C : RenormalisationConstants) (τ : Symbol) :
    shiftedPiReg N κ C (ξ ω) x t τ =
      shiftedPiKernelInt t x (shiftedPiVec (N := N) (κ := κ) x hf hg ht C τ) :=
  regPi_canonicalModelOfLift_eq_integral hf hg τ ht x

omit hf hg in
theorem shiftedPiKernelInt_vecOne (ht : 0 < t) :
    shiftedPiKernelInt t x (shiftedPiVecOne x ht) = shiftedPiMass t x := by
  simp [shiftedPiKernelInt, shiftedPiVecOne, shiftedPiMass]

omit hf hg in
theorem shiftedPiKernelInt_vecCoord (ht : 0 < t) (k : Fin 3) :
    shiftedPiKernelInt t x (shiftedPiVecCoord x ht k) = shiftedPiMoment t x k := rfl

theorem shiftedPi_reg_congr (ht : 0 < t) {τ : Symbol}
    (h : ∀ y, (hairerCanonicalData (κ := κ) N
        (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi C' x (basis τ) y =
      (hairerCanonicalData (κ := κ) N
        (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi C x (basis τ) y) :
    shiftedPiReg N κ C' (ξ ω) x t τ = shiftedPiReg N κ C (ξ ω) x t τ := by
  rw [shiftedPi_reg_eq x hf hg ht, shiftedPi_reg_eq x hf hg ht]
  congr 1
  exact Subtype.ext (funext h)

theorem shiftedPi_reg_psiSq (ht : 0 < t) (h1 : C₁ C' = C₁ C + a) :
    shiftedPiReg N κ C' (ξ ω) x t .psiSq =
      shiftedPiReg N κ C (ξ ω) x t .psiSq - a * shiftedPiMass t x := by
  rw [shiftedPi_reg_eq x hf hg ht, shiftedPi_reg_eq x hf hg ht]
  have : shiftedPiVec (N := N) (κ := κ) x hf hg ht C' .psiSq =
      shiftedPiVec (N := N) (κ := κ) x hf hg ht C .psiSq + (-a) • shiftedPiVecOne x ht :=
    Subtype.ext (funext fun y => by
      simp only [shiftedPiVec, shiftedPiVecOne, Submodule.coe_add, Submodule.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, shiftedPi_shift_psiSq x hf h1 y]
      ring)
  rw [this, map_add, map_smul, shiftedPiKernelInt_vecOne]
  simp only [smul_eq_mul]
  ring

theorem shiftedPi_reg_psiCube (ht : 0 < t) (h1 : C₁ C' = C₁ C + a) :
    shiftedPiReg N κ C' (ξ ω) x t .psiCube =
      shiftedPiReg N κ C (ξ ω) x t .psiCube - 3 * a * shiftedPiReg N κ C (ξ ω) x t .psi := by
  rw [shiftedPi_reg_eq x hf hg ht, shiftedPi_reg_eq x hf hg ht, shiftedPi_reg_eq x hf hg ht]
  have : shiftedPiVec (N := N) (κ := κ) x hf hg ht C' .psiCube =
      shiftedPiVec (N := N) (κ := κ) x hf hg ht C .psiCube +
        (-(3 * a)) • shiftedPiVec (N := N) (κ := κ) x hf hg ht C .psi :=
    Subtype.ext (funext fun y => by
      simp only [shiftedPiVec, Submodule.coe_add, Submodule.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, shiftedPi_shift_psiCube x hf h1 y]
      ring)
  rw [this, map_add, map_smul]
  simp only [smul_eq_mul]
  ring

theorem shiftedPi_reg_psiSqX (ht : 0 < t) (h1 : C₁ C' = C₁ C + a) (k : Fin 3) :
    shiftedPiReg N κ C' (ξ ω) x t (.psiSqX k) =
      shiftedPiReg N κ C (ξ ω) x t (.psiSqX k) - a * shiftedPiMoment t x k := by
  rw [shiftedPi_reg_eq x hf hg ht, shiftedPi_reg_eq x hf hg ht]
  have : shiftedPiVec (N := N) (κ := κ) x hf hg ht C' (.psiSqX k) =
      shiftedPiVec (N := N) (κ := κ) x hf hg ht C (.psiSqX k) +
        (-a) • shiftedPiVecCoord x ht k :=
    Subtype.ext (funext fun y => by
      simp only [shiftedPiVec, shiftedPiVecCoord, Submodule.coe_add, Submodule.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, shiftedPi_shift_psiSqX x hf h1 k y]
      ring)
  rw [this, map_add, map_smul, shiftedPiKernelInt_vecCoord]
  simp only [smul_eq_mul]
  ring

end RegularityStructures.Phi43

end
