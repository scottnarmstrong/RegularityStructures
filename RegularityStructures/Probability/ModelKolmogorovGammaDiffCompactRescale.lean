/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaNormConversion
public import RegularityStructures.Probability.ModelKolmogorovGammaMeasurability
public import RegularityStructures.Probability.ModelKolmogorovHSCompactRescale
public import RegularityStructures.Statements.Defs.IsContinuousRandomModelWithFieldsOn

/-!
# Compact rescaling for the Gamma difference envelope

This module passes from the unit box to general compact sets in the Kolmogorov criterion for models.
The unit-box induction is applied to the Gamma-only pullback model obtained from the parabolic
affine normalization. The pullback has zero `Π` component and the original `Γ` component evaluated
at the inverse affine map. Thus its Gamma difference bound pulls back exactly, while the zero `Π`
component makes the continuity of the regularised fields automatic in the regularised-field
coordinate.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {𝒯 : RegularityStructure ι}

/-- The Gamma-only model obtained by pulling a model back through the compact
parabolic normalization. -/
def gammaDiffCompactPullbackModel
    (M : Model 𝒯 parabolicSemigroup) (L : ℝ) (hL : L ≠ 0) :
    Model 𝒯 parabolicSemigroup where
  pi := 0
  gamma := fun x y =>
    M.gamma ((hsParabolicBoxHomeomorph hL).symm x)
      ((hsParabolicBoxHomeomorph hL).symm y)
  pi_gamma := by simp
  gamma_self := by
    intro x
    exact M.gamma_self _
  gamma_mul := by
    intro x y z
    exact M.gamma_mul _ _ _
  measurable_diag := by
    intro i t ht
    exact measurable_const
  measurable_pi := by
    intro x i t ht
    exact measurable_const

theorem gammaDiffCompactPullbackModel_gammaMap
    (M : Model 𝒯 parabolicSemigroup) (L : ℝ) (hL : L ≠ 0)
    (x y : ParabolicSpace) (τ : ι → ℝ) :
    (gammaDiffCompactPullbackModel M L hL).gammaMap x y τ =
      M.gammaMap ((hsParabolicBoxHomeomorph hL).symm x)
        ((hsParabolicBoxHomeomorph hL).symm y) τ := rfl

private theorem gammaDiffCompactPullback_map
    {S T : Set ParabolicSpace} (L : ℝ) (hL : 0 < L)
    (f : S ≃ₜ T)
    (hf : ∀ z : T, ((f.symm z : S) : ParabolicSpace) =
      (hsParabolicBoxHomeomorph hL.ne').symm (z : ParabolicSpace))
    (x : S) :
    ((f x : T) : ParabolicSpace) =
      hsParabolicBoxHomeomorph hL.ne' (x : ParabolicSpace) := by
  have heq : (hsParabolicBoxHomeomorph hL.ne').symm (f x : ParabolicSpace) =
      (x : ParabolicSpace) := by
    calc
      (hsParabolicBoxHomeomorph hL.ne').symm (f x : ParabolicSpace) =
          ((f.symm (f x) : S) : ParabolicSpace) := by
            symm
            exact hf (f x)
      _ = (x : ParabolicSpace) := by simp
  calc
    ((f x : T) : ParabolicSpace) =
        (hsParabolicBoxHomeomorph hL.ne')
          ((hsParabolicBoxHomeomorph hL.ne').symm (f x : ParabolicSpace)) := by
            rw [(hsParabolicBoxHomeomorph hL.ne').apply_symm_apply]
    _ = (hsParabolicBoxHomeomorph hL.ne') (x : ParabolicSpace) := by
          rw [heq]

private theorem gammaDiffCompactPullback_positive_rpow_le
    {L d a : ℝ} (hL : 1 ≤ L) (hd : 0 ≤ d) (ha : 0 ≤ a) :
    (L⁻¹ * d) ^ a ≤ d ^ a := by
  have hLin : 0 ≤ L⁻¹ := by positivity
  have hinv : L⁻¹ ≤ 1 := (inv_le_one₀ (by linarith : 0 < L)).2 hL
  have hLd : L⁻¹ * d ≤ d := by
    calc
      L⁻¹ * d ≤ 1 * d :=
        mul_le_mul_of_nonneg_right hinv hd
      _ = d := one_mul d
  exact Real.rpow_le_rpow (by positivity) hLd ha

/-! Continuity of the regularised fields survives the Gamma-only pullback. -/
theorem isContinuousRandomModelWithFieldsOn_gammaDiffCompactPullback
    {Ω : Type*} [MeasurableSpace Ω]
    {S T : Set ParabolicSpace} (L : ℝ) (hL : 0 < L)
    (f : S ≃ₜ T)
    (hf : ∀ z : T, ((f.symm z : S) : ParabolicSpace) =
      (hsParabolicBoxHomeomorph hL.ne').symm (z : ParabolicSpace))
    (Z : Ω → Model 𝒯 parabolicSemigroup)
    (hZ : IsContinuousRandomModelWithFieldsOn Z S) :
    IsContinuousRandomModelWithFieldsOn
      (fun ω => gammaDiffCompactPullbackModel (Z ω) L hL.ne') T := by
  rcases hZ with ⟨hZ, hZwhole⟩
  rcases hZ with ⟨hdiag, hgammaMeas, hregCont, hgammaCont⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i x t ht
      simp [gammaDiffCompactPullbackModel, Model.regPi]
    · intro i j x y
      simpa only [gammaDiffCompactPullbackModel_gammaMap] using
        hgammaMeas i j
          ((hsParabolicBoxHomeomorph hL.ne').symm x)
          ((hsParabolicBoxHomeomorph hL.ne').symm y)
    · intro ω i
      simpa [gammaDiffCompactPullbackModel, Model.regPi] using
        (continuous_const.continuousOn :
          ContinuousOn (fun _ : ℝ × ParabolicSpace => (0 : ℝ))
            (Set.Ioc (0 : ℝ) 1 ×ˢ T))
    · intro ω i j
      apply continuousOn_iff_continuous_domRestrict.mpr
      let eT : (T ×ˢ T) ≃ₜ T × T := Homeomorph.Set.prod T T
      let eS : (S ×ˢ S) ≃ₜ S × S := Homeomorph.Set.prod S S
      let g : (T ×ˢ T) → (S ×ˢ S) :=
        eS.symm ∘ (f.symm.prodCongr f.symm) ∘ eT
      have hg : Continuous g := by
        exact eS.symm.continuous.comp
          ((f.symm.prodCongr f.symm).continuous.comp eT.continuous)
      have hc := (hgammaCont ω i j).domRestrict.comp hg
      change Continuous (fun z : (T ×ˢ T) =>
        (Z ω).gammaMap
          ((f.symm ⟨z.1.2, z.2.2⟩ : S) : ParabolicSpace)
          ((f.symm ⟨z.1.1, z.2.1⟩ : S) : ParabolicSpace)
          (Pi.single i 1) j) at hc
      change Continuous (fun z : (T ×ˢ T) =>
        (gammaDiffCompactPullbackModel (Z ω) L hL.ne').gammaMap
          z.1.2 z.1.1 (Pi.single i 1) j)
      simpa only [gammaDiffCompactPullbackModel_gammaMap, hf] using hc
  · intro ω i x
    simpa [gammaDiffCompactPullbackModel, Model.regPi] using
      (continuous_const.continuousOn :
        ContinuousOn (fun _ : ℝ × ParabolicSpace => (0 : ℝ))
          (Set.Ioc (0 : ℝ) 1 ×ˢ Set.univ))

/-! Pull a unit-box Gamma difference bound back to the original compact set. -/
theorem gammaDiffBoundOn_of_gammaDiffCompactPullback
    {S T : Set ParabolicSpace} (L : ℝ) (hL : 1 ≤ L)
    (f : S ≃ₜ T)
    (hf : ∀ z : T, ((f.symm z : S) : ParabolicSpace) =
      (hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm
        (z : ParabolicSpace))
    (M₁ M₂ : Model 𝒯 parabolicSemigroup) (γ C : ℝ) (hC : 0 ≤ C)
    (hbound :
      (gammaDiffCompactPullbackModel M₁ L (by linarith : L ≠ 0)).GammaDiffBoundOn
        (gammaDiffCompactPullbackModel M₂ L (by linarith : L ≠ 0)) γ C T) :
    M₁.GammaDiffBoundOn M₂ γ C S := by
  let hLpos : 0 < L := by linarith
  let hLne : L ≠ 0 := hLpos.ne'
  intro i j hi hj x hx y hy
  let xS : S := ⟨x, hx⟩
  let yS : S := ⟨y, hy⟩
  have h := hbound i j hi hj (f xS) (f xS).property (f yS) (f yS).property
  have hmapx := gammaDiffCompactPullback_map L hLpos f hf xS
  have hmapy := gammaDiffCompactPullback_map L hLpos f hf yS
  have hscale' :
      parabolicSemigroup.scaleDist
          (hsParabolicBoxHomeomorph hLne (y : ParabolicSpace))
          (hsParabolicBoxHomeomorph hLne (x : ParabolicSpace)) =
        L⁻¹ * parabolicSemigroup.scaleDist y x := by
    change parabolicNorm
        (hsParabolicBoxHomeomorph hLne (y : ParabolicSpace) -
          hsParabolicBoxHomeomorph hLne (x : ParabolicSpace)) =
        L⁻¹ * parabolicNorm ((y : ParabolicSpace) - x)
    exact parabolicNorm_sub_hsParabolicBoxHomeomorph hLpos _ _
  have hβ : 0 ≤ 𝒯.deg i - 𝒯.deg j := by linarith
  rw [gammaDiffCompactPullbackModel_gammaMap,
    gammaDiffCompactPullbackModel_gammaMap] at h
  rw [hmapx, hmapy] at h
  simp only [Homeomorph.symm_apply_apply] at h
  rw [hscale'] at h
  calc
    |M₁.gammaMap y x (Pi.single i 1) j -
        M₂.gammaMap y x (Pi.single i 1) j| ≤
      C * (L⁻¹ * parabolicSemigroup.scaleDist y x) ^
        (𝒯.deg i - 𝒯.deg j) := by simpa using h
    _ ≤ C * parabolicSemigroup.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg j) := by
      exact mul_le_mul_of_nonneg_left
        (gammaDiffCompactPullback_positive_rpow_le hL
          (parabolicSemigroup.scaleDist_nonneg _ _) hβ) hC

/-! The Gamma-difference moment bound on a general compact set. -/
theorem randomModel_gammaDiffNormOn_moment_le_of_compactPullbackEnvelope
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {S T : Set ParabolicSpace} (L : ℝ) (hL : 1 ≤ L)
    (f : S ≃ₜ T)
    (hf : ∀ z : T, ((f.symm z : S) : ParabolicSpace) =
      (hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm
        (z : ParabolicSpace))
    (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup) (γ : ℝ) (p : ℕ)
    (hZ₁ : IsContinuousRandomModelWithFieldsOn Z₁ S)
    (hZ₂ : IsContinuousRandomModelWithFieldsOn Z₂ S)
    {B : Ω → ℝ≥0∞} {A : ℝ≥0∞}
    (_hB : AEMeasurable B P)
    (hBtop : ∀ᵐ ω ∂P, B ω ≠ ∞)
    (hMoment : ∫⁻ ω, B ω ^ p ∂P ≤ A)
    (hPullback : ∀ᵐ ω ∂P,
      (gammaDiffCompactPullbackModel (Z₁ ω) L (by linarith : L ≠ 0)).GammaDiffBoundOn
        (gammaDiffCompactPullbackModel (Z₂ ω) L (by linarith : L ≠ 0)) γ
        (B ω).toNNReal T) :
    AEMeasurable (fun ω => (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ S) P ∧
      ∫⁻ ω, (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ S ^ p ∂P ≤ A := by
  have hOriginal : ∀ᵐ ω ∂P,
      (Z₁ ω).GammaDiffBoundOn (Z₂ ω) γ (B ω).toNNReal S := by
    filter_upwards [hBtop, hPullback] with ω htop hω
    exact gammaDiffBoundOn_of_gammaDiffCompactPullback L hL f hf
      (Z₁ ω) (Z₂ ω) γ (B ω).toNNReal (by positivity) hω
  refine ⟨randomModel_gammaDiffNormOn_aemeasurable_of_continuousWithFields
      hZ₁ hZ₂ γ, ?_⟩
  exact randomModel_gammaDiffNormOn_moment_le_of_gammaDiffBound
    Z₁ Z₂ γ S p hOriginal hBtop hMoment

end RegularityStructures

end
