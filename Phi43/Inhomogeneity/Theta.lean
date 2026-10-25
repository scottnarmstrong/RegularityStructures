/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Inhomogeneity.DuhamelLinear
public import Phi43.Inhomogeneity.Inhom
public import RegularityStructures.Abstract.Model

/-!
# The inhomogeneity with the jet of the Duhamel field `θ`

[Hai14, Section 9.4]. Specialisation of `phi43InhomSlab` to the jet of the Duhamel field
`θ = duhamelField g` of a smooth spatially periodic forcing `g` (in the application
`g = ζ = Q ∗ f` shifted to the restart time).  The derivative bounds of `θ` follow from those of
`g` (`derivBound_duhamelField`), with constants `thetaKc Gc k = duhCst (k 0) · Gc (wt k)`.

* `phi43InhomTheta`: `Ψ·1_{slab} + datumSlab w + jet θ`;
* `norm_phi43InhomTheta_le`: `‖v‖ ≤ 1 + datumConst η 3 ‖w‖ + liftConst 3 (thetaKc Gc) · B`;
* `singularDiffBoundOn_phi43InhomTheta`: two models, with `B'` the bound on the difference of the
  forcings.
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The derivative constants of the Duhamel field in terms of those of the forcing. -/
def thetaKc (Gc : ℕ → ℝ) : (Fin 4 → ℕ) → ℝ :=
  fun k => Inhomogeneity.duhCst (k 0) * Gc (2 * k 0 + k 1 + k 2 + k 3)

end RegularityStructures.Phi43

end

public section

open scoped ContDiff

namespace RegularityStructures.Phi43

open Inhomogeneity

theorem thetaKc_nonneg {Gc : ℕ → ℝ} (hGc : ∀ L, 0 ≤ Gc L) (k : Fin 4 → ℕ) : 0 ≤ thetaKc Gc k :=
  mul_nonneg (duhCst_nonneg _) (hGc _)

theorem measurable_duhamelField {g : ParabolicSpace → ℝ} (hg : PerSmooth g) :
    Measurable (duhamelField hg) :=
  Datum.measurable_of_smoothPos (smoothPos_duhamelField hg) fun _ hz =>
    duhamelField_of_nonpos hg hz

end RegularityStructures.Phi43

end

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open Inhomogeneity

/-- **The inhomogeneity `v = Ψ·1_{slab} + datumLift(w) + jet(θ)`** with `θ` the Duhamel field of
the forcing `g`. -/
def phi43InhomTheta (κ : Kappa) (η : NegExponent)
    (M : Model (phi43RegularityStructureF κ) parabolicSemigroup)
    (hM : M.IsPolyCompatible (phi43PolynomialSectorF κ)) {T : ℝ} (hT : T ≤ 1)
    (w : HolderBesov η) {g : ParabolicSpace → ℝ} (hg : PerSmooth g) {B : ℝ} (hB : 0 ≤ B)
    {Gc : ℕ → ℝ} (hGc : ∀ L, 0 ≤ Gc L) (hG : ∀ L, DerivHyp g (Gc L * B) L) :
    M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T) :=
  phi43InhomSlab κ η M hM hT w
    (derivBound_duhamelField hg η.2.le hB Gc hGc hG) (measurable_duhamelField hg) hB
    (thetaKc_nonneg hGc)

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

open Inhomogeneity

/-- **The norm of the inhomogeneity.** -/
theorem norm_phi43InhomTheta_le (κ : Kappa) (η : NegExponent)
    (M : Model (phi43RegularityStructureF κ) parabolicSemigroup)
    (hM : M.IsPolyCompatible (phi43PolynomialSectorF κ)) {T : ℝ} (hT : T ≤ 1)
    (w : HolderBesov η) {g : ParabolicSpace → ℝ} (hg : PerSmooth g) {B : ℝ} (hB : 0 ≤ B)
    {Gc : ℕ → ℝ} (hGc : ∀ L, 0 ≤ Gc L) (hG : ∀ L, DerivHyp g (Gc L * B) L) :
    ‖phi43InhomTheta κ η M hM hT w hg hB hGc hG‖ ≤
      1 + datumConst η 3 * ‖w‖ + Datum.liftConst 3 (thetaKc Gc) * B :=
  norm_phi43InhomSlab_le κ η M hM hT w _ _ hB _

/-- **Two models.** The forcings `g₁, g₂` have the derivative bounds `Gc · B₁`, `Gc · B₂`,
and their difference `Gc · B'`. -/
theorem singularDiffBoundOn_phi43InhomTheta (κ : Kappa) (η : NegExponent)
    (M₁ M₂ : Model (phi43RegularityStructureF κ) parabolicSemigroup)
    (h₁ : M₁.IsPolyCompatible (phi43PolynomialSectorF κ))
    (h₂ : M₂.IsPolyCompatible (phi43PolynomialSectorF κ)) {T : ℝ} (hT : T ≤ 1)
    (w₁ w₂ : HolderBesov η) {g₁ g₂ : ParabolicSpace → ℝ} (hg₁ : PerSmooth g₁)
    (hg₂ : PerSmooth g₂) {B₁ B₂ B' : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB' : 0 ≤ B')
    {Gc : ℕ → ℝ} (hGc : ∀ L, 0 ≤ Gc L) (hG₁ : ∀ L, DerivHyp g₁ (Gc L * B₁) L)
    (hG₂ : ∀ L, DerivHyp g₂ (Gc L * B₂) L) (hG' : ∀ L, DerivHyp (g₁ - g₂) (Gc L * B') L) :
    M₁.SingularDiffBoundOn M₂ timeZeroDist (gamma κ) η
      (0 + datumConst η 3 * ‖w₁ - w₂‖ + Datum.liftConst 3 (thetaKc Gc) * B') (timeSlab T)
      (phi43InhomTheta κ η M₁ h₁ hT w₁ hg₁ hB₁ hGc hG₁).val
      (phi43InhomTheta κ η M₂ h₂ hT w₂ hg₂ hB₂ hGc hG₂).val := by
  have hd : Datum.DerivBound (η : ℝ) B' (thetaKc Gc) (duhamelField hg₁ - duhamelField hg₂) := by
    rw [← duhamelField_sub hg₁ hg₂]
    exact derivBound_duhamelField (hg₁.sub hg₂) η.2.le hB' Gc hGc hG'
  exact singularDiffBoundOn_phi43InhomSlab κ η M₁ M₂ h₁ h₂ hT w₁ w₂ _ _
    (measurable_duhamelField hg₁) (measurable_duhamelField hg₂) hB₁ hB₂ hd hB' (thetaKc_nonneg hGc)

end RegularityStructures.Phi43

end
