/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Inhomogeneity.Psi
public import Phi43.Inhomogeneity.DatumSlab
public import Phi43.FixedPointF.Hypotheses
public import RegularityStructures.Abstract.Model

/-!
# The inhomogeneity `v = Ψ · 1_{slab} + datumLift(w) + jet(θ)` of the `Φ⁴₃` fixed point

[Hai14, Section 9.4, Lemma 7.5]. For the enlarged structure, the polynomial sector
`phi43PolynomialSectorF κ` (order `3`) and the solution sector `V = phi43SectorV`,
`phi43InhomSlab` is the element
`Ψ · 1_{(0,T]×ℝ³} + datumSlab (w) + liftSlabElem (θ)` of
`M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T)`, where

* `w ∈ 𝒞^η` is the datum of the free heat evolution,
* `θ` is a smooth function with `DerivBound η B Kc θ` (a bounded jet).

Bounds (`T ≤ 1`, `M` polynomial compatible, for instance by `IsRealisingP.poly`):

* `‖v‖ ≤ 1 + datumConst η 3 * ‖w‖_η + liftConst 3 Kc * B` (`norm_phi43InhomSlab_le`);
* for two models, `|||v₁; v₂||| ≤ datumConst η 3 * ‖w₁ - w₂‖_η + liftConst 3 Kc * B'` where
  `B'` bounds the derivatives of `θ₁ - θ₂` (`singularDiffBoundOn_phi43InhomSlab`).
-/

public section

namespace RegularityStructures.Phi43

theorem phi43_gamma_pos (κ : Kappa) : 0 < gamma κ := by
  have := κ.2.1
  simp only [gamma]
  linarith

theorem phi43_gamma_le_three (κ : Kappa) : gamma κ ≤ ((3 : ℕ) : ℝ) := by
  have := κ.2.2
  simp only [gamma]
  push_cast
  linarith

end RegularityStructures.Phi43

end

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

/-- **The inhomogeneity of the fixed point at a restart time.** -/
def phi43InhomSlab (κ : Kappa) (η : NegExponent)
    (M : Model (phi43RegularityStructureF κ) parabolicSemigroup)
    (hM : M.IsPolyCompatible (phi43PolynomialSectorF κ)) {T : ℝ} (hT : T ≤ 1)
    (w : HolderBesov η) {B : ℝ} {Kc : (Fin 4 → ℕ) → ℝ} {θ : ParabolicSpace → ℝ}
    (hθ : Datum.DerivBound (η : ℝ) B Kc θ) (hθm : Measurable θ) (hB : 0 ≤ B)
    (hKc : ∀ k, 0 ≤ Kc k) :
    M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T) :=
  phi43PsiSlab κ η T M +
    Inhomogeneity.datumSlab M (phi43PolynomialSectorF κ) (phi43_hpolyV κ) hM w
      (phi43_gamma_pos κ) (phi43_gamma_le_three κ) hT +
    Inhomogeneity.liftSlabElem M (phi43PolynomialSectorF κ) (phi43_hpolyV κ) hM hθ hθm η.2 hB hKc
      (phi43_gamma_pos κ) (phi43_gamma_le_three κ) hT

end RegularityStructures.Phi43

end

public section

open MeasureTheory Set

namespace RegularityStructures.Phi43

theorem phi43InhomSlab_val (κ : Kappa) (η : NegExponent)
    (M : Model (phi43RegularityStructureF κ) parabolicSemigroup)
    (hM : M.IsPolyCompatible (phi43PolynomialSectorF κ)) {T : ℝ} (hT : T ≤ 1)
    (w : HolderBesov η) {B : ℝ} {Kc : (Fin 4 → ℕ) → ℝ} {θ : ParabolicSpace → ℝ}
    (hθ : Datum.DerivBound (η : ℝ) B Kc θ) (hθm : Measurable θ) (hB : 0 ≤ B)
    (hKc : ∀ k, 0 ≤ Kc k) :
    (phi43InhomSlab κ η M hM hT w hθ hθm hB hKc).val =
      Inhomogeneity.slabConst T phi43PsiVec +
        Inhomogeneity.liftSlab (phi43PolynomialSectorF κ) (gamma κ) T (Datum.datumField η w) +
        Inhomogeneity.liftSlab (phi43PolynomialSectorF κ) (gamma κ) T θ :=
  rfl

/-- **The norm of the inhomogeneity** is at most
`1 + datumConst η 3 * ‖w‖_η + liftConst 3 Kc * B`. -/
theorem norm_phi43InhomSlab_le (κ : Kappa) (η : NegExponent)
    (M : Model (phi43RegularityStructureF κ) parabolicSemigroup)
    (hM : M.IsPolyCompatible (phi43PolynomialSectorF κ)) {T : ℝ} (hT : T ≤ 1)
    (w : HolderBesov η) {B : ℝ} {Kc : (Fin 4 → ℕ) → ℝ} {θ : ParabolicSpace → ℝ}
    (hθ : Datum.DerivBound (η : ℝ) B Kc θ) (hθm : Measurable θ) (hB : 0 ≤ B)
    (hKc : ∀ k, 0 ≤ Kc k) :
    ‖phi43InhomSlab κ η M hM hT w hθ hθm hB hKc‖ ≤
      1 + Inhomogeneity.datumConst η 3 * ‖w‖ + Datum.liftConst 3 Kc * B := by
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    (norm_phi43PsiSlab_le κ η T M)
    (Inhomogeneity.norm_datumSlab_le M _ _ hM w _ _ hT))) ?_)
  exact Inhomogeneity.norm_liftSlabElem_le M _ _ hM hθ hθm η.2 hB hKc _ _ hT

/-- **Two models.** The comparison norm of the inhomogeneities of two models, built from
data `w₁, w₂` and jets `θ₁, θ₂` with `DerivBound η B' Kc (θ₁ - θ₂)`, is at most
`datumConst η 3 * ‖w₁ - w₂‖_η + liftConst 3 Kc * B'` (the `Ψ`-parts cancel). -/
theorem singularDiffBoundOn_phi43InhomSlab (κ : Kappa) (η : NegExponent)
    (M₁ M₂ : Model (phi43RegularityStructureF κ) parabolicSemigroup)
    (h₁ : M₁.IsPolyCompatible (phi43PolynomialSectorF κ))
    (h₂ : M₂.IsPolyCompatible (phi43PolynomialSectorF κ)) {T : ℝ} (hT : T ≤ 1)
    (w₁ w₂ : HolderBesov η) {B₁ B₂ B' : ℝ} {Kc : (Fin 4 → ℕ) → ℝ} {θ₁ θ₂ : ParabolicSpace → ℝ}
    (hθ₁ : Datum.DerivBound (η : ℝ) B₁ Kc θ₁) (hθ₂ : Datum.DerivBound (η : ℝ) B₂ Kc θ₂)
    (hθ₁m : Measurable θ₁) (hθ₂m : Measurable θ₂) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hθ : Datum.DerivBound (η : ℝ) B' Kc (θ₁ - θ₂)) (hB' : 0 ≤ B') (hKc : ∀ k, 0 ≤ Kc k) :
    M₁.SingularDiffBoundOn M₂ timeZeroDist (gamma κ) η
      (0 + Inhomogeneity.datumConst η 3 * ‖w₁ - w₂‖ + Datum.liftConst 3 Kc * B') (timeSlab T)
      (phi43InhomSlab κ η M₁ h₁ hT w₁ hθ₁ hθ₁m hB₁ hKc).val
      (phi43InhomSlab κ η M₂ h₂ hT w₂ hθ₂ hθ₂m hB₂ hKc).val := by
  rw [phi43InhomSlab_val, phi43InhomSlab_val]
  refine Model.SingularDiffBoundOn.add (Model.SingularDiffBoundOn.add
    (singularDiffBoundOn_phi43PsiSlab κ η T M₁ M₂)
    (Inhomogeneity.singularDiffBoundOn_datumSlab (phi43PolynomialSectorF κ) (phi43_hpolyV κ) h₁
      h₂ w₁ w₂ (phi43_gamma_pos κ) (phi43_gamma_le_three κ) hT)) ?_
  exact Inhomogeneity.singularDiffBoundOn_liftSlab h₁ h₂ hθ₁.smooth hθ₂.smooth hθ η.2 hB' hKc
    (phi43_gamma_pos κ) (phi43_gamma_le_three κ) hT

end RegularityStructures.Phi43

end
