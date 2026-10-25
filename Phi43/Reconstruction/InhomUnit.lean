/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.UnitCoeff
public import Phi43.Inhomogeneity.Theta

/-!
# The unit coefficient of the inhomogeneity

For `v = phi43InhomTheta κ η M hM hT w hg hB hGc hG = Ψ·1_{slab} + datumSlab w + jet θ`, at a point
`x` of the time slab: `v(x)_1 = (P_t w)(x) + θ(x)` (`phi43InhomTheta_unit`), where
`(P_t w)(x) = datumField η w x` and `θ = duhamelField hg`; and `v(x) - Ψ` is a polynomial
(`phi43InhomTheta_sub_psi_mem`).
-/

public section

open scoped ContDiff

namespace RegularityStructures.Phi43

open Inhomogeneity

theorem liftCoeff_one (F : ParabolicSpace → ℝ) (x : ParabolicSpace) (κ : Kappa) :
    Datum.liftCoeff 3 (gamma κ) F x phi43OneIdx = F x := by
  have hk : 0 < κ.1 := κ.2.1
  have h : polyDeg 3 phi43OneIdx < gamma κ := by
    simp only [polyDeg, phi43OneIdx, gamma]
    simp
    linarith
  simp only [Datum.liftCoeff, h, ite_true]
  have e : ((⇑(phi43OneIdx.1 : Fin 4 →₀ ℕ)) : Fin 4 → ℕ) = 0 := by
    funext i; simp [phi43OneIdx]
  rw [e]
  simp [Datum.D, Datum.pdIter, Datum.multiFactorial]

theorem liftSlab_unit (κ : Kappa) {T : ℝ} (F : ParabolicSpace → ℝ) {x : ParabolicSpace}
    (hx : x ∈ timeSlab T) :
    liftSlab (phi43PolynomialSectorF κ) (gamma κ) T F x (.old .one) = F x := by
  rw [liftSlab_of_mem _ _ _ hx, ← emb_phi43OneIdx κ, Datum.liftOf_apply_emb, liftCoeff_one]

theorem phi43InhomSlab_unit (κ : Kappa) (η : NegExponent)
    (M : Model (phi43RegularityStructureF κ) parabolicSemigroup)
    (hM : M.IsPolyCompatible (phi43PolynomialSectorF κ)) {T : ℝ} (hT : T ≤ 1)
    (w : HolderBesov η) {B : ℝ} {Kc : (Fin 4 → ℕ) → ℝ} {θ : ParabolicSpace → ℝ}
    (hθ : Datum.DerivBound (η : ℝ) B Kc θ) (hθm : Measurable θ) (hB : 0 ≤ B)
    (hKc : ∀ k, 0 ≤ Kc k) {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    (phi43InhomSlab κ η M hM hT w hθ hθm hB hKc).val x (.old .one) =
      Datum.datumField η w x + θ x := by
  rw [phi43InhomSlab_val]
  simp only [Pi.add_apply, slabConst_of_mem _ hx, liftSlab_unit κ _ hx]
  simp [phi43PsiVec]

theorem phi43InhomSlab_sub_psi_mem (κ : Kappa) (η : NegExponent)
    (M : Model (phi43RegularityStructureF κ) parabolicSemigroup)
    (hM : M.IsPolyCompatible (phi43PolynomialSectorF κ)) {T : ℝ} (hT : T ≤ 1)
    (w : HolderBesov η) {B : ℝ} {Kc : (Fin 4 → ℕ) → ℝ} {θ : ParabolicSpace → ℝ}
    (hθ : Datum.DerivBound (η : ℝ) B Kc θ) (hθm : Measurable θ) (hB : 0 ≤ B)
    (hKc : ∀ k, 0 ≤ Kc k) {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    (phi43InhomSlab κ η M hM hT w hθ hθm hB hKc).val x - phi43EF .psi ∈
      (phi43PolynomialSectorF κ).subspace := by
  rw [phi43InhomSlab_val]
  simp only [Pi.add_apply, slabConst_of_mem _ hx, liftSlab_of_mem _ _ _ hx]
  have : phi43PsiVec + Datum.liftOf (phi43PolynomialSectorF κ) (gamma κ) (Datum.datumField η w) x +
      Datum.liftOf (phi43PolynomialSectorF κ) (gamma κ) θ x - phi43EF .psi =
      Datum.liftOf (phi43PolynomialSectorF κ) (gamma κ) (Datum.datumField η w) x +
      Datum.liftOf (phi43PolynomialSectorF κ) (gamma κ) θ x := by
    change phi43EF .psi + _ + _ - phi43EF .psi = _
    abel
  rw [this]
  exact Submodule.add_mem _ (Datum.liftOf_mem_subspace _ _ _ _) (Datum.liftOf_mem_subspace _ _ _ _)

theorem phi43InhomTheta_unit (κ : Kappa) (η : NegExponent)
    (M : Model (phi43RegularityStructureF κ) parabolicSemigroup)
    (hM : M.IsPolyCompatible (phi43PolynomialSectorF κ)) {T : ℝ} (hT : T ≤ 1)
    (w : HolderBesov η) {g : ParabolicSpace → ℝ} (hg : PerSmooth g) {B : ℝ} (hB : 0 ≤ B)
    {Gc : ℕ → ℝ} (hGc : ∀ L, 0 ≤ Gc L) (hG : ∀ L, DerivHyp g (Gc L * B) L)
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    (phi43InhomTheta κ η M hM hT w hg hB hGc hG).val x (.old .one) =
      Datum.datumField η w x + duhamelField hg x :=
  phi43InhomSlab_unit κ η M hM hT w _ _ hB _ hx

theorem phi43InhomTheta_sub_psi_mem (κ : Kappa) (η : NegExponent)
    (M : Model (phi43RegularityStructureF κ) parabolicSemigroup)
    (hM : M.IsPolyCompatible (phi43PolynomialSectorF κ)) {T : ℝ} (hT : T ≤ 1)
    (w : HolderBesov η) {g : ParabolicSpace → ℝ} (hg : PerSmooth g) {B : ℝ} (hB : 0 ≤ B)
    {Gc : ℕ → ℝ} (hGc : ∀ L, 0 ≤ Gc L) (hG : ∀ L, DerivHyp g (Gc L * B) L)
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    (phi43InhomTheta κ η M hM hT w hg hB hGc hG).val x - phi43EF .psi ∈
      (phi43PolynomialSectorF κ).subspace :=
  phi43InhomSlab_sub_psi_mem κ η M hM hT w _ _ hB _ hx

end RegularityStructures.Phi43

end
