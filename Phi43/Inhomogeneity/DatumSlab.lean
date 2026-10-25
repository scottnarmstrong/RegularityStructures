/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Inhomogeneity.LiftSlab
public import RegularityStructures.Abstract.Model

/-!
# The slab-space element of the lift of the heat evolution of a datum

[Hai14, Lemma 7.5]. For `a ∈ 𝒞^η` (`η < 0`), the Taylor lift `datumLift P γ₀ a` of the free heat
evolution `P_t a` cut to the slab `(0, T] × ℝ³` is the element `datumSlab` of
`SlabSpace timeZeroDist V γ₀ η (timeSlab T)`, with

* `‖datumSlab a‖ ≤ datumConst η N * ‖a‖_η` (`norm_datumSlab_le`),
* two models: `|||datumSlab a; datumSlab b||| ≤ datumConst η N * ‖a - b‖_η`
  (`singularDiffBoundOn_datumSlab`), for polynomial compatible models.

The constant `datumConst η N = liftConst N Kc_η` depends only on `η` and the polynomial order `N`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Inhomogeneity

/-- The universal derivative constants of the heat evolution of a datum in `𝒞^η`. -/
def datumKc (η : NegExponent) : (Fin 4 → ℕ) → ℝ :=
  (Datum.exists_derivBound η).choose

/-- The constant of the singular bound of the lift of the heat evolution of a datum. -/
def datumConst (η : NegExponent) (N : ℕ) : ℝ :=
  Datum.liftConst N (datumKc η)

end RegularityStructures.Inhomogeneity

end

public section

open MeasureTheory Set

namespace RegularityStructures.Inhomogeneity

theorem datumKc_nonneg (η : NegExponent) (k : Fin 4 → ℕ) : 0 ≤ datumKc η k :=
  (Datum.exists_derivBound η).choose_spec.1 k

theorem datumKc_spec (η : NegExponent) (a : HolderBesov η) :
    Datum.DerivBound (η : ℝ) ‖a‖ (datumKc η) (Datum.datumField η a) :=
  (Datum.exists_derivBound η).choose_spec.2 a

theorem datumConst_nonneg (η : NegExponent) (N : ℕ) : 0 ≤ datumConst η N :=
  Datum.liftConst_nonneg (datumKc_nonneg η)

theorem measurable_datumField (η : NegExponent) (a : HolderBesov η) :
    Measurable (Datum.datumField η a) :=
  Datum.measurable_of_smoothPos (Datum.smoothPos_datumField η a)
    fun _ hz => Datum.datumField_of_nonpos η a hz

end RegularityStructures.Inhomogeneity

end

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Inhomogeneity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}

/-- **The datum lift as an element of the slab space.** -/
def datumSlab (M : Model 𝒯 parabolicSemigroup) (P : PolynomialSector 𝒯 N)
    {V : Submodule ℝ (ι → ℝ)} (hPV : ∀ k, (Pi.single (P.emb k) 1 : ι → ℝ) ∈ V)
    (hM : M.IsPolyCompatible P) {η : NegExponent} (a : HolderBesov η) {γ₀ : ℝ} (hγ₀ : 0 < γ₀)
    (hγN : γ₀ ≤ N) {T : ℝ} (hT : T ≤ 1) :
    M.SlabSpace timeZeroDist V γ₀ η (timeSlab T) :=
  liftSlabElem M P hPV hM (datumKc_spec η a) (measurable_datumField η a) η.2 (norm_nonneg a)
    (datumKc_nonneg η) hγ₀ hγN hT

end RegularityStructures.Inhomogeneity

end

public section

open MeasureTheory Set

namespace RegularityStructures.Inhomogeneity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}

/-- **The norm of the datum lift** is at most `datumConst η N * ‖a‖_η`. -/
theorem norm_datumSlab_le (M : Model 𝒯 parabolicSemigroup) (P : PolynomialSector 𝒯 N)
    {V : Submodule ℝ (ι → ℝ)} (hPV : ∀ k, (Pi.single (P.emb k) 1 : ι → ℝ) ∈ V)
    (hM : M.IsPolyCompatible P) {η : NegExponent} (a : HolderBesov η) {γ₀ : ℝ} (hγ₀ : 0 < γ₀)
    (hγN : γ₀ ≤ N) {T : ℝ} (hT : T ≤ 1) :
    ‖datumSlab M P hPV hM a hγ₀ hγN hT‖ ≤ datumConst η N * ‖a‖ :=
  norm_liftSlabElem_le M P hPV hM (datumKc_spec η a) (measurable_datumField η a) η.2
    (norm_nonneg a) (datumKc_nonneg η) hγ₀ hγN hT

/-- **Two models: Lipschitz dependence of the datum lift on the datum.** -/
theorem singularDiffBoundOn_datumSlab {M₁ M₂ : Model 𝒯 parabolicSemigroup}
    (P : PolynomialSector 𝒯 N) {V : Submodule ℝ (ι → ℝ)}
    (hPV : ∀ k, (Pi.single (P.emb k) 1 : ι → ℝ) ∈ V) (h₁ : M₁.IsPolyCompatible P)
    (h₂ : M₂.IsPolyCompatible P) {η : NegExponent} (a b : HolderBesov η) {γ₀ : ℝ}
    (hγ₀ : 0 < γ₀) (hγN : γ₀ ≤ N) {T : ℝ} (hT : T ≤ 1) :
    M₁.SingularDiffBoundOn M₂ timeZeroDist γ₀ η (datumConst η N * ‖a - b‖) (timeSlab T)
      (datumSlab M₁ P hPV h₁ a hγ₀ hγN hT).val (datumSlab M₂ P hPV h₂ b hγ₀ hγN hT).val := by
  have hsub : Datum.DerivBound (η : ℝ) ‖a - b‖ (datumKc η)
      (Datum.datumField η a - Datum.datumField η b) := by
    rw [← Datum.datumField_sub]
    exact datumKc_spec η (a - b)
  exact singularDiffBoundOn_liftSlab h₁ h₂ (Datum.smoothPos_datumField η a)
    (Datum.smoothPos_datumField η b) hsub η.2 (norm_nonneg _) (datumKc_nonneg η) hγ₀ hγN hT

end RegularityStructures.Inhomogeneity

end
