/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Inhomogeneity.SlabConst
public import RegularityStructures.Abstract.Datum.DatumLift
public import RegularityStructures.Abstract.Model

/-!
# The Taylor lift of a function with derivative bounds, cut to the time slab

[Hai14, Lemma 7.5 and Proposition A.1]. For a function `F` on `ℝ⁴` which is smooth on `{t > 0}`
with the derivative bounds `DerivBound η A Kc F` (`|D^k F(z)| ≤ Kc k · A · t^{(η - |k|_𝔰)/2}` for
`0 < t ≤ 1`), `liftSlab P γ₀ T F = 1_{(0,T]×ℝ³} · liftOf P γ₀ F` is an element of the slab space
`SlabSpace timeZeroDist V γ₀ η (timeSlab T)` (`liftSlabElem`) of norm at most `liftConst N Kc * A`,
as soon as `T ≤ 1`, the model is polynomial compatible and the polynomial sector is contained in
`V`.  Both the lift of the heat evolution of a datum (`datumLiftOn`) and the jets of smooth
bounded functions are of this form.

For two polynomial compatible models the actions of `Γ` on the polynomial sector coincide
(`Datum.gammaMap_polyEmbed`), hence the comparison of `liftSlab F` and `liftSlab G` is controlled by
`DerivBound` of `F - G` (`singularDiffBoundOn_liftSlab`).
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Inhomogeneity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}

/-- The Taylor lift of `F` into the polynomial sector `P` on the time slab `(0, T] × ℝ³`
(zero elsewhere). -/
def liftSlab (P : PolynomialSector 𝒯 N) (γ₀ T : ℝ) (F : ParabolicSpace → ℝ) :
    ParabolicSpace → ι → ℝ :=
  (timeSlab T).indicator (Datum.liftOf P γ₀ F)

end RegularityStructures.Inhomogeneity

end

public section

open MeasureTheory Set

namespace RegularityStructures.Inhomogeneity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}

theorem liftSlab_of_mem (P : PolynomialSector 𝒯 N) (γ₀ : ℝ) {T : ℝ} (F : ParabolicSpace → ℝ)
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    liftSlab P γ₀ T F x = Datum.liftOf P γ₀ F x :=
  indicator_of_mem hx _

theorem liftSlab_of_notMem (P : PolynomialSector 𝒯 N) (γ₀ : ℝ) {T : ℝ} (F : ParabolicSpace → ℝ)
    {x : ParabolicSpace} (hx : x ∉ timeSlab T) :
    liftSlab P γ₀ T F x = 0 :=
  indicator_of_notMem hx _

theorem measurable_liftSlab (P : PolynomialSector 𝒯 N) (γ₀ T : ℝ) {F : ParabolicSpace → ℝ}
    (hF : Measurable F) : Measurable (liftSlab P γ₀ T F) :=
  (Datum.measurable_liftOf P γ₀ hF).indicator (measurableSet_timeSlab T)

theorem liftSlab_eq_polyEmbed (P : PolynomialSector 𝒯 N) (γ₀ T : ℝ) (F : ParabolicSpace → ℝ)
    (x : ParabolicSpace) : ∃ σ : PolyIndex N → ℝ, liftSlab P γ₀ T F x = P.polyEmbed σ := by
  by_cases hx : x ∈ timeSlab T
  · exact ⟨Datum.liftCoeff N γ₀ F x, by rw [liftSlab_of_mem P γ₀ F hx]; rfl⟩
  · exact ⟨0, by
      rw [liftSlab_of_notMem P γ₀ F hx]
      simp [PolynomialSector.polyEmbed]⟩

theorem polyEmbed_mem_of_single_mem (P : PolynomialSector 𝒯 N) {V : Submodule ℝ (ι → ℝ)}
    (hPV : ∀ k, (Pi.single (P.emb k) 1 : ι → ℝ) ∈ V) (σ : PolyIndex N → ℝ) :
    P.polyEmbed σ ∈ V :=
  Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hPV k)

/-- **The slab-cut Taylor lift satisfies the singular bound** with the constant
`liftConst N Kc * A`. -/
theorem singularBoundOn_liftSlab {M : Model 𝒯 parabolicSemigroup} {P : PolynomialSector 𝒯 N}
    (hM : M.IsPolyCompatible P) {η A : ℝ} {Kc : (Fin 4 → ℕ) → ℝ} {F : ParabolicSpace → ℝ}
    (hF : Datum.DerivBound η A Kc F) (hη : η < 0) (hA : 0 ≤ A) (hKc : ∀ k, 0 ≤ Kc k) {γ₀ : ℝ}
    (hγ₀ : 0 < γ₀) (hγN : γ₀ ≤ N) {T : ℝ} (hT : T ≤ 1) :
    M.SingularBoundOn timeZeroDist γ₀ η (Datum.liftConst N Kc * A) (timeSlab T)
      (liftSlab P γ₀ T F) :=
  Datum.singularBoundOn_congr (fun _ hx => (liftSlab_of_mem P γ₀ F hx).symm)
    (Datum.singularBoundOn_liftOf hM hF hη hA hKc hγ₀ hγN hT)

end RegularityStructures.Inhomogeneity

end

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Inhomogeneity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}

/-- **The slab-cut Taylor lift as an element of the slab space.** -/
def liftSlabElem (M : Model 𝒯 parabolicSemigroup) (P : PolynomialSector 𝒯 N)
    {V : Submodule ℝ (ι → ℝ)} (hPV : ∀ k, (Pi.single (P.emb k) 1 : ι → ℝ) ∈ V)
    (hM : M.IsPolyCompatible P) {η A : ℝ} {Kc : (Fin 4 → ℕ) → ℝ} {F : ParabolicSpace → ℝ}
    (hF : Datum.DerivBound η A Kc F) (hFm : Measurable F) (hη : η < 0) (hA : 0 ≤ A)
    (hKc : ∀ k, 0 ≤ Kc k) {γ₀ : ℝ} (hγ₀ : 0 < γ₀) (hγN : γ₀ ≤ N) {T : ℝ} (hT : T ≤ 1) :
    M.SlabSpace timeZeroDist V γ₀ η (timeSlab T) :=
  Model.SlabSpace.mk (liftSlab P γ₀ T F)
    ⟨measurable_liftSlab P γ₀ T hFm,
      fun x hx _ => by
        rw [liftSlab_of_mem P γ₀ F hx]
        exact ⟨polyEmbed_mem_of_single_mem P hPV _, Datum.liftOf_mem_lowerSubspace P γ₀ F x⟩,
      fun x hx => liftSlab_of_notMem P γ₀ F fun h => hx ⟨h, timeZeroDist_pos_of_mem_timeSlab h⟩,
      _, singularBoundOn_liftSlab hM hF hη hA hKc hγ₀ hγN hT⟩

end RegularityStructures.Inhomogeneity

end

public section

open MeasureTheory Set

namespace RegularityStructures.Inhomogeneity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}

/-- **The norm of the slab-cut Taylor lift** is at most `liftConst N Kc * A`. -/
theorem norm_liftSlabElem_le (M : Model 𝒯 parabolicSemigroup) (P : PolynomialSector 𝒯 N)
    {V : Submodule ℝ (ι → ℝ)} (hPV : ∀ k, (Pi.single (P.emb k) 1 : ι → ℝ) ∈ V)
    (hM : M.IsPolyCompatible P) {η A : ℝ} {Kc : (Fin 4 → ℕ) → ℝ} {F : ParabolicSpace → ℝ}
    (hF : Datum.DerivBound η A Kc F) (hFm : Measurable F) (hη : η < 0) (hA : 0 ≤ A)
    (hKc : ∀ k, 0 ≤ Kc k) {γ₀ : ℝ} (hγ₀ : 0 < γ₀) (hγN : γ₀ ≤ N) {T : ℝ} (hT : T ≤ 1) :
    ‖liftSlabElem M P hPV hM hF hFm hη hA hKc hγ₀ hγN hT‖ ≤ Datum.liftConst N Kc * A :=
  M.slabNorm_le (singularBoundOn_liftSlab hM hF hη hA hKc hγ₀ hγN hT)
    (mul_nonneg (Datum.liftConst_nonneg hKc) hA)

/-- If `g x` is in the polynomial sector for all `x`, two polynomial compatible models act on it
by the same `Γ`: the second model can be exchanged in the comparison norm. -/
theorem singularDiffBoundOn_of_gammaMap_eq {M₁ M₂ : Model 𝒯 parabolicSemigroup} {γ η C : ℝ}
    {S : Set ParabolicSpace} {f g : ParabolicSpace → ι → ℝ}
    (hΓ : ∀ x ∈ S, ∀ y ∈ S, M₁.gammaMap y x (g x) = M₂.gammaMap y x (g x))
    (h : M₁.SingularDiffBoundOn M₁ timeZeroDist γ η C S f g) :
    M₁.SingularDiffBoundOn M₂ timeZeroDist γ η C S f g := by
  refine ⟨h.1, fun x hx y hy hρx hρy hd j hj => ?_⟩
  rw [← hΓ x hx y hy]
  exact h.2 x hx y hy hρx hρy hd j hj

/-- **Two-model comparison of slab-cut Taylor lifts** for polynomial compatible models:
`|||liftSlab F; liftSlab G||| ≤ liftConst N Kc * A` when `F - G` has `DerivBound η A Kc`. -/
theorem singularDiffBoundOn_liftSlab {M₁ M₂ : Model 𝒯 parabolicSemigroup}
    {P : PolynomialSector 𝒯 N} (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    {η A : ℝ} {Kc : (Fin 4 → ℕ) → ℝ} {F G : ParabolicSpace → ℝ}
    (hF : Datum.SmoothPos F) (hG : Datum.SmoothPos G) (hFG : Datum.DerivBound η A Kc (F - G))
    (hη : η < 0) (hA : 0 ≤ A) (hKc : ∀ k, 0 ≤ Kc k) {γ₀ : ℝ} (hγ₀ : 0 < γ₀) (hγN : γ₀ ≤ N)
    {T : ℝ} (hT : T ≤ 1) :
    M₁.SingularDiffBoundOn M₂ timeZeroDist γ₀ η (Datum.liftConst N Kc * A) (timeSlab T)
      (liftSlab P γ₀ T F) (liftSlab P γ₀ T G) := by
  refine singularDiffBoundOn_of_gammaMap_eq (fun x _ y _ => ?_)
    (Datum.singularDiffBoundOn_of_sub (Datum.singularBoundOn_congr (f := liftSlab P γ₀ T (F - G))
      (fun x hx => ?_) (singularBoundOn_liftSlab h₁ hFG hη hA hKc hγ₀ hγN hT)))
  · obtain ⟨σ, hσ⟩ := liftSlab_eq_polyEmbed P γ₀ T G x
    rw [hσ, Datum.gammaMap_polyEmbed h₁, Datum.gammaMap_polyEmbed h₂]
  · rw [liftSlab_of_mem P γ₀ _ hx, liftSlab_of_mem P γ₀ _ hx, liftSlab_of_mem P γ₀ _ hx,
      Datum.liftOf_sub P γ₀ hF hG]

end RegularityStructures.Inhomogeneity

end
