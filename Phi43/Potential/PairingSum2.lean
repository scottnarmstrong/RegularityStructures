/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.PairingSum
public import RegularityStructures.Abstract.Singular.WindowAt.Basic

/-!
# Pairing with the union of two families of scaled test functions

`abs_integral_family2_le`: if `K₁ = ∑_{j ∈ J₁} g₁_j` and `K₂ = ∑_{j ∈ J₂} g₂_j` are two families of
scaled test functions as in `abs_integral_family_le`, the pairing with `K₁ + K₂` is bounded by the sum
of the two bounds (the families are combined over `J₁ ⊕ J₂`).
-/

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Potential

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam : ℝ}

/-- Data of a family of scaled test functions with its summability. -/
structure TestFamily (J : Type*) where
  zj : J → ParabolicSpace
  g : J → ParabolicSpace → ℝ
  R : J → ℝ
  A : J → ℝ
  base : ∀ j, 0 ≤ (zj j).1 ∧ (zj j).1 ≤ 1
  test : ∀ j, IsScaledTest (g j) (zj j) (R j) (A j)

/-- The union of two families, indexed by `J₁ ⊕ J₂`. -/
@[expose] def TestFamily.add {J₁ J₂ : Type*} (F₁ : TestFamily J₁) (F₂ : TestFamily J₂) :
    TestFamily (J₁ ⊕ J₂) where
  zj := Sum.elim F₁.zj F₂.zj
  g := Sum.elim F₁.g F₂.g
  R := Sum.elim F₁.R F₂.R
  A := Sum.elim F₁.A F₂.A
  base j := by rcases j with j | j; exacts [F₁.base j, F₂.base j]
  test j := by rcases j with j | j; exacts [F₁.test j, F₂.test j]

theorem TestFamily.hasSum_add {J₁ J₂ : Type*} (F₁ : TestFamily J₁) (F₂ : TestFamily J₂)
    {K₁ K₂ : ParabolicSpace → ℝ} (h₁ : ∀ y, HasSum (fun j => F₁.g j y) (K₁ y))
    (h₂ : ∀ y, HasSum (fun j => F₂.g j y) (K₂ y)) (y : ParabolicSpace) :
    HasSum (fun j => (F₁.add F₂).g j y) (K₁ y + K₂ y) :=
  HasSum.sum (f := fun j => (F₁.add F₂).g j y) (h₁ y) (h₂ y)

/-- The bound attached to a family. -/
@[expose] noncomputable def TestFamily.term {J : Type*} (F : TestFamily J) (r4K : ℝ) (d : ℝ)
    (j : J) : ℝ := r4K * (F.A j * F.R j ^ 5) * F.R j ^ d

theorem TestFamily.summable_add {J₁ J₂ : Type*} (F₁ : TestFamily J₁) (F₂ : TestFamily J₂)
    {r4K d : ℝ} (h₁ : Summable (F₁.term r4K d)) (h₂ : Summable (F₂.term r4K d)) :
    Summable ((F₁.add F₂).term r4K d) :=
  Summable.sum _ h₁ h₂

theorem TestFamily.tsum_add {J₁ J₂ : Type*} (F₁ : TestFamily J₁) (F₂ : TestFamily J₂)
    {r4K d : ℝ} (h₁ : Summable (F₁.term r4K d)) (h₂ : Summable (F₂.term r4K d)) :
    ∑' j, (F₁.add F₂).term r4K d j = (∑' j, F₁.term r4K d j) + ∑' j, F₂.term r4K d j :=
  Summable.tsum_sum h₁ h₂

theorem abs_integral_testFamily_le (hPi : M.PiBoundOn γ CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam hairerTimeWindow) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {o : ι} (ho : 𝒯.deg o < γ) {ξ : ParabolicSpace → ℝ} (hξ : Continuous ξ) {B : ℝ} {n : ℕ}
    (hB : ∀ u, |ξ u| ≤ B * (1 + parabolicNorm u) ^ n)
    (hreg : ∀ (x : ParabolicSpace) (t : ℝ), 0 < t → ∀ y,
      M.regPi x (Pi.single o 1) t y = parabolicSemigroup.apply t ξ y)
    (hgrowth : ∀ z : ParabolicSpace, 0 ≤ z.1 → z.1 ≤ 1 → M.HasQualitativeGrowthAt γ z)
    {Bξ : ℝ} (hξb : ∀ y : ParabolicSpace, -1 ≤ y.1 → y.1 ≤ 2 → |ξ y| ≤ Bξ)
    {J : Type*} [Countable J] (F : TestFamily J) (K : ParabolicSpace → ℝ)
    (hK : ∀ y, HasSum (fun j => F.g j y) (K y)) (hs1 : Summable fun j => F.A j * F.R j ^ 5)
    (hs2 : Summable (F.term (r4ModelConst 𝒯 γ * (max 1 CGam * CPi)) (𝒯.deg o))) :
    |∫ y, ξ y * K y| ≤ ∑' j, F.term (r4ModelConst 𝒯 γ * (max 1 CGam * CPi)) (𝒯.deg o) j :=
  abs_integral_family_le M hPi hCPi hGam hdeg ho hξ hB hreg hgrowth hξb F.zj F.base F.g F.R F.A
    F.test K hK hs1 hs2

end RegularityStructures.Potential

end
