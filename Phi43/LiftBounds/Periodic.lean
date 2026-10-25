/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.LiftBounds.Translate
public import Phi43.LiftBounds.Norm

/-!
# From box bounds to strip bounds under spatial periodicity

If a model is invariant under integer spatial translations on the quantities entering its bounds
(`PiSpatialPeriodic`, `GammaSpatialPeriodic`), then the `Π`-bound on a box
`[a, b] × [-1, 2]³` extends to the strip `[a, b] × ℝ³` with the same constant, and the `Γ`-bound
for pairs at parabolic distance at most `1` (`GammaBoundNearOn`) likewise.

The `Γ`-bound for far pairs does not follow abstractly from near pairs and periodicity: for a
general (abstract) structure group, a cocycle `Γ_{yx} = exp((y₁ - x₁) N)` with `N` of degree gap
`1/2` satisfies the near bound and `Γ_{y + n, x + n} = Γ_{y x}`, but fails the far bound.
-/

@[expose] public section

namespace RegularityStructures.Phi43.LiftBounds

/-- The integer lattice translation `(0, n)`. -/
def latticeShift (n : Fin 3 → ℤ) : ParabolicSpace := (0, fun i => (n i : ℝ))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- Invariance of the diagonal regularisations `Q_t Π_x e_i (x)` under integer spatial shifts. -/
def PiSpatialPeriodic (Z : Model 𝒯 parabolicSemigroup) : Prop :=
  ∀ (n : Fin 3 → ℤ) (x : ParabolicSpace) (i : ι) (t : ℝ),
    Z.regPi (x + latticeShift n) (Pi.single i 1) t (x + latticeShift n) =
      Z.regPi x (Pi.single i 1) t x

/-- Invariance of `Γ` under simultaneous integer spatial shifts. -/
def GammaSpatialPeriodic (Z : Model 𝒯 parabolicSemigroup) : Prop :=
  ∀ (n : Fin 3 → ℤ) (x y : ParabolicSpace),
    Z.gammaMap (y + latticeShift n) (x + latticeShift n) = Z.gammaMap y x

/-- The `Γ`-bound restricted to pairs at parabolic distance at most `1`. -/
def GammaBoundNearOn (Z : Model 𝒯 parabolicSemigroup) (γ C : ℝ) (S : Set ParabolicSpace) :
    Prop :=
  ∀ i j, 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x ∈ S, ∀ y ∈ S, parabolicNorm (y - x) ≤ 1 →
    |Z.gammaMap y x (Pi.single i 1) j| ≤ C * parabolicNorm (y - x) ^ (𝒯.deg i - 𝒯.deg j)

end RegularityStructures.Phi43.LiftBounds

end

public section

namespace RegularityStructures.Phi43.LiftBounds

open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- The integer part of the spatial coordinates, as a lattice shift. -/
noncomputable def floorShift (x : ParabolicSpace) : Fin 3 → ℤ := fun i => ⌊x.2 i⌋

theorem sub_floorShift_mem (x : ParabolicSpace) :
    ∀ i, (x - latticeShift (floorShift x)).2 i ∈ Ico (0 : ℝ) 1 := fun i => by
  simp only [latticeShift, floorShift, Prod.snd_sub, Pi.sub_apply]
  exact ⟨by linarith [Int.floor_le (x.2 i)], by linarith [Int.lt_floor_add_one (x.2 i)]⟩

theorem sub_floorShift_time (x : ParabolicSpace) : (x - latticeShift (floorShift x)).1 = x.1 := by
  simp [latticeShift]

/-- A box bound extends to the strip for periodic `Π`. -/
theorem piBoundOn_timeStrip_of_periodic {Z : Model 𝒯 parabolicSemigroup}
    (hper : PiSpatialPeriodic Z) {γ C a b : ℝ} {S : Set ParabolicSpace}
    (hS : ∀ z : ParabolicSpace, a ≤ z.1 → z.1 ≤ b → (∀ i, z.2 i ∈ Ico (0 : ℝ) 1) → z ∈ S)
    (h : Z.PiBoundOn γ C S) : Z.PiBoundOn γ C (timeStrip a b) := by
  intro i hi t ht x hx
  have hmem := hS (x - latticeShift (floorShift x))
    (by rw [sub_floorShift_time]; exact hx.1) (by rw [sub_floorShift_time]; exact hx.2)
    (sub_floorShift_mem x)
  have := h i hi t ht _ hmem
  rwa [← hper (floorShift x) (x - latticeShift (floorShift x)) i t, sub_add_cancel] at this

/-- Near pairs: a box bound extends to the strip for periodic `Γ`. -/
theorem gammaBoundNearOn_timeStrip_of_periodic {Z : Model 𝒯 parabolicSemigroup}
    (hper : GammaSpatialPeriodic Z) {γ C a b : ℝ} {S : Set ParabolicSpace}
    (hS : ∀ z w : ParabolicSpace, a ≤ z.1 → z.1 ≤ b → a ≤ w.1 → w.1 ≤ b →
      (∀ i, z.2 i ∈ Ico (0 : ℝ) 1) → parabolicNorm (w - z) ≤ 1 → z ∈ S ∧ w ∈ S)
    (h : GammaBoundNearOn Z γ C S) : GammaBoundNearOn Z γ C (timeStrip a b) := by
  intro i j hi hj x hx y hy hxy
  set n := floorShift x
  have hd : (y - latticeShift n) - (x - latticeShift n) = y - x := by abel
  have hxy' : parabolicNorm ((y - latticeShift n) - (x - latticeShift n)) ≤ 1 := by
    rw [hd]; exact hxy
  obtain ⟨h1, h2⟩ := hS (x - latticeShift n) (y - latticeShift n)
    (by rw [sub_floorShift_time]; exact hx.1) (by rw [sub_floorShift_time]; exact hx.2)
    (by simp [latticeShift]; exact hy.1) (by simp [latticeShift]; exact hy.2)
    (sub_floorShift_mem x) hxy'
  have := h i j hi hj _ h1 _ h2 hxy'
  rw [hd, ← hper n (x - latticeShift n) (y - latticeShift n), sub_add_cancel, sub_add_cancel]
    at this
  simpa only [hd] using this

end RegularityStructures.Phi43.LiftBounds

end
