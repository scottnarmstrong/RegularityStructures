/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.QFamilyR4ModelBound
public import RegularityStructures.Analysis.Parabolic.ScaledTest

/-!
# Pairing a model vector `Π_z e_i` with a scaled test function

A test function `g` *scaled at `z` with radius `R` and constant `A`* (`IsScaledTest`) is smooth,
vanishes outside `B(z, R)` (`0 < R ≤ 1`), and its scaled profile `v ↦ g (z + S^R v)` has
derivatives of order `≤ 4` bounded by `A`. Then `g = (A R⁵) φ^R_z` with `φ ∈ B^4`, so Hairer's
model bound (2.15) applies: `|⟨Π_z e_i, g⟩| ≤ C (A R⁵) R^{deg i}`.

Source: [Hai14] = arXiv:1303.5113v4, (2.15), Proposition 7.2.
-/

@[expose] public section

namespace RegularityStructures

/-- `g` is a test function scaled at `z` with radius `R ∈ (0, 1]` and constant `A > 0`. -/
structure IsScaledTest (g : ParabolicSpace → ℝ) (z : ParabolicSpace) (R A : ℝ) : Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) g
  radius_pos : 0 < R
  radius_le_one : R ≤ 1
  const_pos : 0 < A
  supp : ∀ w, R < parabolicNorm (w - z) → g w = 0
  deriv : ∀ k ≤ 4, ∀ v, ‖iteratedFDeriv ℝ k (fun v => g (z + parabolicDilate R v)) v‖ ≤ A

end RegularityStructures

end

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures

variable {g : ParabolicSpace → ℝ} {z : ParabolicSpace} {R A : ℝ}

theorem IsScaledTest.exists_eq_smul (hg : IsScaledTest g z R A) :
    ∃ φ ∈ testFunctionClass 4, g = (A * R ^ 5) • rescaledTestFunction φ R z :=
  exists_eq_smul_rescaledTestFunction hg.contDiff hg.radius_pos hg.radius_le_one hg.const_pos
    hg.supp hg.deriv

theorem IsScaledTest.integrable (hg : IsScaledTest g z R A) : Integrable g := by
  obtain ⟨φ, hφ, rfl⟩ := hg.exists_eq_smul
  exact (integrable_rescaledTestFunction hφ hg.radius_pos z).smul _

theorem IsScaledTest.continuous (hg : IsScaledTest g z R A) : Continuous g :=
  hg.contDiff.continuous

theorem IsScaledTest.measurable (hg : IsScaledTest g z R A) : Measurable g :=
  hg.continuous.measurable

end RegularityStructures

end
