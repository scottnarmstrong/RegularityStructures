/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Restart.Window
public import RegularityStructures.Abstract.IntExt.Bounds

/-!
# Near-pair `Γ`-bounds: translation, the strip bridge, and the integration extension

* `Model.gammaBoundNearOn_translate_iff`: translation covariance of `GammaBoundNearOn`;
* `LiftBounds.gammaBoundNearOn_iff_model`: the norm-based near-`1` bound of `LiftBounds` is the
  radius-`1` bound `Model.GammaBoundNearOn M γ C 1 S`;
* `IntExtHyp.gammaBoundNearOn_intExtend_radius`: below the planted symbols the extended model has
  the near-pair bounds of the old model, at any radius;
* `restart_canonical_gammaBoundNearOn_window`: near-`1` `Γ`-bound of the restarted canonical model
  on the window at level `gamma κ`.
-/

public section

open Set
open scoped ENNReal

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) (a : ParabolicSpace) {γ C R : ℝ} {S : Set ParabolicSpace}

/-- Translation covariance of the near-pair `Γ`-bound. -/
theorem gammaBoundNearOn_translate_iff :
    (M.translate a).GammaBoundNearOn γ C R S ↔ M.GammaBoundNearOn γ C R ((· + a) '' S) := by
  constructor
  · intro h i j hi hj x hx y hy hxy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    have := h i j hi hj x hx y hy (by
      simpa only [parabolicSemigroup_scaleDist_translate] using hxy)
    simpa only [gammaMap_translate, parabolicSemigroup_scaleDist_translate] using this
  · intro h i j hi hj x hx y hy hxy
    have := h i j hi hj (x + a) ⟨x, hx, rfl⟩ (y + a) ⟨y, hy, rfl⟩ (by
      simpa only [parabolicSemigroup_scaleDist_translate] using hxy)
    simpa only [gammaMap_translate, parabolicSemigroup_scaleDist_translate] using this

end Model

end RegularityStructures

namespace RegularityStructures.Phi43.Restart

open RegularityStructures.Phi43.LiftBounds

variable {N : ℕ} {κ : Kappa} {noise : CanonicalNoise} {Cg : ℝ} {q : ℕ}
  {hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q}
  {C : RenormalisationConstants}
  {Z : Model (phi43RegularityStructure κ) parabolicSemigroup} {η T B s : ℝ}
  {ψ : ℝ → C(Torus3, ℝ)}

/-- Near-`1` `Γ`-bound of the restarted canonical model on the window, level `gamma κ`. -/
theorem restart_canonical_gammaBoundNearOn_window
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z) (hB : 0 ≤ B)
    (hs : s ∈ Icc (0 : ℝ) T) (h : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B) :
    ((canonicalRenormalisedModel N κ noise Cg q hg C).translate (restartPoint s)).GammaBoundNearOn
      (gamma κ) B 1 hairerTimeWindow := by
  rw [Model.gammaBoundNearOn_translate_iff, hairerTimeWindow_eq_timeStrip,
    image_add_restartPoint_timeStrip]
  exact canonical_gammaBoundNearOn_strip (hg := hg) hZ hB hs h

end RegularityStructures.Phi43.Restart

end
