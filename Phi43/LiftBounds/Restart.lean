/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.LiftBounds.Periodic
public import Phi43Statements.Defs.Phi43Size
public import Phi43.Structure.Abstract

/-!
# Restart bounds of a lift from the size of the lift

Combination of the time translation, the extraction of real constants and spatial periodicity:
if `phi43Size κ η T Z ψ ≤ ofReal B`, `s ∈ [0, T]`, and `Z` is spatially periodic, then the
restarted model `Z.translate (s, 0)` has `PiBoundOn γ B hairerTimeWindow` for every `γ ≤ gamma κ`
(in particular at the level `κ < gamma κ`), and its `Γ`-bounds for pairs at distance at most `1`.
-/

public section

namespace RegularityStructures.Phi43.LiftBounds

open Set

variable {κ : Phi43.Kappa} {η T B s : ℝ}
  {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
  {ψ : ℝ → C(Torus3, ℝ)}

theorem mem_phi43Box_of_cell {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ T + 1 + 1) {z : ParabolicSpace}
    (h1 : a ≤ z.1) (h2 : z.1 ≤ b) (h3 : ∀ i, z.2 i ∈ Ico (0 : ℝ) 1) :
    z ∈ Statements.phi43Box (T + 1) :=
  ⟨⟨ha.trans h1, by linarith⟩, fun i _ => ⟨by linarith [(h3 i).1], by linarith [(h3 i).2]⟩⟩

theorem abs_sub_le_parabolicNorm (z w : ParabolicSpace) (i : Fin 3) :
    |w.2 i - z.2 i| ≤ parabolicNorm (w - z) := by
  have h := Finset.single_le_sum (f := fun j => |(w - z).2 j|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)
  unfold parabolicNorm
  have := Real.sqrt_nonneg |(w - z).1|
  simp only [Prod.snd_sub, Pi.sub_apply] at h ⊢
  linarith

end RegularityStructures.Phi43.LiftBounds

end
