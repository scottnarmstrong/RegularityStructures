/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Restart.Periodic
public import Phi43.Pinned
public import Phi43.LiftBounds
public import Phi43.Structure.CanonicalModelExistence
public import RegularityStructures.Abstract.ModelNear

/-!
# Window bounds of the restarted canonical model from the size of `Z`

For `Z` with `IsRenormalisedCanonicalModel N κ noise C Z` and `phi43Size κ η T Z ψ ≤ ofReal B`, the
canonical model `M₀ = canonicalRenormalisedModel N κ noise Cg q hg C` (same noise and constants)
agrees with `Z` on the pinned `Π` and on `Γ` away from `X₀` (`Phi43.Pinned`).  Consequently, for
`s ∈ [0, T]` the time translate `M₀.translate (s, 0)` has, with constant `B`,

* `Π`-bound at level `κ` (the symbols of homogeneity `< κ` are pinned) on `hairerTimeWindow`;
* near-`1` `Γ`-bound at level `gamma κ` on `hairerTimeWindow`,

using the spatial periodicity of `M₀` to pass from the box `phi43Box (T + 1)` of the size
`phi43Size` to the strip `[s - 1, s + 2] × ℝ³`.
-/

public section

open Set
open scoped ENNReal

namespace RegularityStructures.Phi43.Restart

open RegularityStructures.Phi43.LiftBounds

variable {N : ℕ} {κ : Kappa} {noise : CanonicalNoise} {Cg : ℝ} {q : ℕ}
  {hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q}
  {C : RenormalisationConstants}
  {Z : Model (phi43RegularityStructure κ) parabolicSemigroup} {η T B s : ℝ}
  {ψ : ℝ → C(Torus3, ℝ)}

/-- Symbols of homogeneity `< κ` are pinned. -/
theorem isPinnedSymbol_of_homogeneity_lt {τ : Symbol} (h : homogeneity κ τ < κ.1) :
    IsPinnedSymbol τ := by
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  cases τ <;> simp only [homogeneity] at h <;>
    first
    | (left; simp [mem_fMinus_iff_isFMinus, isFMinus]; done)
    | (right; left; rfl)
    | (right; right; left; exact ⟨_, rfl⟩)
    | (exfalso; linarith)

/-- The `Π`-bound of the canonical model at level `κ` on the box, with the bound `B` on the size
`phi43Size` as constant. -/
theorem canonical_piBoundOn_box (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hB : 0 ≤ B) (h : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B) :
    (canonicalRenormalisedModel N κ noise Cg q hg C).PiBoundOn κ.1 B
      (Statements.phi43Box (T + 1)) := by
  intro τ hτ t ht x hx
  have hpin := isPinnedSymbol_of_homogeneity_lt (κ := κ) hτ
  have hk := kappa_pos κ
  have hZb := piBoundOn_of_phi43Size_le hB h τ (by
    have : homogeneity κ τ < κ.1 := hτ
    have hk' : κ.1 < 1 / 16 := κ.2.2
    simp only [gamma]; linarith) t ht x hx
  rw [abs_regPi_diag_eq_of_pinned hZ
    (canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise Cg q hg C) hpin x ht.1]
    at hZb
  exact hZb

/-- The `Γ`-bound of the canonical model at level `gamma κ` on the box. -/
theorem canonical_gammaBoundOn_box (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hB : 0 ≤ B) (h : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B) :
    (canonicalRenormalisedModel N κ noise Cg q hg C).GammaBoundOn (gamma κ) B
      (Statements.phi43Box (T + 1)) :=
  (gammaBoundOn_iff_of_isRenormalisedCanonicalModel hZ
    (canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise Cg q hg C) B _).1
    (gammaBoundOn_of_phi43Size_le hB h)

/-- `Π`-bound of the restarted canonical model on the window. -/
theorem restart_canonical_piBoundOn_window (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hB : 0 ≤ B) (hs : s ∈ Icc (0 : ℝ) T) (h : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B) :
    ((canonicalRenormalisedModel N κ noise Cg q hg C).translate (restartPoint s)).PiBoundOn
      κ.1 B hairerTimeWindow := by
  refine (piBoundOn_translate_window _ s).2 ?_
  exact piBoundOn_timeStrip_of_periodic (canonicalRenormalisedModel_piSpatialPeriodic N κ noise Cg q hg C)
    (hS := fun _ h1 h2 h3 => mem_phi43Box_of_cell (a := -1 + s) (b := 2 + s)
      (by linarith [hs.1]) (by linarith [hs.2]) h1 h2 h3)
    (canonical_piBoundOn_box hZ hB h)

/-- Near-`1` `Γ`-bound of the canonical model on the strip `[s - 1, s + 2] × ℝ³`. -/
theorem canonical_gammaBoundNearOn_strip (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hB : 0 ≤ B) (hs : s ∈ Icc (0 : ℝ) T) (h : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B) :
    LiftBounds.GammaBoundNearOn (canonicalRenormalisedModel N κ noise Cg q hg C) (gamma κ) B
      (timeStrip (-1 + s) (2 + s)) := by
  have hbox := canonical_gammaBoundOn_box (hg := hg) hZ hB h
  have hnear : LiftBounds.GammaBoundNearOn (canonicalRenormalisedModel N κ noise Cg q hg C)
      (gamma κ) B (Statements.phi43Box (T + 1)) :=
    fun i j hi hj x hx y hy _ => hbox i j hi hj x hx y hy
  refine gammaBoundNearOn_timeStrip_of_periodic
    (canonicalRenormalisedModel_gammaSpatialPeriodic N κ noise Cg q hg C) ?_ hnear
  intro z w h1 h2 h1' h2' h3 hzw
  have hz := mem_phi43Box_of_cell (a := -1 + s) (b := 2 + s) (T := T)
    (by linarith [hs.1]) (by linarith [hs.2]) h1 h2 h3
  refine ⟨hz, ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, fun i _ => ?_⟩⟩
  have := abs_le.1 ((abs_sub_le_parabolicNorm z w i).trans hzw)
  have hi := h3 i
  exact ⟨by linarith [hi.1, hi.2], by linarith [hi.1, hi.2]⟩

end RegularityStructures.Phi43.Restart

end
