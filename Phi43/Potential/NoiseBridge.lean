/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.DerivHyp
public import Phi43.LiftBounds.Translate
public import RegularityStructures.Abstract.Translate.Realising
public import Phi43.BPHZ.TreeFormulas
public import Phi43Statements.Defs.IsRenormalisedCanonicalModel
public import Phi43.Potential.Convolution

/-!
# The noise coordinate of the renormalised canonical model

For a renormalised canonical model `Z` of the noise `noise` (`IsRenormalisedCanonicalModel`), the
realisation of the noise symbol is the noise itself: `Q_t Π_x Ξ = Q_t ζ` for `t > 0`
(`regPi_noise_eq_apply`), and after the restart translation by `(s, 0)` it is `Q_t` of the shifted
noise `potShift s ζ` (`regPi_translate_noise_eq_apply`).  Every symbol has degree `> -4`
(`neg_four_lt_homogeneity`), and `Ξ` has degree `< gamma κ`.
-/

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Phi43.Potential

open RegularityStructures RegularityStructures.Potential RegularityStructures.Phi43.LiftBounds

theorem neg_four_lt_homogeneity (κ : Kappa) (τ : Symbol) : -4 < homogeneity κ τ := by
  have hk := kappa_pos κ
  have hk₀ : κ.1 < 1 / 16 := κ.2.2
  cases τ <;> simp only [homogeneity] <;> linarith

theorem noise_mem_fMinus : Symbol.noise ∈ fMinus := by
  rw [mem_fMinus_iff_isFMinus]
  simp [isFMinus]

/-- The noise coordinate of the renormalised canonical model is `Q_t ζ`. -/
theorem regPi_noise_eq_apply {N : ℕ} {κ : Kappa} {noise : CanonicalNoise}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z) (x : ParabolicSpace) {t : ℝ}
    (ht : 0 < t) (y : ParabolicSpace) :
    Z.regPi x (Pi.single Symbol.noise 1) t y = parabolicSemigroup.apply t noise.zeta y := by
  rw [hZ.2.1 Symbol.noise noise_mem_fMinus x t ht y,
    CanonicalData.renormalisedPi_basis_noise_eq]
  rfl

/-- The noise coordinate of the restarted model is `Q_t` of the time-shifted noise. -/
theorem regPi_translate_noise_eq_apply {N : ℕ} {κ : Kappa} {noise : CanonicalNoise}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z) (s : ℝ) (x : ParabolicSpace)
    {t : ℝ} (ht : 0 < t) (y : ParabolicSpace) :
    (Z.translate (restartPoint s)).regPi x (Pi.single Symbol.noise 1) t y =
      parabolicSemigroup.apply t (potShift s noise.zeta) y := by
  rw [Model.regPi_translate, regPi_noise_eq_apply hZ _ ht]
  have e : (fun y : ParabolicSpace => noise.zeta (y + restartPoint s)) =
      potShift s noise.zeta := by
    funext y
    simp only [potShift, restartPoint]
    congr 1
    ext <;> simp
  rw [← e]
  exact (parabolicSemigroup_apply_translate _ t _ y).symm

end RegularityStructures.Phi43.Potential

end
