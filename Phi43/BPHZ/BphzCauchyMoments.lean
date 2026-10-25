/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.BphzCauchyMomentDefs
public import Phi43.BPHZ.ProductIPsiPsiAll
public import Phi43.BPHZ.ProductPiMoment
public import Phi43.BPHZ.ProductPiMomentDiff
public import Phi43.BPHZ.ModelRegPiTreesDiffI3Psi
public import Phi43.BPHZ.ModelRegPiTreesDiffI2Psi2
public import Phi43.BPHZ.ModelRegPiTreesDiffI3Psi2

/-!
# The moment families of `BphzCauchyMoments` hold

`bphzCauchyMoments_holds`: the nine moment families of `BphzCauchyMoments`
(`Phi43.BPHZ.BphzCauchyMomentDefs`) hold for every `N` and `κ`. Each field is one of the proved
moment bounds, specialised to the consumer's hypotheses:

* `I(Ψ)Ψ`, `I(Ψ)Ψ²` (single and two-mollifier difference): `regPi_iPsiPsi(Sq)(_sub)_lintegral_enorm_pow_le`
  (`Phi43.BPHZ.ProductIPsiPsi*`);
* `I(Ψ²)Ψ` (single and difference): `regPi_iPsiSqPsi(_sub)_lintegral_enorm_pow_le`
  (`Phi43.BPHZ.ProductPiMoment*`);
* the differences of the `I`-trees `I(Ψ³)Ψ`, `I(Ψ²)Ψ²`, `I(Ψ³)Ψ²` for the random models:
  `regPi_iPsiCubePsi_sub_lintegral_enorm_pow_le` and its two siblings
  (`Phi43.BPHZ.ModelRegPiTreesDiff*`).

The consumer hypotheses `0 ≤ κ̄`, `0 < θ`, `κ̄ + θ ≤ κ/2` imply those of the provers
(`κ̄ ≤ κ/2`, `θ ≤ κ`); unused hypotheses (Wick constants for the symbols that do not need them)
are dropped.
-/

public section

universe u

namespace RegularityStructures.Phi43

/-- **The moment families of `BphzCauchyMoments` hold.** -/
theorem bphzCauchyMoments_holds (N : ℕ) (κ : Kappa) : BphzCauchyMoments.{u} N κ where
  iPsiPsi := by
    intro ρ hρ κbar hκb0 hκb q hq
    obtain ⟨C, hC, h⟩ := regPi_iPsiPsi_lintegral_enorm_pow_le.{u} N hρ κ hκb0 hκb hq
    exact ⟨C, hC, fun hW hε hξ _ hg t ht x => h hW hε hξ hg t ht x⟩
  iPsiPsi_sub := by
    intro ρ ρ' hρ hρ' κbar θ hκb0 hθ hκθ q hq
    obtain ⟨C, hC, h⟩ := regPi_iPsiPsi_sub_lintegral_enorm_pow_le.{u} N hρ hρ' κ hκb0 hθ hκθ hq
    exact ⟨C, hC, fun hW hε hε' hξ hξ' _ _ hg hg' t ht x => h hW hε hε' hξ hξ' hg hg' t ht x⟩
  iPsiPsiSq := by
    intro ρ hρ κbar hκb0 hκb q hq
    exact regPi_iPsiPsiSq_lintegral_enorm_pow_le.{u} N hρ κ hκb0 hκb hq
  iPsiPsiSq_sub := by
    intro ρ ρ' hρ hρ' κbar θ hκb0 hθ hκθ q hq
    exact regPi_iPsiPsiSq_sub_lintegral_enorm_pow_le.{u} N hρ hρ' κ hκb0 hθ hκθ hq
  iPsiSqPsi := by
    intro ρ hρ κbar hκb0 hκb q hq
    obtain ⟨C, hC, h⟩ := regPi_iPsiSqPsi_lintegral_enorm_pow_le.{u} N hρ κ hκb hq
    exact ⟨C, hC, fun hW hε hξ _ hg t ht x => h hW hε hξ hg t ht x⟩
  iPsiSqPsi_sub := by
    intro ρ ρ' hρ hρ' κbar θ hκb0 hθ hκθ q hq
    obtain ⟨C, hC, h⟩ := regPi_iPsiSqPsi_sub_lintegral_enorm_pow_le.{u} N hρ hρ' κ (κbar := κbar) (θ := θ)
      (by linarith) hθ (by linarith [κ.2.1]) hq
    exact ⟨C, hC, fun hW hε hε' hξ hξ' _ _ hg hg' t ht x => h hW hε hε' hξ hξ' hg hg' t ht x⟩
  iPsiCubePsi_sub := by
    intro ρ ρ' hρ hρ' κbar θ hκb0 hθ hκθ q hq
    exact Phi43.regPi_iPsiCubePsi_sub_lintegral_enorm_pow_le.{u} N hρ hρ' κ (κbar := κbar) (by linarith) hθ
      (by linarith [κ.2.1]) hq
  iPsiSqPsiSq_sub := by
    intro ρ ρ' hρ hρ' κbar θ hκb0 hθ hκθ q hq
    exact Phi43.regPi_iPsiSqPsiSq_sub_lintegral_enorm_pow_le.{u} N hρ hρ' κ (κbar := κbar) (by linarith) hθ
      (by linarith [κ.2.1]) hq
  iPsiCubePsiSq_sub := by
    intro ρ ρ' hρ hρ' κbar θ hκb0 hθ hκθ q hq
    exact Phi43.regPi_iPsiCubePsiSq_sub_lintegral_enorm_pow_le.{u} N hρ hρ' κ (κbar := κbar) (by linarith) hθ
      (by linarith [κ.2.1]) hq

end RegularityStructures.Phi43

end
