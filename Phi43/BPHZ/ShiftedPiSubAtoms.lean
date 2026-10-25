/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSingleBase
public import Phi43.BPHZ.BphzCauchyPiAll
public import Phi43.BPHZ.PositivePiMomentIPsiBound
public import Phi43.BPHZ.GammaFullKernels
import Mathlib.Tactic

/-!
# The atoms of the shifted difference bounds

`ShiftedPiSubAtoms` bundles, for two mollifiers `ρ, ρ'`, the single atoms of both
(`ShiftedPiAtoms`, with common constants) and the unshifted difference bounds of all rows
(exponents `q` and `2q`), of the `iPsi` row and of the gradients `gₖ`.
-/

@[expose] public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The unshifted inputs of the shifted difference bounds. -/
structure ShiftedPiSubAtoms (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (κ : Kappa) (κbar θ : ℝ)
    (q : ℕ) (C1 C2 Ci Cg S1 S2 Si Sg : ℝ) : Prop where
  left : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg
  right : ShiftedPiAtoms.{u} N ρ' κ κbar q C1 C2 Ci Cg
  nonneg : 0 ≤ S1 ∧ 0 ≤ S2 ∧ 0 ≤ Si ∧ 0 ≤ Sg
  sub1 : ∀ i, i ∉ piDeterministic → (phi43RegularityStructure κ).deg i < gamma κ →
    PiSubBound.{u} N ρ ρ' κ κbar θ q i S1
  sub2 : ∀ i, i ∉ piDeterministic → (phi43RegularityStructure κ).deg i < gamma κ →
    PiSubBound.{u} N ρ ρ' κ κbar θ (2 * q) i S2
  iPsi : PiSubBound.{u} N ρ ρ' κ κbar θ q Symbol.iPsi Si
  grad1 : ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}, IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 →
    ε' ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
    ∀ (x : ParabolicSpace) (k : Fin 3),
    ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k - shiftedPiGrad N ξ' ω x k)
      (Sg * (max ε ε') ^ θ)
  grad2 : ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}, IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 →
    ε' ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
    ∀ (x : ParabolicSpace) (k : Fin 3),
    ShiftMom P (2 * q) (fun ω => shiftedPiGrad N ξ ω x k - shiftedPiGrad N ξ' ω x k)
      (Sg * (max ε ε') ^ θ)

end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar θ : ℝ} {q : ℕ}

theorem ShiftedPiAtoms.mono {C1 C2 Ci Cg D1 D2 Di Dg : ℝ}
    (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) (h1 : C1 ≤ D1) (h2 : C2 ≤ D2)
    (hi : Ci ≤ Di) (hg : Cg ≤ Dg) : ShiftedPiAtoms.{u} N ρ κ κbar q D1 D2 Di Dg := by
  obtain ⟨a1, a2, a3, a4⟩ := A.nonneg
  refine ⟨⟨a1.trans h1, a2.trans h2, a3.trans hi, a4.trans hg⟩,
    fun i hi' hl => PiSingleBound.mono (A.single i hi' hl) h1, fun i hi' hl => PiSingleBound.mono (A.double i hi' hl) h2,
    PiSingleBound.mono A.iPsi hi, fun hW hε hξ x k => (A.grad1 hW hε hξ x k).mono hg,
    fun hW hε hξ x k => (A.grad hW hε hξ x k).mono hg⟩

theorem shiftedPiSubAtoms_exists (hmiss : BphzCauchyMoments.{u} N κ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') (hκ0 : 0 ≤ κbar) (hθ : 0 < θ) (hκθ : κbar + θ ≤ κ.1 / 2)
    (hq : 1 ≤ q) :
    ∃ C1 C2 Ci Cg S1 S2 Si Sg : ℝ,
      ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg := by
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hκb : κbar ≤ κ.1 / 2 := by linarith
  obtain ⟨C1, C2, Ci, Cg, A⟩ := shiftedPiAtoms_exists hmiss hρ hκ0 hκb hq
  obtain ⟨C1', C2', Ci', Cg', A'⟩ := shiftedPiAtoms_exists hmiss hρ' hκ0 hκb hq
  obtain ⟨S1, hS1, h1⟩ := exists_piSubBound_all hmiss hρ hρ' hκ0 hθ hκθ hq
  obtain ⟨S2, hS2, h2⟩ := exists_piSubBound_all hmiss hρ hρ' hκ0 hθ hκθ (q := 2 * q) (by omega)
  obtain ⟨Si, hSi, hi⟩ := regPi_iPsi_sub_lintegral_enorm_pow_le.{u} N hρ hρ' κ hκ0 hθ
    (by linarith) hq
  obtain ⟨Sg, hSg, hg⟩ := gammaFull_grad_sub_lintegral_le.{u} N hρ hρ' hθ (by linarith) hq
  obtain ⟨Sg2, hSg2, hg2⟩ := gammaFull_grad_sub_lintegral_le.{u} N hρ hρ' hθ (by linarith)
    (q := 2 * q) (by omega)
  have hA := A.nonneg
  have hA' := A'.nonneg
  refine ⟨C1 + C1', C2 + C2', Ci + Ci', Cg + Cg', S1, S2, Si, Sg + Sg2,
    ⟨A.mono (by linarith [hA'.1]) (by linarith [hA'.2.1]) (by linarith [hA'.2.2.1])
      (by linarith [hA'.2.2.2]),
     A'.mono (by linarith [hA.1]) (by linarith [hA.2.1]) (by linarith [hA.2.2.1])
      (by linarith [hA.2.2.2]), ⟨hS1, hS2, hSi, by positivity⟩, h1, h2, ?_, ?_, ?_⟩⟩
  · intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' hgr hgr' t ht x
    exact hi hW hε hε' hξ hξ' (Filter.Eventually.of_forall hgr) (Filter.Eventually.of_forall hgr')
      t ht x
  · intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x k
    refine (hg hW hε hε' hξ hξ' k (spaceTimeProj x)).trans ?_
    refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q
    have : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
    nlinarith
  · intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x k
    refine (hg2 hW hε hε' hξ hξ' k (spaceTimeProj x)).trans ?_
    refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) (2 * q)
    have : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
    nlinarith

end RegularityStructures.Phi43

end
