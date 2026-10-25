/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.IsModerateRenormalisedCanonicalModel
public import Phi43.Structure.CanonicalWeightedPositiveDetermination
public import RegularityStructures.Probability.ModelKolmogorovNorm

/-!
# Uniqueness of moderate canonical models from the weighted determination lemma

Two `IsModerateRenormalisedCanonicalModel` models carry possibly different moderate weights `ρ`,
`ρ'`. The product `ρ ρ'` is moderate (exponent `p + p'`) and dominates both, so
`canonicalModels_agree_below_gamma_of_weighted_growth` applies with one common weight.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43.ModerateWitnesses

/-- The product of two moderate weights is moderate. -/
theorem isModerateWeight_mul {ρ ρ' : RegularityStructures.ParabolicSpace → ℝ} {p p' : ℝ}
    (hρ : RegularityStructures.parabolicSemigroup.IsModerateWeight ρ p)
    (hρ' : RegularityStructures.parabolicSemigroup.IsModerateWeight ρ' p') :
    RegularityStructures.parabolicSemigroup.IsModerateWeight (fun z => ρ z * ρ' z) (p + p') where
  one_le x := one_le_mul_of_one_le_of_one_le (hρ.one_le x) (hρ'.one_le x)
  measurable := hρ.measurable.mul hρ'.measurable
  nonneg_exp := add_nonneg hρ.nonneg_exp hρ'.nonneg_exp
  le y z := by
    have hd : 0 < 1 + RegularityStructures.parabolicSemigroup.scaleDist z y := by
      linarith [RegularityStructures.parabolicSemigroup.scaleDist_nonneg z y]
    calc ρ z * ρ' z
        ≤ (ρ y * (1 + RegularityStructures.parabolicSemigroup.scaleDist z y) ^ p) *
            (ρ' y * (1 + RegularityStructures.parabolicSemigroup.scaleDist z y) ^ p') :=
          mul_le_mul (hρ.le y z) (hρ'.le y z) (zero_le_one.trans (hρ'.one_le z))
            (mul_nonneg (zero_le_one.trans (hρ.one_le y)) (Real.rpow_nonneg hd.le _))
      _ = ρ y * ρ' y * (1 + RegularityStructures.parabolicSemigroup.scaleDist z y) ^ (p + p') := by
          rw [Real.rpow_add hd]; ring

/-- A larger weight preserves `PiBoundGrowth` (for `B ≥ 0`). -/
theorem piBoundGrowth_mono {κ : RegularityStructures.Phi43.Kappa}
    {Z : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
      RegularityStructures.parabolicSemigroup}
    {B : ℝ} {ρ σ : RegularityStructures.ParabolicSpace → ℝ} (hB : 0 ≤ B)
    (hρσ : ∀ x, ρ x ≤ σ x) (h : Z.PiBoundGrowth (RegularityStructures.Phi43.gamma κ) B ρ) :
    Z.PiBoundGrowth (RegularityStructures.Phi43.gamma κ) B σ := by
  intro i hi t ht x
  exact (h i hi t ht x).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hρσ x) hB) (Real.rpow_nonneg ht.1.le _))

/-- **Uniqueness, `Π` part.** Two moderate renormalised canonical models of the same noise and
constants agree on every symbol below `γ`. -/
theorem isModerateRenormalisedCanonicalModel_pi_eq (N : ℕ) (κ : RegularityStructures.Phi43.Kappa)
    (noise : RegularityStructures.Phi43.CanonicalNoise)
    (C : RegularityStructures.Phi43.RenormalisationConstants)
    (Z Z' : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
      RegularityStructures.parabolicSemigroup)
    (hZ : Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z') :
    ∀ (x : RegularityStructures.ParabolicSpace) (τ : RegularityStructures.Phi43.Symbol),
      RegularityStructures.Phi43.homogeneity κ τ < RegularityStructures.Phi43.gamma κ →
      Z.pi x (Pi.single τ 1) = Z'.pi x (Pi.single τ 1) := by
  obtain ⟨h1, h2, h3, ρ, p, B, hρ, hB, hPi⟩ := hZ
  obtain ⟨h1', h2', h3', ρ', p', B', hρ', hB', hPi'⟩ := hZ'
  exact RegularityStructures.Phi43.canonicalModels_agree_below_gamma_of_weighted_growth
    N κ noise C Z Z' (fun z => ρ z * ρ' z) (p + p') (isModerateWeight_mul hρ hρ') B B'
    (piBoundGrowth_mono hB (fun x => le_mul_of_one_le_right
      (zero_le_one.trans (hρ.one_le x)) (hρ'.one_le x)) hPi)
    (piBoundGrowth_mono hB' (fun x => le_mul_of_one_le_left
      (zero_le_one.trans (hρ'.one_le x)) (hρ.one_le x)) hPi')
    ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩

/-- **Uniqueness, `Π` half of `diffNormOn`:** `piDiffNormOn = 0` on all of space. -/
theorem isModerateRenormalisedCanonicalModel_piDiffNormOn_eq_zero (N : ℕ)
    (κ : RegularityStructures.Phi43.Kappa)
    (noise : RegularityStructures.Phi43.CanonicalNoise)
    (C : RegularityStructures.Phi43.RenormalisationConstants)
    (Z Z' : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
      RegularityStructures.parabolicSemigroup)
    (hZ : Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z') :
    Z.piDiffNormOn Z' (RegularityStructures.Phi43.gamma κ) Set.univ = 0 := by
  have h := isModerateRenormalisedCanonicalModel_pi_eq N κ noise C Z Z' hZ hZ'
  refine le_antisymm ((iInf₂_le 0 ?_).trans (by simp)) bot_le
  intro τ hτ t _ x _
  simp [RegularityStructures.Model.regPi, h x τ hτ]


end RegularityStructures.Phi43.ModerateWitnesses

end
