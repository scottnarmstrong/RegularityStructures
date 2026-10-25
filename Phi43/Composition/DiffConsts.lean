/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Composition.Structural

/-!
# Explicit constants of the two-model restart composition

* `diffW cd B = max 1 (restartGammaDiffConst cd B)`: the near-`1` `Γ`-difference constant (per unit
  lift distance) on the window and the slab;
* `diffChain c cd B`: the difference constant (per unit lift distance) of the two-model fixed point,
  dominating the chained near-`4` constants;
* `diffConst`: the Lipschitz constant of the fixed point in `(‖w₁ - w₂‖_η, δ)`;
* `sliceDiffConst`: the constant of the two-model time slice;
* `compK'`: the constant of `Composition.restart_fixedPoint_diff`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43.Composition

/-- The near-`1` `Γ`-difference constant per unit lift distance. -/
def diffW (cd B : ℝ) : ℝ := max 1 (Restart.restartGammaDiffConst cd B)

/-- The difference constant of the two-model fixed point per unit lift distance. -/
def diffChain (c cd B : ℝ) : ℝ :=
  max (diffW cd B) (max (gammaDiffChainConst (Fintype.card SymbolF) B (diffW cd B) 16)
    (gammaDiffChainConst (Fintype.card SymbolF) (Restart.restartGammaConst c B) (diffW cd B) 16))

/-- The cube factor `c² (R + 1)³ (1 + C_Γ)⁴`. -/
def cubeFac (κ : Kappa) (c B R : ℝ) : ℝ :=
  (phi43ProductF κ).truncMulConst ^ 2 * (R + 1) ^ 3 * (1 + chainΓ c B) ^ 4

/-- The second operator constant of the two-model fixed point. -/
def fpConstDiff' (κ : Kappa) (C₀d c B : ℝ) : ℝ :=
  C₀d * ((max 1 (chainG B) * max B 1 +
    Fintype.card (TwoModel.NonPoly (phi43PolynomialSectorF κ) ⊕ SymbolF) * 1) *
      max 1 (chainΓ c B)) * (1 + Fintype.card SymbolF * chainΓ c B + Fintype.card SymbolF)

/-- The Lipschitz constant of the two-model fixed point. -/
def diffConst (κ : Kappa) (η : NegExponent) (Gc : ℕ → ℝ) (C₀d c cd L B : ℝ) : ℝ :=
  2 * (Inhomogeneity.datumConst η 3 + Datum.liftConst 3 (thetaKc Gc) * B +
    (fpConstDiff κ C₀d c B * (4 * cubeFac κ c B (datumR η Gc L B)) +
      cubeFac κ c B (datumR η Gc L B) * fpConstDiff' κ C₀d c B) * diffChain c cd B)

/-- The constant of the two-model time slice. -/
def sliceDiffConst (κ : Kappa) (Csd c B R : ℝ) : ℝ :=
  Csd * ((((max 1 (chainG B) * max B 1 +
    Fintype.card (TwoModel.NonPoly (phi43PolynomialSectorF κ) ⊕ SymbolF) * 1) *
      max 1 (chainΓ c B)) * ((phi43ProductF κ).truncMulConst ^ 2 * (1 + chainΓ c B) ^ 4 * 5)) *
        (R + 1) ^ 3)

variable (κ : Kappa) (η : NegExponent) (hη₁ : -2 / 3 < (η : ℝ)) (hκη : κ.1 < -1 / 2 - η)
  (N : ℕ) (hN : 3 ≤ N)

/-- **The constant `K'` of the two-model restart composition.** -/
def compK' (Gc : ℕ → ℝ) (L B : ℝ) : ℝ :=
  max (diffConst κ η Gc (fpCd κ η hη₁ hκη N hN) (rqC κ N hN) (rqCd κ N hN) L B)
    (sliceDiffConst κ (tsCd κ η hη₁ hκη N hN) (rqC κ N hN) B (datumR η Gc L B) *
      (diffConst κ η Gc (fpCd κ η hη₁ hκη N hN) (rqC κ N hN) (rqCd κ N hN) L B +
        diffChain (rqC κ N hN) (rqCd κ N hN) B))

end RegularityStructures.Phi43.Composition

end

public section

namespace RegularityStructures.Phi43.Composition

theorem one_le_diffW (cd B : ℝ) : 1 ≤ diffW cd B := le_max_left _ _

theorem diffW_le_diffChain (c cd B : ℝ) : diffW cd B ≤ diffChain c cd B := le_max_left _ _

theorem one_le_diffChain (c cd B : ℝ) : 1 ≤ diffChain c cd B :=
  (one_le_diffW cd B).trans (diffW_le_diffChain c cd B)

theorem cubeFac_nonneg (κ : Kappa) (c B : ℝ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ cubeFac κ c B R := by
  unfold cubeFac
  have := chainΓ_nonneg c B
  positivity

theorem fpConstDiff'_nonneg (κ : Kappa) {C₀d : ℝ} (hC : 0 ≤ C₀d) (c B : ℝ) :
    0 ≤ fpConstDiff' κ C₀d c B := by
  unfold fpConstDiff'
  have h1 := chainΓ_nonneg c B
  have h2 : (0 : ℝ) ≤ max 1 (chainG B) := zero_le_one.trans (le_max_left _ _)
  have h3 : (0 : ℝ) ≤ max 1 (chainΓ c B) := zero_le_one.trans (le_max_left _ _)
  have h4 : (0 : ℝ) ≤ max B 1 := zero_le_one.trans (le_max_right _ _)
  positivity

theorem diffConst_nonneg (κ : Kappa) (η : NegExponent) {Gc : ℕ → ℝ} (hGc : ∀ L, 0 ≤ Gc L)
    {C₀d c cd L B : ℝ} (hC : 0 ≤ C₀d) (hL : 0 ≤ L) (hB : 0 ≤ B) :
    0 ≤ diffConst κ η Gc C₀d c cd L B := by
  unfold diffConst
  have h1 := Inhomogeneity.datumConst_nonneg η 3
  have h2 : 0 ≤ Datum.liftConst 3 (thetaKc Gc) := Datum.liftConst_nonneg (thetaKc_nonneg hGc)
  have h3 := cubeFac_nonneg κ c B (datumR_nonneg η hGc hL hB)
  have h4 := fpConstDiff_nonneg κ (c := c) (B := B) hC
  have h5 := fpConstDiff'_nonneg κ hC c B
  have h6 := (zero_le_one.trans (one_le_diffChain c cd B))
  positivity

theorem sliceDiffConst_nonneg (κ : Kappa) {Csd : ℝ} (hC : 0 ≤ Csd) (c B : ℝ) {R : ℝ}
    (hR : 0 ≤ R) : 0 ≤ sliceDiffConst κ Csd c B R := by
  unfold sliceDiffConst
  have h1 := chainΓ_nonneg c B
  have h2 : (0 : ℝ) ≤ max 1 (chainG B) := zero_le_one.trans (le_max_left _ _)
  have h3 : (0 : ℝ) ≤ max 1 (chainΓ c B) := zero_le_one.trans (le_max_left _ _)
  have h4 : (0 : ℝ) ≤ max B 1 := zero_le_one.trans (le_max_right _ _)
  positivity

/-- The chained difference constant at near-`1` constant `diffW cd B · δ` is at most
`diffChain c cd B · δ`. -/
theorem gammaDiffChainConst_diffW_le {C c cd B δ : ℝ} (hδ : 0 ≤ δ)
    (hC : C = B ∨ C = Restart.restartGammaConst c B) :
    gammaDiffChainConst (Fintype.card SymbolF) C (diffW cd B * δ) 16 ≤ diffChain c cd B * δ := by
  have hW : 0 ≤ diffW cd B := zero_le_one.trans (one_le_diffW cd B)
  have e : gammaDiffChainConst (Fintype.card SymbolF) C (diffW cd B * δ) 16 =
      gammaDiffChainConst (Fintype.card SymbolF) C (diffW cd B) 16 * δ := by
    rw [Restart.gammaDiffChainConst_eq_mul _ _ (mul_nonneg hW hδ) 16,
      Restart.gammaDiffChainConst_eq_mul (Fintype.card SymbolF) C hW 16]
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ hδ
  unfold diffChain
  rcases hC with rfl | rfl
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

end RegularityStructures.Phi43.Composition

end
