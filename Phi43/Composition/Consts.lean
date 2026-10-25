/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Restart.Package
public import Phi43.RestartDiff.Package
public import Phi43.Inhomogeneity.Theta
public import RegularityStructures.Abstract.FixedPointBanach

/-!
# Explicit constants of the restart compositions

The constants of `Composition.restart_fixedPoint_exists` and `Composition.restart_fixedPoint_diff`
as explicit functions of the datum size `L` and the lift size `B` (a bound on `phi43Size`), given
the structural constants `C₀` (one-model fixed point), `C₀d` (two-model fixed point), `Cs`, `Csd`
(time slices), `c` (one-model restart package) and `cd` (two-model restart package), which depend
only on `(κ, N, η)`:

* `chainG B`, `chainΓ c B`: the near-`4` `Γ`-constants on the window and on the slab;
* `datumR η Gc L B`: the bound on the inhomogeneity `v` (`norm_phi43InhomTheta_le`);
* `restartTime`: the existence time, the minimum of `1` and of the one- and two-model
  `fixedPointTime`s;
* `sliceConst`: the bound on the `1`-coefficient of `𝒦 (U⋆³)`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43.Composition

open RegularityStructures.Inhomogeneity

/-- The near-`4` `Γ`-constant on the window at lift size `B`. -/
def chainG (B : ℝ) : ℝ := gammaChainConst (Fintype.card SymbolF) B 16

/-- The near-`4` `Γ`-constant on the slab at lift size `B`. -/
def chainΓ (c B : ℝ) : ℝ :=
  gammaChainConst (Fintype.card SymbolF) (Restart.restartGammaConst c B) 16

/-- The time exponent of the window fixed point. -/
def theta (κ : Kappa) (η : ℝ) : ℝ := (min (min (phi43Zeta κ) (3 * η) + 2) (gamma κ) - η) / 2

/-- The Lipschitz constant of the cube in the window fixed point. -/
def lipC (κ : Kappa) (c B : ℝ) : ℝ :=
  3 * (phi43ProductF κ).truncMulConst ^ 2 * (1 + chainΓ c B) ^ 4

/-- The bound on the inhomogeneity at datum size `L` and forcing size `B`. -/
def datumR (η : NegExponent) (Gc : ℕ → ℝ) (L B : ℝ) : ℝ :=
  1 + datumConst η 3 * L + Datum.liftConst 3 (thetaKc Gc) * B

/-- The operator constant of the one-model window fixed point. -/
def fpConst (C₀ c B : ℝ) : ℝ :=
  C₀ * ((max 1 (chainG B) * B + Fintype.card SymbolF * 1) * max 1 (chainΓ c B)) *
    (1 + Fintype.card SymbolF * chainΓ c B)

/-- The operator constant of the two-model window fixed point. -/
def fpConstDiff (κ : Kappa) (C₀d c B : ℝ) : ℝ :=
  C₀d * ((max 1 (chainG B) * max B 1 +
    Fintype.card (TwoModel.NonPoly (phi43PolynomialSectorF κ) ⊕ SymbolF) * 1) *
      max 1 (chainΓ c B)) * (1 + Fintype.card SymbolF * chainΓ c B)

/-- **The restart existence time.** -/
def restartTime (κ : Kappa) (η : NegExponent) (Gc : ℕ → ℝ) (C₀ C₀d c L B : ℝ) : ℝ :=
  min 1 (min (fixedPointTime (fpConst C₀ c B) (theta κ η) (lipC κ c B) 0 (datumR η Gc L B) 2)
    (fixedPointTime (fpConstDiff κ C₀d c B) (theta κ η) (lipC κ c B) 0 (datumR η Gc L B) 2))

/-- The slice constant: the bound on the `1`-coefficient of `𝒦 (U⋆³)` for `‖U‖ ≤ R + 1`. -/
def sliceConst (κ : Kappa) (Cs c B R : ℝ) : ℝ :=
  Cs * (((max 1 (chainG B) * B + Fintype.card SymbolF * 1) * max 1 (chainΓ c B)) *
    ((phi43ProductF κ).truncMulConst ^ 2 * (1 + chainΓ c B) ^ 4)) * (R + 1) ^ 3

end RegularityStructures.Phi43.Composition

end

public section

namespace RegularityStructures.Phi43.Composition

open RegularityStructures.Inhomogeneity

theorem gammaChainConst_nonneg' (n : ℕ) (C : ℝ) (m : ℕ) : 0 ≤ gammaChainConst n C m :=
  le_trans (pow_nonneg (mul_nonneg (Nat.cast_nonneg n) (zero_le_one.trans (le_max_left _ _))) m)
    (le_max_right _ _)

theorem chainG_nonneg (B : ℝ) : 0 ≤ chainG B := gammaChainConst_nonneg' _ _ _

theorem chainΓ_nonneg (c B : ℝ) : 0 ≤ chainΓ c B := gammaChainConst_nonneg' _ _ _

theorem theta_pos (κ : Kappa) {η : ℝ} (hη₁ : -2 / 3 < η) (hκη : κ.1 < -1 / 2 - η) :
    0 < theta κ η := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  unfold theta
  have : η < min (min (phi43Zeta κ) (3 * η) + 2) (gamma κ) := by
    refine lt_min ?_ ?_
    · rw [← sub_lt_iff_lt_add, lt_min_iff]
      constructor
      · simp only [phi43Zeta]; linarith
      · linarith
    · simp only [gamma]; linarith
  linarith

theorem lipC_nonneg (κ : Kappa) (c B : ℝ) : 0 ≤ lipC κ c B := by
  unfold lipC
  have := chainΓ_nonneg c B
  positivity

theorem datumR_nonneg (η : NegExponent) {Gc : ℕ → ℝ} (hGc : ∀ L, 0 ≤ Gc L) {L B : ℝ}
    (hL : 0 ≤ L) (hB : 0 ≤ B) : 0 ≤ datumR η Gc L B := by
  unfold datumR
  have h1 := datumConst_nonneg η 3
  have h2 : 0 ≤ Datum.liftConst 3 (thetaKc Gc) := Datum.liftConst_nonneg (thetaKc_nonneg hGc)
  positivity

theorem fpConst_nonneg {C₀ c B : ℝ} (hC₀ : 0 ≤ C₀) (hB : 0 ≤ B) : 0 ≤ fpConst C₀ c B := by
  unfold fpConst
  have h1 := chainΓ_nonneg c B
  have h2 : (0 : ℝ) ≤ max 1 (chainG B) := zero_le_one.trans (le_max_left _ _)
  have h3 : (0 : ℝ) ≤ max 1 (chainΓ c B) := zero_le_one.trans (le_max_left _ _)
  positivity

theorem fpConstDiff_nonneg (κ : Kappa) {C₀d c B : ℝ} (hC₀ : 0 ≤ C₀d) :
    0 ≤ fpConstDiff κ C₀d c B := by
  unfold fpConstDiff
  have h1 := chainΓ_nonneg c B
  have h2 : (0 : ℝ) ≤ max 1 (chainG B) := zero_le_one.trans (le_max_left _ _)
  have h3 : (0 : ℝ) ≤ max 1 (chainΓ c B) := zero_le_one.trans (le_max_left _ _)
  have h4 : (0 : ℝ) ≤ max B 1 := zero_le_one.trans (le_max_right _ _)
  positivity

theorem restartTime_pos (κ : Kappa) (η : NegExponent) {Gc : ℕ → ℝ} (hGc : ∀ L, 0 ≤ Gc L)
    {C₀ C₀d c L B : ℝ} (hC₀ : 0 ≤ C₀) (hC₀d : 0 ≤ C₀d) (hL : 0 ≤ L) (hB : 0 ≤ B) :
    0 < restartTime κ η Gc C₀ C₀d c L B := by
  unfold restartTime
  refine lt_min one_pos (lt_min ?_ ?_)
  · exact fixedPointTime_pos _ _ _ _ _ _ (fpConst_nonneg hC₀ hB) (lipC_nonneg κ c B) le_rfl
      (datumR_nonneg η hGc hL hB)
  · exact fixedPointTime_pos _ _ _ _ _ _ (fpConstDiff_nonneg κ hC₀d) (lipC_nonneg κ c B) le_rfl
      (datumR_nonneg η hGc hL hB)

theorem restartTime_le_one (κ : Kappa) (η : NegExponent) (Gc : ℕ → ℝ) (C₀ C₀d c L B : ℝ) :
    restartTime κ η Gc C₀ C₀d c L B ≤ 1 := min_le_left _ _

theorem restartTime_le_fixedPointTime (κ : Kappa) (η : NegExponent) (Gc : ℕ → ℝ)
    (C₀ C₀d c L B : ℝ) :
    restartTime κ η Gc C₀ C₀d c L B ≤
      fixedPointTime (fpConst C₀ c B) (theta κ η) (lipC κ c B) 0 (datumR η Gc L B) 2 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem restartTime_le_fixedPointTime_diff (κ : Kappa) (η : NegExponent) (Gc : ℕ → ℝ)
    (C₀ C₀d c L B : ℝ) :
    restartTime κ η Gc C₀ C₀d c L B ≤
      fixedPointTime (fpConstDiff κ C₀d c B) (theta κ η) (lipC κ c B) 0 (datumR η Gc L B) 2 :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem sliceConst_nonneg (κ : Kappa) {Cs c B R : ℝ} (hCs : 0 ≤ Cs) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    0 ≤ sliceConst κ Cs c B R := by
  unfold sliceConst
  have h1 := chainΓ_nonneg c B
  have h2 : (0 : ℝ) ≤ max 1 (chainG B) := zero_le_one.trans (le_max_left _ _)
  have h3 : (0 : ℝ) ≤ max 1 (chainΓ c B) := zero_le_one.trans (le_max_left _ _)
  positivity

/-- On the slab `(0, T]`, `T ≤ 1`, the time weight `x.1 ^ ((3η + 2)/2)` is at most `1`. -/
theorem rpow_time_le_one {η : ℝ} (hη₁ : -2 / 3 < η) {T : ℝ} (hT : T ≤ 1) {x : ParabolicSpace}
    (hx : x ∈ timeSlab T) : x.1 ^ ((3 * η + 2) / 2) ≤ 1 :=
  Real.rpow_le_one hx.1.le (hx.2.trans hT) (by linarith)

end RegularityStructures.Phi43.Composition

end
