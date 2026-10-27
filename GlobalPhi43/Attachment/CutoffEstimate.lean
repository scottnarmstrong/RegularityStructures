module

public import GlobalPhi43.Attachment.GammaRecenterBound
public import GlobalPhi43.Attachment.PartitionProfiles
public import GlobalPhi43.Attachment.TestGeometry
public import GlobalPhi43.Attachment.FourDerivativeNorm
public import GlobalPhi43.Attachment.SmallScalePairing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The single recentered cutoff estimate in the large-scale conversion. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 GlobalPhi43.Local

/-- Scale powers after recentering have exactly the original homogeneity. -/
theorem recenter_scale_power {T r : ℝ} (hT : 0 < T) (hr : 0 < r) (α β : ℝ) :
    (4 * T) ^ (α - β) * (4 * (T * r)) ^ β =
      (4 ^ (α - β) * (4 * r) ^ β) * T ^ α := by
  rw [Real.mul_rpow (by norm_num) hT.le,
    show 4 * (T * r) = (4 * r) * T by ring,
    Real.mul_rpow (mul_pos (by norm_num) hr).le hT.le]
  calc _ = (4 ^ (α - β) * (4 * r) ^ β) * (T ^ (α - β) * T ^ β) := by ring
    _ = _ := by rw [← Real.rpow_add hT, sub_add_cancel]

/-- A fixed coefficient for one pair of symbols and one fixed cutoff allowance. -/
def cutoffPairingCoefficient (κ : Kappa) (τ σ : Symbol) (r B : ℝ) : ℝ :=
  r ^ 5 * Fintype.card Symbol * parabolicSemigroup.pairingConst
    ((phi43RegularityStructure κ).degreesAtMost (homogeneity κ σ)) * 16 * B *
      (volume.real {z : ParabolicSpace | pdist 0 z ≤ 1} +
        volume.real {z : ParabolicSpace | pdist 0 z ≤ 1} *
          (generatorTimeCoeff + 3 * generatorSpaceCoeff) * 4 ^ 4) *
      (4 ^ (homogeneity κ τ - homogeneity κ σ) * (4 * r) ^ homogeneity κ σ)

open scoped ContDiff in
/-- One cutoff contribution is controlled with a coefficient independent of the noise,
model and test, and the final cubic model-norm allowance. -/
theorem cutoff_recenter_estimate {N : ℕ} {κ : Kappa} {f₀ : SpaceTime → ℝ}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hZ : Statements.IsModeratePhi43ModelOf N κ f₀ C Z)
    (hg : Statements.HasPhi43NoiseGrowth f₀) {D : Set ParabolicSpace}
    (hfin : Z.normOn (gamma κ) D ≠ ⊤) {x w b : ParabolicSpace} (hx : x ∈ D) (hw : w ∈ D)
    {τ σ : Symbol} (hτ : homogeneity κ τ < gamma κ) (hσ : homogeneity κ σ < 0)
    {T r : ℝ} (hT : 0 < T) (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 4 * (T * r) ≤ 1)
    (hR : parabolicNorm (w - x) ≤ 4 * T)
    (hball : ∀ y, parabolicNorm (y - w) ≤ 4 * (T * r) → y ∈ D)
    {φ χ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ)
    {A B : ℝ} (hA : ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k φ z‖ ≤ A)
    (hB : ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k χ z‖ ≤ B)
    (hχs : tsupport χ ⊆ {z | parabolicNorm (z - b) < r})
    {f : ParabolicSpace → ℝ} (hf : Continuous f) (hfg : PolyBounded f)
    (hreal : ∀ u, 0 < u → ∀ y, Z.regPi w (Pi.single σ 1) u y = parabolicSemigroup.apply u f y) :
    let p := fun z => φ (b + parabolicDilate r z) * χ (b + parabolicDilate r z)
    let M := (Z.normOn (gamma κ) D).toReal
    |Z.gammaMap w x (Pi.single τ 1) σ * (r ^ 5 * ∫ y, f y * rescaledTestFunction p (T * r) w y)| ≤
      |cutoffPairingCoefficient κ τ σ r B| * A * (1 + M) ^ 3 * T ^ homogeneity κ τ := by
  let p := fun z => φ (b + parabolicDilate r z) * χ (b + parabolicDilate r z)
  let M := (Z.normOn (gamma κ) D).toReal
  let V := volume.real {z : ParabolicSpace | pdist 0 z ≤ 1}
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (by decide) 0)
  obtain ⟨hp, hp1, hpder⟩ := partition_profile_bounds hφ hχ hA hB hr hr1 hχs
  have hpK : ∀ z, z ∉ {z | pdist 0 z ≤ 1} → p z = 0 := by
    intro z hz
    apply hp1 z
    have hd := pdist_le_parabolicNorm 0 z
    simp only [zero_sub, parabolicNorm_neg] at hd
    have hz' : 1 < pdist 0 z := lt_of_not_ge hz
    linarith
  have hp4 : ∀ z, 4 < parabolicNorm z → p z = 0 := fun z hz => hp1 z (by linarith)
  have hpin : IsPinnedSymbol σ := Or.inl ((mem_fMinus_iff_isFMinus σ).mpr
    ((homogeneity_neg_iff_isFMinus κ σ).mp hσ))
  have hcut : homogeneity κ σ < gamma κ := by
    have hk := kappa_pos κ
    dsimp [gamma]; linarith
  have hpair := smallScale_integral_le hg hZ hpin hcut hfin hw (mul_pos hT hr) hsmall hball
    hf hfg hreal hp (isCompact_pdist_ball (by norm_num : (0 : ℝ) ≤ 1)) hpK hp4 hpder
  change |∫ y, f y * rescaledTestFunction p (T * r) w y| ≤
    (Fintype.card Symbol * M * (1 + M)) * parabolicSemigroup.pairingConst
      ((phi43RegularityStructure κ).degreesAtMost (homogeneity κ σ)) *
      (V * (16 * A * B) + V * (generatorTimeCoeff + 3 * generatorSpaceCoeff) * (16 * A * B) * 4 ^ 4) *
        (4 * (T * r)) ^ homogeneity κ σ at hpair
  have hgam := gamma_single_le_norm_radius Z hfin hτ hx hw hR σ
  change |Z.gammaMap w x (Pi.single τ 1) σ| ≤
    (1 + M) * (4 * T) ^ (homogeneity κ τ - homogeneity κ σ) at hgam
  have hgam0 : 0 ≤ (1 + M) * (4 * T) ^ (homogeneity κ τ - homogeneity κ σ) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (mul_pos (by norm_num) hT).le _)
  have hr5 : 0 ≤ r ^ 5 := pow_nonneg hr.le 5
  have hraw := mul_le_mul hgam (mul_le_mul_of_nonneg_left hpair hr5)
    (mul_nonneg hr5 (abs_nonneg (∫ y, f y * rescaledTestFunction p (T * r) w y))) hgam0
  have hn : M * (1 + M) ^ 2 ≤ (1 + M) ^ 3 := by
    calc _ ≤ (1 + M) * (1 + M) ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = _ := by ring
  have hraw' : |Z.gammaMap w x (Pi.single τ 1) σ| *
      (r ^ 5 * |∫ y, f y * rescaledTestFunction p (T * r) w y|) ≤
      cutoffPairingCoefficient κ τ σ r B * A * (M * (1 + M) ^ 2) * T ^ homogeneity κ τ := by
    refine hraw.trans_eq ?_
    calc _ = (r ^ 5 * Fintype.card Symbol * parabolicSemigroup.pairingConst
        ((phi43RegularityStructure κ).degreesAtMost (homogeneity κ σ)) * 16 * B *
        (V + V * (generatorTimeCoeff + 3 * generatorSpaceCoeff) * 4 ^ 4)) * A *
        (M * (1 + M) ^ 2) *
        ((4 * T) ^ (homogeneity κ τ - homogeneity κ σ) * (4 * (T * r)) ^ homogeneity κ σ) := by
          ring
      _ = _ := by
        rw [recenter_scale_power hT hr]
        dsimp [cutoffPairingCoefficient, V]
        ring
  change |Z.gammaMap w x (Pi.single τ 1) σ *
    (r ^ 5 * ∫ y, f y * rescaledTestFunction p (T * r) w y)| ≤
      |cutoffPairingCoefficient κ τ σ r B| * A * (1 + M) ^ 3 * T ^ homogeneity κ τ
  rw [abs_mul, abs_mul, abs_of_nonneg hr5]
  refine hraw'.trans ?_
  calc _ ≤ |cutoffPairingCoefficient κ τ σ r B| * A * (M * (1 + M) ^ 2) * T ^ homogeneity κ τ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hA0)
          (mul_nonneg hM (sq_nonneg _))) (Real.rpow_nonneg hT.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hn (mul_nonneg (abs_nonneg _) hA0)) (Real.rpow_nonneg hT.le _)

end GlobalPhi43.Attachment
