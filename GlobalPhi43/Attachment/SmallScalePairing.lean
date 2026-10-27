module

public import GlobalPhi43.Attachment.ModelLocalBall
public import GlobalPhi43.Attachment.PairingRealisation
public import GlobalPhi43.Attachment.ScaledTestSupport
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Small-scale pairing from the actual moderate-model inputs and explicit C4 test estimates. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43

open scoped ContDiff in
/-- The small-scale ordinary integral estimate. The profile may occupy the parabolicNorm ball
of radius four, as required when converting a unit test for the parabolic maximum metric. -/
theorem smallScale_integral_le {N : ℕ} {κ : Kappa} {f₀ : SpaceTime → ℝ}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hg : Statements.HasPhi43NoiseGrowth f₀)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f₀ C Z)
    {τ : Symbol} (hτ : IsPinnedSymbol τ) (hdeg : homogeneity κ τ < gamma κ)
    {S : Set ParabolicSpace} (hfin : Z.normOn (gamma κ) S ≠ ⊤)
    {x : ParabolicSpace} (hx : x ∈ S) {T : ℝ} (hT : 0 < T) (hT1 : 4 * T ≤ 1)
    (hS : ∀ y, parabolicNorm (y - x) ≤ 4 * T → y ∈ S)
    {f : ParabolicSpace → ℝ} (hf : Continuous f) (hfg : PolyBounded f)
    (hreal : ∀ r, 0 < r → ∀ y, Z.regPi x (Pi.single τ 1) r y = parabolicSemigroup.apply r f y)
    {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Set ParabolicSpace} (hK : IsCompact K) (hsK : ∀ y, y ∉ K → φ y = 0)
    (hs4 : ∀ y, 4 < parabolicNorm y → φ y = 0)
    {B : ℝ} (hB : ∀ k ≤ 4, ∀ y, ‖iteratedFDeriv ℝ k φ y‖ ≤ B) :
    let M := (Z.normOn (gamma κ) S).toReal
    |∫ y, f y * rescaledTestFunction φ T x y| ≤
      (Fintype.card Symbol * M * (1 + M)) * parabolicSemigroup.pairingConst
        ((phi43RegularityStructure κ).degreesAtMost (homogeneity κ τ)) *
      (volume.real K * B + volume.real K * (generatorTimeCoeff + 3 * generatorSpaceCoeff) * B * 4 ^ 4) *
        (4 * T) ^ homogeneity κ τ := by
  have hball := model_localBall hg hZ hτ hdeg hfin hx hT1 hS
  have hsupp := isSupported_rescaled_of_radius hφ (by norm_num : (0 : ℝ) < 4) hs4 hT x
  have hc : HasCompactSupport (rescaledTestFunction φ T x) :=
    hasCompactSupport_of_eq_zero (mul_pos (by norm_num) hT) x
      (fun _ hy => rescaled_eq_zero_outside hs4 hT hy)
  have hφ0 (y : ParabolicSpace) : |φ y| ≤ B := by
    simpa using hB 0 (by decide) y
  have hscale : T ^ (-(4 : ℝ)) = (4 : ℝ) ^ 4 * (4 * T) ^ (-(4 : ℝ)) := by
    have hp1 : T ^ (4 : ℝ) = T ^ (4 : ℕ) := Real.rpow_natCast T 4
    have hp2 : (4 * T) ^ (4 : ℝ) = (4 * T) ^ (4 : ℕ) := Real.rpow_natCast (4 * T) 4
    rw [Real.rpow_neg hT.le, Real.rpow_neg (mul_pos (by norm_num) hT).le, hp1, hp2]
    field_simp
  have hL1 := integral_abs_rescaled_le hφ.continuous hK hsK hφ0 hT x
  have hG := integral_abs_generator_rescaled_le hφ hK hsK hB hT x
  rw [hscale] at hG
  have hG' : ∫ y, |parabolicGenerator (rescaledTestFunction φ T x) y| ≤
      (volume.real K * (generatorTimeCoeff + 3 * generatorSpaceCoeff) * B * 4 ^ 4) *
        (4 * T) ^ (-(4 : ℝ)) := by
    simpa only [mul_assoc] using hG
  exact integral_realisation_le hball (model_degreesAtMost_gt_neg_four κ τ) hf hfg hreal
    (contDiff_rescaledTestFunction hφ T x) hc (mul_pos (by norm_num) hT) hT1 hsupp hL1 hG'

end GlobalPhi43.Attachment
