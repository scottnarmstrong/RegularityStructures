module


public import GlobalPhi43.MW20.ClosingCompleteSecond
public import GlobalPhi43.MW20.SecondForcingEnvelope
public import GlobalPhi43.MW20.ReciprocalSourceGeometry

/-! Actual complete renormalised B forcing supremum at T=d0/k. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- The complete second forcing, including both counterterms and the
ordinary V contribution, has one parent cubic-amplitude supremum bound. -/
theorem source_complete_second_forcing_sup_positive
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J Y Z V : ParabolicSpace → ℝ) (C₂ : ℝ)
    (hv : ContDiff ℝ ∞ v) (hJ : ContDiff ℝ ∞ J) (hY : ContDiff ℝ ∞ Y)
    (hZ : ContDiff ℝ ∞ Z) (hV : ContDiff ℝ ∞ V)
    {r k ε c A : ℝ} (hr : 0 ≤ r) (hk : 2 < k)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hMpos : 0 < sourceSup v r)
    (hS : r + 1 / sourceSup v r ≤ 1 / 2)
    (hnorm : Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r (1 / sourceSup v r) ((3 / 2 : ℝ) - 5 * ε) ≤
      ENNReal.ofReal (A * sourceSup v r))
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hc1 : c ≤ 1)
    (hbudgetA : recenteredASeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Y V C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (hbudgetV : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) (-1 - 2 * ε) V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetX : recenteredXVSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetD : recenteredDSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z V J C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (5 / 2 - 5 * ε))) :
    let M := sourceSup v r
    let γ := (3 / 2 : ℝ) - 5 * ε
    let P := 4 ^ γ * A + 1
    let Cγ := 200 * (2 ^ γ + 4) * (1 + 2 ^ γ)
    let K := secondProductConstant ε *
      ((312 * P) * (2 : ℝ) ^ (1 / 2 - 3 * ε) +
        (A + 6 + 216 * P) * (2 : ℝ) ^ γ +
        (4 ^ γ * (5 * Cγ) * P) * (2 : ℝ) ^ γ + 2 + 2 * (72 * P)) + 1
    let T := (1 / M) / k
    let μ := infiniteKernelMeasure Φ hΦ T
      (div_pos (one_div_pos.mpr hMpos) (by linarith : 0 < k))
    sourceSup (fun x => pastSmooth μ (fun y => v y * V y) x +
      3 * C₂ * (pastSmooth μ v x + pastSmooth μ J x)) (r + 1 / M) ≤
      K * c * M ^ (3 : ℝ) * k ^ (3 / 2 + 3 * ε) := by
  have hg := reciprocal_source_geometry hr hMpos hk hS
  let γ := (3 / 2 : ℝ) - 5 * ε
  let P := (4 : ℝ) ^ γ * A + 1
  let Cγ := 200 * ((2 : ℝ) ^ γ + 4) * (1 + (2 : ℝ) ^ γ)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hCγ : 0 ≤ Cγ := by dsimp [Cγ]; positivity
  have he := second_forcing_envelope_bound (Cv := 312 * P) (CU := A + 6 + 216 * P)
    (Cν := (4 : ℝ) ^ γ * (5 * Cγ) * P) (CN := 72 * P)
    hMpos hk (by positivity) (by positivity) (by positivity) (by positivity) hε hsmall
  have hVenv := ordinary_V_forcing_envelope_bound hMpos hk hε
  have hK := (secondProductConstant_pos hsmall).le
  dsimp only [P, γ, Cγ] at he
  dsimp only at hg ⊢
  apply csSup_le ((sourceCylinder_nonempty
    (show r + 1 / sourceSup v r ∈ Icc (0 : ℝ) (1 / 2) from ⟨by positivity, hS⟩)).image _)
  rintro z ⟨x, hx, rfl⟩
  have hball := large_scale_testing_ball_subset hr (one_div_pos.mpr hMpos) hk hx
  have hxP := sourceCylinder_antitone hr (le_add_of_nonneg_right (by positivity)) hx
  have hp := source_complete_second_forcing_from_radius_bound_positive Φ hΦ v J Y Z V C₂ hv hJ hY hZ hV
    hr hg.2.2.2.2.1 hg.2.2.1 hg.1 hg.2.1 hε hsmall hc hA hMpos hg.2.2.2.1
    hg.2.2.2.2.2 hnorm hbudgetY hbudgetZ hc1 hxP hball hbudgetA hbudgetV hbudgetX hbudgetD
  apply hp.trans
  have hb := add_le_add
    (mul_le_mul_of_nonneg_left he (show 0 ≤ secondProductConstant ε * c by positivity))
    (mul_le_mul_of_nonneg_left hVenv hc)
  convert hb using 1 <;> ring

end GlobalPhi43.MW20
