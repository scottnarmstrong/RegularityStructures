/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.FixedPointF.Hypotheses
public import RegularityStructures.Abstract.Singular.Phi4FixedPointWinNearOne
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Integration.Theorem512.MeasKGamma
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG

/-!
# The `Φ⁴₃` window fixed point on the enlarged structure, near-pair `Γ`-bounds

[Hai14, Thm. 7.1, Thm. 7.8, Prop. 9.8 (local part)]. `phi43FixedPointF_window_nearOne` is
`Model.exists_unique_phi4_fixedPoint_causal_win_nearOne` (all `Γ`-bounds only for pairs at parabolic
distance `≤ 1`) at the `Φ⁴₃` data:

* `𝒯 = phi43RegularityStructureF κ`, product `phi43ProductF κ`, polynomial sector
  `phi43PolynomialSectorF κ` (`N' = 3`), block `A = phi43XiFreeF`, integration `phi43IntegrationF`;
* `γ₀ = gamma κ = 1 + 3κ`, `α = -1/2 - κ`, `η₀ = η`, `η' = 2η`, `η'' = 3η`, `ζ = -3/2 - 3κ`;
* sectors `V = phi43SectorV`, `W = phi43SectorW`.

Every structural hypothesis (sectors, regularity, regular pairs, `η`-inequalities, degree and
non-resonance conditions, block invariance, the integration clauses) is discharged; only the
per-model hypotheses remain.  The structural hypotheses need only `3 ≤ N`, `-2/3 < η` and `κ < -1/2 - η` (hence `η < -1/2`); no exclusion of `κ` is used.
-/

public section

namespace RegularityStructures.Phi43

/-- **The `Φ⁴₃` window fixed point on the enlarged structure**, with all structural hypotheses
discharged; near-pair `Γ`-bounds. -/
theorem phi43FixedPointF_window_nearOne (κ : Kappa) {η : ℝ} (hη₁ : -2 / 3 < η)
    (hκη : κ.1 < -1 / 2 - η) {N : ℕ} (hN : 3 ≤ N) {h r : ParabolicSpace → ℝ}
    (hp : KernelPair h r N) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (M : Model (phi43RegularityStructureF κ) parabolicSemigroup)
        {CPi CGam CΓ CGam₁ CΓ₁ R₀ T : ℝ}
        (v : M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T)),
      M.PiBoundOn (gamma κ + phi43Alpha κ + phi43Alpha κ) CPi hairerTimeWindow →
      M.GammaBoundNearOn (gamma κ + phi43Alpha κ + phi43Alpha κ) CGam₁ 1 hairerTimeWindow →
      gammaChainConst (Fintype.card SymbolF) CGam₁ 16 ≤ CGam →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M.GrowthModel (gamma κ + phi43Alpha κ + phi43Alpha κ) C' C'' ρP ρG p q) →
      0 ≤ CPi → M.IsJointMeasurable →
      M.IsRealisingP h (gamma κ + phi43Alpha κ + phi43Alpha κ) (phi43PolynomialSectorF κ)
        phi43IntegrationF (blockSpan phi43XiFreeF) →
      M.GammaBoundNearOn (gamma κ) CΓ₁ 1 (timeSlab T) →
      M.GammaBoundNearOn (gamma κ + phi43Alpha κ) CΓ₁ 1 (timeSlab T) →
      M.GammaBoundNearOn (gamma κ + phi43Alpha κ + phi43Alpha κ + 2) CΓ₁ 1 (timeSlab T) →
      gammaChainConst (Fintype.card SymbolF) CΓ₁ 16 ≤ CΓ →
      0 ≤ CΓ → 0 ≤ R₀ → 0 < T → T ≤ 1 →
      T ≤ fixedPointTime
        (C₀ * ((max 1 CGam * CPi + Fintype.card SymbolF * 1) * max 1 CΓ) *
          (1 + Fintype.card SymbolF * CΓ))
        ((min (min (phi43Zeta κ) (3 * η) + 2) (gamma κ) - η) / 2)
        (3 * (phi43ProductF κ).truncMulConst ^ 2 * (1 + CΓ) ^ 4) 0 R₀ 2 →
      ‖v‖ ≤ R₀ →
      ∃ 𝒦 : M.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η)
            (timeSlab T) →ₗ[ℝ] M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T),
        (∀ g : M.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η)
            (timeSlab T), ∀ x ∈ timeSlab T, (𝒦 g).val x =
          lowerProj (phi43RegularityStructureF κ).deg (gamma κ)
            (M.kGammaRemG h r (phi43PolynomialSectorF κ) phi43IntegrationF
              (gamma κ + phi43Alpha κ + phi43Alpha κ)
              (Model.SlabSpace.blockProj phi43XiFreeF
                (Model.gammaMap_blockProj_of_isBlockInvariant (phi43XiFreeF_isBlockInvariant κ) M)
                g).val x)) ∧
        ∃! U : M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T), ‖U‖ ≤ R₀ + 1 ∧
          U = -𝒦 (Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ)
            (3 * η) U) + v := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  obtain ⟨C₀, hC₀, hspec⟩ := Model.exists_unique_phi4_fixedPoint_causal_win_nearOne
    (𝒯 := phi43RegularityStructureF κ) (phi43ProductF κ) hp (phi43PolynomialSectorF κ)
    phi43XiFreeF (V := phi43SectorV) (W := phi43SectorW) (α := phi43Alpha κ) (γ₀ := gamma κ)
    (η₀ := η) (η' := 2 * η) (η'' := 3 * η) (ζ := phi43Zeta κ)
    (phi43SectorV_isSector κ) (phi43SectorW_isSector κ) (phi43SectorV_ofRegularity κ)
    (phi43SectorW_ofRegularity κ) (phi43ProductF_mul_mem κ) (phi43ProductF_isRegularPair_VV κ)
    (phi43ProductF_isRegularPair_VW κ)
    (by simp only [phi43Alpha]; linarith) (by linarith)
    (by simp only [gamma, phi43Alpha]; linarith) (by simp only [phi43Alpha]; linarith)
    (by simp only [phi43Alpha]; linarith) (by linarith)
    (by simp only [gamma, phi43Alpha]; linarith) isCoordClosed_phi43SectorV
    (by simp only [gamma, phi43Alpha]; linarith)
    (by
      rw [← sub_lt_iff_lt_add, lt_min_iff]
      constructor <;> (try simp only [phi43Zeta]) <;> linarith)
    (by simp only [gamma]; linarith)
    (fun i hi => phi43DegreeF_xiFree_ge κ hi)
    (by simp only [gamma, phi43Alpha, phi43Zeta]; linarith)
    (lt_min_iff.2 ⟨by simp only [phi43Zeta]; linarith, by linarith⟩)
    (by simp only [gamma, phi43Alpha]; linarith)
    (fun j _ => phi43DegreeF_gt_neg_four κ j) hN (phi43DegreeTwo_hNgamma κ)
    (fun k _ l => phi43_hnat κ k l) (fun k _ i hi _ _ => phi43_hni κ k i hi)
    (phi43XiFreeF_isSector κ) (phi43XiFreeF_isBlockInvariant κ)
    (fun k _ => phi43_hpolyV κ k)
  refine ⟨C₀, hC₀, ?_⟩
  intro M CPi CGam CΓ CGam₁ CΓ₁ R₀ T v hPi hGam hCG hgr hCPi hJ hreal hΓ₀ hΓ₁ hΓK hCΓr hCΓ hR₀ hT
    hT1 hTT₀ hv
  exact hspec M phi43IntegrationF (CI := 1) v hPi hGam hCG hgr hCPi hJ hreal
    (phi43IntegrationF_isAbstractIntegration κ)
    (fun a _ kk => phi43IntegrationF_polyEmb_eq_zero κ a kk)
    (fun i j => phi43IntegrationF_single_abs_le i j)
    (fun a _ => phi43IntegrationF_mem_sectorV a) hΓ₀ hΓ₁ hΓK hCΓr hCΓ hR₀ hT hT1 hTT₀ hv

end RegularityStructures.Phi43

end
