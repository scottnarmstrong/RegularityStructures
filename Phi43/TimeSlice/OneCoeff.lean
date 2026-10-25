/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.FixedPointF.WindowNear
public import Phi43.TimeSlice.AbstractOne
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG

/-!
# The constant-coefficient of the `Φ⁴₃` fixed-point operator applied to a cube

At the `Φ⁴₃` data of `phi43FixedPointF_window_nearOne`, for any linear operator `𝒦` with the
characterisation clause of that theorem and any slab element `U` with `‖U‖ ≤ R₀ + 1`, the
coefficient of `𝒦 (U³)` at the symbol `1` is bounded by `C₀ K₁ (R₀ + 1)³ t^{(3η+2)/2}` at
`x = (t, ·) ∈ timeSlab T`, `T ≤ 1`.
-/

public section

namespace RegularityStructures.Phi43.TimeSlice

open RegularityStructures

/-- On the time slab with `T ≤ 1`, `singularWeight timeZeroDist x ^ e = x.1 ^ (e / 2)`. -/
theorem singularWeight_timeZeroDist_rpow_of_mem_timeSlab {T : ℝ} (hT : T ≤ 1)
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) (e : ℝ) :
    singularWeight timeZeroDist x ^ e = x.1 ^ (e / 2) := by
  have h0 : 0 < x.1 := hx.1
  have h1 : x.1 ≤ 1 := hx.2.trans hT
  have hs : singularWeight timeZeroDist x = Real.sqrt x.1 := by
    unfold singularWeight timeZeroDist
    rw [abs_of_pos h0]
    exact min_eq_right (Real.sqrt_le_one.2 h1)
  rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_mul h0.le]
  congr 1
  ring

/-- **The `1`-coefficient of `𝒦 (U³)` at the `Φ⁴₃` window fixed point.** -/
theorem phi43_one_coeff_fixedPoint_le (κ : Kappa) {η : ℝ} (hη₁ : -2 / 3 < η)
    (hκη : κ.1 < -1 / 2 - η) {N : ℕ} (hN : 3 ≤ N) {h r : ParabolicSpace → ℝ}
    (hp : KernelPair h r N) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (M : Model (phi43RegularityStructureF κ) parabolicSemigroup)
        {CPi CGam CΓ CGam₁ CΓ₁ R₀ T : ℝ},
      M.PiBoundOn (gamma κ + phi43Alpha κ + phi43Alpha κ) CPi hairerTimeWindow →
      M.GammaBoundNearOn (gamma κ + phi43Alpha κ + phi43Alpha κ) CGam₁ 1 hairerTimeWindow →
      gammaChainConst (Fintype.card SymbolF) CGam₁ 16 ≤ CGam →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M.GrowthModel (gamma κ + phi43Alpha κ + phi43Alpha κ) C' C'' ρP ρG p q) →
      0 ≤ CPi →
      M.IsRealisingP h (gamma κ + phi43Alpha κ + phi43Alpha κ) (phi43PolynomialSectorF κ)
        phi43IntegrationF (blockSpan phi43XiFreeF) →
      M.GammaBoundNearOn (gamma κ) CΓ₁ 1 (timeSlab T) →
      M.GammaBoundNearOn (gamma κ + phi43Alpha κ) CΓ₁ 1 (timeSlab T) →
      M.GammaBoundNearOn (gamma κ + phi43Alpha κ + phi43Alpha κ + 2) CΓ₁ 1 (timeSlab T) →
      gammaChainConst (Fintype.card SymbolF) CΓ₁ 16 ≤ CΓ →
      0 ≤ CΓ → T ≤ 1 →
      ∀ 𝒦 : M.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η)
            (timeSlab T) →ₗ[ℝ] M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T),
        (∀ g : M.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η)
            (timeSlab T), ∀ x ∈ timeSlab T, (𝒦 g).val x =
          lowerProj (phi43RegularityStructureF κ).deg (gamma κ)
            (M.kGammaRemG h r (phi43PolynomialSectorF κ) phi43IntegrationF
              (gamma κ + phi43Alpha κ + phi43Alpha κ)
              (Model.SlabSpace.blockProj phi43XiFreeF
                (Model.gammaMap_blockProj_of_isBlockInvariant (phi43XiFreeF_isBlockInvariant κ) M)
                g).val x)) →
        ∀ U : M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T), ‖U‖ ≤ R₀ + 1 →
          ∀ x ∈ timeSlab T,
            |(𝒦 (Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ)
                (3 * η) U)).val x (SymbolF.old .one)| ≤
              C₀ * (((max 1 CGam * CPi + Fintype.card SymbolF * 1) * max 1 CΓ) *
                ((phi43ProductF κ).truncMulConst ^ 2 * (1 + CΓ) ^ 4)) * (R₀ + 1) ^ 3 *
                x.1 ^ ((3 * η + 2) / 2) := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  obtain ⟨C₀, hC₀, hspec⟩ := exists_abs_kernel_cube_apply_le
    (𝒯 := phi43RegularityStructureF κ) (phi43ProductF κ) hp (phi43PolynomialSectorF κ)
    phi43XiFreeF (V := phi43SectorV) (W := phi43SectorW) (α := phi43Alpha κ) (γ₀ := gamma κ)
    (η₀ := η) (η' := 2 * η) (η'' := 3 * η) (ζ := phi43Zeta κ)
    (phi43SectorV_isSector κ) (phi43SectorW_isSector κ) (phi43SectorV_ofRegularity κ)
    (phi43SectorW_ofRegularity κ) (phi43ProductF_mul_mem κ) (phi43ProductF_isRegularPair_VV κ)
    (phi43ProductF_isRegularPair_VW κ)
    (by simp only [phi43Alpha]; linarith) (by linarith)
    (by simp only [gamma, phi43Alpha]; linarith) (by simp only [phi43Alpha]; linarith)
    (by simp only [phi43Alpha]; linarith) (by linarith)
    (by simp only [gamma, phi43Alpha]; linarith)
    (by simp only [gamma, phi43Alpha]; linarith)
    (fun i hi => phi43DegreeF_xiFree_ge κ hi)
    (by simp only [gamma, phi43Alpha, phi43Zeta]; linarith)
    (lt_min_iff.2 ⟨by simp only [phi43Zeta]; linarith, by linarith⟩)
    (by simp only [gamma, phi43Alpha]; linarith)
    (fun j _ => phi43DegreeF_gt_neg_four κ j) hN (phi43DegreeTwo_hNgamma κ)
    (fun k _ l => phi43_hnat κ k l) (fun k _ i hi _ _ => phi43_hni κ k i hi)
    (phi43XiFreeF_isSector κ) (phi43XiFreeF_isBlockInvariant κ)
  refine ⟨C₀, hC₀, ?_⟩
  intro M CPi CGam CΓ CGam₁ CΓ₁ R₀ T hPi hGam hCG hgr hCPi hreal hΓ₀ hΓ₁ hΓK hCΓr hCΓ hT1 𝒦 h𝒦 U
    hU x hx
  have hdeg : (phi43RegularityStructureF κ).deg (SymbolF.old .one) < gamma κ := by
    change homogeneity κ .one < gamma κ
    simp only [homogeneity, gamma]
    linarith
  have hb := hspec M phi43IntegrationF (CI := 1) hPi hGam hCG hgr hCPi hreal
    (phi43IntegrationF_isAbstractIntegration κ)
    (fun a _ kk => phi43IntegrationF_polyEmb_eq_zero κ a kk)
    (fun i j => phi43IntegrationF_single_abs_le i j) zero_le_one hΓ₀ hΓ₁ hΓK hCΓr hCΓ hT1 𝒦 h𝒦 U hU
    x hx (SymbolF.old .one) hdeg
  have hmin : min (phi43Zeta κ) (3 * η) = 3 * η := by
    refine min_eq_right ?_
    simp only [phi43Zeta]
    linarith
  have hd : (phi43RegularityStructureF κ).deg (SymbolF.old .one) = 0 := rfl
  rw [hmin, hd, sub_zero, singularWeight_timeZeroDist_rpow_of_mem_timeSlab hT1 hx] at hb
  refine hb.trans (le_of_eq ?_)
  ring

end RegularityStructures.Phi43.TimeSlice

end
