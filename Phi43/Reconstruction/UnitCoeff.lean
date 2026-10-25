/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.SlabExpansion
public import Phi43.Reconstruction.FunctionModel
public import Phi43.Inhomogeneity.Inhom
public import RegularityStructures.Abstract.Singular.IdentNear.Combine

/-!
# The unit coefficient of the solution is the heat potential of the cube

The abstract part of the derivation of the mild equation.  For `U = -𝒦 (U³) + v` as in
`phi43FixedPointF_window_nearOne`, the unit coordinate of `U(x)`, `x` in the slab, is
`U(x)_1 = v(x)_1 - ∫ H(x - y) 𝟙_{slab}(y) (w³ - c w)(y) dy`, `H = heatKernelR4`,
`w(y) = (K ∗ ζ)(y + a) + U(y)_1`, `c = 3C₁ - 9C₂` (`phi43_unit_coeff`); the coefficient of the
unit of `𝒦_γ f + R_γ f` is `∫ H(x - y) R̃f(y) dy` (`kGammaRemG_apply_emb_zero_eq_integral_wnear`),
and `R̃(U³) = w³ - c w` on the slab by `pointwiseReconstruct_cube_ansatz`.
-/

public section

namespace RegularityStructures.Phi43

/-- The multi-index `0`, i.e. the unit `X^0` of the polynomial sector. -/
@[expose] def phi43OneIdx : PolyIndex 3 := ⟨0, by simp⟩

theorem emb_phi43OneIdx (κ : Kappa) : (phi43PolynomialSectorF κ).emb phi43OneIdx = .old .one := by
  change SymbolF.old (phi43QuadraticPolyEmb phi43OneIdx) = _
  norm_num [phi43QuadraticPolyEmb, phi43QuadraticSymbolOfIndex, phi43OneIdx]

private theorem gamma_alpha_alpha' (κ : Kappa) :
    gamma κ + phi43Alpha κ + phi43Alpha κ = κ.1 := by
  simp only [gamma, phi43Alpha]; ring

variable {κ : Kappa} {N : ℕ} {M : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {CPi CGam CΓ CGam₁ CΓ₁ T : ℝ} {η : ℝ}

theorem phi43IntegrationF_apply_one (κ : Kappa) (a : SymbolF → ℝ) :
    phi43IntegrationF a (.old .one) = 0 := by
  have := phi43IntegrationF_polyEmb_eq_zero κ a phi43OneIdx
  rwa [emb_phi43OneIdx] at this

open MeasureTheory in
/-- **Unit coefficient of the solution**. -/
theorem phi43_unit_coeff
    (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T) (hN : 3 ≤ N)
    (hη₁ : -2 / 3 < η) (hκη : κ.1 < -1 / 2 - η)
    (noise : CanonicalNoise) (C : RenormalisationConstants) (a : ParabolicSpace)
    (gF : ParabolicSpace → SymbolF → ParabolicSpace → ℝ)
    (hgF : M.IsSmoothFunctionModelBelow gF (gamma κ + phi43Alpha κ + phi43Alpha κ))
    (hdiag : ∀ y τ, gF y (.old τ) y = phi43BaseFunctions N κ noise C (y + a) τ (y + a))
    (U v : M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T))
    (𝒦 : M.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η)
        (timeSlab T) →ₗ[ℝ] M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T))
    (h𝒦 : ∀ g : M.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η)
        (timeSlab T), ∀ x ∈ timeSlab T, (𝒦 g).val x =
      RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg (gamma κ)
        (M.kGammaRemG (annKernel0C N) (annRemainderC N) (phi43PolynomialSectorF κ) phi43IntegrationF
          (gamma κ + phi43Alpha κ + phi43Alpha κ)
          (Model.SlabSpace.blockProj phi43XiFreeF (phi43_hAG κ M) g).val x))
    (hfix : U = -𝒦 (Model.SlabSpace.cube (phi43ProductF κ)
      (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η) U) + v)
    (hv : ∀ y ∈ timeSlab T, v.val y - phi43EF .psi ∈ (phi43PolynomialSectorF κ).subspace)
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    U.val x (.old .one) = v.val x (.old .one) -
      ∫ y, heatKernelR4 (x - y) * (timeSlab T).indicator (fun y =>
        (phi43PsiAt N κ noise C (y + a) + U.val y (.old .one)) ^ 3 -
          (3 * C₁ C - 9 * C₂ C) * (phi43PsiAt N κ noise C (y + a) + U.val y (.old .one))) y := by
  set cU := Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η) U
    with hcU
  set f := (Model.SlabSpace.blockProj phi43XiFreeF (phi43_hAG κ M) cU).val with hf
  have S := hyp.layerSetting hη₁ cU
  -- the cube block on the slab
  have hfy : ∀ y ∈ timeSlab T, f y = -phi43OldEmbF (phi43FDisplayOld (U.val y (.old .one))
      (fun i => U.val y (.old (.x i)))) := by
    intro y hy
    have he := phi43_slab_expansion hyp hκη U v 𝒦 h𝒦 hfix hv hy
    rw [hf, phi43_blockProj_cube_val hyp hκη U y]
    change RegularityStructures.blockProj phi43XiFreeF
      (RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg
        (gamma κ + phi43Alpha κ + phi43Alpha κ)
        ((phi43ProductF κ).mul (U.val y) ((phi43ProductF κ).mul (U.val y) (U.val y)))) = _
    rw [gamma_alpha_alpha' κ]
    have h := blockProj_lowerProj_cube_ansatz κ (U.val y (.old .one))
      (fun i => U.val y (.old (.x i)))
    rw [← he] at h
    exact h
  have hRec : ∀ y, RegularityStructures.pointwiseReconstruct gF f y =
      (timeSlab T).indicator (fun y =>
        (phi43PsiAt N κ noise C (y + a) + U.val y (.old .one)) ^ 3 -
          (3 * C₁ C - 9 * C₂ C) * (phi43PsiAt N κ noise C (y + a) + U.val y (.old .one))) y := by
    intro y
    by_cases hy : y ∈ timeSlab T
    · rw [Set.indicator_of_mem hy]
      exact pointwiseReconstruct_cube_ansatz N κ noise C a gF hdiag f y _ _ (hfy y hy)
    · rw [Set.indicator_of_notMem hy]
      exact Model.pointwiseReconstruct_eq_zero_of_not_mem_wnear S hy
  have hI0 : phi43IntegrationF (f x) ((phi43PolynomialSectorF κ).emb phi43OneIdx) = 0 := by
    rw [emb_phi43OneIdx]; exact phi43IntegrationF_apply_one κ _
  have key := Model.kGammaRemG_apply_emb_zero_eq_integral_wnear (kernelPair_ann N)
    (show 3 ≤ N from hN) hyp.real.poly phi43IntegrationF hgF S hx phi43OneIdx rfl hI0
    (H := heatKernelR4) (fun _ hz => heatKernelR4_eq_tsum_annShellC hz)
  rw [emb_phi43OneIdx] at key
  have hU := phi43_slab_equation U v 𝒦 h𝒦 hfix hx
  have h1 := congrFun hU (.old .one)
  rw [Pi.add_apply, Pi.neg_apply, RegularityStructures.lowerProj_apply_of_lt] at h1
  · rw [h1]
    change -(M.kGammaRemG (annKernel0C N) (annRemainderC N) (phi43PolynomialSectorF κ)
      phi43IntegrationF (gamma κ + phi43Alpha κ + phi43Alpha κ) f x (.old .one)) + _ = _
    have hint : (∫ y, heatKernelR4 (x - y) * pointwiseReconstruct gF f y) =
        ∫ y, heatKernelR4 (x - y) * (timeSlab T).indicator (fun y =>
          (phi43PsiAt N κ noise C (y + a) + U.val y (.old .one)) ^ 3 -
            (3 * C₁ C - 9 * C₂ C) * (phi43PsiAt N κ noise C (y + a) + U.val y (.old .one))) y := by
      congr 1
      funext y
      rw [hRec y]
    have key' : M.kGammaRemG (annKernel0C N) (annRemainderC N) (phi43PolynomialSectorF κ)
        phi43IntegrationF (gamma κ + phi43Alpha κ + phi43Alpha κ) f x (.old .one) = _ :=
      key.trans hint
    rw [key']
    ring
  · have hk : 0 < κ.1 := κ.2.1
    change (0 : ℝ) < gamma κ
    simp only [gamma]
    linarith

end RegularityStructures.Phi43

end
