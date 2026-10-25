/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.Setting
public import Phi43.Inhomogeneity.SlabConst
public import RegularityStructures.Abstract.Singular.TwoModel.IdentG

/-!
# The solution of the fixed point equation is the expansion, on the slab

For `U` with `U = -𝒦 (U³) + v` (`𝒦` as in `phi43FixedPointF_window_nearOne`), `v ≡ Ψ` modulo the
polynomials, every value `U(y)`, `y` in the time slab, is
`Ψ + φ·1 - I(Ψ³) - 3φ I(Ψ²) + φᵢ Xᵢ` with `φ = U(y)_1`, `φᵢ = U(y)_{Xᵢ}`
(`phi43_slab_expansion`), and the block projection of the cube is `-(F(U) - Ξ)`
(`phi43_slab_cube`).
-/

public section

namespace RegularityStructures.Phi43

variable {κ : Kappa} {N : ℕ} {M : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {CPi CGam CΓ CGam₁ CΓ₁ T : ℝ} {η : ℝ}

private theorem gamma_alpha_alpha (κ : Kappa) :
    gamma κ + phi43Alpha κ + phi43Alpha κ = κ.1 := by
  simp only [gamma, phi43Alpha]; ring

/-- The identity `U = -𝒦 (U³) + v` read off at a point of the slab. -/
theorem phi43_slab_equation
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
    {y : ParabolicSpace} (hy : y ∈ timeSlab T) :
    U.val y = -RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg (gamma κ)
      (M.kGammaRemG (annKernel0C N) (annRemainderC N) (phi43PolynomialSectorF κ) phi43IntegrationF
        (gamma κ + phi43Alpha κ + phi43Alpha κ)
        (Model.SlabSpace.blockProj phi43XiFreeF (phi43_hAG κ M)
          (Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ)
            (3 * η) U)).val y) + v.val y := by
  have := congrArg (fun W => W.val y) hfix
  simp only [Model.SlabSpace.val_add, Model.SlabSpace.val_neg, Pi.add_apply, Pi.neg_apply,
    h𝒦 _ y hy] at this
  exact this

theorem phi43_blockProj_cube_val
    (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T) (hκη : κ.1 < -1 / 2 - η)
    (U : M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T)) (y : ParabolicSpace) :
    (Model.SlabSpace.blockProj phi43XiFreeF (phi43_hAG κ M)
      (Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ)
        (3 * η) U)).val y =
      RegularityStructures.blockProj phi43XiFreeF
        ((phi43ProductF κ).truncCube (gamma κ + phi43Alpha κ + phi43Alpha κ) U.val y) := by
  rw [Model.SlabSpace.val_blockProj, hyp.val_cube hκη U]

/-- **B1 on the slab**: the expansion of the abstract solution. -/
theorem phi43_slab_expansion
    (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T) (hκη : κ.1 < -1 / 2 - η)
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
    {y : ParabolicSpace} (hy : y ∈ timeSlab T) :
    U.val y = phi43AnsatzF 1 (U.val y (.old .one)) (-1) (-3 * U.val y (.old .one))
      (fun i => U.val y (.old (.x i))) := by
  have hρ : 0 < timeZeroDist y := Inhomogeneity.timeZeroDist_pos_of_mem_timeSlab hy
  obtain ⟨hV, hT⟩ := Submodule.mem_inf.1 (U.mem_inf hy hρ)
  have hU := phi43_slab_equation U v 𝒦 h𝒦 hfix hy
  rw [gamma_alpha_alpha] at hU
  refine phi43_expansion_pointwise κ (U.val y) _ (v.val y) hV hT hU ?_ (hv y hy)
  have h := RegularityStructures.TwoModel.kGammaRemG_sub_mem_subspace (P := phi43PolynomialSectorF κ)
    (I := phi43IntegrationF) (γ := κ.1) M (annKernel0C N) (annRemainderC N)
    (Model.SlabSpace.blockProj phi43XiFreeF (phi43_hAG κ M)
      (Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ)
        (3 * η) U)).val y
  rw [phi43_blockProj_cube_val hyp hκη U y, gamma_alpha_alpha] at h
  exact h

end RegularityStructures.Phi43

end
