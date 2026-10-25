/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.InhomUnit
public import Phi43.Reconstruction.MildGlue
public import Phi43.Potential.ZetaBound
public import Phi43.Restart.Package

/-!
# The reconstruction of the fixed point is the classical solution

The identification of the reconstructed solution with the classical one, from the expansion of the
abstract solution to the mild equation, assembled
(`phi43_reconstruction_eq_classical_of_potential`, with the potential identity and the continuity of
the path as hypotheses).
-/

public section

open Set MeasureTheory RegularityStructures.PDE

namespace RegularityStructures.Phi43

open Inhomogeneity

theorem datumField_toHolderBesov_apply (η : NegExponent) (w : C(Torus3, ℝ)) {t : ℝ} (ht : 0 < t)
    (x : Fin 3 → ℝ) : Datum.datumField η (toHolderBesov η w) (t, x) = heatOp t w (torusProj x) := by
  simp only [Datum.datumField, ht, ↓reduceIte]
  rw [Datum.heatExt_toHolderBesov η w ht]

theorem restartPoint_add (t s : ℝ) (x : Fin 3 → ℝ) :
    ((t, x) : ParabolicSpace) + LiftBounds.restartPoint s = (t + s, x) := by
  ext <;> simp [LiftBounds.restartPoint]


/-- **The reconstruction of the fixed point is the classical solution.**

Let `U` be a solution of the fixed point equation `U = -𝒦 (U³) + v` of
`phi43FixedPointF_window_nearOne` on the slab `(0, T]` for the enlarged model `M` compatible with
the translate by `(s, 0)` of the renormalised canonical model of the noise `ζ = f`, with the
inhomogeneity `v = Ψ·1 + datum(w_s) + jet(θ_s)`.  Suppose that `w = ⟨1, U⟩ + K ∗ ζ(· + (s, 0))`
extends to a continuous path `W : ℝ → C(T³)` with `W 0 = u(s)`, and that the potential identity
holds.  Then `w(t, ·) = u(s + t)` for `0 < t ≤ T`. -/
theorem phi43_reconstruction_eq_classical_of_potential
    {κ : Kappa} {N : ℕ} (hN : 3 ≤ N) (η : NegExponent) (hη₁ : -2 / 3 < (η : ℝ))
    (hκη : κ.1 < -1 / 2 - (η : ℝ))
    {M : Model (phi43RegularityStructureF κ) parabolicSemigroup}
    {CPi CGam CΓ CGam₁ CΓ₁ T : ℝ} (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) {s : ℝ} (hs : 0 < s)
    (hC : Restart.EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate
      (LiftBounds.restartPoint s)) M)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    {u₀ : C(Torus3, ℝ)} {u : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution (3 * C₁ C - 9 * C₂ C) f u₀ u)
    (ws : C(Torus3, ℝ)) {B : ℝ} (hB : 0 ≤ B) {Gc : ℕ → ℝ} (hGc : ∀ L, 0 ≤ Gc L)
    (hGζ : ∀ L, DerivHyp (Potential.potZeta noise.zeta N s) (Gc L * B) L)
    (U : M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T))
    (𝒦 : M.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * (η : ℝ))
        (timeSlab T) →ₗ[ℝ] M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T))
    (h𝒦 : ∀ g : M.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * (η : ℝ))
        (timeSlab T), ∀ x ∈ timeSlab T, (𝒦 g).val x =
      RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg (gamma κ)
        (M.kGammaRemG (annKernel0C N) (annRemainderC N) (phi43PolynomialSectorF κ) phi43IntegrationF
          (gamma κ + phi43Alpha κ + phi43Alpha κ)
          (Model.SlabSpace.blockProj phi43XiFreeF (phi43_hAG κ M) g).val x))
    (hfix : U = -𝒦 (Model.SlabSpace.cube (phi43ProductF κ)
      (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * (η : ℝ)) U) +
        phi43InhomTheta κ η M hyp.real.poly hyp.hT1 (toHolderBesov η ws)
          (Potential.perSmooth_zeta_restart noise N s) hB hGc hGζ)
    (W : ℝ → C(Torus3, ℝ)) (hWc : Continuous W) (hW0 : W 0 = u s)
    (hWdef : ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ, W t (torusProj x) = U.val (t, x) (.old .one) +
      phi43PsiAt N κ noise C ((t, x) + LiftBounds.restartPoint s))
    (hpot : ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ,
      phi43PsiAt N κ noise C ((t, x) + LiftBounds.restartPoint s) +
        duhamelField (Potential.perSmooth_zeta_restart noise N s) (t, x) =
      heatOp t (u s - ws) (torusProj x) + duhamel (fun r => nemytskii (cubicHeatNonlinearity
        (3 * C₁ C - 9 * C₂ C) (isSmoothOnSpaceTime_shiftForcing hf s)) r 0) t (torusProj x)) :
    ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ, U.val (t, x) (.old .one) +
      phi43PsiAt N κ noise C ((t, x) + LiftBounds.restartPoint s) = u (s + t) (torusProj x) := by
  set a := LiftBounds.restartPoint s with ha
  set c := 3 * C₁ C - 9 * C₂ C with hc
  set v := phi43InhomTheta κ η M hyp.real.poly hyp.hT1 (toHolderBesov η ws)
    (Potential.perSmooth_zeta_restart noise N s) hB hGc hGζ with hv
  have hgF : M.IsSmoothFunctionModelBelow (phi43EnlargedBase N κ noise C a)
      (gamma κ + phi43Alpha κ + phi43Alpha κ) := by
    rw [Restart.gamma_add_alpha_add_alpha]
    exact isSmoothFunctionModelBelow_phi43EnlargedBase N κ noise Cg q hg C a hC
  have hvm : ∀ y ∈ timeSlab T, v.val y - phi43EF .psi ∈ (phi43PolynomialSectorF κ).subspace :=
    fun y hy => phi43InhomTheta_sub_psi_mem κ η M hyp.real.poly hyp.hT1 _ _ hB hGc hGζ hy
  have hunit : ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ, U.val (t, x) (.old .one) =
      (heatOp t ws (torusProj x) + duhamelField (Potential.perSmooth_zeta_restart noise N s) (t, x)) -
        ∫ y, heatKernelR4 (((t, x) : ParabolicSpace) - y) * (timeSlab T).indicator (fun y =>
          (phi43PsiAt N κ noise C (y + a) + U.val y (.old .one)) ^ 3 -
            (3 * C₁ C - 9 * C₂ C) * (phi43PsiAt N κ noise C (y + a) + U.val y (.old .one))) y := by
    intro t ht x
    have hx : ((t, x) : ParabolicSpace) ∈ timeSlab T := ⟨ht.1, ht.2⟩
    have h1 := phi43_unit_coeff hyp hN hη₁ hκη noise C a (phi43EnlargedBase N κ noise C a) hgF
      (fun y τ => rfl) U v 𝒦 h𝒦 hfix hvm hx
    rw [h1, hv, phi43InhomTheta_unit κ η M hyp.real.poly hyp.hT1 _ _ hB hGc hGζ hx,
      datumField_toHolderBesov_apply η ws ht.1 x]
  have hrep : ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ, W t (torusProj x) =
      heatOp t ws (torusProj x) + duhamelField (Potential.perSmooth_zeta_restart noise N s) (t, x) +
        phi43PsiAt N κ noise C ((t, x) + a) -
        ∫ z : ParabolicSpace, heatKernelR4 (((t, x) : ParabolicSpace) - z) *
          (timeSlab T).indicator (fun y => W y.1 (torusProj y.2) ^ 3 -
            c * W y.1 (torusProj y.2)) z := by
    intro t ht x
    rw [hWdef t ht x, hunit t ht x]
    have : (timeSlab T).indicator (fun y => (phi43PsiAt N κ noise C (y + a) + U.val y (.old .one)) ^ 3 -
            c * (phi43PsiAt N κ noise C (y + a) + U.val y (.old .one))) =
        (timeSlab T).indicator (fun y => W y.1 (torusProj y.2) ^ 3 - c * W y.1 (torusProj y.2)) := by
      funext y
      by_cases hy : y ∈ timeSlab T
      · rw [indicator_of_mem hy, indicator_of_mem hy, hWdef y.1 ⟨hy.1, hy.2⟩ y.2]
        rw [add_comm (U.val y (.old .one))]
      · rw [indicator_of_notMem hy, indicator_of_notMem hy]
    rw [this]
    ring
  have hmild := mild_of_pointwise (c := c) hf s (T := T) W hWc (u s) ws
    (fun z => duhamelField (Potential.perSmooth_zeta_restart noise N s) z)
    (fun z => phi43PsiAt N κ noise C (z + a)) hrep hpot
  have hcl := mild_path_eq_classical (c := c) hf hu hs hyp.hT0.le W hWc hW0 hmild
  intro t ht x
  have := hcl t ⟨ht.1.le, ht.2⟩
  rw [← hWdef t ht x, this]

end RegularityStructures.Phi43

end
