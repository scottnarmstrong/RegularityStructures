/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSpatialTranslationKernel
public import Phi43.Structure.AbstractPolynomial

/-!
# Spatial translation symmetry of the actual canonical Pi

Hairer [Hai14, Section 8.2, Proposition 8.27]: periodicity of the canonical
model on the retained finite sector. Smoothness
and periodicity of the noise are the only source hypotheses.
-/

public noncomputable section

namespace RegularityStructures.Phi43

private theorem relCoord_translate (a x y : ParabolicSpace) (i : Fin 4) :
    CanonicalData.relCoord (x + a) (y + a) i = CanonicalData.relCoord x y i := by
  simp only [CanonicalData.relCoord, parabolicCoords_add, Pi.add_apply]
  ring

open scoped ContDiff in
private theorem integrate_translate (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (r : ℝ) {f : ParabolicSpace → ℝ} (hfs : ContDiff ℝ ∞ f)
    (a : ParabolicSpace) (hf : ∀ z, f (z + a) = f z) (x y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).integrate r f (x + a) (y + a) =
      (hairerCanonicalData (κ := κ) N noise).integrate r f x y := by
  have hk := hairerConvolution_translate_of_periodic N f a hf
  have hg := hairerSpatialGradient_translate_of_periodic N hfs a hf
  have hc (i : Fin 4) : parabolicCoords (y + a) i - parabolicCoords (x + a) i =
      parabolicCoords y i - parabolicCoords x i := by
    simp only [parabolicCoords_add, Pi.add_apply]
    ring
  change hairerConvolution N f (y + a) -
      ((if 0 < r then hairerConvolution N f (x + a) else 0) +
        (if 1 < r then ∑ i : Fin 3, hairerSpatialGradient N f i (x + a) *
          (parabolicCoords (y + a) i.succ - parabolicCoords (x + a) i.succ) else 0)) =
    hairerConvolution N f y -
      ((if 0 < r then hairerConvolution N f x else 0) +
        (if 1 < r then ∑ i : Fin 3, hairerSpatialGradient N f i x *
          (parabolicCoords y i.succ - parabolicCoords x i.succ) else 0))
  simp only [hk, hg, hc]

open scoped ContDiff in
/-- The actual based canonical lift is invariant under simultaneous integer
spatial translation of base and evaluation points. -/
theorem canonicalPi_spatial_translation (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (n : Fin 3 → ℤ) (x y : ParabolicSpace) (τ : Symbol) :
    (hairerCanonicalData (κ := κ) N noise).canonicalPi
        (x.1, fun i => x.2 i + (n i : ℝ)) (basis τ)
        (y.1, fun i => y.2 i + (n i : ℝ)) =
      (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis τ) y := by
  let D := hairerCanonicalData (κ := κ) N noise
  let a : ParabolicSpace := (0, fun i => (n i : ℝ))
  have ha (z : ParabolicSpace) : (z.1, fun i => z.2 i + (n i : ℝ)) = z + a := by
    apply Prod.ext
    · change z.1 = z.1 + 0
      rw [add_zero]
    · rfl
  have hn (z : ParabolicSpace) : noise.zeta (z + a) = noise.zeta z := by
    rw [← ha z]
    exact noise.periodic n z
  have hp (z : ParabolicSpace) : D.localPsi (z + a) = D.localPsi z := by
    rw [CanonicalData.localPsi_eq_globalPsi]
    exact hairerConvolution_translate_of_periodic N noise.zeta a hn z
  have hs (z : ParabolicSpace) : D.localPsiSq (z + a) = D.localPsiSq z := by
    simp only [CanonicalData.localPsiSq, hp]
  have hc (z : ParabolicSpace) : D.localPsiCube (z + a) = D.localPsiCube z := by
    simp only [CanonicalData.localPsiCube, hs, hp]
  have hps : ContDiff ℝ ∞ D.localPsi := by
    rw [CanonicalData.localPsi_eq_globalPsi]
    exact canonicalGlobalPiBasis_smooth N noise .psi
  have hi (u v : ParabolicSpace) : D.localIPsi (u + a) (v + a) = D.localIPsi u v :=
    integrate_translate N κ noise _ hps a hp u v
  have his (u v : ParabolicSpace) : D.localIPsiSq (u + a) (v + a) = D.localIPsiSq u v :=
    integrate_translate N κ noise _ (hps.mul hps) a hs u v
  have hic (u v : ParabolicSpace) : D.localIPsiCube (u + a) (v + a) = D.localIPsiCube u v :=
    integrate_translate N κ noise _ ((hps.mul hps).mul hps) a hc u v
  rw [ha x, ha y, CanonicalData.canonicalPi_basis, CanonicalData.canonicalPi_basis]
  change D.localPiBasis (x + a) τ (y + a) = D.localPiBasis x τ y
  cases τ with
  | noise => exact hn y
  | xMul p =>
      refine Sym2.inductionOn p ?_
      intro i j
      simp only [CanonicalData.localPiBasis, CanonicalData.localPolynomialQuadratic,
        Sym2.lift_mk, relCoord_translate]
  | _ =>
    simp only [CanonicalData.localPiBasis, CanonicalData.localPsiX,
      CanonicalData.localPsiSqX, CanonicalData.localIPsiPsi,
      CanonicalData.localIPsiPsiSq, CanonicalData.localIPsiSqPsi,
      CanonicalData.localIPsiSqPsiSq, CanonicalData.localIPsiCubePsi,
      CanonicalData.localIPsiCubePsiSq, CanonicalData.localIPsiCubeSq,
      hp, hs, hc, hi, his, hic, relCoord_translate]

end RegularityStructures.Phi43

end
