/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.WindowedIntegral

/-!
# Physical form of a window Fourier coefficient

This module transports a Fourier coefficient on the unit window torus to the corresponding
physical space-time integral.  The transport is the finite-window change of variables proved in
`Phi43.RegularisedNoise.SmoothVersion.WindowedIntegral`; the character identity is the one used
in the Fourier construction of a smooth regularised noise (Definition 2.4 of the statement).

The integrability hypothesis is deliberately stated on the physical pullback.  This keeps the
transport theorem independent of the later compact-support estimates for the translated kernel.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

namespace RegularityStructures.Phi43

def windowWeightedIntegrand (g : SpaceTime → ℂ) (a b : ℝ) (k : WindowFrequency)
    (z : SpaceTime) : ℂ :=
  g z * conj (windowFourierModeShift a b k z)

theorem integrable_windowWeightedIntegrand {a b : ℝ} (_hab : a < b)
    {g : SpaceTime → ℂ} (hg : Integrable g (volume : Measure SpaceTime))
    (k : WindowFrequency) :
    Integrable (windowWeightedIntegrand g a b k) (volume : Measure SpaceTime) := by
  apply hg.mul_bdd (c := 1)
  · exact (Complex.continuous_conj.measurable.comp
      (measurable_windowFourierModeShift a b k)).aestronglyMeasurable
  · filter_upwards [] with z
    simp [norm_windowFourierModeShift]

theorem mFourierCoeff_windowPoint_eq_windowIntegral
    {a b : ℝ} (hab : a < b) {g : SpaceTime → ℂ}
    (hg : Integrable g (volume : Measure SpaceTime))
    (k : WindowFrequency)
    (hgp : Integrable
      (fun x : ℝ × (Fin 3 → ℝ) =>
        windowWeightedIntegrand g a b k
          (a + (b - a) * x.1, torusProj x.2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (Measure.pi (fun _ : Fin 3 => volume.restrict (Ioc (0 : ℝ) 1))))) :
    UnitAddTorus.mFourierCoeff (fun y : UnitAddTorus (Fin 4) =>
      g (windowPoint a b y)) k =
      (b - a)⁻¹ • ∫ z in windowInterval a b,
        windowWeightedIntegrand g a b k z := by
  let f : SpaceTime → ℂ := windowWeightedIntegrand g a b k
  have hf : Integrable f (volume : Measure SpaceTime) := by
    exact integrable_windowWeightedIntegrand hab hg k
  have hfp : Integrable
      (fun x : ℝ × (Fin 3 → ℝ) => f
        (a + (b - a) * x.1, torusProj x.2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (Measure.pi (fun _ : Fin 3 => volume.restrict (Ioc (0 : ℝ) 1)))) := by
    simpa [f] using hgp
  calc
    UnitAddTorus.mFourierCoeff (fun y : UnitAddTorus (Fin 4) =>
        g (windowPoint a b y)) k =
        ∫ y : UnitAddTorus (Fin 4), f (windowPoint a b y) := by
          unfold UnitAddTorus.mFourierCoeff
          have hfun :
              (fun y : UnitAddTorus (Fin 4) =>
                UnitAddTorus.mFourier (-k) y • g (windowPoint a b y)) =
              (fun y : UnitAddTorus (Fin 4) => f (windowPoint a b y)) := by
            funext y
            simp only [f, windowWeightedIntegrand]
            rw [windowFourierModeShift_windowPoint hab k y]
            rw [← UnitAddTorus.mFourier_neg]
            simp only [smul_eq_mul]
            ring
          convert (congrArg (fun q => ∫ y : UnitAddTorus (Fin 4), q y) hfun) using 1
          simp [volume, AddCircle.haarAddCircle]
    _ = (b - a)⁻¹ • ∫ z in windowInterval a b, f z :=
      integral_windowPoint hab f hf hfp
    _ = (b - a)⁻¹ • ∫ z in windowInterval a b,
        windowWeightedIntegrand g a b k z := by rfl

end RegularityStructures.Phi43

end
