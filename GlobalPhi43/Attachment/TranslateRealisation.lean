module

public import Phi43.BPHZ.TreeFormulas
public import Phi43.Structure.CanonicalKernelHairer
public import RegularityStructures.Abstract.Translate.Model
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Generic smooth-noise translation of the negative realisations.
This does not specialise the noise to a random regularisation or assume a growth event. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment

open MeasureTheory RegularityStructures RegularityStructures.Phi43

/-- Translation of a smooth spatially periodic noise. -/
def translateNoise (noise : CanonicalNoise) (a : ParabolicSpace) : CanonicalNoise where
  zeta z := noise.zeta (z + a)
  smooth := noise.smooth.comp (contDiff_id.add contDiff_const)
  periodic n z := by
    change noise.zeta (z.1 + a.1, (fun i => z.2 i + (n i : ℝ)) + a.2) =
      noise.zeta (z.1 + a.1, z.2 + a.2)
    have he : (z.1 + a.1, (fun i => z.2 i + (n i : ℝ)) + a.2) =
        ((z + a).1, fun i => (z + a).2 i + (n i : ℝ)) := by
      apply Prod.ext
      · simp only [Prod.fst_add]
      · funext i
        simp only [Pi.add_apply, Prod.snd_add]
        ring
    rw [he]
    exact noise.periodic n (z + a)

/-- Convolution by the truncated kernel commutes with every translation. -/
theorem hairerConvolution_translate (N : ℕ) (f : ParabolicSpace → ℝ)
    (a z : ParabolicSpace) :
    hairerConvolution N (fun w => f (w + a)) z = hairerConvolution N f (z + a) := by
  unfold hairerConvolution
  rw [← integral_add_right_eq_self (fun w => hairerKernel N (z + a - w) * f w) a]
  congr 1
  funext w
  rw [show z + a - (w + a) = z - w by abel]

/-- The translated lift has the translated stochastic convolution. -/
theorem localPsi_translate (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (a z : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (translateNoise noise a)).localPsi z =
      (hairerCanonicalData (κ := κ) N noise).localPsi (z + a) := by
  rw [CanonicalData.localPsi_eq_globalPsi, CanonicalData.localPsi_eq_globalPsi]
  exact hairerConvolution_translate N noise.zeta a z

/-- Constant-order Taylor subtraction commutes with translation. -/
theorem integrate_translate_const (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (a : ParabolicSpace) {r : ℝ} (hr : 0 < r) (hr1 : ¬ 1 < r)
    (f : ParabolicSpace → ℝ) (x y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (translateNoise noise a)).integrate r
        (fun w => f (w + a)) x y =
      (hairerCanonicalData (κ := κ) N noise).integrate r f (x + a) (y + a) := by
  rw [CanonicalData.integrate_eq_of_pos_of_not_gt_one _ hr hr1,
    CanonicalData.integrate_eq_of_pos_of_not_gt_one _ hr hr1]
  exact congrArg₂ (· - ·) (hairerConvolution_translate N f a y)
    (hairerConvolution_translate N f a x)

/-- The generic negative-realisation identity needed by predicate covariance. -/
theorem renormalisedPi_fMinus_translate (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (a x y : ParabolicSpace) (τ : Symbol) (hτ : τ ∈ fMinus) :
    (hairerCanonicalData (κ := κ) N (translateNoise noise a)).renormalisedPi C x (basis τ) y =
      (hairerCanonicalData (κ := κ) N noise).renormalisedPi C (x + a) (basis τ) (y + a) := by
  let D := hairerCanonicalData (κ := κ) N noise
  let Da := hairerCanonicalData (κ := κ) N (translateNoise noise a)
  have hp : Da.localPsi = fun z => D.localPsi (z + a) :=
    funext (localPsi_translate N κ noise a)
  have hs : Da.localPsiSq = fun z => D.localPsiSq (z + a) := by
    funext z; simp only [CanonicalData.localPsiSq, hp]
  have hc : Da.localPsiCube = fun z => D.localPsiCube (z + a) := by
    funext z; simp only [CanonicalData.localPsiCube, hs, hp]
  have hI (r : ℝ) (hr : 0 < r) (hr1 : ¬ 1 < r) (f : ParabolicSpace → ℝ) :
      Da.integrate r (fun w => f (w + a)) x y = D.integrate r f (x + a) (y + a) :=
    integrate_translate_const N κ noise a hr hr1 f x y
  have hκ0 := κ.2.1
  have hκ1 := κ.2.2
  have hsq : 0 < homogeneity κ .iPsiSq := by simp only [homogeneity]; linarith
  have hsq1 : ¬ 1 < homogeneity κ .iPsiSq := by simp only [homogeneity]; linarith
  have hcu : 0 < homogeneity κ .iPsiCube := by simp only [homogeneity]; linarith
  have hcu1 : ¬ 1 < homogeneity κ .iPsiCube := by simp only [homogeneity]; linarith
  change Da.renormalisedPi C x (basis τ) y = D.renormalisedPi C (x + a) (basis τ) (y + a)
  have hrel (i : Fin 4) : CanonicalData.relCoord (x + a) (y + a) i =
      CanonicalData.relCoord x y i := by
    simp only [CanonicalData.relCoord, parabolicCoords_add, Pi.add_apply]; ring
  cases τ <;> simp only [mem_fMinus_iff_isFMinus, isFMinus] at hτ
  all_goals first
    | contradiction
    | simp only [CanonicalData.renormalisedPi_basis_noise_eq,
        CanonicalData.renormalisedPi_basis_psi_eq,
        CanonicalData.renormalisedPi_basis_psiSq_eq,
        CanonicalData.renormalisedPi_basis_psiCube_eq,
        CanonicalData.renormalisedPi_basis_psiSqX_eq,
        CanonicalData.renormalisedPi_basis_iPsiCubePsi_eq,
        CanonicalData.renormalisedPi_basis_iPsiSqPsiSq_eq,
        CanonicalData.renormalisedPi_basis_iPsiCubePsiSq_eq, hp, hs, hc,
        hI (homogeneity κ .iPsiSq) hsq hsq1, hI (homogeneity κ .iPsiCube) hcu hcu1, hrel]
  rfl

end GlobalPhi43.Attachment
