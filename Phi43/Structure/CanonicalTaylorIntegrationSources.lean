/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalTaylorConvolutionLow
public import Phi43.Structure.CanonicalTaylorConvolutionSpatial

/-!
# Causal Taylor shell identities on every retained integration source

Hairer [Hai14, Definition 5.9, Proposition 8.27, (8.18)–(8.20)].
These ordinary integral identities use only smoothness and spatial
periodicity of the noise, without whole-space growth assumptions.
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

local instance : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

local instance : (volume : Measure ParabolicSpace).IsNegInvariant := by
  rw [Measure.volume_eq_prod]
  have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
  have : (volume.prod volume : Measure ParabolicSpace).Regular := inferInstance
  infer_instance

private theorem noise_taylorIdx_empty (κ : Kappa) :
    taylorIdx (homogeneity κ .noise + 2) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro k hk
  rw [mem_taylorIdx_iff] at hk
  have hn : (0 : ℝ) ≤ multiDeg k := Nat.cast_nonneg _
  have hκ := κ.property.1
  simp only [homogeneity] at hk
  linarith

/-- The noise requires no Taylor subtraction after integration. -/
theorem canonicalPi_integration_shell_sum_noise (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (x y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis .psi) y =
      ∑' n : ℕ, ∫ w,
        (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis .noise) w *
          taylorKernel (annKernel0C N) n (homogeneity κ .noise + 2) x y w := by
  have hker (n : ℕ) :
      taylorKernel (annKernel0C N) n (homogeneity κ .noise + 2) x y =
        fun w => annShellC N n (y - w) := by
    funext w
    simp only [taylorKernel, noise_taylorIdx_empty, Finset.sum_empty, sub_zero, annShellC]
  have ht (n : ℕ) :
      (∫ w, (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis .noise) w *
        taylorKernel (annKernel0C N) n (homogeneity κ .noise + 2) x y w) =
        ∫ w, annShellC N n w * noise.zeta (y - w) := by
    rw [hker]
    simp_rw [CanonicalData.canonicalPi_noise]
    simpa only [hairerCanonicalData, sub_sub_cancel, mul_comm] using
      (integral_sub_left_eq_self
        (fun w => annShellC N n w * noise.zeta (y - w)) volume y)
  simp_rw [ht]
  rw [CanonicalData.canonicalPi_basis]
  change (hairerCanonicalData (κ := κ) N noise).localPsi y = _
  rw [CanonicalData.localPsi_eq_globalPsi]
  exact hairerConvolution_eq_tsum_shellConvolution N noise.smooth.continuous y

end RegularityStructures.Phi43

end
