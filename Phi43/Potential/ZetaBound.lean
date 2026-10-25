/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.NoiseBridge
public import Phi43.Potential.Convolution
public import RegularityStructures.Abstract.Polynomial.Model.Growth
public import RegularityStructures.Abstract.Singular.WindowAt.Basic

/-!
# The forcing bound: the forcing `ζ = Q ∗ f` of the restarted inhomogeneity

For a renormalised canonical model `Z` of the periodic noise `noise` and a restart time `s`, the
forcing `ζ_s = (Q ∗ ζ)(· + (s, 0)) = potShift s (potConv noise.zeta (potQ N))` is smooth and
spatially periodic (`perSmooth_zeta_restart`) and has the derivative bounds
`DerivHyp ζ_s (Gc L * B) L` with `Gc = potGc N (phi43RegularityStructure κ) (gamma κ)` and
`B = max(1, C_Γ) C_Π` (`derivHyp_zeta_restart`), where `C_Π`, `C_Γ` are the window bounds of the
restarted model `Z.translate (s, 0)` (`restart_piBoundOn_window` gives `C_Π`).  This is the form
`hG` consumed by `phi43InhomTheta`.
-/

open scoped ContDiff

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Phi43.Potential

open RegularityStructures RegularityStructures.Potential RegularityStructures.Phi43.LiftBounds
  RegularityStructures.Inhomogeneity

/-- The restarted forcing `ζ_s = (ξ(· + (s, 0)) ⋆ Q)`, i.e. `(ξ ⋆ Q)(· + (s, 0))`
(`potZeta_eq`). -/
@[expose] noncomputable def potZeta (ξ : ParabolicSpace → ℝ) (N : ℕ) (s : ℝ) :
    ParabolicSpace → ℝ :=
  potConv (potShift s ξ) (potQ N)

theorem potZeta_eq (ξ : ParabolicSpace → ℝ) (N : ℕ) (s : ℝ) :
    potZeta ξ N s = potShift s (potConv ξ (potQ N)) := by
  funext z; rw [potZeta, potConv_potShift]; rfl

theorem hasQualitativeGrowthAt_translate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝒯 : RegularityStructure ι} {M : Model 𝒯 parabolicSemigroup} {γ : ℝ} {a z : ParabolicSpace}
    (h : M.HasQualitativeGrowthAt γ (z + a)) : (M.translate a).HasQualitativeGrowthAt γ z := by
  obtain ⟨C', β, q, h⟩ := h
  refine ⟨C', β, q, fun i hi t ht y => ?_⟩
  have := h i hi t ht (y + a)
  rwa [add_sub_add_right_eq_sub] at this

theorem abs_potShift_le {ξ : ParabolicSpace → ℝ} {B : ℝ} {n : ℕ}
    (hB : ∀ u, |ξ u| ≤ B * (1 + parabolicNorm u) ^ n) (s : ℝ) (u : ParabolicSpace) :
    |potShift s ξ u| ≤ (B * (1 + parabolicNorm (restartPoint s)) ^ n) * (1 + parabolicNorm u) ^ n := by
  have e : potShift s ξ u = ξ (u + restartPoint s) := by
    simp only [potShift, restartPoint]
    congr 1
    ext <;> simp
  rw [e]
  have h1 := one_add_parabolicNorm_le (u + restartPoint s) (restartPoint s)
  rw [add_sub_cancel_right] at h1
  have hB0 : 0 ≤ B := by
    have := (abs_nonneg _).trans (hB 0)
    rw [parabolicNorm_zero] at this
    simpa using this
  have h2 : (1 + parabolicNorm (u + restartPoint s)) ^ n ≤
      ((1 + parabolicNorm (restartPoint s)) * (1 + parabolicNorm u)) ^ n :=
    pow_le_pow_left₀ (by linarith [parabolicNorm_nonneg (u + restartPoint s)]) (by linarith) n
  calc |ξ (u + restartPoint s)| ≤ B * (1 + parabolicNorm (u + restartPoint s)) ^ n := hB _
    _ ≤ B * ((1 + parabolicNorm (restartPoint s)) * (1 + parabolicNorm u)) ^ n :=
        mul_le_mul_of_nonneg_left h2 hB0
    _ = _ := by rw [mul_pow]; ring

theorem perSmooth_potShift {ξ : ParabolicSpace → ℝ} (hξ : PerSmooth ξ) (s : ℝ) :
    PerSmooth (potShift s ξ) where
  smooth := hξ.smooth.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
  periodic z c hc := hξ.periodic (z.1 + s, z.2) c hc

theorem perSmooth_noise_zeta (noise : CanonicalNoise) : PerSmooth noise.zeta :=
  perSmooth_of_integer_periodic noise.smooth noise.periodic

/-- The restarted forcing is smooth and spatially periodic. -/
theorem perSmooth_zeta_restart (noise : CanonicalNoise) (N : ℕ) (s : ℝ) :
    PerSmooth (potZeta noise.zeta N s) :=
  by
  exact perSmooth_potConv' (perSmooth_potShift (perSmooth_noise_zeta noise) s) N

end RegularityStructures.Phi43.Potential

end
