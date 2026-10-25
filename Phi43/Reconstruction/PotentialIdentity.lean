/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.PsiPDE
public import Phi43.Reconstruction.PsiSmooth
public import Phi43.Reconstruction.ClassicalSolution
public import Phi43.Inhomogeneity.DuhamelLinear

/-!
# The potential identity

`phi43_potential_identity`: with `Ψ = K ∗ ζ` (`phi43PsiAt`), `ζ_s = Q ∗ ζ(· + (s, 0))` and
`θ_s = duhamelField ζ_s`,
`Ψ(s + t) + θ_s(t) = P_t Ψ(s) + ∫₀ᵗ P_{t-r} f(s + r) dr`.  Proof: `a = Ψ(· + (s, 0))` is smooth and
periodic with `(∂_t - Δ) a = ζ(· + (s, 0)) - ζ_s` (`psi_pde`), so the Duhamel principle applies.
-/

public section

open Set MeasureTheory RegularityStructures.PDE RegularityStructures.Inhomogeneity
  RegularityStructures.Potential
open scoped ContDiff

namespace RegularityStructures.Phi43

theorem add_restartPoint_eq (z : ParabolicSpace) (s : ℝ) :
    z + LiftBounds.restartPoint s = (z.1 + s, z.2) :=
  Prod.ext rfl (by simp [LiftBounds.restartPoint])

theorem ddv_potShift {F : ParabolicSpace → ℝ} (s : ℝ) (j : Fin 4) :
    ddv j (potShift s F) = potShift s (ddv j F) := by
  have e : potShift s F = fun z => F (z + LiftBounds.restartPoint s) := by
    funext z
    simp only [potShift, add_restartPoint_eq]
  funext z
  rw [e]
  simp only [ddv, potShift]
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := z) (LiftBounds.restartPoint s)
  rw [h, add_restartPoint_eq]

/-- **The potential identity.** -/
theorem phi43_potential_identity (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hnz : ∀ z : ParabolicSpace, noise.zeta z = f (z.1, torusProj z.2)) (s c : ℝ)
    (us ws : C(Torus3, ℝ))
    (hws : ∀ x : Fin 3 → ℝ, ws (torusProj x) = us (torusProj x) - phi43PsiAt N κ noise C (s, x))
    {t : ℝ} (ht : 0 < t) (x : Fin 3 → ℝ) :
    phi43PsiAt N κ noise C ((t, x) + LiftBounds.restartPoint s) +
        duhamelField (Potential.perSmooth_zeta_restart noise N s) (t, x) =
      heatOp t (us - ws) (torusProj x) + duhamel (fun r => nemytskii (cubicHeatNonlinearity c
        (isSmoothOnSpaceTime_shiftForcing hf s)) r 0) t (torusProj x) := by
  set ζ := noise.zeta with hζdef
  have hΨ : PerSmooth (hairerConvolution N ζ) := by
    have := perSmooth_phi43PsiAt N κ noise C
    rwa [phi43PsiAt_eq] at this
  have hΨs : ContDiff ℝ ∞ (hairerConvolution N ζ) := hΨ.smooth
  have hζP : PerSmooth ζ := Potential.perSmooth_noise_zeta noise
  have hâ := Potential.perSmooth_potShift hΨ s
  have hζs := Potential.perSmooth_potShift hζP s
  have hζr := Potential.perSmooth_zeta_restart noise N s
  have hg := hζs.sub hζr
  have hΨd : ∀ j : Fin 4, Differentiable ℝ (ddv j (hairerConvolution N ζ)) := fun j =>
    (hΨ.ddv j).smooth.differentiable (by simp)
  have hag : ∀ z, ddv 0 (potShift s (hairerConvolution N ζ)) z -
      ∑ j : Fin 3, ddv j.succ (ddv j.succ (potShift s (hairerConvolution N ζ))) z =
      (potShift s ζ - Potential.potZeta ζ N s) z := by
    intro z
    rw [ddv_potShift s 0]
    simp only [ddv_potShift s, Pi.sub_apply, Potential.potZeta_eq]
    simp only [potShift]
    have := psi_pde N noise (z.1 + s, z.2)
    rw [hζdef]
    exact this
  have hP := duhamel_principle hâ hg hag ht.le
  have hpt := congrArg (fun F : C(Torus3, ℝ) => F (torusProj x)) hP
  simp only [ContinuousMap.add_apply] at hpt
  -- evaluate the terms
  have e1 : forcePath hâ t (torusProj x) = phi43PsiAt N κ noise C ((t, x) + LiftBounds.restartPoint s) := by
    rw [forcePath_apply, phi43PsiAt_eq, restartPoint_add]
    rfl
  have e2 : forcePath hâ 0 = us - ws := by
    ext xb
    obtain ⟨y, rfl⟩ := torusProj_surjective xb
    rw [forcePath_apply, ContinuousMap.sub_apply, hws y, phi43PsiAt_eq]
    simp only [potShift, zero_add]
    ring
  have e3 : duhamel (forcePath hg) t = duhamel (forcePath hζs) t - duhamel (forcePath hζr) t := by
    have : forcePath hg = fun r => forcePath hζs r - forcePath hζr r :=
      funext (forcePath_sub hζs hζr)
    rw [this, duhamel_sub (continuous_forcePath hζs) (continuous_forcePath hζr)]
  have e4 : forcePath hζs = fun r => nemytskii (cubicHeatNonlinearity c
      (isSmoothOnSpaceTime_shiftForcing hf s)) r 0 := by
    funext r
    ext xb
    obtain ⟨y, rfl⟩ := torusProj_surjective xb
    rw [forcePath_apply]
    simp only [potShift, nemytskii_apply, cubicHeatNonlinearity_apply, shiftForcing, hnz]
    simp
  have e5 : duhamelField hζr (t, x) = duhamel (forcePath hζr) t (torusProj x) :=
    duhamelField_of_pos hζr ht
  rw [e1, e2, e3, ContinuousMap.sub_apply] at hpt
  rw [e5, ← e4]
  linarith

end RegularityStructures.Phi43

end
