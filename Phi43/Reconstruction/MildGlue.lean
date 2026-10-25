/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.Classical
public import Phi43.Reconstruction.HeatPotential

/-!
# From the pointwise identities to the mild equation

`mild_of_pointwise`: let `W : ℝ → C(T³)` be a continuous path with
`W t (y) = (P_t w_s)(y) + θ(t, y) + ψ(t, y) - ∫ H((t, y) - z) 𝟙_{(0,T]}(z) (W³ - c W)(z) dz`
(the unit coefficient of the fixed point, `phi43_unit_coeff` and `phi43InhomTheta_unit`) and
`ψ(t, y) + θ(t, y) = (P_t (u₀ - w_s))(y) + duhamel (f(s + ·)) t (y)` (the potential identity).
Then `W` solves the mild equation `W t = P_t u₀ + ∫₀ᵗ P_{t-r}(f(s + r) - W³ + c W) dr` of
`cubicHeatNonlinearity c f(s + ·)`.
-/

public section

open Set MeasureTheory RegularityStructures.PDE

namespace RegularityStructures.Phi43

theorem mild_of_pointwise {c : ℝ} {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (s : ℝ)
    {T : ℝ} (W : ℝ → C(Torus3, ℝ)) (hW : Continuous W) (u₀ ws : C(Torus3, ℝ))
    (θ ψ : ParabolicSpace → ℝ)
    (hrep : ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ, W t (torusProj x) =
      heatOp t ws (torusProj x) + θ (t, x) + ψ (t, x) -
        ∫ z : ParabolicSpace, heatKernelR4 (((t, x) : ParabolicSpace) - z) *
          (timeSlab T).indicator (fun y => W y.1 (torusProj y.2) ^ 3 -
            c * W y.1 (torusProj y.2)) z)
    (hpot : ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ, ψ (t, x) + θ (t, x) =
      heatOp t (u₀ - ws) (torusProj x) + duhamel (fun r =>
        nemytskii (cubicHeatNonlinearity c (isSmoothOnSpaceTime_shiftForcing hf s)) r 0) t
          (torusProj x)) :
    ∀ t ∈ Ioc 0 T, W t = heatOp t u₀ + duhamel (fun r =>
      nemytskii (cubicHeatNonlinearity c (isSmoothOnSpaceTime_shiftForcing hf s)) r (W r)) t := by
  intro t ht
  set G := cubicHeatNonlinearity c (isSmoothOnSpaceTime_shiftForcing hf s) with hG
  set hN : ℝ → C(Torus3, ℝ) := fun r => W r ^ 3 - c • W r with hhN
  have hNc : Continuous hN := (hW.pow 3).sub (hW.const_smul c)
  have hFc : Continuous (fun r => nemytskii G r 0) :=
    continuous_nemytskii_comp G (u := fun _ => (0 : C(Torus3, ℝ))) continuous_const
  have hdecomp : (fun r => nemytskii G r (W r)) = fun r => nemytskii G r 0 - hN r := by
    funext r
    ext x
    simp [hG, hhN, cubicHeatNonlinearity_apply]
    ring
  have hP := heatPotential_eq_duhamel hN hNc ht.1 ht.2 (fun y => W y.1 (torusProj y.2) ^ 3 -
    c * W y.1 (torusProj y.2)) (fun r _ y => by simp [hhN]) 
  ext x'
  obtain ⟨x, rfl⟩ := torusProj_surjective x'
  rw [hrep t ht x]
  have h1 := hpot t ht x
  have h2 := hP x
  rw [hdecomp, duhamel_sub hFc hNc]
  simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply]
  have h3 : heatOp t ws (torusProj x) + heatOp t (u₀ - ws) (torusProj x) =
      heatOp t u₀ (torusProj x) := by
    rw [← ContinuousMap.add_apply, ← heatOp_add]; simp
  rw [h2]
  linarith

end RegularityStructures.Phi43

end
