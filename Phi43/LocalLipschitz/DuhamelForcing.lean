/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.LocalLipschitz.DuhamelMassive
public import Phi43.LocalLipschitz.DuhamelNorm
public import Phi43.Potential.TruncIdentity
public import Phi43.Potential.HolderSmul
public import Phi43.Reconstruction.Classical
public import Phi43.ClassicalSolution.MildNonlinearity

/-!
# Lipschitz dependence of the forcing Duhamel integral on the massive potential

For `t ∈ [0, 1]`, the difference of the Duhamel integrals of the forcings `f(s + ·)` and `g(s + ·)`
is bounded in `𝒞^η` by four times the supremum of `‖ψ - ψ'‖_η` over `[s, s + t]`, where `ψ, ψ'` are
the massive potentials of `f, g` (`holderBesovENorm_duhamel_forcing_sub_le`).  Here the Duhamel
integral is that of the Nemytskii forcing path of the cubic nonlinearity at the argument `0`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43.LocalLipschitz

open RegularityStructures

/-- At the argument `0` the cubic nonlinearity reduces to the time slice of the shifted forcing. -/
theorem nemytskii_cubicHeatNonlinearity_zero (c : ℝ) {f : SpaceTime → ℝ}
    (hF : Potential.PotForcing f) (hf : IsSmoothOnSpaceTime f) (s r : ℝ) :
    PDE.nemytskii (cubicHeatNonlinearity c (isSmoothOnSpaceTime_shiftForcing hf s)) r 0 =
      Potential.potSlice hF.cont (r + s) := by
  ext x
  simp [PDE.nemytskii_apply, cubicHeatNonlinearity_apply, shiftForcing, Potential.potSlice_apply]

/-- The massive Duhamel integral of the forcing slices is the potential increment. -/
theorem massiveDuhamel_potSlice {f : SpaceTime → ℝ} (hF : Potential.PotForcing f)
    {ψ : ℝ → C(Torus3, ℝ)} (hψ : RegularityStructures.IsMassivePotential f ψ) (s : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    massiveDuhamel (fun q => Potential.potSlice hF.cont (q + s)) r =
      ψ (s + r) - Real.exp (-r) • PDE.heatOp r (ψ s) := by
  unfold massiveDuhamel
  have e : ∀ q : ℝ, Real.exp (-(r - q)) • PDE.heatOp (r - q) (Potential.potSlice hF.cont (q + s)) =
      Potential.potF hF.cont (s + r) (q + s) := by
    intro q
    unfold Potential.potF
    rw [show s + r - (q + s) = r - q by ring]
  simp_rw [e]
  rw [intervalIntegral.integral_comp_add_right (fun x => Potential.potF hF.cont (s + r) x) s,
    zero_add, add_comm r s, intervalIntegral.integral_of_le (by linarith),
    Potential.integral_potF_Ioc hF hψ (by linarith)]
  simp

private theorem holderBesovENorm_heatOp_le_of_nonneg (η : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (g : C(Torus3, ℝ)) : holderBesovENorm η (PDE.heatOp r g) ≤ holderBesovENorm η g := by
  rcases hr.eq_or_lt with rfl | h
  · rw [PDE.heatOp_zero_left]
  · exact Potential.holderBesovENorm_heatOp_le η h g

private theorem holderBesovENorm_exp_smul_heatOp_le (η : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (g : C(Torus3, ℝ)) :
    holderBesovENorm η (Real.exp (-r) • PDE.heatOp r g) ≤ holderBesovENorm η g := by
  rw [Potential.holderBesovENorm_smul]
  have h1 : ENNReal.ofReal |Real.exp (-r)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (by linarith))
  calc ENNReal.ofReal |Real.exp (-r)| * holderBesovENorm η (PDE.heatOp r g)
      ≤ 1 * holderBesovENorm η g :=
        mul_le_mul' h1 (holderBesovENorm_heatOp_le_of_nonneg η hr g)
    _ = _ := one_mul _

/-- **Lipschitz dependence of the forcing Duhamel integral on the potential**, in the form with an
explicit bound `D`. -/
theorem holderBesovENorm_duhamel_forcing_sub_le_of_le {f g : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : IsSmoothOnSpaceTime g)
    (hFf : Potential.PotForcing f) (hFg : Potential.PotForcing g)
    {ψ ψ' : ℝ → C(Torus3, ℝ)} (hψ : RegularityStructures.IsMassivePotential f ψ)
    (hψ' : RegularityStructures.IsMassivePotential g ψ') (c c' s : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (η : ℝ) {D : ℝ≥0∞} (hD : ∀ r ∈ Icc s (s + t), holderBesovENorm η (ψ r - ψ' r) ≤ D) :
    holderBesovENorm η
      (PDE.duhamel (fun r => PDE.nemytskii
        (cubicHeatNonlinearity c (isSmoothOnSpaceTime_shiftForcing hf s)) r 0) t -
       PDE.duhamel (fun r => PDE.nemytskii
        (cubicHeatNonlinearity c' (isSmoothOnSpaceTime_shiftForcing hg s)) r 0) t) ≤ 4 * D := by
  set Ff : ℝ → C(Torus3, ℝ) := fun q => Potential.potSlice hFf.cont (q + s) with hFfdef
  set Fg : ℝ → C(Torus3, ℝ) := fun q => Potential.potSlice hFg.cont (q + s) with hFgdef
  have cF : Continuous Ff :=
    (Potential.continuous_potSlice hFf.cont).comp (continuous_id.add continuous_const)
  have cG : Continuous Fg :=
    (Potential.continuous_potSlice hFg.cont).comp (continuous_id.add continuous_const)
  have e1 : (fun r => PDE.nemytskii
      (cubicHeatNonlinearity c (isSmoothOnSpaceTime_shiftForcing hf s)) r 0) = Ff :=
    funext fun r => nemytskii_cubicHeatNonlinearity_zero c hFf hf s r
  have e2 : (fun r => PDE.nemytskii
      (cubicHeatNonlinearity c' (isSmoothOnSpaceTime_shiftForcing hg s)) r 0) = Fg :=
    funext fun r => nemytskii_cubicHeatNonlinearity_zero c' hFg hg s r
  rw [e1, e2, duhamel_eq_massiveDuhamel_add cF ht.1, duhamel_eq_massiveDuhamel_add cG ht.1]
  have hsub : PDE.duhamel (massiveDuhamel Ff) t - PDE.duhamel (massiveDuhamel Fg) t =
      PDE.duhamel (fun r => massiveDuhamel Ff r - massiveDuhamel Fg r) t :=
    (PDE.duhamel_sub (continuous_massiveDuhamel cF) (continuous_massiveDuhamel cG) t).symm
  have hΔ : ∀ r ∈ Icc (0 : ℝ) t,
      holderBesovENorm η (massiveDuhamel Ff r - massiveDuhamel Fg r) ≤ 2 * D := by
    intro r hr
    rw [massiveDuhamel_potSlice hFf hψ s hr.1, massiveDuhamel_potSlice hFg hψ' s hr.1]
    have hmem : ∀ x ∈ Icc (0 : ℝ) t, s + x ∈ Icc s (s + t) := fun x hx =>
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h1 := hD (s + r) (hmem r hr)
    have h2 := hD s (by exact ⟨le_rfl, by linarith [ht.1]⟩)
    have hs0 : holderBesovENorm η (Real.exp (-r) • PDE.heatOp r (ψ s - ψ' s)) ≤ D :=
      (holderBesovENorm_exp_smul_heatOp_le η hr.1 _).trans h2
    have e : ψ (s + r) - Real.exp (-r) • PDE.heatOp r (ψ s) -
        (ψ' (s + r) - Real.exp (-r) • PDE.heatOp r (ψ' s)) =
        (ψ (s + r) - ψ' (s + r)) + -(Real.exp (-r) • PDE.heatOp r (ψ s - ψ' s)) := by
      rw [PDE.heatOp_sub, smul_sub]; abel
    rw [e, two_mul]
    refine (holderBesovENorm_add_le _ _ _).trans (add_le_add h1 ?_)
    rwa [holderBesovENorm_neg]
  have hmain := holderBesovENorm_duhamel_le η
    ((continuous_massiveDuhamel cF).sub (continuous_massiveDuhamel cG)) ht hΔ
  have e3 : ∀ a b c d : C(Torus3, ℝ), a + b - (c + d) = (a - c) + (b - d) := fun a b c d => by abel
  rw [e3]
  refine (holderBesovENorm_add_le _ _ _).trans ?_
  have hm : holderBesovENorm η (massiveDuhamel Ff t - massiveDuhamel Fg t) ≤ 2 * D :=
    hΔ t ⟨ht.1, le_rfl⟩
  calc _ ≤ 2 * D + 2 * D := add_le_add hm (by rw [hsub]; exact hmain)
    _ = 4 * D := by rw [← add_mul]; norm_num

end RegularityStructures.Phi43.LocalLipschitz

end
