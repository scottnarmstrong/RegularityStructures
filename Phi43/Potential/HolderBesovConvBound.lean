/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.NoiseModelHyp
public import Phi43.Potential.MassIdentity

/-!
# The potential bound: the `𝒞^η` norm of `(K ∗ f)(s)`

`holderBesovENorm_conv_le`: for `V ∈ C(T³)` with `V(proj x̃) = (K_N ∗ ζ)(s, x̃)`,

  `‖V‖_η ≤ r4ModelConst · max(1, C_Γ) C_Π · (potKernelConst (potTail N) + potK1Const N (deg o)) + 2 N'`,

where `N'` bounds `‖ψ(r)‖_η` for `r ∈ [s - 1/4, s]`.  Proof: `K = (1 - χ) K + χ (K - G^m) + χ G^m`;
the first two parts are bounded in sup norm by the model constants; `P_u` of the third part is bounded
by `2 u^{η/2} N'` (`abs_integral_cutoff_potF_le`).
-/

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures.Potential

open RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam : ℝ} {o : ι}

/-- The sup norm of the non-potential part is bounded by the model constants. -/
theorem NoiseModelHyp.abs_nonpot_le {ζ : ParabolicSpace → ℝ} {s : ℝ}
    (H : NoiseModelHyp M γ CPi CGam o (potShift s ζ)) (N : ℕ) (xt : Fin 3 → ℝ) :
    |potConv ζ (potTail N) (s, xt) + potConv ζ (potK1 N) (s, xt)| ≤
      r4ModelConst 𝒯 γ * (max 1 CGam * CPi) *
        (potKernelConst (potTail N) + potK1Const N (𝒯.deg o)) := by
  have h := H.abs_conv_nonpot_le N (z := (0, xt)) le_rfl zero_le_one
  have e : ∀ k : ParabolicSpace → ℝ, potConv (potShift s ζ) k (0, xt) = potConv ζ k (s, xt) :=
    fun k => by
      rw [potConv_potShift]
      simp
  rwa [e, e] at h

/-- **The potential bound (one model).** -/
theorem holderBesovENorm_conv_le {ζ : ParabolicSpace → ℝ} {s : ℝ}
    (H : NoiseModelHyp M γ CPi CGam o (potShift s ζ)) (N : ℕ) {f : SpaceTime → ℝ}
    (hF : PotForcing f) (hζf : ∀ z : ParabolicSpace, ζ z = f (z.1, torusProj z.2))
    (hζ : Continuous ζ) {ψ : ℝ → C(Torus3, ℝ)} (hψ : IsMassivePotential f ψ)
    (η : ℝ) (hη : η ≤ 0) {N' : ℝ} (hN' : 0 ≤ N')
    (hψN : ∀ r ∈ Icc (s - 1 / 4) s, holderBesovENorm η (ψ r) ≤ ENNReal.ofReal N')
    (V : C(Torus3, ℝ)) (hV : ∀ xt : Fin 3 → ℝ, V (torusProj xt) = Phi43.hairerConvolution N ζ (s, xt)) :
    holderBesovENorm η V ≤ ENNReal.ofReal
      (r4ModelConst 𝒯 γ * (max 1 CGam * CPi) *
        (potKernelConst (potTail N) + potK1Const N (𝒯.deg o)) + 2 * N') := by
  set Cs : ℝ := r4ModelConst 𝒯 γ * (max 1 CGam * CPi) *
    (potKernelConst (potTail N) + potK1Const N (𝒯.deg o)) with hCs
  obtain ⟨Bξ, hBξ⟩ := H.bdd
  have hζb : ∀ y : ParabolicSpace, s - 1 ≤ y.1 → y.1 ≤ s → |ζ y| ≤ Bξ := by
    intro y h1 h2
    have := hBξ (y.1 - s, y.2) (by simp; linarith) (by simp; linarith)
    simpa [potShift] using this
  set C₃ : C(Torus3, ℝ) := ∫ r in Ioc (s - 1 / 4) s, potCutoff (s - r) • potF hF.cont s r with hC₃
  set D : C(Torus3, ℝ) := V - C₃ with hD
  have hDeq : ∀ xt : Fin 3 → ℝ, D (torusProj xt) =
      potConv ζ (potTail N) (s, xt) + potConv ζ (potK1 N) (s, xt) := by
    intro xt
    have h1 := hairerConvolution_decomp N hζ (s, xt) (Bζ := Bξ) (fun y h1 h2 =>
      hζb y h1 (by simpa using h2))
    have h2 := potConv_potMass_eq hF.cont hζf hζ (Bζ := Bξ) s
      (fun y h1 h2 => hζb y (by linarith) h2) xt
    have h3 : D (torusProj xt) = V (torusProj xt) - C₃ (torusProj xt) := rfl
    have h2' : potConv ζ potMass (s, xt) = C₃ (torusProj xt) := h2
    rw [h3, hV, h1, h2']
    ring
  have hDb : ∀ x : Torus3, ‖D x‖ ≤ Cs := by
    intro x
    have := H.abs_nonpot_le (ζ := ζ) (s := s) N (torusRep x)
    rw [← hDeq, PDE.torusProj_torusRep, ← hCs] at this
    simpa [Real.norm_eq_abs] using this
  have hCs0 : 0 ≤ Cs := (norm_nonneg _).trans (hDb 0)
  have hDn : ‖D‖ ≤ Cs := (ContinuousMap.norm_le _ hCs0).2 hDb
  have hI : IntegrableOn (fun r : ℝ => potCutoff (s - r) • potF hF.cont s r) (Ioc (s - 1 / 4) s) :=
    (((contDiff_potCutoff_sub s).continuous).smul (continuous_potF hF.cont s)).integrableOn_Ioc
  have key : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ x : Torus3,
      ‖heatSemigroup u V x‖ ≤ Cs + 2 * (u ^ (η / 2) * N') := by
    intro u hu x
    have hVeq : V = C₃ + D := by simp [hD]
    rw [hVeq, heatSemigroup_add hu.1 C₃ D x]
    refine (norm_add_le _ _).trans (add_comm Cs _ ▸ add_le_add ?_ ?_)
    · rw [← PDE.heatOp_eq_heatSemigroup hu.1]
      have hΛ := ((ContinuousMap.evalCLM ℝ x).comp (PDE.heatOpCLM (E := ℝ) u)).integral_comp_comm hI
      have e : ∀ g : C(Torus3, ℝ), ((ContinuousMap.evalCLM ℝ x).comp (PDE.heatOpCLM (E := ℝ) u)) g =
          PDE.heatOp u g x := fun g => rfl
      have h1 : PDE.heatOp u C₃ x = ∫ r in Ioc (s - 1 / 4) s,
          potCutoff (s - r) * PDE.heatOp u (potF hF.cont s r) x := by
        have := hΛ.symm
        simp only [e] at this
        rw [hC₃, this]
        refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
        simp only [PDE.heatOp_smul, ContinuousMap.smul_apply, smul_eq_mul]
      rw [h1, ← intervalIntegral.integral_of_le (by linarith : s - 1 / 4 ≤ s)]
      rw [Real.norm_eq_abs]
      exact abs_integral_cutoff_potF_le hF hψ η s hu x hN' hψN
    · exact (norm_heatSemigroup_le hu.1 D x).trans hDn
  refine iSup₂_le fun u hu => ?_
  have hu0 : 0 < u := hu.1
  have hpos : 0 ≤ u ^ (-η / 2) := Real.rpow_nonneg hu0.le _
  have h1 : ⨆ x, ‖heatSemigroup u V x‖ₑ ≤ ENNReal.ofReal (Cs + 2 * (u ^ (η / 2) * N')) := by
    refine iSup_le fun x => ?_
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (key u hu x)
  refine (mul_le_mul_right h1 _).trans ?_
  rw [← ENNReal.ofReal_mul hpos]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : u ^ (-η / 2) * u ^ (η / 2) = 1 := by
    rw [← Real.rpow_add hu0, show -η / 2 + η / 2 = 0 by ring, Real.rpow_zero]
  have hle : u ^ (-η / 2) ≤ 1 := Real.rpow_le_one hu0.le hu.2 (by linarith)
  have hv : 0 ≤ u ^ (η / 2) * N' := mul_nonneg (Real.rpow_nonneg hu0.le _) hN'
  calc u ^ (-η / 2) * (Cs + 2 * (u ^ (η / 2) * N'))
      = u ^ (-η / 2) * Cs + 2 * ((u ^ (-η / 2) * u ^ (η / 2)) * N') := by ring
    _ = u ^ (-η / 2) * Cs + 2 * N' := by rw [e, one_mul]
    _ ≤ Cs + 2 * N' := by nlinarith

end RegularityStructures.Potential

end
