/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.HolderBesovConvBound
public import Phi43.Potential.NoiseModelSum
public import Phi43.Potential.HolderSmul
public import Phi43.Potential.PotentialLinear

/-!
# The potential bound, two models

`holderBesovENorm_conv_sub_le`: for two models with the data of the potential bound and the
difference bounds, the `𝒞^η` norm of `V₁ - V₂`, `V_i = (K_N ∗ ζ_i)(s)`, is bounded by
`λ · C(M⊕) + 2 δ_ψ`, `δ_ψ ≥ sup_{r ∈ [s - 1/4, s]} ‖ψ₁(r) - ψ₂(r)‖_η`.  It is the one-model theorem `holderBesovENorm_conv_le`
applied to the difference model `modelSum M₁ M₂` with `ζ = λ⁻¹ (ζ₁ - ζ₂)`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RegularityStructures.Potential

open RegularityStructures

theorem PotForcing.sub_smul {f₁ f₂ : SpaceTime → ℝ} (h₁ : PotForcing f₁) (h₂ : PotForcing f₂)
    (c : ℝ) : PotForcing (fun w => c * (f₁ w - f₂ w)) := by
  refine ⟨continuous_const.mul (h₁.cont.sub h₂.cont), ?_⟩
  obtain ⟨B₁, n₁, hB₁, b₁⟩ := h₁.bound
  obtain ⟨B₂, n₂, hB₂, b₂⟩ := h₂.bound
  refine ⟨|c| * (B₁ + B₂), max n₁ n₂, by positivity, fun r y => ?_⟩
  have hb : (1 : ℝ) ≤ 1 + |r| := by linarith [abs_nonneg r]
  have e1 : (1 + |r|) ^ n₁ ≤ (1 + |r|) ^ max n₁ n₂ := pow_le_pow_right₀ hb (le_max_left _ _)
  have e2 : (1 + |r|) ^ n₂ ≤ (1 + |r|) ^ max n₁ n₂ := pow_le_pow_right₀ hb (le_max_right _ _)
  rw [abs_mul]
  have := (abs_sub _ _).trans (add_le_add (b₁ r y) (b₂ r y))
  calc |c| * |f₁ (r, y) - f₂ (r, y)| ≤ |c| * (B₁ * (1 + |r|) ^ n₁ + B₂ * (1 + |r|) ^ n₂) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ ≤ |c| * (B₁ * (1 + |r|) ^ max n₁ n₂ + B₂ * (1 + |r|) ^ max n₁ n₂) := by
        gcongr
    _ = |c| * (B₁ + B₂) * (1 + |r|) ^ max n₁ n₂ := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

/-- **The potential bound, two models, with the parameter `λ` of the difference model.** -/
theorem holderBesovENorm_conv_sub_le {lam : ℝ} (hlam : 0 < lam) (h₁ : M₁.IsPolyCompatible P)
    (h₂ : M₂.IsPolyCompatible P) {γ CPi₁ CPi₂ CG₁ CG₂ CdPi CdGam : ℝ} {o : ι}
    {ζ₁ ζ₂ : ParabolicSpace → ℝ} {s : ℝ}
    (H₁ : NoiseModelHyp M₁ γ CPi₁ CG₁ o (potShift s ζ₁))
    (H₂ : NoiseModelHyp M₂ γ CPi₂ CG₂ o (potShift s ζ₂))
    (hdPi : M₁.PiDiffBoundOn M₂ γ CdPi hairerTimeWindow)
    (hdGam : M₁.GammaDiffNearOn M₂ γ CdGam hairerTimeWindow)
    (h0 : 0 ≤ max (max CG₁ CG₂) (lam⁻¹ * CdGam)) (hnp : o ∉ Set.range P.emb) (N : ℕ)
    {f₁ f₂ : SpaceTime → ℝ} (hF₁ : PotForcing f₁) (hF₂ : PotForcing f₂)
    (hζf₁ : ∀ z : ParabolicSpace, ζ₁ z = f₁ (z.1, torusProj z.2))
    (hζf₂ : ∀ z : ParabolicSpace, ζ₂ z = f₂ (z.1, torusProj z.2))
    (hζ₁ : Continuous ζ₁) (hζ₂ : Continuous ζ₂) {ψ₁ ψ₂ : ℝ → C(Torus3, ℝ)}
    (hψ₁ : IsMassivePotential f₁ ψ₁) (hψ₂ : IsMassivePotential f₂ ψ₂)
    (η : ℝ) (hη : η ≤ 0) {δψ : ℝ} (hδ : 0 ≤ δψ)
    (hψN : ∀ r ∈ Icc (s - 1 / 4) s, holderBesovENorm η (ψ₁ r - ψ₂ r) ≤ ENNReal.ofReal δψ)
    (V₁ V₂ : C(Torus3, ℝ))
    (hV₁ : ∀ xt : Fin 3 → ℝ, V₁ (torusProj xt) = Phi43.hairerConvolution N ζ₁ (s, xt))
    (hV₂ : ∀ xt : Fin 3 → ℝ, V₂ (torusProj xt) = Phi43.hairerConvolution N ζ₂ (s, xt)) :
    holderBesovENorm η (V₁ - V₂) ≤ ENNReal.ofReal
      (lam * (r4ModelConst (TwoModel.structSumU P) γ *
        (max 1 (max (max CG₁ CG₂) (lam⁻¹ * CdGam)) * max CPi₂ (lam⁻¹ * CdPi)) *
        (potKernelConst (potTail N) + potK1Const N (𝒯.deg o))) + 2 * δψ) := by
  set Cs : ℝ := r4ModelConst (TwoModel.structSumU P) γ *
    (max 1 (max (max CG₁ CG₂) (lam⁻¹ * CdGam)) * max CPi₂ (lam⁻¹ * CdPi)) *
    (potKernelConst (potTail N) + potK1Const N (𝒯.deg o)) with hCs
  have hS := NoiseModelHyp.modelSum hlam h₁ h₂ H₁ H₂ hdPi hdGam h0 hnp
  obtain ⟨B₁, hB₁⟩ := H₁.bdd
  obtain ⟨B₂, hB₂⟩ := H₂.bdd
  have hbζ : ∀ (B : ℝ) (ζ : ParabolicSpace → ℝ),
      (∀ y : ParabolicSpace, -1 ≤ y.1 → y.1 ≤ 2 → |potShift s ζ y| ≤ B) →
      ∀ y : ParabolicSpace, s - 1 ≤ y.1 → y.1 ≤ s → |ζ y| ≤ B := by
    intro B ζ hB y h1 h2
    have := hB (y.1 - s, y.2) (by simp; linarith) (by simp; linarith)
    simpa [potShift] using this
  have hb₁ := hbζ B₁ ζ₁ hB₁
  have hb₂ := hbζ B₂ ζ₂ hB₂
  have hcore := holderBesovENorm_conv_le (ζ := fun w => lam⁻¹ * (ζ₁ w - ζ₂ w)) (s := s)
    (by exact hS) N (f := fun w => lam⁻¹ * (f₁ w - f₂ w)) (hF₁.sub_smul hF₂ _)
    (fun z => by simp only [hζf₁, hζf₂]) (continuous_const.mul (hζ₁.sub hζ₂))
    (ψ := fun t => lam⁻¹ • (ψ₁ t - ψ₂ t)) (isMassivePotential_sub_smul hψ₁ hψ₂ _) η hη
    (N' := lam⁻¹ * δψ) (mul_nonneg (inv_pos.2 hlam).le hδ)
    (fun r hr => by
      show holderBesovENorm η (lam⁻¹ • (ψ₁ r - ψ₂ r)) ≤ _
      rw [holderBesovENorm_smul, abs_of_pos (inv_pos.2 hlam),
        ENNReal.ofReal_mul (inv_pos.2 hlam).le]
      exact mul_le_mul_right (hψN r hr) _)
    (lam⁻¹ • (V₁ - V₂))
    (fun xt => by
      have := hairerConvolution_sub_smul N hζ₁ hζ₂ (s, xt) (fun y a b => hb₁ y (by simpa using a)
        (by simpa using b)) (fun y a b => hb₂ y (by simpa using a) (by simpa using b)) lam⁻¹
      rw [this]
      simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul, hV₁, hV₂])
  have hV : V₁ - V₂ = lam • (lam⁻¹ • (V₁ - V₂)) := by
    rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
  have e1 : holderBesovENorm η (V₁ - V₂) =
      ENNReal.ofReal lam * holderBesovENorm η (lam⁻¹ • (V₁ - V₂)) := by
    conv_lhs => rw [hV]
    rw [holderBesovENorm_smul, abs_of_pos hlam]
  rw [e1]
  refine (mul_le_mul_right hcore _).trans ?_
  rw [← ENNReal.ofReal_mul hlam.le]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [hCs]
  field_simp
  rfl

end RegularityStructures.Potential

end
