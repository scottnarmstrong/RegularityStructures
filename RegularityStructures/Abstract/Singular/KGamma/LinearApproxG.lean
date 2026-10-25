/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.PairingG
public import RegularityStructures.Abstract.Singular.Kernel.LinearG
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Linearity of the lattice reconstruction in `f`, weighted models

Weighted (`_growth`) version, for a `Model.GrowthModel`.

* `pairing_regPi_add_of_scaled_growth`, `pairing_regPi_const_smul_of_scaled_growth`: `τ ↦ ⟨Π_z τ, g⟩` is linear
  on `T_{<γ}` for `g` scaled at `z`;
* `latticeApprox_add_fun_growth`, `latticeApprox_smul_fun_growth`: `f ↦ S_n f ψ` is additive and homogeneous
  for `n ≥ 3` and smooth `ψ` supported in a ball (`f z ∈ T_{<γ}`);
* `tendsto_latticeApprox_add_fun_growth`, `latticeRecon_add_fun_growth` and the `smul` versions: the same for
  `f ↦ ⟨R f, ψ⟩` whenever the approximations converge.
-/

public section

open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace RegularityStructures.Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

/-- Additivity of `τ ↦ ⟨Π_z τ, g⟩` on `T_{<γ}`. -/
theorem pairing_regPi_add_of_scaled_growth (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {τ₁ τ₂ : ι → ℝ} (h₁ : τ₁ ∈ lowerSubspace 𝒯.deg γ) (h₂ : τ₂ ∈ lowerSubspace 𝒯.deg γ)
    {g : ParabolicSpace → ℝ} {z : ParabolicSpace} {R A : ℝ} (hg : IsScaledTest g z R A) :
    parabolicSemigroup.pairing (M.regPi z (τ₁ + τ₂)) g =
      parabolicSemigroup.pairing (M.regPi z τ₁) g + parabolicSemigroup.pairing (M.regPi z τ₂) g := by
  rw [M.pairing_regPi_eq_sum_single_of_scaled_growth G hdeg (Submodule.add_mem _ h₁ h₂) hg,
    M.pairing_regPi_eq_sum_single_of_scaled_growth G hdeg h₁ hg,
    M.pairing_regPi_eq_sum_single_of_scaled_growth G hdeg h₂ hg, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring

/-- Homogeneity of `τ ↦ ⟨Π_z τ, g⟩` on `T_{<γ}`. -/
theorem pairing_regPi_const_smul_of_scaled_growth (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ) (c : ℝ)
    {g : ParabolicSpace → ℝ} {z : ParabolicSpace} {R A : ℝ} (hg : IsScaledTest g z R A) :
    parabolicSemigroup.pairing (M.regPi z (c • τ)) g =
      c * parabolicSemigroup.pairing (M.regPi z τ) g := by
  rw [M.pairing_regPi_eq_sum_single_of_scaled_growth G hdeg (Submodule.smul_mem _ c hτ) hg,
    M.pairing_regPi_eq_sum_single_of_scaled_growth G hdeg hτ hg, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

variable {f₁ f₂ : ParabolicSpace → ι → ℝ}

/-- `f ↦ S_n f ψ` is additive (`n ≥ 3`, `ψ` smooth supported in a ball). -/
theorem latticeApprox_add_fun_growth (hf₁ : ∀ z, f₁ z ∈ lowerSubspace 𝒯.deg γ)
    (hf₂ : ∀ z, f₂ z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {ψ : ParabolicSpace → ℝ}
    {x : ParabolicSpace} {R : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ w, R < parabolicNorm (w - x) → ψ w = 0) {n : ℕ} (hn : 3 ≤ n) :
    M.latticeApprox (f₁ + f₂) ψ n = M.latticeApprox f₁ ψ n + M.latticeApprox f₂ ψ n := by
  obtain ⟨s, hs'⟩ := exists_finset_support_mul_latticeCell hs n
  rw [M.latticeApprox_eq_sum hs', M.latticeApprox_eq_sum hs', M.latticeApprox_eq_sum hs',
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨A, hA⟩ := exists_isScaledTest_of_latticeCell
    (hψ.mul (contDiff_latticeCell n k)) hn fun w h => right_ne_zero_of_mul h
  exact M.pairing_regPi_add_of_scaled_growth G hdeg (hf₁ _) (hf₂ _) hA

/-- `f ↦ S_n f ψ` is homogeneous (`n ≥ 3`, `ψ` smooth supported in a ball). -/
theorem latticeApprox_smul_fun_growth {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (c : ℝ) {ψ : ParabolicSpace → ℝ}
    {x : ParabolicSpace} {R : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ w, R < parabolicNorm (w - x) → ψ w = 0) {n : ℕ} (hn : 3 ≤ n) :
    M.latticeApprox (c • f) ψ n = c * M.latticeApprox f ψ n := by
  obtain ⟨s, hs'⟩ := exists_finset_support_mul_latticeCell hs n
  rw [M.latticeApprox_eq_sum hs', M.latticeApprox_eq_sum hs', Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨A, hA⟩ := exists_isScaledTest_of_latticeCell
    (hψ.mul (contDiff_latticeCell n k)) hn fun w h => right_ne_zero_of_mul h
  exact M.pairing_regPi_const_smul_of_scaled_growth G hdeg (hf _) c hA

/-- Convergence of `S_n (f₁ + f₂) ψ`. -/
theorem tendsto_latticeApprox_add_fun_growth (hf₁ : ∀ z, f₁ z ∈ lowerSubspace 𝒯.deg γ)
    (hf₂ : ∀ z, f₂ z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {ψ : ParabolicSpace → ℝ}
    {x : ParabolicSpace} {R : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ w, R < parabolicNorm (w - x) → ψ w = 0) {L₁ L₂ : ℝ}
    (t₁ : Tendsto (M.latticeApprox f₁ ψ) atTop (𝓝 L₁))
    (t₂ : Tendsto (M.latticeApprox f₂ ψ) atTop (𝓝 L₂)) :
    Tendsto (M.latticeApprox (f₁ + f₂) ψ) atTop (𝓝 (L₁ + L₂)) := by
  refine (t₁.add t₂).congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact (M.latticeApprox_add_fun_growth hf₁ hf₂ G hdeg hψ hs hn).symm

/-- `⟨R (f₁ + f₂), ψ⟩ = ⟨R f₁, ψ⟩ + ⟨R f₂, ψ⟩` when both approximations converge. -/
theorem latticeRecon_add_fun_growth (hf₁ : ∀ z, f₁ z ∈ lowerSubspace 𝒯.deg γ)
    (hf₂ : ∀ z, f₂ z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {ψ : ParabolicSpace → ℝ}
    {x : ParabolicSpace} {R : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ w, R < parabolicNorm (w - x) → ψ w = 0) {L₁ L₂ : ℝ}
    (t₁ : Tendsto (M.latticeApprox f₁ ψ) atTop (𝓝 L₁))
    (t₂ : Tendsto (M.latticeApprox f₂ ψ) atTop (𝓝 L₂)) :
    Tendsto (M.latticeApprox (f₁ + f₂) ψ) atTop (𝓝 (M.latticeRecon f₁ ψ + M.latticeRecon f₂ ψ)) ∧
      M.latticeRecon (f₁ + f₂) ψ = M.latticeRecon f₁ ψ + M.latticeRecon f₂ ψ := by
  have t := M.tendsto_latticeApprox_add_fun_growth hf₁ hf₂ G hdeg hψ hs t₁ t₂
  have e₁ : M.latticeRecon f₁ ψ = L₁ := t₁.limUnder_eq
  have e₂ : M.latticeRecon f₂ ψ = L₂ := t₂.limUnder_eq
  rw [e₁, e₂]
  exact ⟨t, t.limUnder_eq⟩

/-- Convergence of `S_n (c • f) ψ`. -/
theorem tendsto_latticeApprox_smul_fun_growth {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (c : ℝ) {ψ : ParabolicSpace → ℝ}
    {x : ParabolicSpace} {R : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ w, R < parabolicNorm (w - x) → ψ w = 0) {L : ℝ}
    (t : Tendsto (M.latticeApprox f ψ) atTop (𝓝 L)) :
    Tendsto (M.latticeApprox (c • f) ψ) atTop (𝓝 (c * L)) := by
  refine (t.const_mul c).congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact (M.latticeApprox_smul_fun_growth hf G hdeg c hψ hs hn).symm

/-- `⟨R (c • f), ψ⟩ = c ⟨R f, ψ⟩` when the approximation converges. -/
theorem latticeRecon_smul_fun_growth {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (c : ℝ) {ψ : ParabolicSpace → ℝ}
    {x : ParabolicSpace} {R : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ w, R < parabolicNorm (w - x) → ψ w = 0) {L : ℝ}
    (t : Tendsto (M.latticeApprox f ψ) atTop (𝓝 L)) :
    Tendsto (M.latticeApprox (c • f) ψ) atTop (𝓝 (c * M.latticeRecon f ψ)) ∧
      M.latticeRecon (c • f) ψ = c * M.latticeRecon f ψ := by
  have h := M.tendsto_latticeApprox_smul_fun_growth hf G hdeg c hψ hs t
  have e : M.latticeRecon f ψ = L := t.limUnder_eq
  rw [e]
  exact ⟨h, h.limUnder_eq⟩

end RegularityStructures.Model

end
