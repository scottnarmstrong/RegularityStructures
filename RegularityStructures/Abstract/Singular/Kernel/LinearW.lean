/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Kernel.LinearG
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Linearity of the lattice reconstruction in the test function (window setting)

Window version of `RegularityStructures.Abstract.Singular.Kernel.LinearG`: only convergence of the
model pairings is used, so a qualitative growth model suffices.
-/

public section

open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace RegularityStructures.Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ : ℝ}

theorem tendsto_latticeApprox_finset_sum_win {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (hgrowth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M.GrowthModel γ C' C'' ρP ρG p q)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {κ : Type*} (S : Finset κ)
    (ψ : κ → ParabolicSpace → ℝ) (x : κ → ParabolicSpace) (R : κ → ℝ)
    (hψ : ∀ j ∈ S, ContDiff ℝ ∞ (ψ j))
    (hsupp : ∀ j ∈ S, ∀ w, R j < parabolicNorm (w - x j) → ψ j w = 0) (L : κ → ℝ)
    (hL : ∀ j ∈ S, Tendsto (M.latticeApprox f (ψ j)) atTop (𝓝 (L j))) :
    Tendsto (M.latticeApprox f (∑ j ∈ S, ψ j)) atTop (𝓝 (∑ j ∈ S, L j)) := by
  obtain ⟨_, _, _, _, _, _, G⟩ := hgrowth
  exact M.tendsto_latticeApprox_finset_sum_growth hf G hdeg S ψ x R hψ hsupp L hL

theorem tendsto_latticeApprox_add_win {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (hgrowth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M.GrowthModel γ C' C'' ρP ρG p q)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {ψ₁ ψ₂ : ParabolicSpace → ℝ}
    {x₁ x₂ : ParabolicSpace} {R₁ R₂ L₁ L₂ : ℝ} (h₁ : ContDiff ℝ ∞ ψ₁) (h₂ : ContDiff ℝ ∞ ψ₂)
    (s₁ : ∀ w, R₁ < parabolicNorm (w - x₁) → ψ₁ w = 0)
    (s₂ : ∀ w, R₂ < parabolicNorm (w - x₂) → ψ₂ w = 0)
    (t₁ : Tendsto (M.latticeApprox f ψ₁) atTop (𝓝 L₁))
    (t₂ : Tendsto (M.latticeApprox f ψ₂) atTop (𝓝 L₂)) :
    Tendsto (M.latticeApprox f (ψ₁ + ψ₂)) atTop (𝓝 (L₁ + L₂)) := by
  obtain ⟨_, _, _, _, _, _, G⟩ := hgrowth
  exact M.tendsto_latticeApprox_add_growth hf G hdeg h₁ h₂ s₁ s₂ t₁ t₂

theorem tendsto_latticeApprox_smul_win {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (hgrowth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M.GrowthModel γ C' C'' ρP ρG p q)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {ψ : ParabolicSpace → ℝ}
    {x : ParabolicSpace} {R L : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ w, R < parabolicNorm (w - x) → ψ w = 0) (c : ℝ)
    (t : Tendsto (M.latticeApprox f ψ) atTop (𝓝 L)) :
    Tendsto (M.latticeApprox f (c • ψ)) atTop (𝓝 (c * L)) := by
  obtain ⟨_, _, _, _, _, _, G⟩ := hgrowth
  exact M.tendsto_latticeApprox_smul_growth hf G hdeg hψ hs c t

theorem latticeRecon_smul_win {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (hgrowth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M.GrowthModel γ C' C'' ρP ρG p q)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {ψ : ParabolicSpace → ℝ}
    {x : ParabolicSpace} {R L : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ w, R < parabolicNorm (w - x) → ψ w = 0) (c : ℝ)
    (t : Tendsto (M.latticeApprox f ψ) atTop (𝓝 L)) :
    M.latticeRecon f (c • ψ) = c * M.latticeRecon f ψ := by
  obtain ⟨_, _, _, _, _, _, G⟩ := hgrowth
  exact M.latticeRecon_smul_growth hf G hdeg hψ hs c t

end RegularityStructures.Model

end
