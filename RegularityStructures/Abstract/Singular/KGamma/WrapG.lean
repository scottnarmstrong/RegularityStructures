/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Kernel.LinearG
public import RegularityStructures.Abstract.Singular.ModelPairingGrowth
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The local and layer bounds for scaled test functions, weighted models

Weighted (`_growth`) versions of the local bound (6.6) and the layer bound
(Prop. 6.9) for `g` scaled at `x`, for a `Model.GrowthModel` whose weights are bounded by `Rw` on
`timeWindow8`; the constant `max 1 CGam * CPi` becomes `max 1 CGam * CPi * Rw ^ 2`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

/-- `⟨Π_z τ, c • ψ⟩ = c ⟨Π_z τ, ψ⟩` if `c • ψ` is scaled at `z` (weighted models). -/
theorem pairing_regPi_smul_of_scaled_growth (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ) {g ψ : ParabolicSpace → ℝ}
    {z : ParabolicSpace} {R A c : ℝ} (hg : IsScaledTest g z R A) (hc : c ≠ 0) (hgψ : g = c • ψ) :
    parabolicSemigroup.pairing (M.regPi z τ) g = c * parabolicSemigroup.pairing (M.regPi z τ) ψ := by
  have ht := M.tendsto_integral_regPi_mul_of_scaled_growth G hdeg hτ hg
  have ht' : Tendsto (fun s => ∫ y, M.regPi z τ s y * ψ y) (𝓝[>] 0)
      (𝓝 (c⁻¹ * parabolicSemigroup.pairing (M.regPi z τ) g)) := by
    refine (ht.const_mul c⁻¹).congr fun s => ?_
    rw [← integral_const_mul]
    congr 1; funext y
    rw [hgψ]; simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [parabolicSemigroup.pairing_eq_of_tendsto ht']
  field_simp

/-- Convergence and homogeneity of the lattice reconstruction along `g = c • ψ`
(weighted models). -/
theorem tendsto_latticeApprox_smul_rescaled_growth (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {f : ParabolicSpace → ι → ℝ} (hfT : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4) {R : ℝ} (hR : 0 < R)
    {x : ParabolicSpace}
    (t : Tendsto (M.latticeApprox f (rescaledTestFunction φ R x)) atTop
      (𝓝 (M.latticeRecon f (rescaledTestFunction φ R x)))) (c : ℝ) :
    Tendsto (M.latticeApprox f (c • rescaledTestFunction φ R x)) atTop
      (𝓝 (M.latticeRecon f (c • rescaledTestFunction φ R x))) ∧
    M.latticeRecon f (c • rescaledTestFunction φ R x) =
      c * M.latticeRecon f (rescaledTestFunction φ R x) := by
  have hψ := contDiff_rescaledTestFunction hφ.1 R x
  have hs : ∀ w, R < parabolicNorm (w - x) → rescaledTestFunction φ R x w = 0 :=
    fun w hw => rescaledTestFunction_eq_zero hφ.2.1 hR hw
  have h1 := M.tendsto_latticeApprox_smul_growth hfT G hdeg hψ hs c t
  have h2 := M.latticeRecon_smul_growth hfT G hdeg hψ hs c t
  rw [h2]
  exact ⟨h1, rfl⟩

end Model

end RegularityStructures

end
