/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.Increment
public import RegularityStructures.Abstract.Integration.Theorem512.MeasKGamma
public import RegularityStructures.Abstract.Integration.Theorem512.MeasurableKGamma

/-!
# Hairer's Theorem 5.12: `𝒦_γ : D^γ → D^{γ+2}`

`Model.kGamma_mem_modelledDistributions`: there is a constant `c` (depending on `𝒯, γ, N`, not on
the model or on `f`) such that for a model satisfying a `SchauderSetting` and the joint
measurability `Model.IsJointMeasurable`, and every `f ∈ D^γ` with values in the sector `V`,
`x ↦ 𝒦_γ f(x)` lies in `D^{γ+2}` with the bound
`c · max 1 C_I · max 1 C_Π · max C_Γ 1 · C_f`.

Source: [Hai14, Theorem 5.12].
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

/-- **Hairer's Theorem 5.12** (first part): `𝒦_γ f ∈ D^{γ+2}`, with an explicit bound. -/
theorem kGamma_mem_modelledDistributions {γ : ℝ} (hγ : 0 < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j) (N : ℕ) (P : PolynomialSector 𝒯 N') (hNN : N' ≤ N)
    (hn : SchauderNonIntegral 𝒯 γ N' P) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam CI Cf : ℝ}
      (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ)),
      SchauderSetting M N γ P I V CPi CGam CI → M.IsJointMeasurable →
      ∀ {f : ParabolicSpace → ι → ℝ}, f ∈ M.modelledDistributions γ →
      M.ModelledBoundOn γ Cf univ f → 0 ≤ Cf → (∀ x, f x ∈ V) →
      (fun x => kGamma M N P I γ f x) ∈ M.modelledDistributions (γ + 2) ∧
      M.ModelledBoundOn (γ + 2) (c * max 1 CI * max 1 CPi * max CGam 1 * Cf) univ
        (fun x => kGamma M N P I γ f x) := by
  obtain ⟨c, hc0, hc⟩ := exists_modelledBoundOn_kGamma hγ hdeg N P hNN hn
  refine ⟨c, hc0, fun M CPi CGam CI Cf I V S hJ f hf hfb hCf hfV => ?_⟩
  have hb := hc M I V S hf hfb hCf hfV
  exact ⟨⟨measurable_kGamma hJ S hf hfb hCf, fun x => kGamma_mem_lowerSubspace S hf hfV x,
    _, hb⟩, hb⟩

end Model

end RegularityStructures

end
