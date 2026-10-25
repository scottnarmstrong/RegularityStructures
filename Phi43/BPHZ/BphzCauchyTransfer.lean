/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.RandomCanonical
public import Phi43.BPHZ.StepStatements
public import RegularityStructures.BPHZ.ModelNormTriangle

/-!
# Transfer of the local model norms between two models of the same noise

* `Model.diffNormOn_mono_set`, `Model.normOn_eq_of_diffNormOn_eq_zero`,
  `Model.diffNormOn_eq_of_diffNormOn_eq_zero`: pseudo-metric bookkeeping for the local model
  difference norm (`ModelNormTriangle`).
* `diffNormOn_eq_zero_of_isModeratePhi43ModelOf`: two moderate Φ⁴₃ models
  (`Statements.IsModeratePhi43ModelOf`) of the same noise and constants have vanishing difference
  norm on every set (the uniqueness clause of `renormalisedCanonicalModel_existsUnique`).
* `CanonicalLiftGrowth`, `isModeratePhi43ModelOf_canonicalModelOfLift`: the canonical model of a
  lifted noise is a moderate Φ⁴₃ model as soon as it has the weighted growth clause.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E] {μ : Measure E}
  {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M₁ M₂ M₃ M₄ : Model 𝒯 K}
  {γ : ℝ} {S S' : Set E}

theorem diffNormOn_mono_set (hS : S ⊆ S') : M₁.diffNormOn M₂ γ S ≤ M₁.diffNormOn M₂ γ S' := by
  unfold diffNormOn piDiffNormOn gammaDiffNormOn
  refine add_le_add ?_ ?_
  · refine le_iInf fun C => le_iInf fun h => iInf₂_le (f := fun (C : NNReal) _ => (C : ENNReal)) C ?_
    exact fun i hi t ht x hx => h i hi t ht x (hS hx)
  · refine le_iInf fun C => le_iInf fun h => iInf₂_le (f := fun (C : NNReal) _ => (C : ENNReal)) C ?_
    exact fun i j hi hj x hx y hy => h i j hi hj x (hS hx) y (hS hy)

theorem normOn_eq_of_diffNormOn_eq_zero (h : M₁.diffNormOn M₂ γ S = 0) :
    M₁.normOn γ S = M₂.normOn γ S := by
  refine le_antisymm ?_ ?_
  · simpa [h] using (normOn_le_add_diffNormOn (M₁ := M₁) (M₂ := M₂) (γ := γ) (S := S))
  · have h' : M₂.diffNormOn M₁ γ S = 0 := by rw [diffNormOn_comm]; exact h
    simpa [h'] using (normOn_le_add_diffNormOn (M₁ := M₂) (M₂ := M₁) (γ := γ) (S := S))

theorem diffNormOn_eq_of_diffNormOn_eq_zero (h₁ : M₁.diffNormOn M₃ γ S = 0)
    (h₂ : M₂.diffNormOn M₄ γ S = 0) : M₁.diffNormOn M₂ γ S = M₃.diffNormOn M₄ γ S := by
  have h₁' : M₃.diffNormOn M₁ γ S = 0 := by rw [diffNormOn_comm]; exact h₁
  have h₂' : M₄.diffNormOn M₂ γ S = 0 := by rw [diffNormOn_comm]; exact h₂
  refine le_antisymm ?_ ?_
  · calc M₁.diffNormOn M₂ γ S ≤ M₁.diffNormOn M₃ γ S + M₃.diffNormOn M₂ γ S := diffNormOn_triangle
      _ ≤ M₁.diffNormOn M₃ γ S + (M₃.diffNormOn M₄ γ S + M₄.diffNormOn M₂ γ S) :=
        add_le_add le_rfl diffNormOn_triangle
      _ = M₃.diffNormOn M₄ γ S := by rw [h₁, h₂', zero_add, add_zero]
  · calc M₃.diffNormOn M₄ γ S ≤ M₃.diffNormOn M₁ γ S + M₁.diffNormOn M₄ γ S := diffNormOn_triangle
      _ ≤ M₃.diffNormOn M₁ γ S + (M₁.diffNormOn M₂ γ S + M₂.diffNormOn M₄ γ S) :=
        add_le_add le_rfl diffNormOn_triangle
      _ = M₁.diffNormOn M₂ γ S := by rw [h₁', h₂, zero_add, add_zero]

end Model

end RegularityStructures

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {C : RenormalisationConstants} {f : SpaceTime → ℝ}

/-- The uniqueness clause of `renormalisedCanonicalModel_existsUnique`, for two moderate Φ⁴₃
models of the same lifted noise and constants: their difference norm vanishes on every set. -/
theorem diffNormOn_eq_zero_of_isModeratePhi43ModelOf (hG1 : Phi43.RenormalisedCanonicalModelStatement)
    (hgrowth : Statements.HasPhi43NoiseGrowth f)
    {Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (h : Statements.IsModeratePhi43ModelOf N κ f C Z) (h' : Statements.IsModeratePhi43ModelOf N κ f C Z')
    (S : Set ParabolicSpace) : Z.diffNormOn Z' (gamma κ) S = 0 := by
  obtain ⟨n, hn, hZ⟩ := h
  obtain ⟨n', hn', hZ'⟩ := h'
  have hnn : n' = n := by
    obtain ⟨z, s, p⟩ := n
    obtain ⟨z', s', p'⟩ := n'
    have : z' = z := (funext hn').trans (funext hn).symm
    subst this
    rfl
  subst hnn
  obtain ⟨Cg, q, hg⟩ := hgrowth
  have hzeta : n'.zeta = fun w : ParabolicSpace => f (w.1, torusProj w.2) := funext hn
  have := (hG1 N κ n' Cg q (fun k hk z => by rw [hzeta]; exact hg k hk z) C).2 Z Z' hZ hZ'
  exact le_antisymm ((Model.diffNormOn_mono_set (Set.subset_univ S)).trans this.le) bot_le

/-- The weighted growth clause of `Statements.IsModeratePhi43ModelOf` for the canonical
renormalised model of every lifted noise of polynomial growth: the analytic input
([Hai14, Proposition 8.27]) that upgrades the renormalised canonical model property of
`canonicalModelOfLift` to the moderate one. -/
def CanonicalLiftGrowth (N : ℕ) (κ : Kappa) : Prop :=
  ∀ (C : RenormalisationConstants) (f : SpaceTime → ℝ), IsSmoothOnSpaceTime f →
    Statements.HasPhi43NoiseGrowth f →
    ∃ (ρ : ParabolicSpace → ℝ) (p B : ℝ),
      RegularisingSemigroup.IsModerateWeight parabolicSemigroup ρ p ∧ 0 ≤ B ∧
        Model.PiBoundGrowth (canonicalModelOfLift N κ C f) (gamma κ) B ρ

theorem isModeratePhi43ModelOf_canonicalModelOfLift (hcan : CanonicalLiftGrowth N κ)
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f) :
    Statements.IsModeratePhi43ModelOf N κ f C (canonicalModelOfLift N κ C f) := by
  obtain ⟨ρ, p, B, hρ, hB, hPi⟩ := hcan C f hf hg
  obtain ⟨h1, h2, h3⟩ := canonicalModelOfLift_isRenormalisedCanonicalModel (N := N) (κ := κ)
    (C := C) hf hg
  exact ⟨canonicalNoiseOfSpaceTime f hf, fun _ => rfl, h1, h2, h3, ρ, p, B, hρ, hB, hPi⟩

end RegularityStructures.Phi43

end
