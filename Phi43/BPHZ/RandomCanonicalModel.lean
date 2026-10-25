/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.MeasurableCharacters
public import Phi43.BPHZ.RandomCanonicalContinuity
public import RegularityStructures.Statements.Defs.IsContinuousRandomModelOn
import Mathlib.Tactic

/-!
# The canonical models of a regularised noise form a continuous random model

For a family of smooth noises `ξ ω` with polynomial growth, jointly measurable in `ω` (as for a
regularised noise), the family of canonical models `ω ↦ canonicalModelOfLift N κ C (ξ ω)` satisfies
the predicate `Statements.IsContinuousRandomModelOn` for EVERY compact (indeed every) set `S` and
every symbol (`isContinuousRandomModelOn_canonicalModelOfLift`):

* `ω ↦ (Q_t Π_x e_i)(x)` and `ω ↦ (Γ_{yx} e_i)(j)` are measurable;
* `(t, x) ↦ (Q_t Π_x e_i)(x)` is continuous on `t > 0` and `(x, y) ↦ (Γ_{yx} e_i)(j)` is continuous
  for each `ω`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {C : RenormalisationConstants} {f : SpaceTime → ℝ}

theorem canonicalModelOfLift_eq (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f) :
    ∃ (Cg : ℝ) (q : ℕ) (hg' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
        ‖iteratedFDeriv ℝ k (canonicalNoiseOfSpaceTime f hf).zeta z‖ ≤
          Cg * (1 + parabolicNorm z) ^ q),
      canonicalModelOfLift N κ C f =
        canonicalRenormalisedModel N κ (canonicalNoiseOfSpaceTime f hf) Cg q hg' C := by
  unfold canonicalModelOfLift
  split_ifs with h
  · exact ⟨Classical.choose h.2, Classical.choose (Classical.choose_spec h.2),
      Classical.choose_spec (Classical.choose_spec h.2), rfl⟩
  · exact absurd ⟨hf, hg⟩ h

/-- Joint measurability of a regularised noise family. -/
theorem measurable_noiseFamily {Ω : Type*} [MeasurableSpace Ω] {ξ : Ω → SpaceTime → ℝ}
    (hmeas : ∀ z, Measurable fun ω => ξ ω z) (hsm : ∀ ω, IsSmoothOnSpaceTime (ξ ω)) :
    NoiseFamilyMeasurable (fun ω => canonicalNoiseOfSpaceTime (ξ ω) (hsm ω)) := by
  have h : Measurable (Function.uncurry fun (z : SpaceTime) (ω : Ω) => ξ ω z) :=
    measurable_uncurry_of_continuous_of_measurable (u := fun (z : SpaceTime) (ω : Ω) => ξ ω z)
      (fun ω => IsSmoothOnSpaceTime.continuous (hsm ω)) hmeas
  have hproj : Measurable fun w : ParabolicSpace => spaceTimeProj w :=
    measurable_fst.prodMk ((continuous_pi fun i =>
      (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)).measurable.comp measurable_snd)
  exact h.comp (hproj.comp measurable_snd |>.prodMk measurable_fst)

theorem isContinuousRandomModelOn_canonicalModelOfLift {Ω : Type*} [MeasurableSpace Ω]
    {ξ : Ω → SpaceTime → ℝ} (hmeas : ∀ z, Measurable fun ω => ξ ω z)
    (hsm : ∀ ω, IsSmoothOnSpaceTime (ξ ω)) (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω))
    (S : Set ParabolicSpace) :
    RegularityStructures.IsContinuousRandomModelOn (fun ω => canonicalModelOfLift N κ C (ξ ω)) S := by
  have hn := measurable_noiseFamily hmeas hsm
  refine ⟨fun i x t ht => ?_, fun i j x y => ?_, fun ω i => ?_, fun ω i j => ?_⟩
  · have e : ∀ ω, (canonicalModelOfLift N κ C (ξ ω)).regPi x (Pi.single i (1 : ℝ) : Symbol → ℝ) t x =
        ∑ τ : Symbol, structureGroupMap ((hairerCanonicalData (κ := κ) N
          (canonicalNoiseOfSpaceTime (ξ ω) (hsm ω))).renormalisedExtensionCharacter C x)
          (basis i) τ * parabolicSemigroup.apply t
          ((hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) (hsm ω))).renormalisedExtensionGlobalBasis
            C τ) x := fun ω => by
      obtain ⟨Cg, q, hg', hE⟩ := canonicalModelOfLift_eq (N := N) (κ := κ) (C := C) (hsm ω) (hgr ω)
      rw [hE]
      exact regPi_single_canonicalRenormalisedModel_eq_sum N κ _ Cg q hg' C x i ht x
    simp_rw [e]
    refine Finset.measurable_sum _ fun τ _ => ?_
    refine (measurable_extensionCharacter_coeff hn C x i τ).mul ?_
    have hB := measurable_renormalisedExtensionGlobalBasis_uncurry (κ := κ) (N := N) hn C τ
    exact ((((measurable_parabolicKernel t).comp (measurable_const.sub measurable_snd)).mul
      hB).stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ParabolicSpace))).measurable
  · have e : ∀ ω, (canonicalModelOfLift N κ C (ξ ω)).gammaMap y x (Pi.single i (1 : ℝ) : Symbol → ℝ) j =
        (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) (hsm ω))).renormalisedExtensionGamma
          C y x (basis i) j := fun ω => by
      obtain ⟨Cg, q, hg', hE⟩ := canonicalModelOfLift_eq (N := N) (κ := κ) (C := C) (hsm ω) (hgr ω)
      rw [hE]
      change (phi43StructureGroupElement _ : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) (Pi.single i 1) j = _
      rw [phi43StructureGroupElement_apply_single]
      rfl
    simp_rw [e]
    exact measurable_extensionGamma_coeff hn C y x i j
  · obtain ⟨Cg, q, hg', hE⟩ := canonicalModelOfLift_eq (N := N) (κ := κ) (C := C) (hsm ω) (hgr ω)
    simp only [hE]
    exact (continuousOn_regPi_diag_canonicalRenormalisedModel N κ _ Cg q hg' C i).mono
      (Set.prod_mono (fun t ht => ht.1) (Set.subset_univ _))
  · obtain ⟨Cg, q, hg', hE⟩ := canonicalModelOfLift_eq (N := N) (κ := κ) (C := C) (hsm ω) (hgr ω)
    simp only [hE]
    exact (continuous_gammaMap_entry_canonicalRenormalisedModel N κ _ Cg q hg' C i j).continuousOn

end RegularityStructures.Phi43

end
