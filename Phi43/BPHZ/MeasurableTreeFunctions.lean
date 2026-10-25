/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.MeasurableConvolutions
public import Phi43.Structure.RenormalisedExtensionData
import Mathlib.Tactic

/-!
# Joint measurability of the global tree functions of a measurable family of noises

For a family of canonical noises `n : Ω → CanonicalNoise` with `(ω, w) ↦ (n ω).zeta w` measurable,
the global functions `Ψ_ω, I(Ψ)_ω, I(Ψ²)_ω, I(Ψ³)_ω` and every `globalPiBasis τ`,
`renormalisedExtensionGlobalBasis C τ` are jointly measurable in `(ω, w)`.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {κ : Kappa}

/-- The family of noises is jointly measurable. -/
@[expose] def NoiseFamilyMeasurable (n : Ω → CanonicalNoise) : Prop :=
  Measurable fun q : Ω × ParabolicSpace => (n q.1).zeta q.2

section
variable {n : Ω → CanonicalNoise}

theorem measurable_globalPsi_uncurry (hn : NoiseFamilyMeasurable n) :
    Measurable fun q : Ω × ParabolicSpace =>
      (hairerCanonicalData (κ := κ) N (n q.1)).globalPsi q.2 :=
  measurable_hairerConvolution_uncurry N (Y := fun ω => (n ω).zeta) hn
    (fun ω => (contDiff_hairerConvolution N (n ω).smooth).continuous)

theorem measurable_globalIPsi_uncurry (hn : NoiseFamilyMeasurable n) :
    Measurable fun q : Ω × ParabolicSpace =>
      (hairerCanonicalData (κ := κ) N (n q.1)).globalIPsi q.2 :=
  measurable_hairerConvolution_uncurry N (measurable_globalPsi_uncurry (κ := κ) (N := N) hn)
    (fun ω => (contDiff_hairerConvolution N (canonicalGlobalPiBasis_smooth N (κ := κ) (n ω) .psi)).continuous)

theorem measurable_globalIPsiSq_uncurry (hn : NoiseFamilyMeasurable n) :
    Measurable fun q : Ω × ParabolicSpace =>
      (hairerCanonicalData (κ := κ) N (n q.1)).globalIPsiSq q.2 :=
  measurable_hairerConvolution_uncurry N (Y := fun ω => (hairerCanonicalData (κ := κ) N (n ω)).globalPsiSq)
    (by
      have h := measurable_globalPsi_uncurry (κ := κ) (N := N) hn
      exact h.mul h)
    (fun ω => (contDiff_hairerConvolution N
      (canonicalGlobalPiBasis_smooth N (κ := κ) (n ω) .psiSq)).continuous)

theorem measurable_globalIPsiCube_uncurry (hn : NoiseFamilyMeasurable n) :
    Measurable fun q : Ω × ParabolicSpace =>
      (hairerCanonicalData (κ := κ) N (n q.1)).globalIPsiCube q.2 :=
  measurable_hairerConvolution_uncurry N
    (Y := fun ω => (hairerCanonicalData (κ := κ) N (n ω)).globalPsiCube)
    (by
      have h := measurable_globalPsi_uncurry (κ := κ) (N := N) hn
      exact (h.mul h).mul h)
    (fun ω => (contDiff_hairerConvolution N
      (canonicalGlobalPiBasis_smooth N (κ := κ) (n ω) .psiCube)).continuous)

theorem measurable_coord_uncurry (i : Fin 4) :
    Measurable fun q : Ω × ParabolicSpace => parabolicCoords q.2 i := by
  fin_cases i
  · exact measurable_fst.comp measurable_snd
  · exact ((measurable_pi_apply 0).comp measurable_snd).comp measurable_snd
  · exact ((measurable_pi_apply 1).comp measurable_snd).comp measurable_snd
  · exact ((measurable_pi_apply 2).comp measurable_snd).comp measurable_snd

theorem measurable_globalPiBasis_uncurry (hn : NoiseFamilyMeasurable n) (τ : Symbol) :
    Measurable fun q : Ω × ParabolicSpace =>
      (hairerCanonicalData (κ := κ) N (n q.1)).globalPiBasis τ q.2 := by
  have hP := measurable_globalPsi_uncurry (κ := κ) (N := N) hn
  have hI := measurable_globalIPsi_uncurry (κ := κ) (N := N) hn
  have hIS := measurable_globalIPsiSq_uncurry (κ := κ) (N := N) hn
  have hIC := measurable_globalIPsiCube_uncurry (κ := κ) (N := N) hn
  have hc := fun i => measurable_coord_uncurry (Ω := Ω) i
  cases τ with
  | one => exact measurable_const
  | noise => exact hn
  | x0 => exact hc 0
  | x i => exact hc i.succ
  | xMul p =>
      refine Sym2.inductionOn p fun i j => ?_
      exact (hc i.succ).mul (hc j.succ)
  | psi => exact hP
  | iPsi => exact hI
  | psiSq => exact hP.mul hP
  | psiCube => exact (hP.mul hP).mul hP
  | psiX i => exact hP.mul (hc i.succ)
  | psiSqX i => exact (hP.mul hP).mul (hc i.succ)
  | iPsiSq => exact hIS
  | iPsiCube => exact hIC
  | iPsiPsi => exact hI.mul hP
  | iPsiPsiSq => exact hI.mul (hP.mul hP)
  | iPsiSqPsi => exact hIS.mul hP
  | iPsiSqPsiSq => exact hIS.mul (hP.mul hP)
  | iPsiCubePsi => exact hIC.mul hP
  | iPsiCubePsiSq => exact hIC.mul (hP.mul hP)
  | iPsiCubeSq => exact hIC.mul hIC

theorem measurable_renormalisedExtensionGlobalBasis_uncurry (hn : NoiseFamilyMeasurable n)
    (C : RenormalisationConstants) (τ : Symbol) :
    Measurable fun q : Ω × ParabolicSpace =>
      (hairerCanonicalData (κ := κ) N (n q.1)).renormalisedExtensionGlobalBasis C τ q.2 := by
  have hP := measurable_globalPsi_uncurry (κ := κ) (N := N) hn
  have hI := measurable_globalIPsi_uncurry (κ := κ) (N := N) hn
  have hIS := measurable_globalIPsiSq_uncurry (κ := κ) (N := N) hn
  have hIC := measurable_globalIPsiCube_uncurry (κ := κ) (N := N) hn
  have hc := fun i => measurable_coord_uncurry (Ω := Ω) i
  have hpot : Measurable fun q : Ω × ParabolicSpace =>
      (hairerCanonicalData (κ := κ) N (n q.1)).renormalisedExtensionPotential C q.2 :=
    hIC.sub (hI.const_mul _)
  have hsq : Measurable fun q : Ω × ParabolicSpace =>
      (hairerCanonicalData (κ := κ) N (n q.1)).globalPsiSq q.2 - C₁ C := (hP.mul hP).sub_const _
  cases τ with
  | psiSq => exact hsq
  | psiCube => exact ((hP.mul hP).mul hP).sub (hP.const_mul _)
  | psiSqX i => exact hsq.mul (hc i.succ)
  | iPsiCube => exact hpot
  | iPsiPsiSq => exact hI.mul hsq
  | iPsiSqPsiSq => exact (hIS.mul hsq).sub_const _
  | iPsiCubePsi => exact hpot.mul hP
  | iPsiCubePsiSq => exact (hpot.mul hsq).sub (hP.const_mul _)
  | iPsiCubeSq => exact hpot.mul hpot
  | one => exact measurable_globalPiBasis_uncurry (κ := κ) (N := N) hn .one
  | noise => exact measurable_globalPiBasis_uncurry (κ := κ) (N := N) hn .noise
  | x0 => exact measurable_globalPiBasis_uncurry (κ := κ) (N := N) hn .x0
  | x i => exact measurable_globalPiBasis_uncurry (κ := κ) (N := N) hn (.x i)
  | xMul p => exact measurable_globalPiBasis_uncurry (κ := κ) (N := N) hn (.xMul p)
  | psi => exact measurable_globalPiBasis_uncurry (κ := κ) (N := N) hn .psi
  | iPsi => exact measurable_globalPiBasis_uncurry (κ := κ) (N := N) hn .iPsi
  | psiX i => exact measurable_globalPiBasis_uncurry (κ := κ) (N := N) hn (.psiX i)
  | iPsiSq => exact measurable_globalPiBasis_uncurry (κ := κ) (N := N) hn .iPsiSq
  | iPsiPsi => exact measurable_globalPiBasis_uncurry (κ := κ) (N := N) hn .iPsiPsi
  | iPsiSqPsi => exact measurable_globalPiBasis_uncurry (κ := κ) (N := N) hn .iPsiSqPsi

end

end RegularityStructures.Phi43

end
