/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Kernel
public import RegularityStructures.Analysis.Heat.Decomposition.LineIter
public import RegularityStructures.Analysis.Heat.Schauder.TaylorDeriv

/-!
# Derivatives of the heat kernel are polynomials in `t⁻¹, x` times the kernel

`IsGaussPoly f` says that `f` is a polynomial expression in `t⁻¹, x₀, x₁, x₂` (as a function on
`ℝ × ℝ³`).  On `{t > 0}` the directional derivative of such a function is again of this form
(`IsGaussPoly.exists_dirDeriv`), and so is the directional derivative of `heatKernelR4` divided by
`heatKernelR4` (`exists_dirDeriv_heatKernelR4`).  Consequently every iterated derivative of the heat
kernel is `P · heatKernelR4` on `{t > 0}` with `P` such a polynomial (`exists_lineIter_heatKernelR4`).
-/

@[expose] public section

namespace RegularityStructures

/-- Polynomial expressions in `t⁻¹, x₀, x₁, x₂` on `ℝ × ℝ³`. -/
inductive IsGaussPoly : (ParabolicSpace → ℝ) → Prop
  | const (c : ℝ) : IsGaussPoly fun _ => c
  | invT : IsGaussPoly fun z => z.1⁻¹
  | coord (i : Fin 3) : IsGaussPoly fun z => z.2 i
  | add {f g : ParabolicSpace → ℝ} : IsGaussPoly f → IsGaussPoly g →
      IsGaussPoly fun z => f z + g z
  | mul {f g : ParabolicSpace → ℝ} : IsGaussPoly f → IsGaussPoly g →
      IsGaussPoly fun z => f z * g z

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

theorem IsGaussPoly.sum {s : Finset (Fin 3)} {f : Fin 3 → ParabolicSpace → ℝ}
    (h : ∀ i ∈ s, IsGaussPoly (f i)) : IsGaussPoly fun z => ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsGaussPoly.const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsGaussPoly.contDiffAt {f : ParabolicSpace → ℝ} (hf : IsGaussPoly f)
    {z : ParabolicSpace} (hz : 0 < z.1) : ContDiffAt ℝ ∞ f z := by
  induction hf with
  | const c => exact contDiffAt_const
  | invT => exact contDiffAt_fst.inv hz.ne'
  | coord i => exact ((contDiff_apply ℝ ℝ i).comp contDiff_snd).contDiffAt
  | add _ _ ih1 ih2 => exact ih1.add ih2
  | mul _ _ ih1 ih2 => exact ih1.mul ih2

theorem hasFDerivAt_invT (z : ParabolicSpace) (hz : 0 < z.1) (d : ParabolicSpace) :
    fderiv ℝ (fun w : ParabolicSpace => w.1⁻¹) z d = -(d.1 * (z.1⁻¹ * z.1⁻¹)) := by
  have h := (hasDerivAt_inv hz.ne').comp_hasFDerivAt z (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  rw [show (fun w : ParabolicSpace => w.1⁻¹) = (fun x : ℝ => x⁻¹) ∘ Prod.fst from rfl,
    h.fderiv]
  simp
  ring

theorem IsGaussPoly.exists_dirDeriv {f : ParabolicSpace → ℝ} (hf : IsGaussPoly f)
    (d : ParabolicSpace) :
    ∃ g, IsGaussPoly g ∧ ∀ z : ParabolicSpace, 0 < z.1 → dirDeriv d f z = g z := by
  induction hf with
  | const c => exact ⟨fun _ => 0, IsGaussPoly.const 0, fun z _ => by simp [dirDeriv]⟩
  | invT =>
    refine ⟨fun z => (-d.1) * (z.1⁻¹ * z.1⁻¹), ((IsGaussPoly.const _).mul
      (IsGaussPoly.invT.mul IsGaussPoly.invT)), fun z hz => ?_⟩
    simp only [dirDeriv, hasFDerivAt_invT z hz d]
    ring
  | coord i =>
    refine ⟨fun _ => d.2 i, IsGaussPoly.const _, fun z _ => ?_⟩
    have h : HasFDerivAt (fun w : ParabolicSpace => w.2 i)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp
          (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))) z :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp z
        (hasFDerivAt_snd (𝕜 := ℝ) (p := z)))
    simp [dirDeriv, h.fderiv]
  | @add f g hf hg ihf ihg =>
    obtain ⟨a, ha, hfa⟩ := ihf
    obtain ⟨b, hb, hgb⟩ := ihg
    refine ⟨fun z => a z + b z, ha.add hb, fun z hz => ?_⟩
    have h1 := (hf.contDiffAt hz).differentiableAt (by simp)
    have h2 := (hg.contDiffAt hz).differentiableAt (by simp)
    simp only [dirDeriv] at hfa hgb ⊢
    rw [fderiv_fun_add h1 h2]
    simp only [add_apply]
    rw [hfa z hz, hgb z hz]
  | @mul f g hf hg ihf ihg =>
    obtain ⟨a, ha, hfa⟩ := ihf
    obtain ⟨b, hb, hgb⟩ := ihg
    refine ⟨fun z => f z * b z + a z * g z, (hf.mul hb).add (ha.mul hg), fun z hz => ?_⟩
    have h1 := (hf.contDiffAt hz).differentiableAt (by simp)
    have h2 := (hg.contDiffAt hz).differentiableAt (by simp)
    simp only [dirDeriv] at hfa hgb ⊢
    rw [fderiv_fun_mul h1 h2]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [hfa z hz, hgb z hz]
    ring

end RegularityStructures

end
