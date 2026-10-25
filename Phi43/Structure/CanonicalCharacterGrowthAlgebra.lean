/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalDerivativeGrowthAlgebra
public import Phi43.Structure.CanonicalGammaActionBounds
import RegularityStructures.Abstract.Integration.Theorem512.Helpers

/-!
# Polynomial growth through the finite character action

Hairer [Hai14, Proposition 8.27]. The multiplicatively defined finite
action has a polynomial coefficient bound in its primitive parameters.
This transports proved primitive growth to coefficient growth, without
postulating analytic bounds on a canonical model.
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

private theorem const_growth (c : ℝ) : PolyBounded (fun _ : ParabolicSpace => c) :=
  ⟨measurable_const, |c|, 0, fun _ => by simp⟩

private theorem abs_growth {f : ParabolicSpace → ℝ} (hf : PolyBounded f) :
    PolyBounded (fun z => |f z|) := by
  simpa only [Real.norm_eq_abs] using canonicalPolyBounded_norm hf

private theorem pow_growth {f : ParabolicSpace → ℝ} (hf : PolyBounded f) (n : ℕ) :
    PolyBounded (fun z => f z ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using const_growth 1
  | succ n ih =>
      simpa only [pow_succ, Pi.mul_apply] using! canonicalPolyBounded_mul ih hf

/-- Polynomial growth of primitive characters controls every coefficient
of the actual finite action. Measurability is explicit for this algebraic helper. -/
theorem polyBounded_structureGroup_coeff (κ : Kappa) (g : ParabolicSpace → G)
    (hx : ∀ i, PolyBounded (fun z => (g z).shift i))
    (hp : PolyBounded (fun z => (g z).cPsi))
    (hpg : ∀ i, PolyBounded (fun z => (g z).cPsiGrad i))
    (hs : PolyBounded (fun z => (g z).cPsiSq))
    (hc : PolyBounded (fun z => (g z).cPsiCube)) (τ σ : Symbol)
    (hm : Measurable (fun z => structureGroupMap (g z) (basis τ) σ)) :
    PolyBounded (fun z => structureGroupMap (g z) (basis τ) σ) := by
  let H : ParabolicSpace → ℝ := fun z =>
    1 + (∑ i : Fin 4, |(g z).shift i|) + |(g z).cPsi| +
      (∑ i : Fin 3, |(g z).cPsiGrad i|) + |(g z).cPsiSq| + |(g z).cPsiCube|
  have hsumx : PolyBounded (fun z => ∑ i : Fin 4, |(g z).shift i|) := by
    simpa only [one_mul] using PolyBounded.finsetSum Finset.univ
      (fun _ : Fin 4 => (1 : ℝ)) _ (fun i _ => abs_growth (hx i))
  have hsumpg : PolyBounded (fun z => ∑ i : Fin 3, |(g z).cPsiGrad i|) := by
    simpa only [one_mul] using PolyBounded.finsetSum Finset.univ
      (fun _ : Fin 3 => (1 : ℝ)) _ (fun i _ => abs_growth (hpg i))
  have hH : PolyBounded H :=
    ((((const_growth 1).add hsumx).add (abs_growth hp)).add hsumpg).add
      (abs_growth hs) |>.add (abs_growth hc)
  have hH0 (z : ParabolicSpace) : 0 ≤ H z := by
    dsimp [H]
    positivity
  have hxH (i : Fin 4) (z : ParabolicSpace) : |(g z).shift i| ≤ H z := by
    have hh := Finset.single_le_sum (f := fun i : Fin 4 => |(g z).shift i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have hg0 := Finset.sum_nonneg (s := Finset.univ)
      (f := fun i : Fin 3 => |(g z).cPsiGrad i|) (fun _ _ => abs_nonneg _)
    dsimp [H]
    linarith [abs_nonneg (g z).cPsi, abs_nonneg (g z).cPsiSq, abs_nonneg (g z).cPsiCube]
  have hpgH (i : Fin 3) (z : ParabolicSpace) : |(g z).cPsiGrad i| ≤ H z := by
    have hh := Finset.single_le_sum (f := fun i : Fin 3 => |(g z).cPsiGrad i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have hx0 := Finset.sum_nonneg (s := Finset.univ)
      (f := fun i : Fin 4 => |(g z).shift i|) (fun _ _ => abs_nonneg _)
    dsimp [H]
    linarith [abs_nonneg (g z).cPsi, abs_nonneg (g z).cPsiSq, abs_nonneg (g z).cPsiCube]
  have hpH (z : ParabolicSpace) : |(g z).cPsi| ≤ H z := by
    have hx0 : 0 ≤ ∑ i : Fin 4, |(g z).shift i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hg0 : 0 ≤ ∑ i : Fin 3, |(g z).cPsiGrad i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    dsimp [H]
    linarith [abs_nonneg (g z).cPsiSq, abs_nonneg (g z).cPsiCube]
  have hsH (z : ParabolicSpace) : |(g z).cPsiSq| ≤ H z := by
    have hx0 : 0 ≤ ∑ i : Fin 4, |(g z).shift i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hg0 : 0 ≤ ∑ i : Fin 3, |(g z).cPsiGrad i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    dsimp [H]
    linarith [abs_nonneg (g z).cPsi, abs_nonneg (g z).cPsiCube]
  have hcH (z : ParabolicSpace) : |(g z).cPsiCube| ≤ H z := by
    have hx0 : 0 ≤ ∑ i : Fin 4, |(g z).shift i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hg0 : 0 ≤ ∑ i : Fin 3, |(g z).cPsiGrad i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    dsimp [H]
    linarith [abs_nonneg (g z).cPsi, abs_nonneg (g z).cPsiSq]
  let P : ParabolicSpace → ℝ := fun z => 1 + 4 * H z
  let n : ℝ := (Fintype.card Symbol : ℝ) ^ 2
  let Q : ParabolicSpace → ℝ := fun z => P z + n * P z ^ 2 + n ^ 2 * P z ^ 3
  have hP : PolyBounded P := (const_growth 1).add (hH.const_mul 4)
  have hQ : PolyBounded Q :=
    (hP.add ((pow_growth hP 2).const_mul n)).add ((pow_growth hP 3).const_mul (n ^ 2))
  apply canonicalPolyBounded_of_domination hm hQ
  intro z
  have hb := gammaStructureBasis_weighted_bound κ (g z) (d := 1) (A := H z)
    (by norm_num) (hH0 z)
    (fun i => by simpa only [Real.one_rpow, mul_one] using hxH i z)
    (by simpa only [Real.one_rpow, mul_one] using hpH z)
    (fun i => by simpa only [Real.one_rpow, mul_one] using hpgH i z)
    (by simpa only [Real.one_rpow, mul_one] using hsH z)
    (by simpa only [Real.one_rpow, mul_one] using hcH z) τ σ
  have hb' : |structureGroupMap (g z) (basis τ) σ| ≤ Q z := by
    simpa only [structureGroupMap_basis, Real.one_rpow, mul_one] using hb
  exact hb'.trans (le_abs_self _)

end RegularityStructures.Phi43

end
