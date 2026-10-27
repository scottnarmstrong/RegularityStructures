/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AffineProbeComparison
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Identification of the spatial derivative by the same strictly past
probes used to compare affine approximants. -/
public noncomputable section

namespace GlobalPhi43.Local

open Filter RegularityStructures
open scoped Topology

theorem coefficientProbe_hasDerivAt (x : ParabolicSpace) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => coefficientProbe x s i) (0, Pi.single i 1) 0 := by
  have ht := (hasDerivAt_const (0 : ℝ) x.1).sub ((hasDerivAt_id (0 : ℝ)).pow 2)
  have hx := ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : Fin 3 → ℝ)).const_add x.2
  convert ht.prodMk hx using 1 <;> simp [coefficientProbe]
  funext s
  congr 1
  ext j
  by_cases h : j = i <;> simp [h]

theorem verticalProbe_hasDerivAt (x : ParabolicSpace) :
    HasDerivAt (fun s : ℝ => verticalProbe x s) (0 : ParabolicSpace) 0 := by
  have ht := (hasDerivAt_const (0 : ℝ) x.1).sub ((hasDerivAt_id (0 : ℝ)).pow 2)
  convert ht.prodMk (hasDerivAt_const (0 : ℝ) x.2) using 1 <;> simp [verticalProbe, Prod.zero_eq_mk]

/-- The difference of the two past-probe values, divided by their spatial
separation, converges to the spatial derivative. Time derivatives cancel. -/
theorem probe_slope_tendsto (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (D : ParabolicSpace →L[ℝ] ℝ) (hf : HasFDerivAt f D x) (i : Fin 3) :
    Tendsto (fun s : ℝ =>
      (f (coefficientProbe x s i) - f (verticalProbe x s)) / s)
      (𝓝[>] 0) (𝓝 (D (0, Pi.single i 1))) := by
  have hp := hf.comp_hasDerivAt_of_eq 0 (coefficientProbe_hasDerivAt x i)
    (by simp [coefficientProbe])
  have hv := hf.comp_hasDerivAt_of_eq 0 (verticalProbe_hasDerivAt x)
    (by simp [verticalProbe])
  have hg := (hp.sub hv).tendsto_slope_zero_right
  simpa [Function.comp_def, coefficientProbe, verticalProbe, smul_eq_mul, div_eq_mul_inv,
    mul_comm] using hg

end GlobalPhi43.Local
