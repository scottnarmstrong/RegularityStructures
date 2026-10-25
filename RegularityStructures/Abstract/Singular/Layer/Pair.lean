/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.Classify
public import RegularityStructures.Abstract.Singular.LatticeApprox

/-!
# Bound for one term of the telescoping sum

For `r = 2^{-n}`, `32 r ≤ λ ≤ 1`, `ψ = φ^λ_x` vanishing after time `T`, and lattice indices `k, l`,
the term `⟨Π_{z'} (f(z') - Γ_{z'z} f(z)), ψ χ_{n+1,k} χ_{n,l}⟩`, `z' = z_{n+1,k}`, `z = z_{n,l}`, is
bounded by

* `0` unless `l` lies in the box `latticeBox n z' (144 r²) (12 r)`;
* otherwise by the sum of a *regular* part, present if `z'_0 > 0`, of size
  `C₁ (max 1 CGam * CPi) Cf λ^{-5} r^{5+γ'} G(k_0)` with `G` the weight bound `2^θ(1 + u^{-θ})`, `u = 2^{-(n+1)}√k_0`,
  `θ = max (γ' - η) 0`, and a *near* part, present if `k` lies in the box `NB` of indices with
  `z'_0 ∈ (-144 r², 288 r²]`, of size `C₂ (max 1 CGam * CPi) Cf λ^{-5} r^{5 + α ∧ η}`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Layer

/-- The weight bound `2^θ (1 + (2^{-m} √j)^{-θ})`. -/
def weightBound (θ : ℝ) (m : ℕ) (j : ℤ) : ℝ :=
  (2 : ℝ) ^ θ * (1 + (((2 : ℝ) ^ m)⁻¹ * Real.sqrt (j : ℝ)) ^ (-θ))

end RegularityStructures.Layer

end

public section

open MeasureTheory Filter Set

namespace RegularityStructures.Layer

theorem weightBound_nonneg (θ : ℝ) (m : ℕ) (j : ℤ) : 0 ≤ weightBound θ m j := by
  unfold weightBound
  have : 0 ≤ (((2 : ℝ) ^ m)⁻¹ * Real.sqrt (j : ℝ)) ^ (-θ) :=
    Real.rpow_nonneg (by positivity) _
  positivity

theorem sqrt_latticePoint_fst {m : ℕ} {k : LatticeIndex} (h : 0 < (latticePoint m k).1) :
    Real.sqrt |(latticePoint m k).1| = ((2 : ℝ) ^ m)⁻¹ * Real.sqrt (k.1 : ℝ) := by
  rw [abs_of_pos h, latticePoint_fst, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

end RegularityStructures.Layer

end
