/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration

/-!
# Hairer's map `J(x)` as a linear map into the abstract polynomials

[Hai14, (5.11)]: for `a ∈ T_α`,
`J(x) a = ∑_{|k|_𝔰 < α + β} X^k / k! · ∫ D₁^k K(x, z) (Π_x a)(dz)`, β = 2. With the dyadic
decomposition `K = ∑_n K_n` of the heat kernel (`annShell N n`) the integral is
`∑_n ⟨Π_x a, D^k K_n(x − ·)⟩ = jCoeff M N x i k` for `a = e_i`. Given a polynomial sector
`P : PolynomialSector 𝒯 N'` (basis vectors `X^k`, `|k|_𝔰 < N'`), `jMap` is the linear map with

  `J(x) e_i = ∑_{k : |k|_𝔰 < min(deg i + 2, N')} jCoeff M N x i k / k! · X^k`.

`jMap_mem_subspace`: `J(x)` takes values in `T̄`. The coefficients are finite and bounded
(`abs_jCoeff_le`) when `|k|_𝔰 < deg i + 2` and all homogeneities below `γ` exceed `-4`.

Source: [Hai14] = arXiv:1303.5113v4, (5.11).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The multi-index factorial `k! = ∏ᵢ kᵢ!`. -/
def multiFactorial (k : Fin 4 →₀ ℕ) : ℕ := ∏ i, (k i).factorial

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem multiFactorial_pos (k : Fin 4 →₀ ℕ) : 0 < multiFactorial k :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem single_emb_mem_subspace {N' : ℕ} (P : PolynomialSector 𝒯 N') (k : PolyIndex N') :
    (Pi.single (P.emb k) 1 : ι → ℝ) ∈ P.subspace := by
  intro j hj
  have : j ≠ P.emb k := fun h => hj ⟨k, h.symm⟩
  simp [this]

end RegularityStructures

end
