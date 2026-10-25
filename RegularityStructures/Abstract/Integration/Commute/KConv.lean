/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Decomposition
public import RegularityStructures.Analysis.Heat.Schauder.TaylorPairing

/-!
# The function `K ∗ Λ` for a distribution of local order above `-2`

For a `Q`-family `Λ` (for instance `Π_x e_i`) all of whose local exponents exceed `-2`, the
convolution `K ∗ Λ` with the heat kernel `K = ∑_n K_n` (`K_n = annShell N n`) is a function

  `kConv N Λ z = ∑_n ⟨Λ, K_n(z - ·)⟩`.

The series converges absolutely by the small-scale bound
`|⟨Λ, K_n(z - ·)⟩| ≲ C ∑_{a ∈ A} 2^{-(a+2) n} (2^{-n} + d(z, x))^{α - a}` (`abs_pairing_scaledShell_centre_le`,
[Hai14, proof of Lemma 5.19]), and `|kConv N Λ z| ≲ C (1 + d(z, x))^p`
(`abs_kConv_le`), so `kConv N Λ` has polynomial growth. Input of [Hai14, Lemma 5.16].
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The geometric constant `∑_a κ_a / (1 - 2^{-(a+2)})`. -/
def kConvRate (A : Finset ℝ) : ℝ :=
  ∑ a ∈ A, pairingWeight a * (1 - (2 : ℝ) ^ (-(a + 2)))⁻¹

end RegularityStructures

end

public section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace RegularityStructures

/-- Geometric rate `2^{-(a+2)}` of the dyadic decay. -/
theorem two_rpow_neg_lt_one {a : ℝ} (ha : -2 < a) : (2 : ℝ) ^ (-(a + 2)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem two_rpow_neg_pow (a : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (-(a + 2) * n) = ((2 : ℝ) ^ (-(a + 2))) ^ n :=
  Real.rpow_mul_natCast (by norm_num) _ _

theorem kConvRate_nonneg {A : Finset ℝ} (hA : ∀ a ∈ A, -2 < a) : 0 ≤ kConvRate A :=
  Finset.sum_nonneg fun a ha => mul_nonneg (pairingWeight_nonneg (by linarith [hA a ha]))
    (inv_nonneg.2 (sub_nonneg.2 (two_rpow_neg_lt_one (hA a ha)).le))

theorem hasSum_annShell_bound (A : Finset ℝ) (hA : ∀ a ∈ A, -2 < a) (B : ℝ) :
    HasSum (fun n : ℕ => B * ∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2))) ^ n)
      (B * kConvRate A) := by
  refine HasSum.mul_left B ?_
  have : HasSum (fun n : ℕ => ∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2))) ^ n)
      (∑ a ∈ A, pairingWeight a * (1 - (2 : ℝ) ^ (-(a + 2)))⁻¹) :=
    hasSum_sum fun a ha => (hasSum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _)
      (two_rpow_neg_lt_one (hA a ha))).mul_left _
  exact this

end RegularityStructures

end
