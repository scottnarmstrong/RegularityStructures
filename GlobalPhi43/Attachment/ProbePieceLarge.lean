module

public import GlobalPhi43.Attachment.ProbePieceGeometry
public import GlobalPhi43.Attachment.ProbeLargeAnnulus

/-! One large-scale full-jet allowance for all physical pieces, including
the core. Constants are fixed before the physical scale and annular index. -/

@[expose] public noncomputable section

open RegularityStructures
open scoped ContDiff

namespace GlobalPhi43.Attachment

theorem probeGaussianPiece_large_C4 : ∃ D : ℝ, 0 ≤ D ∧
    ∀ r : ℝ, 0 < r → ∀ n : ℕ, 1 ≤ probePieceFactor n*r →
    ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k (probeGaussianPiece r n) z‖ ≤
      D*((probePieceFactor n)⁻¹)^5 := by
  obtain ⟨D, hD, hb⟩ := probePieceTest_C4
  refine ⟨D, hD, ?_⟩
  intro r hr n hT k hk z
  have hc0 : 0 < probePieceFactor n := lt_of_lt_of_le (by norm_num) (probePieceFactor_ge_two _)
  have hT0 := mul_pos hc0 hr
  have hi : (probePieceFactor n*r)⁻¹ ≤ 1 := (inv_le_one₀ hT0).mpr hT
  let L := probeNegativeDilate ((probePieceFactor n*r)⁻¹)
  have hL : ‖L‖ ≤ 1 := probeNegativeDilate_norm_small (inv_nonneg.mpr hT0.le) hi
  have hA : 0 ≤ D*((probePieceFactor n)⁻¹)^5 := by positivity
  have hh := probe_jet_comp_bound (probePieceTest_smooth n) L k z hA hL (hb n k hk (L z))
  have he : probeGaussianPiece r n = ((probePieceFactor n*r)⁻¹)^5 • (probePieceTest n ∘ L) := by
    funext v
    exact probeGaussianPiece_formula hr n v
  rw [he, iteratedFDeriv_const_smul_apply
    (((probePieceTest_smooth n).comp L.contDiff).of_le
      (by exact_mod_cast le_top)).contDiffAt, norm_smul,
    Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hT0.le) _)]
  have hp : ((probePieceFactor n*r)⁻¹)^5 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr hT0.le) hi
  calc _ ≤ ((probePieceFactor n*r)⁻¹)^5 * (D*((probePieceFactor n)⁻¹)^5) :=
      mul_le_mul_of_nonneg_left (by simpa only [one_pow, mul_one] using hh)
        (pow_nonneg (inv_nonneg.mpr hT0.le) _)
    _ ≤ D*((probePieceFactor n)⁻¹)^5 := mul_le_of_le_one_left hA hp

theorem probeGaussianPiece_folded_C4 : ∃ D : ℝ, 0 ≤ D ∧
    ∀ r : ℝ, 0 < r → ∀ n : ℕ, 1 ≤ probePieceFactor n*r →
    ∀ m : Fin 3 → ℤ, ∀ k ≤ 4, ∀ z,
      ‖iteratedFDeriv ℝ k (probeFoldedProfile (probeGaussianPiece r n) m) z‖ ≤
        D*((probePieceFactor n)⁻¹)^5 := by
  obtain ⟨A, hA, ha⟩ := probeGaussianPiece_large_C4
  obtain ⟨B, hB, hb⟩ := probeFoldedProfile_C4
  refine ⟨B*A, mul_nonneg hB hA, ?_⟩
  intro r hr n hT m k hk z
  have hc : 0 ≤ probePieceFactor n := le_trans (by norm_num) (probePieceFactor_ge_two n)
  exact (hb _ (probeGaussianPiece_smooth hr n) _ (by positivity)
    (ha r hr n hT) m k hk z).trans_eq (mul_assoc _ _ _).symm

end GlobalPhi43.Attachment
