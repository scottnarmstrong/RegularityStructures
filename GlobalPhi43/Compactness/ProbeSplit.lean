module

public import GlobalPhi43.Compactness.Interpolation
public import GlobalPhi43.Compactness.Smoothing

@[expose] public noncomputable section

open Set RegularityStructures RegularityStructures.PDE RegularityStructures.Datum
open scoped ENNReal

namespace GlobalPhi43

/-- Splitting the probe times bounds the weak norm by a small-scale term and one heat probe. -/
theorem norm_toHolderBesov_le_max_heatOp (η γ : NegExponent) (hηγ : (η : ℝ) < γ)
    {δ M : ℝ} (hδ : 0 < δ)
    (f : C(Torus3, ℝ)) (hf : ‖toHolderBesov γ f‖ ≤ M) :
    ‖toHolderBesov η f‖ ≤ max (δ ^ (((γ : ℝ) - η) / 2) * M) ‖heatOp δ f‖ := by
  let R := max (δ ^ (((γ : ℝ) - η) / 2) * M) ‖heatOp δ f‖
  have hR : 0 ≤ R := (norm_nonneg _).trans (le_max_right _ _)
  have hbound : holderBesovENorm η f ≤ ENNReal.ofReal R := by
    refine iSup₂_le fun s hs => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun x => ?_
    have hh : s ^ (-(η : ℝ) / 2) * |heatSemigroup s f x| ≤ R := by
      by_cases hsd : s ≤ δ
      · have hg := weighted_heatAt_le_norm γ ⟨s, hs⟩ x (toHolderBesov γ f)
        rw [heatAt_toHolderBesov] at hg
        have he : s ^ (-(η : ℝ) / 2) =
            s ^ (((γ : ℝ) - η) / 2) * s ^ (-(γ : ℝ) / 2) := by
          rw [← Real.rpow_add hs.1]
          congr 1
          ring
        rw [he, mul_assoc]
        exact (mul_le_mul (Real.rpow_le_rpow hs.1.le hsd (by linarith)) (hg.trans hf)
          (mul_nonneg (Real.rpow_nonneg hs.1.le _) (abs_nonneg _))
          (Real.rpow_nonneg hδ.le _)).trans (le_max_left _ _)
      · have he : heatOp s f = heatOp (s - δ) (heatOp δ f) := by
          rw [heatOp_heatOp hδ.le (by linarith : 0 ≤ s - δ), add_sub_cancel]
        have hb : |heatSemigroup s f x| ≤ ‖heatOp δ f‖ := by
          rw [← heatOp_eq_heatSemigroup hs.1]
          exact ((heatOp s f).norm_coe_le_norm x).trans (he ▸ norm_heatOp_le _ _)
        have hw : s ^ (-(η : ℝ) / 2) ≤ 1 := Real.rpow_le_one hs.1.le hs.2 (by linarith [η.2])
        exact (mul_le_mul hw hb (abs_nonneg _) (by norm_num)).trans (by simpa only [one_mul] using le_max_right (δ ^ (((γ : ℝ) - η) / 2) * M) ‖heatOp δ f‖)
    rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _)]
    exact ENNReal.ofReal_le_ofReal hh
  rw [norm_toHolderBesov]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hR)

end GlobalPhi43
