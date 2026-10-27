module

public import GlobalPhi43.Compactness.Norm

@[expose] public noncomputable section

open Set RegularityStructures
open scoped ENNReal

namespace GlobalPhi43

/-- A weighted point probe is bounded by the source completion norm. -/
theorem weighted_heatAt_le_norm (η : NegExponent) (s : Ioc (0 : ℝ) 1)
    (x : Torus3) (z : HolderBesov η) :
    (s : ℝ) ^ (-(η : ℝ) / 2) * |heatAt η s x z| ≤ ‖z‖ := by
  have he : ENNReal.ofReal ((s : ℝ) ^ (-(η : ℝ) / 2)) * ‖heatAt η s x z‖ₑ ≤
      extNorm η η z :=
    (mul_le_mul_right (le_iSup (fun y => ‖heatAt η s y z‖ₑ) x) _).trans (le_iSup (fun r : Ioc (0 : ℝ) 1 =>
      ENNReal.ofReal ((r : ℝ) ^ (-(η : ℝ) / 2)) * ⨆ y, ‖heatAt η r y z‖ₑ) s)
  have ht := ENNReal.toReal_mono enorm_ne_top (he.trans (extNorm_self_le η z))
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg s.2.1.le _),
    toReal_enorm, Real.norm_eq_abs] using ht

/-- The elementary weighted geometric-mean identity behind heat-probe interpolation. -/
private theorem weighted_probe_interpolation {s a η β γ θ : ℝ}
    (hs : 0 < s) (ha : 0 ≤ a) (hθ : 0 < θ) (hθ' : θ < 1)
    (hβ : β = θ * η + (1 - θ) * γ) :
    s ^ (-β / 2) * a =
      (s ^ (-η / 2) * a) ^ θ * (s ^ (-γ / 2) * a) ^ (1 - θ) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hs.le _) ha,
    Real.mul_rpow (Real.rpow_nonneg hs.le _) ha,
    ← Real.rpow_mul hs.le, ← Real.rpow_mul hs.le]
  have he : -β / 2 = -η / 2 * θ + -γ / 2 * (1 - θ) := by rw [hβ]; ring
  rw [he, Real.rpow_add hs]
  have hpow : a ^ θ * a ^ (1 - θ) = a := by
    rw [← Real.rpow_add_of_nonneg ha hθ.le (by linarith), add_sub_cancel, Real.rpow_one]
  calc
    s ^ (-η / 2 * θ) * s ^ (-γ / 2 * (1 - θ)) * a =
        s ^ (-η / 2 * θ) * s ^ (-γ / 2 * (1 - θ)) * (a ^ θ * a ^ (1 - θ)) := by rw [hpow]
    _ = _ := by ring

/-- Heat-probe interpolation on continuous functions, with the weighted geometric-mean exponent. -/
theorem norm_toHolderBesov_interpolation (η β γ : NegExponent)
    (hηβ : (η : ℝ) < β) (hβγ : (β : ℝ) < γ) (f : C(Torus3, ℝ)) :
    ‖toHolderBesov β f‖ ≤
      ‖toHolderBesov η f‖ ^ (((γ : ℝ) - β) / ((γ : ℝ) - η)) *
      ‖toHolderBesov γ f‖ ^ (1 - (((γ : ℝ) - β) / ((γ : ℝ) - η))) := by
  let θ : ℝ := ((γ : ℝ) - β) / ((γ : ℝ) - η)
  have hd : 0 < (γ : ℝ) - η := by linarith
  have hθ : 0 < θ := div_pos (by linarith) hd
  have hθ' : θ < 1 := (div_lt_one hd).mpr (by linarith)
  have hβ : (β : ℝ) = θ * η + (1 - θ) * γ := by
    dsimp [θ]
    field_simp
    ring
  let R := ‖toHolderBesov η f‖ ^ θ * ‖toHolderBesov γ f‖ ^ (1 - θ)
  have hR : 0 ≤ R := mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (norm_nonneg _) _)
  have hbound : holderBesovENorm β f ≤ ENNReal.ofReal R := by
    refine iSup₂_le fun s hs => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun x => ?_
    have hη := weighted_heatAt_le_norm η ⟨s, hs⟩ x (toHolderBesov η f)
    have hγ := weighted_heatAt_le_norm γ ⟨s, hs⟩ x (toHolderBesov γ f)
    rw [heatAt_toHolderBesov] at hη hγ
    have hp := weighted_probe_interpolation hs.1 (abs_nonneg (heatSemigroup s f x)) hθ hθ' hβ
    have hh : s ^ (-(β : ℝ) / 2) * |heatSemigroup s f x| ≤ R := by
      rw [hp]
      exact mul_le_mul (Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hs.1.le _) (abs_nonneg _)) hη hθ.le)
        (Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hs.1.le _) (abs_nonneg _)) hγ (by linarith))
        (Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hs.1.le _) (abs_nonneg _)) _)
        (Real.rpow_nonneg (norm_nonneg _) _)
    rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _)]
    exact ENNReal.ofReal_le_ofReal hh
  rw [norm_toHolderBesov]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hR)

end GlobalPhi43
