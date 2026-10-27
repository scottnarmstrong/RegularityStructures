module

public import GlobalPhi43.Compactness.Sublevels

@[expose] public noncomputable section

open Set Filter Topology RegularityStructures
open scoped ENNReal

namespace GlobalPhi43

/-- Interpolation upgrades a weakly Cauchy sequence with a uniform stronger bound. -/
theorem cauchySeq_toHolderBesov_of_stronger_bound (η β γ : NegExponent)
    (hηβ : (η : ℝ) < β) (hβγ : (β : ℝ) < γ)
    (f : ℕ → C(Torus3, ℝ)) {M : ℝ} (_hM : 0 ≤ M)
    (hf : ∀ n, ‖toHolderBesov γ (f n)‖ ≤ M)
    (hc : CauchySeq (fun n => toHolderBesov η (f n))) :
    CauchySeq (fun n => toHolderBesov β (f n)) := by
  let θ : ℝ := ((γ : ℝ) - β) / ((γ : ℝ) - η)
  have hd : 0 < (γ : ℝ) - η := by linarith
  have hθ : 0 < θ := div_pos (by linarith) hd
  have hθ' : θ < 1 := (div_lt_one hd).mpr (by linarith)
  obtain ⟨b, hb, hbound, ht⟩ := cauchySeq_iff_le_tendsto_0.mp hc
  apply cauchySeq_of_le_tendsto_0 (fun n => b n ^ θ * (2 * M) ^ (1 - θ))
  · intro n m N hn hm
    have hi := norm_toHolderBesov_interpolation η β γ hηβ hβγ (f n - f m)
    rw [toHolderBesov_sub, toHolderBesov_sub, toHolderBesov_sub] at hi
    rw [dist_eq_norm]
    have hh := hbound n m N hn hm
    rw [dist_eq_norm] at hh
    have hstrong : ‖toHolderBesov γ (f n) - toHolderBesov γ (f m)‖ ≤ 2 * M :=
      (norm_sub_le _ _).trans (by linarith [hf n, hf m])
    exact hi.trans (mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) hh hθ.le)
      (Real.rpow_le_rpow (norm_nonneg _) hstrong (by linarith))
      (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (hb N) _))
  · simpa only [Real.zero_rpow (ne_of_gt hθ), zero_mul] using
      (ht.rpow_const (Or.inr hθ.le)).mul_const ((2 * M) ^ (1 - θ))

/-- Strict slack gives membership in the little stronger completion, with bound `M`. -/
theorem exists_holderBesovEmbed_eq_of_extNorm_le (η β γ : NegExponent)
    (hηβ : (η : ℝ) < β) (hβγ : (β : ℝ) < γ)
    {M : ℝ} (hM : 0 ≤ M) {z : HolderBesov η}
    (hz : extNorm η γ z ≤ ENNReal.ofReal M) :
    ∃ w : HolderBesov β, holderBesovEmbed η β hηβ.le w = z ∧ ‖w‖ ≤ M := by
  have hzcl : z ∈ closure (toHolderBesov η ''
      {f : C(Torus3, ℝ) | holderBesovENorm γ f ≤ ENNReal.ofReal M}) := by
    rw [← extNorm_sublevel_eq_closure]
    exact hz
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp hzcl
  choose f hf hfu using hu
  have hηγ : Tendsto (fun n => toHolderBesov η (f n)) atTop (𝓝 z) := by
    simpa only [hfu] using ht
  have hnormγ (n : ℕ) : ‖toHolderBesov γ (f n)‖ ≤ M := by
    rw [norm_toHolderBesov]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hf n)).trans_eq (ENNReal.toReal_ofReal hM)
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_toHolderBesov_of_stronger_bound η β γ hηβ hβγ f hM hnormγ hηγ.cauchySeq)
  refine ⟨w, ?_, ?_⟩
  · apply tendsto_nhds_unique ((continuous_holderBesovEmbed η β hηβ.le).tendsto w |>.comp hw)
    simpa only [Function.comp_def, holderBesovEmbed_toHolderBesov] using hηγ
  · apply (isClosed_le continuous_norm continuous_const).mem_of_tendsto hw
    apply Eventually.of_forall
    intro n
    have hb : ‖toHolderBesov β (f n)‖ ≤ ‖toHolderBesov γ (f n)‖ := by
      rw [norm_toHolderBesov, norm_toHolderBesov]
      exact ENNReal.toReal_mono (holderBesovENorm_lt_top γ.2.le _).ne
        (holderBesovENorm_mono hβγ.le _)
    exact hb.trans (hnormγ n)

/-- Finite extended sublevels lift to every strictly intermediate little completion. -/
theorem exists_holderBesovEmbed_eq_of_extNorm_le_finite (η β γ : NegExponent)
    (hηβ : (η : ℝ) < β) (hβγ : (β : ℝ) < γ)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) {z : HolderBesov η} (hz : extNorm η γ z ≤ M) :
    ∃ w : HolderBesov β, holderBesovEmbed η β hηβ.le w = z ∧ ‖w‖ₑ ≤ M := by
  obtain ⟨w, hw, hnorm⟩ := exists_holderBesovEmbed_eq_of_extNorm_le η β γ hηβ hβγ
    ENNReal.toReal_nonneg (hz.trans_eq (ENNReal.ofReal_toReal hM).symm)
  refine ⟨w, hw, ?_⟩
  rw [← ofReal_norm]
  exact (ENNReal.ofReal_le_ofReal hnorm).trans_eq (ENNReal.ofReal_toReal hM)

end GlobalPhi43
