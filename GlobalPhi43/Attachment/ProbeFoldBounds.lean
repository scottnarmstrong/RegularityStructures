module

public import GlobalPhi43.Attachment.ProbeFoldIntegral

/-! Uniform fourth-order costs of the constructed periodic folding tests. -/

@[expose] public noncomputable section

open RegularityStructures Set
open scoped ContDiff

namespace GlobalPhi43.Attachment

/-- Translation and reflection preserve the uniform full-jet allowance. -/
theorem probe_reflected_translate_C4 {K : ParabolicSpace → ℝ}
    (hK : ContDiff ℝ ∞ K) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k K z‖ ≤ A) (a : ParabolicSpace) :
    ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k (fun v => K (-v+a)) z‖ ≤ A := by
  let F := fun v => K (v+a)
  have hF : ContDiff ℝ ∞ F := hK.comp (by fun_prop)
  let L : ParabolicSpace →L[ℝ] ParabolicSpace := -ContinuousLinearMap.id ℝ ParabolicSpace
  have hn : ‖L‖ ≤ 1 := by
    change ‖-ContinuousLinearMap.id ℝ ParabolicSpace‖ ≤ 1
    rw [norm_neg]
    exact ContinuousLinearMap.norm_id_le
  intro k hk z
  have hh : ‖iteratedFDeriv ℝ k F (L z)‖ ≤ A := by
    rw [iteratedFDeriv_comp_add_right]
    exact hb k hk _
  have he := probe_jet_comp_bound hF L k z hA hn hh
  change ‖iteratedFDeriv ℝ k (fun v => K (-v+a)) z‖ ≤ A * 1^k at he
  simpa only [one_pow, mul_one] using he

/-- The spatial partition costs one fixed constant, independently of the
integer translate and independently of the noise and model. -/
theorem probeFoldedProfile_C4 : ∃ D : ℝ, 0 ≤ D ∧
    ∀ K : ParabolicSpace → ℝ, ContDiff ℝ ∞ K → ∀ A : ℝ, 0 ≤ A →
    (∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k K z‖ ≤ A) →
    ∀ m : Fin 3 → ℤ, ∀ k ≤ 4, ∀ z,
      ‖iteratedFDeriv ℝ k (probeFoldedProfile K m) z‖ ≤ D*A := by
  obtain ⟨B, hB, hb⟩ := probeFoldPartition_C4
  refine ⟨16*B, mul_nonneg (by norm_num) hB, ?_⟩
  intro K hK A hA ha m
  let L : ParabolicSpace →L[ℝ] ProbeSpace := -ContinuousLinearMap.snd ℝ ℝ ProbeSpace
  have hn : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro z
    change ‖-z.2‖ ≤ 1*‖z‖
    simpa only [norm_neg, one_mul] using norm_snd_le z
  have hθ : ∀ k ≤ 4, ∀ z,
      ‖iteratedFDeriv ℝ k (fun v : ParabolicSpace => probeFoldPartition (-v.2)) z‖ ≤ B := by
    intro k hk z
    have hh := probe_jet_comp_bound probeFoldPartition_smooth L k z hB hn (hb k hk (L z))
    change ‖iteratedFDeriv ℝ k (fun v : ParabolicSpace => probeFoldPartition (-v.2)) z‖ ≤ B * 1^k at hh
    simpa only [one_pow, mul_one] using hh
  have hh := probe_C4_product_local
    (hK.comp (show ContDiff ℝ ∞ (fun v : ParabolicSpace => -v+probeIntegerShift m) by fun_prop))
    (probeFoldPartition_smooth.comp (show ContDiff ℝ ∞ (fun v : ParabolicSpace => -v.2) by fun_prop))
    hA hB (fun z _ k hk => probe_reflected_translate_C4 hK hA ha _ k hk z) hθ
  intro k hk z
  exact (hh k hk z).trans_eq (by ring)

end GlobalPhi43.Attachment
