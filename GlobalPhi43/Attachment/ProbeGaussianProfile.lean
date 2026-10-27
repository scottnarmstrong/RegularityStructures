module

public import GlobalPhi43.Attachment.ProbeGaussianDecay
public import GlobalPhi43.Attachment.ProbeTimeCutoff
public import RegularityStructures.Analysis.Parabolic.ScaledTest
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Actual positive-time averaged Gaussian profile and its proved C4 decay.
The smooth remainder is used only via a global equality with the literal
cutoff Gaussian, not as a replacement probe or an additional hypothesis. -/

@[expose] public noncomputable section

open RegularityStructures Set
open scoped ContDiff

namespace GlobalPhi43.Attachment

/-- The actual unit-time kernel chi(tau) g_tau(y). -/
def probeGaussianProfile (z : ParabolicSpace) : ℝ := probeTimeCutoff z.1 * heatKernelR4 z

/-- On the cutoff support the base heat remainder equals the full Gaussian. -/
theorem probeGaussianProfile_eq_remainder : probeGaussianProfile =
    fun z : ParabolicSpace => probeTimeCutoff z.1 * heatRemainder z := by
  funext z
  by_cases hz : probeTimeCutoff z.1 = 0
  · simp only [probeGaussianProfile, hz, zero_mul]
  have ht := (probeTimeCutoff_support (subset_closure hz)).1
  have hn : 1 / 4 < smoothParabolicNorm z := by
    by_contra hh
    have h4 := pow_le_pow_left₀ (smoothParabolicNorm_nonneg z) (le_of_not_gt hh) 4
    have he := smoothParabolicNorm_pow_four z
    nlinarith [sq_nonneg (sqNorm3 z.2)]
  rw [probeGaussianProfile, heatRemainder_eq_heatKernelR4_of_lt hn]

theorem probeGaussianProfile_smooth : ContDiff ℝ ∞ probeGaussianProfile := by
  rw [probeGaussianProfile_eq_remainder]
  exact (probeTimeCutoff_smooth.comp contDiff_fst).mul contDiff_heatRemainder

theorem probeGaussianProfile_support : tsupport probeGaussianProfile ⊆
    {z : ParabolicSpace | z.1 ∈ Icc (1 / 2 : ℝ) (3 / 4)} := by
  apply closure_minimal _ (isClosed_Icc.preimage continuous_fst)
  intro z hz
  have hc : probeTimeCutoff z.1 ≠ 0 := by
    intro he
    exact hz (by simp only [probeGaussianProfile, he, zero_mul])
  have hh := probeTimeCutoff_support (subset_closure hc)
  exact ⟨hh.1.le, hh.2.le⟩

/-- The scalar cutoff has a global spacetime C4 bound by composition with fst. -/
theorem probeTimeCutoff_spacetime_C4 :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k ≤ 4, ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k (fun w : ParabolicSpace => probeTimeCutoff w.1) z‖ ≤ A := by
  obtain ⟨A, hA, ha⟩ := probeTimeCutoff_compact.exists_bound_iteratedFDeriv probeTimeCutoff_smooth 4
  refine ⟨A, hA, ?_⟩
  intro k hk z
  let L := ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)
  have hn : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro w
    change ‖w.1‖ ≤ 1 * ‖w‖
    rw [one_mul]
    exact norm_fst_le w
  change ‖iteratedFDeriv ℝ k (probeTimeCutoff ∘ L) z‖ ≤ A
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (n := k) L
    (probeTimeCutoff_smooth.of_le (by exact_mod_cast le_top)) z (by exact_mod_cast le_refl k)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _i : Fin k, ‖L‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) hn
  exact (mul_le_mul (ha k hk (L z)) hp (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hA).trans_eq
    (mul_one _)

/-- Arbitrarily high spatial decay of all four Frechet derivatives of the
ACTUAL averaged Gaussian. Each allowance is chosen before scale/noise/model. -/
theorem probeGaussianProfile_C4_decay (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ 4, ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k probeGaussianProfile z‖ ≤ C * (1 + sqNorm3 z.2)⁻¹ ^ m := by
  obtain ⟨A, hA, ha⟩ := probeTimeCutoff_spacetime_C4
  obtain ⟨B, hB, hb⟩ := probeHeatRemainder_C4_decay m
  refine ⟨16 * A * B, mul_nonneg (mul_nonneg (by norm_num) hA) hB, ?_⟩
  intro k hk z
  have hs : 0 ≤ sqNorm3 z.2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd : 0 ≤ (1 + sqNorm3 z.2)⁻¹ ^ m := by positivity
  by_cases ht : z.1 ≤ 1
  · rw [probeGaussianProfile_eq_remainder]
    refine (_root_.norm_iteratedFDeriv_mul_le (N := k)
      ((probeTimeCutoff_smooth.comp contDiff_fst).of_le (by exact_mod_cast le_top))
      (contDiff_heatRemainder.of_le (by exact_mod_cast le_top)) z
      (by exact_mod_cast le_refl k)).trans ?_
    have hsum : ∀ i ∈ Finset.range (k+1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w : ParabolicSpace => probeTimeCutoff w.1) z‖ *
          ‖iteratedFDeriv ℝ (k-i) heatRemainder z‖ ≤ k.choose i * (A * (B * (1 + sqNorm3 z.2)⁻¹ ^ m)) := by
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (ha i (hik.trans hk) z)
        (hb _ ((Nat.sub_le _ _).trans hk) z ht) (norm_nonneg _) hA) (Nat.cast_nonneg _)
    refine (Finset.sum_le_sum hsum).trans ?_
    rw [← Finset.sum_mul]
    have he : ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) = 2 ^ k := by exact_mod_cast Nat.sum_range_choose k
    rw [he]
    have hp : (2 : ℝ) ^ k ≤ 16 := by
      exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk).trans_eq (by norm_num)
    calc _ ≤ 16 * (A * (B * (1 + sqNorm3 z.2)⁻¹ ^ m)) :=
        mul_le_mul_of_nonneg_right hp (mul_nonneg hA (mul_nonneg hB hd))
      _ = _ := by ring
  · have he : iteratedFDeriv ℝ k probeGaussianProfile z = 0 := by
      by_contra hh
      have hz := probeGaussianProfile_support (tsupport_iteratedFDeriv_subset k (subset_closure hh))
      linarith [hz.2]
    rw [he, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hB) hd

end GlobalPhi43.Attachment
