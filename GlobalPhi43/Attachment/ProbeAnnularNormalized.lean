module

public import GlobalPhi43.Attachment.ProbeLocalizedProduct
public import GlobalPhi43.Attachment.TestGeometry

/-! The actual normalized annular Gaussian test, with its C4 cost paid by
Gaussian spatial decay. Constants are fixed before the annulus scale. -/

@[expose] public noncomputable section

open RegularityStructures Set
open scoped ContDiff

namespace GlobalPhi43.Attachment

def probeAnnularSpatialLift (z : ParabolicSpace) : ℝ := probeSpaceAnnulus ((-2 : ℝ) • z.2)

theorem probeAnnularSpatialLift_smooth : ContDiff ℝ ∞ probeAnnularSpatialLift := by
  unfold probeAnnularSpatialLift
  exact probeSpaceAnnulus_smooth.comp (by fun_prop)

theorem probeAnnularSpatialLift_support : tsupport probeAnnularSpatialLift ⊆
    {z : ParabolicSpace | 1/4 ≤ ‖z.2‖ ∧ ‖z.2‖ ≤ 1} := by
  apply closure_minimal _ ((isClosed_le continuous_const (continuous_norm.comp continuous_snd)).inter
    (isClosed_le (continuous_norm.comp continuous_snd) continuous_const))
  intro z hz
  have hh := probeSpaceAnnulus_support (subset_closure hz)
  change 1/2 ≤ ‖(-2 : ℝ) • z.2‖ ∧ ‖(-2 : ℝ) • z.2‖ ≤ 2 at hh
  rw [norm_smul, Real.norm_eq_abs] at hh
  norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hh
  change (1/4 : ℝ) ≤ ‖z.2‖ ∧ ‖z.2‖ ≤ 1
  constructor <;> linarith [hh.1, hh.2]

theorem probeAnnularSpatialLift_C4 : ∃ B : ℝ, 0 ≤ B ∧ ∀ k ≤ 4, ∀ z,
    ‖iteratedFDeriv ℝ k probeAnnularSpatialLift z‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := probeSpaceProfiles_derivative_bounds
  let L : ParabolicSpace →L[ℝ] ProbeSpace := (-2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ProbeSpace
  have hn : ‖L‖ ≤ 2 := by
    apply L.opNorm_le_bound (by norm_num)
    intro z
    change ‖(-2 : ℝ) • z.2‖ ≤ 2 * ‖z‖
    rw [norm_smul, Real.norm_eq_abs]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (norm_snd_le z) (by norm_num)
  refine ⟨16 * B, mul_nonneg (by norm_num) hB, ?_⟩
  intro k hk z
  change ‖iteratedFDeriv ℝ k (probeSpaceAnnulus ∘ L) z‖ ≤ _
  have hh := probe_jet_comp_bound probeSpaceAnnulus_smooth L k z hB hn ((hb k hk (L z)).2)
  calc _ ≤ B * (2 : ℝ)^k := hh
    _ ≤ B * 16 := mul_le_mul_of_nonneg_left
      ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk).trans_eq (by norm_num)) hB
    _ = _ := mul_comm _ _

def probeNegativeDilate (c : ℝ) : ParabolicSpace →L[ℝ] ParabolicSpace := -parabolicDilateCLM c

theorem probeNegativeDilate_norm {c : ℝ} (hc : 1 ≤ c) : ‖probeNegativeDilate c‖ ≤ c^2 := by
  change ‖-parabolicDilateCLM c‖ ≤ _
  rw [norm_neg]
  exact norm_parabolicDilateCLM_le hc

/-- This is c^5 k_j(-S_c v) at the unit-time normalization. -/
def probeAnnularNormalized (c : ℝ) (z : ParabolicSpace) : ℝ :=
  c^5 * probeGaussianProfile (probeNegativeDilate c z) * probeAnnularSpatialLift z

theorem probeAnnularNormalized_smooth (c : ℝ) : ContDiff ℝ ∞ (probeAnnularNormalized c) := by
  unfold probeAnnularNormalized
  exact (contDiff_const.mul (probeGaussianProfile_smooth.comp
    (probeNegativeDilate c).contDiff)).mul probeAnnularSpatialLift_smooth

/-- Literal max-parabolic unit support, at the original base point after scaling. -/
theorem probeAnnularNormalized_support {c : ℝ} (hc : 2 ≤ c) :
    tsupport (probeAnnularNormalized c) ⊆ {z | Local.pdist 0 z ≤ 1} := by
  apply closure_minimal _ (isCompact_pdist_ball (by norm_num : (0 : ℝ) ≤ 1)).isClosed
  intro z hz
  have hg : probeGaussianProfile (probeNegativeDilate c z) ≠ 0 := by
    intro he
    exact hz (by simp only [probeAnnularNormalized, he, mul_zero, zero_mul])
  have hs : probeAnnularSpatialLift z ≠ 0 := by
    intro he
    exact hz (by simp only [probeAnnularNormalized, he, mul_zero])
  have hx := (probeAnnularSpatialLift_support (subset_closure hs)).2
  have ht := probeGaussianProfile_support (subset_closure hg)
  change 1/2 ≤ -(c^2 * z.1) ∧ -(c^2 * z.1) ≤ 3/4 at ht
  have hc2 : 0 < c^2 := sq_pos_of_pos (lt_of_lt_of_le (by norm_num) hc)
  have hc2' : 4 ≤ c^2 := by nlinarith
  have hz0 : z.1 ≤ 0 := by
    by_contra hn
    have hp := mul_nonneg (sq_nonneg c) (le_of_not_ge hn)
    linarith [ht.1]
  have habs : |z.1| ≤ 1 := by
    rw [abs_of_nonpos hz0]
    calc -z.1 ≤ (3/4 : ℝ) / c^2 := by rw [le_div_iff₀ hc2]; nlinarith [ht.2]
      _ ≤ 1 := by rw [div_le_iff₀ hc2]; linarith
  change max (Real.sqrt |0-z.1|) ‖0-z.2‖ ≤ 1
  simp only [zero_sub, abs_neg, norm_neg]
  exact max_le ((Real.sqrt_le_left zero_le_one).mpr (by simpa only [one_pow] using habs)) hx
/-- All fourth-order test allowances decay like c^(-5), after paying c^5
normalization and the full parabolic derivative costs. -/
theorem probeAnnularNormalized_C4 : ∃ D : ℝ, 0 ≤ D ∧ ∀ c : ℝ, 2 ≤ c →
    ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k (probeAnnularNormalized c) z‖ ≤ D * (c⁻¹)^5 := by
  obtain ⟨C, hC, hb⟩ := probeGaussianProfile_C4_decay 9
  obtain ⟨B, hB, hg⟩ := probeAnnularSpatialLift_C4
  refine ⟨16 * C * 16^9 * B, by positivity, ?_⟩
  intro c hc
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hc1 : 1 ≤ c := (by norm_num : (1 : ℝ) ≤ 2).trans hc
  let L := probeNegativeDilate c
  let F := fun z => c^5 * probeGaussianProfile (L z)
  have hf : ContDiff ℝ ∞ F := contDiff_const.mul (probeGaussianProfile_smooth.comp L.contDiff)
  let A := C * 16^9 * (c⁻¹)^5
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have ha : ∀ z ∈ tsupport probeAnnularSpatialLift, ∀ k ≤ 4,
      ‖iteratedFDeriv ℝ k F z‖ ≤ A := by
    intro z hz k hk
    have hs := probeAnnularSpatialLift_support hz
    have hy : c/4 ≤ ‖(L z).2‖ := by
      change c/4 ≤ ‖-(c • z.2)‖
      rw [norm_neg, norm_smul, Real.norm_of_nonneg hc0.le]
      nlinarith [hs.1]
    have hdec := probe_annular_decay_arithmetic hc0 hy
    have hsq : 0 ≤ sqNorm3 (L z).2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hd : 0 ≤ (1 + sqNorm3 (L z).2)⁻¹ ^ 9 := by positivity
    have hj := probe_jet_comp_bound probeGaussianProfile_smooth L k z (mul_nonneg hC hd)
      (probeNegativeDilate_norm hc1) (hb k hk (L z))
    have hp : (c^2)^k ≤ c^8 := by
      have hh : (c^2)^k ≤ (c^2)^4 := pow_le_pow_right₀ (one_le_pow₀ hc1) hk
      simpa only [← pow_mul, show 2 * 4 = 8 from rfl] using hh
    have hpre : ‖iteratedFDeriv ℝ k F z‖ ≤ C * c^13 * (1 + sqNorm3 (L z).2)⁻¹ ^ 9 := by
      change ‖iteratedFDeriv ℝ k ((c^5) • (probeGaussianProfile ∘ L)) z‖ ≤ _
      rw [iteratedFDeriv_const_smul_apply
        ((probeGaussianProfile_smooth.comp L.contDiff).of_le (by exact_mod_cast le_top)).contDiffAt,
        norm_smul, Real.norm_of_nonneg (pow_nonneg hc0.le _)]
      calc _ ≤ c^5 * (C * (1 + sqNorm3 (L z).2)⁻¹ ^ 9 * (c^2)^k) :=
          mul_le_mul_of_nonneg_left hj (pow_nonneg hc0.le _)
        _ ≤ c^5 * (C * (1 + sqNorm3 (L z).2)⁻¹ ^ 9 * c^8) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hd)) (pow_nonneg hc0.le _)
        _ = _ := by rw [show (13 : ℕ) = 5 + 8 from rfl, pow_add]; ring
    calc _ ≤ C * c^13 * (1 + sqNorm3 (L z).2)⁻¹ ^ 9 := hpre
      _ ≤ C * c^13 * (16^9 * (c⁻¹)^18) :=
        mul_le_mul_of_nonneg_left hdec (mul_nonneg hC (pow_nonneg hc0.le _))
      _ = (C * 16^9) * (c^13 * (c⁻¹)^18) := by ring
      _ = A := by rw [probe_annular_power_cancel hc0.ne']
  have hh := probe_C4_product_local hf probeAnnularSpatialLift_smooth hA hB ha hg
  intro k hk z
  exact (hh k hk z).trans_eq (by dsimp [A]; ring)

end GlobalPhi43.Attachment
