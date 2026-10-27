module

public import GlobalPhi43.Attachment.ProbeKernelPairing

/-! Dominated convergence identifies the actual Gaussian pairing with the
finite annular sums. The majorant is used solely to justify integration. -/

@[expose] public noncomputable section

open RegularityStructures RegularityStructures.Phi43 MeasureTheory Set Filter Topology

namespace GlobalPhi43.Attachment

theorem probeJ_piece_integrable {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) {r : ℝ} (hr : 0 < r) (n : ℕ) (z : ParabolicSpace) :
    Integrable (fun w => treeJ N f (spaceTimeProj w)*probeGaussianPiece r n (z-w)) := by
  have hp : 0 < probePieceFactor n*r :=
    mul_pos (lt_of_lt_of_le (by norm_num) (probePieceFactor_ge_two n)) hr
  simp_rw [probeGaussianPiece_rescaled hr]
  exact probe_test_pairing_integrable ((continuous_treeJ hf).comp continuous_spaceTimeProj)
    (probePieceTest_smooth n).continuous (probePieceTest_compact n) hp z

theorem probeJ_pairing_tendsto {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (s : ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (z : ParabolicSpace) (hz : z.1 = s+r^2) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n+1),
      ∫ w, treeJ N f (spaceTimeProj w)*probeGaussianPiece r j (z-w)) atTop
      (𝓝 (∫ w, treeJ N f (spaceTimeProj w)*probeGaussianKernel (r^2) (z-w))) := by
  classical
  obtain ⟨M, _, hi, hb⟩ := probeJ_pairing_domination hf s hr hr1 z hz
  let F := fun n : ℕ => fun w : ParabolicSpace =>
    treeJ N f (spaceTimeProj w)*probeGaussianKernel (r^2) (z-w)*
      probeSpaceCore ((probeDyadicRadius r n)⁻¹ • (z-w).2)
  have hF : ∀ n, AEStronglyMeasurable (F n) volume := by
    intro n
    exact ((((continuous_treeJ hf).comp continuous_spaceTimeProj).mul
      ((probeGaussianKernel_smooth hr).continuous.comp (by fun_prop))).mul
      (probeSpaceCore_smooth.continuous.comp (by fun_prop))).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ w, ‖F n w‖ ≤ M*probeGaussianKernel (r^2) (z-w) := by
    intro n
    apply ae_of_all
    intro w
    have h0 : 0 ≤ probeSpaceCore ((probeDyadicRadius r n)⁻¹ • (z-w).2) := probeSpaceBump.nonneg
    have h1 : probeSpaceCore ((probeDyadicRadius r n)⁻¹ • (z-w).2) ≤ 1 := probeSpaceBump.le_one
    change ‖(_ : ℝ)*probeSpaceCore _‖ ≤ _
    rw [norm_mul, Real.norm_of_nonneg h0]
    exact (mul_le_of_le_one_right (norm_nonneg _) h1).trans (hb w)
  have hlim : ∀ᵐ w, Tendsto (fun n => F n w) atTop
      (𝓝 (treeJ N f (spaceTimeProj w)*probeGaussianKernel (r^2) (z-w))) := by
    apply ae_of_all
    intro w
    apply tendsto_const_nhds.congr'
    filter_upwards [probeSpatialPiece_sum_eventually hr (z-w)] with n hn
    rw [probeSpatialPiece_sum] at hn
    dsimp only [F]
    rw [hn, mul_one]
  have hd := tendsto_integral_of_dominated_convergence
    (fun w => M*probeGaussianKernel (r^2) (z-w)) hF hi hbound hlim
  have he (n : ℕ) : (∫ w, F n w) = ∑ j ∈ Finset.range (n+1),
      ∫ w, treeJ N f (spaceTimeProj w)*probeGaussianPiece r j (z-w) := by
    rw [← integral_finsetSum _ (fun j _ => probeJ_piece_integrable hf hr j z)]
    apply integral_congr_ae
    apply ae_of_all
    intro w
    change treeJ N f (spaceTimeProj w)*probeGaussianKernel (r^2) (z-w)*
      probeSpaceCore ((probeDyadicRadius r n)⁻¹ • (z-w).2) =
        ∑ j ∈ Finset.range (n+1), treeJ N f (spaceTimeProj w)*probeGaussianPiece r j (z-w)
    rw [← Finset.mul_sum, probeGaussianPiece_sum]
    exact mul_assoc _ _ _
  simpa only [he] using hd

end GlobalPhi43.Attachment
