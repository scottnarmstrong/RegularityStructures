module

public import GlobalPhi43.MW20.KernelFirstProductCoherence
public import GlobalPhi43.MW20.KernelNormClosure

/-! Apply the proved Theorem 2.8 estimate to the actual first product germ.
All coherence inputs come from the literal local source norms. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- Actual first-product reconstruction error from source norm bounds.
The repeated testing exponent has been merged on the exact diameter 2T. -/
theorem kernel_firstProduct_reconstruction (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v Z J : ParabolicSpace → ℝ) (hv : ContDiff ℝ ∞ v) (hZ : ContDiff ℝ ∞ Z) (hJ : ContDiff ℝ ∞ J)
    (x : ParabolicSpace) {T ε : ℝ} (hT : 0 < T) (hT₁ : T < 1)
    (hε : 0 ≤ ε) (hsmall : ε < 1 / 14)
    {M H Hv HZ NJ NB : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H) (hHv : 0 ≤ Hv) (hHZ : 0 ≤ HZ)
    (hNJ : 0 ≤ NJ) (hNB : 0 ≤ NB) (hsup : ∀ a ∈ pastBall x T, |v a| ≤ M)
    (hplus : scalarHolderSeminorm (fun y => v y + Z y) (pastBall x T) (1 - 2 * ε) ≤ ENNReal.ofReal H)
    (hvnorm : scalarHolderSeminorm v (pastBall x T) (1 / 2 - 3 * ε) ≤ ENNReal.ofReal Hv)
    (hZnorm : scalarHolderSeminorm Z (pastBall x T) (1 / 2 - 3 * ε) ≤ ENNReal.ofReal HZ)
    (hJnorm : negativeTreeSeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) (-(1 / 2) - ε) J ≤ ENNReal.ofReal NJ)
    (hBnorm : recenteredBSeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) ε Z J ≤ ENNReal.ofReal NB) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ T hT)
      (fun y => firstProductGerm v Z J x y - v y ^ 2 * J y) x| ≤
      ((2 * M * H * NJ * (2 * T) ^ (4 * ε) + Hv * HZ * NJ) * T ^ (1 / 2 - 7 * ε) +
        (2 * Hv * NB) * T ^ (1 / 2 - 7 * ε)) / (1 - (1 / 2 : ℝ) ^ (1 / 2 - 7 * ε)) := by
  classical
  let A : Finset ℝ := {-(1 / 2 : ℝ) - ε, -4 * ε}
  let C : ℝ → ℝ := fun β => if β = -(1 / 2) - ε then
    2 * M * H * NJ * (2 * T) ^ (4 * ε) + Hv * HZ * NJ else 2 * Hv * NB
  let γ : ℝ := 1 / 2 - 7 * ε
  have had := firstProduct_exponents_admissible hε hsmall
  have hC : ∀ β ∈ A, 0 ≤ C β := by
    intro β _
    dsimp [C]
    split_ifs <;> positivity
  have hF := (firstProductGerm_contDiff v Z J hv hZ hJ).continuous
  have hh := kernel_reconstruction_bound Φ hΦ had.1 hT hT₁.le x _ hF A C (fun _ => γ)
    hC had.2 (fun _ _ => le_rfl) (by
      intro t ht htT a ha b hb
      have haD : a ∈ pastBall x T := ⟨ha.1.trans (sub_lt_self T ht), ha.2⟩
      have hbD : b ∈ pastBall x T := ⟨hb.1.trans (sub_lt_self T ht), hb.2⟩
      by_cases he : b = a
      · subst b
        simp only [sub_self, pastSmooth, integral_zero, abs_zero]
        apply Finset.sum_nonneg
        intro β hβ
        exact mul_nonneg (mul_nonneg (hC β hβ) (Real.rpow_nonneg (pdist_nonneg a a) _)) (Real.rpow_nonneg ht.le _)
      · have hR : pdist a b ≤ 2 * T := by
          have hh := pdist_triangle a x b
          rw [pdist_symm a x] at hh
          linarith [ha.1, hb.1]
        exact kernel_firstProduct_coherence_exponent_set Φ hΦ v Z J hv hZ hJ
          (pastBall x T) ε a b haD hbD ht (htT.trans hT₁) (pdist_pos_of_ne he)
          hH hHv hHZ hNJ hNB (hsup a haD) (hsup b hbD)
          hplus hvnorm hZnorm hJnorm hBnorm hR hε hsmall)
  have hne : -(1 / 2 : ℝ) - ε ≠ -4 * ε := by intro he; linarith
  simpa only [firstProductGerm_diag, A, C, γ, Finset.sum_pair hne, eq_self, ite_true,
    Ne.symm hne, ite_false] using hh

end GlobalPhi43.MW20
