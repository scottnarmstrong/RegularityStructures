module

public import GlobalPhi43.MW20.KernelSecondProductCoherence
public import GlobalPhi43.MW20.KernelReconstruction

/-! Apply reconstruction to the actual product-compatible second
germ. The source expansion's optimal coefficient is selected, not supplied. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- Second-product reconstruction error from the actual source norms.
This uses the corrected auxiliary germ documented in SecondReconstructionGerm,
while retaining the original signed Lemma 2.10 estimate and its distinct trees. -/
theorem kernel_secondProduct_reconstruction (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v Y Z V : ParabolicSpace → ℝ) (C₂ : ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z) (hV : ContDiff ℝ ∞ V)
    (x : ParabolicSpace) {T ε : ℝ} (hT : 0 < T) (hT₁ : T < 1)
    (hε : 0 < ε) (hsmall : ε < 1 / 14)
    {Hv HU Hν NA NV NX : ℝ} (hHv : 0 ≤ Hv) (hHU : 0 ≤ HU) (hHν : 0 ≤ Hν)
    (hNA : 0 ≤ NA) (hNV : 0 ≤ NV) (hNX : 0 ≤ NX)
    (hvnorm : scalarHolderSeminorm v (pastBall x T) (1 / 2 - 3 * ε) ≤ ENNReal.ofReal Hv)
    (hUnorm : localAffineSeminorm (sourceExpansion v Y Z) (pastBall x T) (3 / 2 - 5 * ε) ≤ ENNReal.ofReal HU)
    (hνnorm : localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) (pastBall x T)
      (1 / 2 - 5 * ε) ≤ ENNReal.ofReal Hν)
    (hAnorm : recenteredASeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) ε Y V C₂ ≤ ENNReal.ofReal NA)
    (hVnorm : negativeTreeSeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) (-1 - 2 * ε) V ≤ ENNReal.ofReal NV)
    (hXnorm : recenteredXVSeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) ε V ≤ ENNReal.ofReal NX) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ T hT)
      (fun y => secondReconstructionGerm v Y Z V (sourceAffineCoefficient v Y Z) Prod.snd C₂ x y - v y * V y) x| ≤
      (3 * Hv * NA + HU * NV + 3 * Hν * NX) * T ^ (1 / 2 - 7 * ε) /
        (1 - (1 / 2 : ℝ) ^ (1 / 2 - 7 * ε)) := by
  classical
  let A : Finset ℝ := {-4 * ε, -1 - 2 * ε, -2 * ε}
  let C : ℝ → ℝ := fun β => if β = -4 * ε then 3 * Hv * NA
    else if β = -1 - 2 * ε then HU * NV else 3 * Hν * NX
  let γ : ℝ := 1 / 2 - 7 * ε
  have hC : ∀ β ∈ A, 0 ≤ C β := by intro β _; dsimp [C]; split_ifs <;> positivity
  have had := secondProduct_exponents_admissible hε hsmall
  have hD : IsOpen (pastBall x T) := by
    rw [reconstruction_pastBall_eq_prod x hT]
    exact isOpen_Ioo.prod Metric.isOpen_ball
  have hFc := (secondReconstructionGerm_contDiff v Y Z V (sourceAffineCoefficient v Y Z)
    Prod.snd C₂ hv hY hZ hV (sourceAffineCoefficient_contDiff v Y Z hv hY hZ) contDiff_snd).continuous
  have hh := kernel_reconstruction_bound Φ hΦ had.1 hT hT₁.le x _ hFc A C (fun _ => γ)
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
      · exact kernel_secondProduct_coherence_exponent_set Φ hΦ v Y Z V C₂ hv hY hZ hV
          (pastBall x T) hD hε hsmall haD hbD he ht (htT.trans hT₁)
          hHv hHU hHν hNA hNV hNX hvnorm hUnorm hνnorm hAnorm hVnorm hXnorm)
  have hAV : -4 * ε ≠ -1 - 2 * ε := by intro he; linarith
  have hAX : -4 * ε ≠ -2 * ε := by intro he; linarith
  have hVX : -1 - 2 * ε ≠ -2 * ε := by intro he; linarith
  have hnot : -4 * ε ∉ ({-1 - 2 * ε, -2 * ε} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hAV, hAX⟩
  simpa only [secondReconstructionGerm_diag, A, C, γ, Finset.sum_insert hnot, Finset.sum_pair hVX,
    eq_self, ite_true, Ne.symm hAV, Ne.symm hAX, Ne.symm hVX, ite_false, ← add_mul, ← add_assoc] using hh

end GlobalPhi43.MW20
