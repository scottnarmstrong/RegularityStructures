module

public import GlobalPhi43.MW20.KernelNormClosure

/-! Restriction and boundary invariance of the actual source norms.
These preserve extended values and all testing scale endpoints. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set
open scoped ENNReal

/-- Restrict the base-point domain of the literal testing supremum. -/
theorem localTestSeminorm_mono_domain (κ : ℝ → Measure ParabolicSpace)
    {D E : Set ParabolicSpace} (hDE : D ⊆ E) (I : Set ℝ) (α : ℝ)
    (G : ParabolicSpace → ParabolicSpace → ℝ) :
    localTestSeminorm κ D I α G ≤ localTestSeminorm κ E I α G := by
  unfold localTestSeminorm
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  exact le_iSup_of_le x (le_iSup_of_le (hDE hx) le_rfl)

/-- Restrict both points in the actual scalar Holder seminorm. -/
theorem scalarHolderSeminorm_mono_domain (f : ParabolicSpace → ℝ)
    {D E : Set ParabolicSpace} (hDE : D ⊆ E) (α : ℝ) :
    scalarHolderSeminorm f D α ≤ scalarHolderSeminorm f E α := by
  unfold scalarHolderSeminorm
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
  exact le_iSup_of_le x (le_iSup_of_le (hDE hx)
    (le_iSup_of_le y (le_iSup_of_le (hDE hy) le_rfl)))


/-- Negative germ seminorms are unchanged by taking the base-domain
closure. Continuity and actual compact kernels suffice, with no finite-norm
assumption; the scale-one endpoint is retained when present in I. -/
theorem mw20_localTestSeminorm_closure (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (D : Set ParabolicSpace) (I : Set ℝ) (hI : I ⊆ Ioc 0 1) (α : ℝ)
    (G : ParabolicSpace × ParabolicSpace → ℝ) (hG : Continuous G) :
    localTestSeminorm (mw20TestingKernel Φ hΦ) (closure D) I α (fun x y => G (x, y)) =
      localTestSeminorm (mw20TestingKernel Φ hΦ) D I α (fun x y => G (x, y)) := by
  let S := localTestSeminorm (mw20TestingKernel Φ hΦ) D I α (fun x y => G (x, y))
  apply le_antisymm _ (localTestSeminorm_mono_domain _ subset_closure I α _)
  by_cases hn : S = ⊤
  · change _ ≤ S
    rw [hn]
    exact le_top
  have hnorm : S ≤ ENNReal.ofReal S.toReal := by rw [ENNReal.ofReal_toReal hn]
  have hh : localTestSeminorm (mw20TestingKernel Φ hΦ) (closure D) I α
      (fun x y => G (x, y)) ≤ ENNReal.ofReal S.toReal := by
    apply (localTestSeminorm_le_iff _ _ _ _ _ ENNReal.toReal_nonneg).2
    intro x hx t htI
    have ht := (hI htI).1
    have ht₁ := (hI htI).2
    have hb := mw20_localTestSeminorm_closure_test_bound Φ hΦ D I α G hG
      ENNReal.toReal_nonneg hnorm hx ht ht₁ htI
    rw [mw20TestingKernel_pos Φ hΦ ht, reconstruction_pastSmooth_eq_density Φ hΦ ht ht₁]
    calc
      t ^ (-α) * |infinitePastSmooth Φ hΦ t ht (fun y => G (x, y)) x| ≤
          t ^ (-α) * (S.toReal * t ^ α) := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.le _)
      _ = S.toReal := by
        rw [mul_left_comm, ← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero, mul_one]
  simpa only [ENNReal.ofReal_toReal hn] using hh

end GlobalPhi43.MW20
