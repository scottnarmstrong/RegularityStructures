module

public import GlobalPhi43.MW20.InfiniteKernelSupport
public import GlobalPhi43.MW20.KernelParabolicGeometry

/-!
# The exact source max-parabolic support of the constructed kernel
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter Topology
open scoped BoundedContinuousFunction

/-- A nonzero scaled seed lies in its exact closed past ball. -/
theorem scaledKernelSeed_parabolic_support (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {c : ℝ} (hc : 0 < c) {x : ParabolicSpace}
    (hx : scaledKernelSeed Φ hΦ c hc x ≠ 0) :
    x.1 ≤ 0 ∧ Local.pdist 0 x ≤ c := by
  have hp : Φ (parabolicDilate c⁻¹ x) ≠ 0 := by
    intro hp; apply hx; simp only [scaledKernelSeed_apply, hp, mul_zero]
  have hs := hΦ.support (subset_tsupport Φ hp)
  have ht : (c⁻¹ ^ 2) * x.1 < 0 := hs.2.1
  have hb : Local.pdist 0 (parabolicDilate c⁻¹ x) ≤ 1 := by
    simp only [Local.pdist, Prod.fst_zero, Prod.snd_zero, zero_sub, abs_neg, norm_neg]
    apply max_le
    · apply Real.sqrt_le_one.mpr
      rw [abs_le]
      exact ⟨hs.1.le, hs.2.1.le.trans (by norm_num)⟩
    · exact (norm_snd_le _).trans (norm_le_one_of_mem_kernelPastUnitBall hs)
  refine ⟨by nlinarith [sq_pos_of_pos (inv_pos.mpr hc)], ?_⟩
  have hd := pdist_zero_parabolicDilate hc.le (parabolicDilate c⁻¹ x)
  rw [parabolicDilate_parabolicDilate_inv hc.ne'] at hd
  rw [hd]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hc.le

/-- Finite densities vanish outside the exact source max-radius T. -/
theorem finiteKernelDensity_eq_zero_of_pdist_gt (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {T : ℝ} (hT : 0 < T) (n : ℕ)
    {x : ParabolicSpace} (hx : T < Local.pdist 0 x) :
    finiteKernelDensity Φ hΦ T hT n x = 0 := by
  have := kernelProfileMeasure_probability Φ hΦ
  let R : ℕ → ℝ := fun j => T * (1 - (1 / 2 : ℝ) ^ (j + 1))
  let r : ℕ → ℝ := fun j => (T / 2 * 1 / 2) * (1 / 2 : ℝ) ^ j
  have hρ : ∀ x y : ParabolicSpace,
      Local.pdist 0 x ≤ Local.pdist 0 (x - y) + Local.pdist 0 y := by
    intro x y
    have ht := Local.pdist_triangle 0 y x
    have he : Local.pdist y x = Local.pdist 0 (x - y) := by
      simp only [Local.pdist, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero,
        zero_sub, abs_neg, norm_neg, abs_sub_comm, norm_sub_rev]
    rw [he] at ht
    linarith
  have hseed : ∀ y, R 0 < Local.pdist 0 y →
      scaledKernelSeed Φ hΦ (T / 2) (half_pos hT) y = 0 := by
    intro y hy
    by_contra hn
    have hb := (scaledKernelSeed_parabolic_support Φ hΦ (half_pos hT) hn).2
    dsimp [R] at hy
    norm_num at hy
    linarith
  have hR : ∀ j, R (j + 1) = R j + r j := by
    intro j; dsimp [R, r]; rw [pow_succ, pow_succ]; ring
  have hμ : ∀ j, ∀ᵐ y ∂dyadicKernelFactor (kernelProfileMeasure Φ) (T / 2) j,
      Local.pdist 0 y ≤ r j := by
    intro j
    filter_upwards [dyadicKernelFactor_ae_parabolic Φ hΦ (half_pos hT).le j] with y hy
    have he : T / 2 / 2 ^ (j + 1) = r j := by
      dsimp [r]; rw [pow_succ, div_pow]; simp only [one_pow]; ring
    exact he ▸ hy.2
  apply convolutionIter_eq_zero_of_gauge_gt _ _ _ hρ R r hseed hR hμ n x
  dsimp [R]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (n + 1)]

end GlobalPhi43.MW20
