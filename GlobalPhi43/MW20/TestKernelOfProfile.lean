module

public import GlobalPhi43.Local.SmallScaleLocalData

/-! A kernel profile gives an admissible test kernel on the unit past ball. -/

public section
namespace GlobalPhi43.MW20
open RegularityStructures Set

theorem isMWTestKernel_of_kernelProfile {Φ : ParabolicSpace → ℝ}
    (hΦ : KernelProfile Φ) : IsMWTestKernel Φ := by
  refine ⟨hΦ.smooth,?_,fun z => ⟨hΦ.nonneg z,hΦ.le_one z⟩,hΦ.mass,?_⟩
  · intro z hz
    have hs := hΦ.support hz
    change max (Real.sqrt |(0:ℝ)-z.1|) ‖(0:Fin 3 → ℝ)-z.2‖ < 1 ∧ z.1 < 0
    simp only [zero_sub,abs_neg,norm_neg]
    refine ⟨max_lt ?_ ?_,hs.2.1⟩
    · have ha : |z.1| < 1 := abs_lt.mpr ⟨hs.1,by linarith [hs.2.1]⟩
      nlinarith [Real.sq_sqrt (abs_nonneg z.1),Real.sqrt_nonneg |z.1|]
    · rw [pi_norm_lt_iff (by norm_num : (0:ℝ)<1)]
      intro i
      simpa only [Real.norm_eq_abs] using hs.2.2 i
  · intro z
    exact hΦ.spatial_even z.1 z.2

end GlobalPhi43.MW20
