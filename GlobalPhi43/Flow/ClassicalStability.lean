module

public import GlobalPhi43.Flow.ClassicalDifference

/-! Independent-data stability for the actual classical cubic solutions.
The forcing norm is continuous and integrable by smoothness, not an extra
analytical premise. The actual common linear coefficient is retained. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

theorem classical_difference_le_barrier {b : ℝ} {f g : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : IsSmoothOnSpaceTime g)
    {x y : C(Torus3, ℝ)} {u v : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution b f x u) (hv : IsClassicalSolution b g y v)
    {T : ℝ} (hT : 0 < T) :
    ∀ t ∈ Icc 0 T, ∀ z, u t z - v t z ≤
      classicalBarrier (max b 0) ‖x - y‖
        (fun q => ‖forcingCurve f hf q - forcingCurve g hg q‖) t := by
  let F : ℝ → ℝ := fun q => ‖forcingCurve f hf q - forcingCurve g hg q‖
  let Q := classicalBarrier (max b 0) ‖x - y‖ F
  have hF : Continuous F := forcingNorm_continuous hf hg
  have hQc : Continuous Q := continuous_iff_continuousAt.mpr
    (fun t => (classicalBarrier_hasDerivAt _ _ hF t).continuousAt)
  apply finiteWindow_scalar_comparison (W := fun p => u p.1 p.2 - v p.1 p.2)
    (Q := Q) (F := F) hT
  · exact (hu.continuousOn.sub hv.continuousOn).mono
      (fun p hp => ⟨hp.1.1, mem_univ _⟩)
  · intro t ht
    exact ((isSmoothOnTorus_of_classical hu ht.1).sub
      (isSmoothOnTorus_of_classical hv ht.1)).of_le (by norm_num)
  · intro t ht z
    have hd := (classical_time_hasDerivAt hu ht.1 z).sub
      (classical_time_hasDerivAt hv ht.1 z)
    exact hd.congr_deriv hd.deriv.symm
  · exact hQc.continuousOn
  · intro t _
    exact classicalBarrier_hasDerivAt _ _ hF t
  · intro t ht
    exact classicalBarrier_nonneg (norm_nonneg _) (fun _ => norm_nonneg _) ht.1
  · intro z
    change u 0 z - v 0 z ≤ classicalBarrier (max b 0) ‖x - y‖ F 0
    rw [hu.initial, hv.initial, classicalBarrier_zero]
    exact (le_abs_self _).trans ((x - y).norm_coe_le_norm z)
  · intro t ht z hp
    have hh := classical_difference_subsolution hu hv ht.1 z hp
    have hn : |f (t, torusProj z) - g (t, torusProj z)| ≤ F t :=
      (forcingCurve f hf t - forcingCurve g hg t).norm_coe_le_norm (torusProj z)
    exact hh.trans (by linarith only [hn])

/-- Sharp integrating-factor estimate, including the independent initial error
and the zero and terminal endpoints. -/
theorem classicalSolution_integratingFactor_stability {b : ℝ} {f g : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : IsSmoothOnSpaceTime g)
    {x y : C(Torus3, ℝ)} {u v : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution b f x u) (hv : IsClassicalSolution b g y v)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖u r - v r‖ ≤ classicalBarrier (max b 0) ‖x - y‖
      (fun q => ‖forcingCurve f hf q - forcingCurve g hg q‖) r := by
  by_cases h0 : r = 0
  · subst r
    rw [hu.initial, hv.initial, classicalBarrier_zero]
  have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm h0)
  have hupp := classical_difference_le_barrier hf hg hu hv hp r ⟨hr, le_rfl⟩
  have hvpp := classical_difference_le_barrier hg hf hv hu hp r ⟨hr, le_rfl⟩
  simp only [norm_sub_rev (forcingCurve g hg _), norm_sub_rev y x] at hvpp
  apply (ContinuousMap.norm_le _ (classicalBarrier_nonneg (norm_nonneg _)
    (fun _ => norm_nonneg _) hr)).mpr
  intro z
  change |u r z - v r z| ≤ _
  exact abs_le.mpr ⟨by linarith only [hvpp z], hupp z⟩

/-- The source's integral-forcing inequality with b_+=max(b,0).
No forcing bound, identical-data assumption or path-size premise is supplied. -/
theorem classicalSolution_integral_stability_pos {b : ℝ} {f g : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : IsSmoothOnSpaceTime g)
    {x y : C(Torus3, ℝ)} {u v : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution b f x u) (hv : IsClassicalSolution b g y v)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖u r - v r‖ ≤ Real.exp (max b 0 * r) *
      (‖x - y‖ + ∫ q in (0 : ℝ)..r, ‖forcingCurve f hf q - forcingCurve g hg q‖) :=
  (classicalSolution_integratingFactor_stability hf hg hu hv hr).trans
    (classicalBarrier_le_integral (le_max_right b 0) (forcingNorm_continuous hf hg)
      (fun _ => norm_nonneg _) hr)

end GlobalPhi43.Flow
