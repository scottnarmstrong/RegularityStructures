/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.SmallTime

/-!
# Continuity of the unit coordinate of a singular modelled distribution

Part of the derivation of the mild equation (continuity of `w` for `t > s`). For `U` in the slab
space and `x` in the slab, the increment bound of `SingularBoundOn` in the unit coordinate
(`|(U(y) - Γ_{yx} U(x))_1| ≲ d(y,x)^γ`) together with `|(Γ_{yx} e_i)_1| ≲ d(y,x)^{deg i}` for
`deg i > 0` (near-pair `Γ`-bounds) gives `U(y)_1 → U(x)_1` as `y → x` in the slab.
-/

public section

open Set Filter Topology

namespace RegularityStructures.Phi43

/-- The unit coordinate of `Γ_{yx} v` differs from that of `v` by the positive-degree coordinates. -/
theorem abs_gammaMap_unit_sub_le {κ : Kappa} (M : Model (phi43RegularityStructureF κ) parabolicSemigroup)
    {γ CΓ : ℝ} {S : Set ParabolicSpace} (hΓ : M.GammaNearOn γ CΓ S) (v : SymbolF → ℝ)
    (hv : v ∈ lowerSubspace (phi43RegularityStructureF κ).deg γ) {x y : ParabolicSpace}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : parabolicNorm (y - x) ≤ gammaNearRadius) :
    |M.gammaMap y x v (.old .one) - v (.old .one)| ≤
      ∑ i ∈ Finset.univ.filter (fun i : SymbolF => 0 < (phi43RegularityStructureF κ).deg i ∧
        (phi43RegularityStructureF κ).deg i < γ),
        |v i| * (CΓ * parabolicNorm (y - x) ^ (phi43RegularityStructureF κ).deg i) := by
  have hdec : M.gammaMap y x v (.old .one) =
      ∑ i, v i * M.gammaMap y x (Pi.single i 1) (.old .one) := by
    conv_lhs => rw [eq_sum_single v]
    simp [map_sum, Finset.sum_apply]
  have hd0 : (phi43RegularityStructureF κ).deg (.old .one) = 0 := rfl
  have hu := M.isGradedUnipotent_gammaMap y x
  rw [hdec, ← Finset.add_sum_erase _ _ (Finset.mem_univ (SymbolF.old .one)),
    hu.apply_single_self, mul_one, add_sub_cancel_left]
  set F := Finset.univ.filter (fun i : SymbolF => 0 < (phi43RegularityStructureF κ).deg i ∧
    (phi43RegularityStructureF κ).deg i < γ) with hF
  have hsub : F ⊆ Finset.univ.erase (SymbolF.old .one) := by
    intro i hi
    have := (Finset.mem_filter.1 hi).2.1
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    rw [hd0] at this
    exact lt_irrefl _ this
  have hzero : ∀ i ∈ Finset.univ.erase (SymbolF.old .one), i ∉ F →
      |v i * M.gammaMap y x (Pi.single i 1) (.old .one)| = 0 := by
    intro i hi hnot
    have hne : SymbolF.old Symbol.one ≠ i := fun h => (Finset.mem_erase.1 hi).1 h.symm
    by_cases hdi : 0 < (phi43RegularityStructureF κ).deg i
    · have hge : γ ≤ (phi43RegularityStructureF κ).deg i := by
        by_contra hlt
        exact hnot (Finset.mem_filter.2 ⟨Finset.mem_univ _, hdi, not_le.1 hlt⟩)
      rw [(mem_lowerSubspace).1 hv i hge, zero_mul, abs_zero]
    · rw [hu.apply_single_of_le hne (by rw [hd0]; exact not_lt.1 hdi), mul_zero, abs_zero]
  calc |∑ i ∈ Finset.univ.erase (SymbolF.old .one), v i * M.gammaMap y x (Pi.single i 1) (.old .one)|
      ≤ ∑ i ∈ Finset.univ.erase (SymbolF.old .one),
          |v i * M.gammaMap y x (Pi.single i 1) (.old .one)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ F, |v i * M.gammaMap y x (Pi.single i 1) (.old .one)| :=
        (Finset.sum_subset hsub hzero).symm
    _ ≤ _ := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨-, hi0, hiγ⟩ := Finset.mem_filter.1 hi
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have h := hΓ i (.old .one) hiγ (by rw [hd0]; exact hi0) x hx y hy hxy
        rw [hd0, sub_zero] at h
        exact h

variable {κ : Kappa} {N : ℕ} {η : NegExponent}
  {M : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {CPi CGam CΓ CGam₁ CΓ₁ T : ℝ}

/-- **Continuity of the unit coordinate on the slab.** -/
theorem phi43_unit_continuousWithinAt (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T)
    {noise : CanonicalNoise} {s : ℝ} (S : Phi43RestartSolution N η hyp.real.poly hyp.hT1 noise s)
    {z₀ : ParabolicSpace} (hz₀ : z₀ ∈ timeSlab T) :
    ContinuousWithinAt (fun y => S.U.val y (.old .one)) (timeSlab T) z₀ := by
  have hk : 0 < κ.1 := κ.2.1
  have hγ : 0 < gamma κ := by simp only [gamma]; linarith
  have hρ₀ : 0 < timeZeroDist z₀ := Inhomogeneity.timeZeroDist_pos_of_mem_timeSlab hz₀
  obtain ⟨hV, hT⟩ := Submodule.mem_inf.1 (S.U.mem_inf hz₀ hρ₀)
  set v := S.U.val z₀ with hv
  set F := Finset.univ.filter (fun i : SymbolF => 0 < (phi43RegularityStructureF κ).deg i ∧
    (phi43RegularityStructureF κ).deg i < gamma κ) with hF
  set w₀ := singularWeight timeZeroDist z₀ with hw₀
  have hw₀pos : 0 < w₀ := singularWeight_pos hρ₀
  set bound : ParabolicSpace → ℝ := fun y => ‖S.U‖ * parabolicNorm (y - z₀) ^ (gamma κ - 0) *
      (min w₀ (singularWeight timeZeroDist y)) ^ ((η : ℝ) - gamma κ) +
      ∑ i ∈ F, |v i| * (CΓ * parabolicNorm (y - z₀) ^ (phi43RegularityStructureF κ).deg i)
    with hbound
  -- the bound tends to zero
  have hd : ContinuousAt (fun y : ParabolicSpace => parabolicNorm (y - z₀)) z₀ :=
    (continuous_parabolicNorm.comp (continuous_id.sub continuous_const)).continuousAt
  have hd0 : parabolicNorm (z₀ - z₀) = 0 := by simp
  have hbc : ContinuousAt bound z₀ := by
    refine ContinuousAt.add ?_ ?_
    · refine ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) ?_
      · exact hd.rpow_const (Or.inr (by linarith))
      · have hw : ContinuousAt (fun y : ParabolicSpace => singularWeight timeZeroDist y) z₀ := by
          unfold singularWeight timeZeroDist
          exact (continuous_const.min (Real.continuous_sqrt.comp
            (continuous_abs.comp continuous_fst))).continuousAt
        have hm : ContinuousAt (fun y : ParabolicSpace => min w₀ (singularWeight timeZeroDist y)) z₀ :=
          continuousAt_const.min hw
        have hmpos : 0 < min w₀ (singularWeight timeZeroDist z₀) := lt_min hw₀pos hw₀pos
        exact hm.rpow_const (Or.inl hmpos.ne')
    · refine tendsto_finsetSum F fun i hi => ?_
      refine ContinuousAt.mul continuousAt_const (ContinuousAt.mul continuousAt_const ?_)
      have hdeg := (Finset.mem_filter.1 hi).2.1
      exact hd.rpow_const (Or.inr hdeg.le)
  have hb0 : bound z₀ = 0 := by
    simp only [hbound, hd0, sub_zero]
    rw [Real.zero_rpow hγ.ne', mul_zero, zero_mul, zero_add]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Real.zero_rpow (Finset.mem_filter.1 hi).2.1.ne', mul_zero, mul_zero]
  have hlim : Tendsto bound (𝓝 z₀) (𝓝 0) := by
    have := hbc.tendsto
    rwa [hb0] at this
  -- the estimate
  have hev : ∀ᶠ y in 𝓝[timeSlab T] z₀, |S.U.val y (.old .one) - S.U.val z₀ (.old .one)| ≤ bound y := by
    have h1 : ∀ᶠ y in 𝓝 z₀, parabolicNorm (y - z₀) < min (w₀ / 2) 1 := by
      have h0 : parabolicNorm (z₀ - z₀) < min (w₀ / 2) 1 := by
        rw [hd0]; exact lt_min (by linarith) one_pos
      exact hd.eventually (gt_mem_nhds h0)
    have h2 : ∀ᶠ y in 𝓝 z₀, w₀ / 2 < singularWeight timeZeroDist y := by
      have hw : ContinuousAt (fun y : ParabolicSpace => singularWeight timeZeroDist y) z₀ := by
        unfold singularWeight timeZeroDist
        exact (continuous_const.min (Real.continuous_sqrt.comp
          (continuous_abs.comp continuous_fst))).continuousAt
      exact hw.eventually (lt_mem_nhds (by linarith))
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, self_mem_nhdsWithin] with y hy1 hy2 hy
    have hρy : 0 < timeZeroDist y := Inhomogeneity.timeZeroDist_pos_of_mem_timeSlab hy
    have hdy : parabolicNorm (y - z₀) ≤ min w₀ (singularWeight timeZeroDist y) := by
      refine le_min ?_ ?_
      · exact (hy1.trans_le (min_le_left _ _)).le.trans (by linarith)
      · exact (hy1.trans_le (min_le_left _ _)).le.trans hy2.le
    have hd4 : parabolicNorm (y - z₀) ≤ gammaNearRadius := by
      unfold gammaNearRadius
      have := hy1.trans_le (min_le_right _ _)
      linarith
    have hinc := S.U.singularBoundOn_norm.2 z₀ hz₀ y hy hρ₀ hρy (by simpa [parabolicSemigroup] using hdy)
      (.old .one) (by
        change homogeneity κ .one < gamma κ
        simp only [homogeneity, gamma]; linarith)
    have hunit := abs_gammaMap_unit_sub_le M hyp.gamBaseNear v hT hz₀ hy hd4
    have e : S.U.val y (.old .one) - S.U.val z₀ (.old .one) =
        (S.U.val y - M.gammaMap y z₀ (S.U.val z₀)) (.old .one) +
          (M.gammaMap y z₀ (S.U.val z₀) (.old .one) - S.U.val z₀ (.old .one)) := by
      simp only [Pi.sub_apply]; ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ hunit)
    have hd0' : (phi43RegularityStructureF κ).deg (.old .one) = 0 := rfl
    rw [hd0'] at hinc
    simpa [parabolicSemigroup] using hinc
  -- conclude
  have hlim' : Tendsto bound (𝓝[timeSlab T] z₀) (𝓝 0) := hlim.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero' (Eventually.of_forall fun y => norm_nonneg _) ?_ hlim'
  filter_upwards [hev] with y hy
  simpa [Real.norm_eq_abs] using hy

end RegularityStructures.Phi43

end
