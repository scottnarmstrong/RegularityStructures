module

public import GlobalPhi43.Attachment.PsiModelTests
public import GlobalPhi43.Attachment.SourceTreeRegularity
public import GlobalPhi43.MW20.KernelCoordinateSeminorm

public section

namespace GlobalPhi43.Attachment

open MeasureTheory RegularityStructures RegularityStructures.Phi43 Local MW20 Set

/-- Vector part of clause (ii), obtained from actual coordinate realisations
and the source spatial sup norm, without an integrability premise on callers. -/
theorem coordinate_tree_seminorm (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsSmoothOnSpaceTime f → Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
    ∀ (S : Set ParabolicSpace), IsCompact S →
      recenteredXVSeminorm (mw20TestingKernel Φ hΦ) S κ.1
        (fun y => treeV N f (C₁ C) (spaceTimeProj y)) ≤
        ENNReal.ofReal K * (1+Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3})^3 := by
  obtain ⟨K,hK,hbound⟩ := psi_model_test_bound N κ Φ hΦ
  refine ⟨K,hK,?_⟩
  intro f C Z hf hg hZ S hS
  let V := fun y => treeV N f (C₁ C) (spaceTimeProj y)
  let B := K*(1+(Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3}).toReal)^3
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hV : Continuous V := (continuous_treeV (N := N) hf (C₁ C)).comp continuous_spaceTimeProj
  have hh : recenteredXVSeminorm (mw20TestingKernel Φ hΦ) S κ.1 V ≤ ENNReal.ofReal B := by
    unfold recenteredXVSeminorm
    refine iSup_le fun x => iSup_le fun hx => iSup_le fun t => iSup_le fun ht => ?_
    have ht1 : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1,ht.2.le⟩
    have hi := mw20_coordinateTree_integrable Φ hΦ V hV x ht.1 ht.2.le
    have hc (i : Fin 3) :
        |coordinateTreeTest (mw20TestingKernel Φ hΦ) V t x i| ≤ B*t^(-2*κ.1) := by
      have hr := source_XV_regular hf hg hZ x i
      have hb := hbound f C Z hZ hg S hS x hx t ht1 (.psiSqX i)
        ((homogeneity_neg_iff_isFMinus κ (.psiSqX i)).mpr (by simp [isFMinus]))
        (fun y => (y.2 i-x.2 i)*V y) hr.1 hr.2 (by
          intro r hrt y
          exact (realise hf hg hZ x hrt y).2.2.2.2.2.2.1 i)
      have he : coordinateTreeTest (mw20TestingKernel Φ hΦ) V t x i =
          infinitePastSmooth Φ hΦ t ht.1 (fun y => (y.2 i-x.2 i)*V y) x := by
        unfold coordinateTreeTest
        change (ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ)
          (∫ z, V (x+z) • z.2 ∂mw20TestingKernel Φ hΦ t) = _
        rw [← (ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).integral_comp_comm hi]
        rw [← reconstruction_pastSmooth_eq_density Φ hΦ ht.1 ht.2.le]
        unfold pastSmooth
        rw [mw20TestingKernel_pos Φ hΦ ht.1]
        apply integral_congr_ae
        filter_upwards [] with w
        simp only [ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul,
          Prod.snd_add, Pi.add_apply, add_sub_cancel_left]
        ring
      rw [he]
      exact hb
    have hn : ‖coordinateTreeTest (mw20TestingKernel Φ hΦ) V t x‖ ≤ B*t^(-2*κ.1) :=
      (pi_norm_le_iff_of_nonneg (mul_nonneg hB (Real.rpow_nonneg ht.1.le _))).mpr
        (fun i => by simpa only [Real.norm_eq_abs] using hc i)
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ t^(2*κ.1)*(B*t^(-2*κ.1)) := mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg ht.1.le _)
      _ = B*(t^(2*κ.1)*t^(-2*κ.1)) := by ring
      _ = B := by
        rw [← Real.rpow_add ht.1]
        have he : 2*κ.1 + -2*κ.1 = 0 := by ring
        rw [he, Real.rpow_zero, mul_one]
  have hfin : Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3} ≠ ⊤ := by
    obtain ⟨noise,hn,hm⟩ := hZ
    exact hm.2.2.1 _ (isCompact_parabolic_enlargement hS (by norm_num : (0 : ℝ) ≤ 3))
  convert hh using 1
  dsimp only [B]
  rw [ENNReal.ofReal_mul hK.le, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal hfin]

end GlobalPhi43.Attachment
