module

public import GlobalPhi43.Compactness.Smoothing
public import RegularityStructures.Abstract.Datum.HeatDeriv1
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public noncomputable section

open Set Filter Topology RegularityStructures RegularityStructures.Datum RegularityStructures.PDE

open scoped NNReal BoundedContinuousFunction

namespace GlobalPhi43

/-- A compact fundamental cube, including its boundary. -/
abbrev HeatCube := ↥(Icc (0 : Fin 3 → ℝ) 1)

/-- Restriction of a torus function to the compact fundamental cube. -/
def heatCubeRestrict (f : C(Torus3, ℝ)) : HeatCube →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => f (torusProj x), f.continuous.comp (continuous_torusProj.comp continuous_subtype_val)⟩

/-- Restriction to the fundamental cube preserves the supremum distance. -/
theorem isometry_heatCubeRestrict : Isometry heatCubeRestrict := by
  apply Isometry.of_dist_eq
  intro f g
  apply le_antisymm
  · apply (BoundedContinuousFunction.dist_le (dist_nonneg)).mpr
    intro x
    exact ContinuousMap.dist_apply_le_dist (f := f) (g := g) (torusProj x)
  · apply (ContinuousMap.dist_le (dist_nonneg)).mpr
    intro x
    have hx : torusRep x ∈ Icc (0 : Fin 3 → ℝ) 1 := by
      constructor
      · intro i
        exact (AddCircle.equivIco (1 : ℝ) 0 (x i)).2.1
      · intro i
        change ((AddCircle.equivIco (1 : ℝ) 0 (x i) : Ico (0 : ℝ) (0 + 1)) : ℝ) ≤ 1
        simpa only [zero_add] using (AddCircle.equivIco (1 : ℝ) 0 (x i)).2.2.le
    have h := BoundedContinuousFunction.dist_coe_le_dist
      (f := heatCubeRestrict f) (g := heatCubeRestrict g) (⟨torusRep x, hx⟩ : HeatCube)
    simpa only [heatCubeRestrict, BoundedContinuousFunction.mkOfCompact_apply,
      ContinuousMap.coe_mk, torusProj_torusRep] using h

/-- A uniform bound on partial derivatives bounds the derivative operator. -/
private theorem norm_ofPartials_le {v : Fin 3 → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ i, |v i| ≤ C) : ‖ofPartials v‖ ≤ 3 * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by have := derivConst_nonneg; positivity)
  intro k
  rw [ofPartials_apply]
  calc
    ‖∑ i : Fin 3, k i • v i‖ ≤ ∑ i : Fin 3, ‖k i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖k‖ * C := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm k i) (by simpa only [Real.norm_eq_abs] using hv i)
        (norm_nonneg _) (norm_nonneg _)
    _ = 3 * C * ‖k‖ := by simp; ring

/-- Positive-time heat evolution is uniformly Lipschitz on the lift of a supremum-norm ball. -/
theorem lipschitzWith_heatOp_lift {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    {f : C(Torus3, ℝ)} (hf : ‖f‖ ≤ M) :
    LipschitzWith ⟨3 * (derivConst * (Real.sqrt t)⁻¹ * M), by have := derivConst_nonneg; positivity⟩
      (fun y : Fin 3 → ℝ => heatOp t f (torusProj y)) := by
  obtain ⟨V, hV, hb⟩ := exists_hasTorusDeriv_heatOp f ht
  apply lipschitzWith_of_nnnorm_fderiv_le
    (fun y => (hV y).differentiableAt)
  intro y
  rw [(hV y).fderiv]
  change ‖ofPartials (V (torusProj y))‖ ≤ _
  apply norm_ofPartials_le (by have := derivConst_nonneg; positivity)
  intro i
  exact (hb _ i).trans (mul_le_mul_of_nonneg_left hf (by have := derivConst_nonneg; positivity))

/-- The image of a supremum-norm ball under a positive heat time is totally bounded. -/
theorem totallyBounded_heatOp_ball {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M) :
    TotallyBounded (heatOp t '' {f : C(Torus3, ℝ) | ‖f‖ ≤ M}) := by
  let S := heatCubeRestrict '' (heatOp t '' {f : C(Torus3, ℝ) | ‖f‖ ≤ M})
  let L : ℝ≥0 := ⟨3 * (derivConst * (Real.sqrt t)⁻¹ * M), by have := derivConst_nonneg; positivity⟩
  have hLip (g : S) : LipschitzWith L (g : HeatCube →ᵇ ℝ) := by
    obtain ⟨_, ⟨f, hf, rfl⟩, hg⟩ := g.2
    rw [← hg]
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (lipschitzWith_heatOp_lift ht hM hf).dist_le_mul x.val y.val
  have heq : Equicontinuous ((↑) : S → HeatCube → ℝ) := by
    intro x
    apply Metric.equicontinuousAt_iff.mpr
    intro ε hε
    refine ⟨ε / ((L : ℝ) + 1), div_pos hε (by have := derivConst_nonneg; positivity), ?_⟩
    intro y hy g
    have h := (hLip g).dist_le_mul x y
    rw [dist_comm x] at h
    have hl : 0 ≤ (L : ℝ) := L.2
    have hd : 0 ≤ dist y x := dist_nonneg
    have hh := (lt_div_iff₀ (by have := derivConst_nonneg; positivity : 0 < (L : ℝ) + 1)).mp hy
    linarith
  have hcompact : IsCompact (closure S) := by
    apply BoundedContinuousFunction.arzela_ascoli (Icc (-M) M) isCompact_Icc S ?_ heq
    intro g x hg
    obtain ⟨_, ⟨f, hf, rfl⟩, rfl⟩ := hg
    have hb := (ContinuousMap.norm_coe_le_norm (heatOp t f) (torusProj x)).trans
      ((norm_heatOp_le t f).trans hf)
    change -M ≤ heatOp t f (torusProj x) ∧ heatOp t f (torusProj x) ≤ M
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hb)
  exact (totallyBounded_image_iff isometry_heatCubeRestrict.isUniformInducing).mp
    (hcompact.totallyBounded.subset subset_closure)

end GlobalPhi43
