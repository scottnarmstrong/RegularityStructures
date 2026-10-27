module

public import GlobalPhi43.Compactness.HeatCompact
public import GlobalPhi43.Compactness.ProbeSplit

@[expose] public noncomputable section

open Set Filter Topology RegularityStructures RegularityStructures.Datum RegularityStructures.PDE
open scoped ENNReal

namespace GlobalPhi43

/-- A positive heat probe of a stronger-norm ball has totally bounded image in `C(T³)`. -/
theorem totallyBounded_heatOp_stronger_ball (γ : NegExponent) {δ M : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 0 ≤ M) :
    TotallyBounded (heatOp δ '' {f : C(Torus3, ℝ) | ‖toHolderBesov γ f‖ ≤ M}) := by
  let C := (δ / 2) ^ ((γ : ℝ) / 2) * M
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by positivity) _) hM
  apply (totallyBounded_heatOp_ball (by linarith : 0 < δ / 2) hC).subset
  rintro _ ⟨f, hf, rfl⟩
  refine ⟨heatOp (δ / 2) f, ?_, ?_⟩
  · have hh := norm_heatOp_le_of_le_one γ (by linarith : 0 < δ / 2)
      (by linarith : δ / 2 ≤ 1) f
    rw [← norm_toHolderBesov] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg (by positivity) _))
  · rw [heatOp_heatOp (by positivity : 0 ≤ δ / 2) (by positivity : 0 ≤ δ / 2)]
    congr 1
    ring

/-- The stronger continuous-function ball is totally bounded in every strictly weaker completion.
The proof splits probe times and applies Arzelà–Ascoli to one positive heat probe. -/
theorem totallyBounded_toHolderBesov_stronger_ball (η γ : NegExponent) (hηγ : (η : ℝ) < γ)
    {M : ℝ} (hM : 0 ≤ M) :
    TotallyBounded (toHolderBesov η '' {f : C(Torus3, ℝ) | ‖toHolderBesov γ f‖ ≤ M}) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  have hp : 0 < ((γ : ℝ) - η) / 2 := by linarith
  have ht : Tendsto (fun δ : ℝ => δ ^ (((γ : ℝ) - η) / 2) * (2 * M)) (𝓝[>] 0) (𝓝 0) := by
    have hh : Tendsto (fun δ : ℝ => δ ^ (((γ : ℝ) - η) / 2)) (𝓝 0) (𝓝 0) := by
      simpa only [id_eq, Real.zero_rpow hp.ne'] using
        (tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 0) (𝓝 0)).rpow_const (Or.inr hp.le)
    simpa only [zero_mul] using (hh.mono_left nhdsWithin_le_nhds).mul_const (2 * M)
  have hevent : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      δ ^ (((γ : ℝ) - η) / 2) * (2 * M) < ε ∧ δ ∈ Ioc 0 1 := by
    filter_upwards [ht.eventually (gt_mem_nhds hε), self_mem_nhdsWithin,
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with δ hsmall hpos hlt
    exact ⟨hsmall, hpos, hlt.le⟩
  obtain ⟨δ, hsmall, hδ, hδ1⟩ := hevent.exists
  obtain ⟨T, hTsub, hTfin, hTcover⟩ := Metric.finite_approx_of_totallyBounded
    (totallyBounded_heatOp_stronger_ball γ hδ hδ1 hM) (ε / 2) (by linarith)
  have hrepr : ∀ y : T, ∃ f : C(Torus3, ℝ), ‖toHolderBesov γ f‖ ≤ M ∧ heatOp δ f = y := by
    intro y
    exact hTsub y.2
  choose g hg hgg using hrepr
  let : Fintype T := hTfin.fintype
  refine ⟨range (fun y : T => toHolderBesov η (g y)), finite_range _, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  change ‖toHolderBesov γ f‖ ≤ M at hf
  have hcover := hTcover (show heatOp δ f ∈ heatOp δ ''
      {f : C(Torus3, ℝ) | ‖toHolderBesov γ f‖ ≤ M} from ⟨f, hf, rfl⟩)
  obtain ⟨y, hy, hnear⟩ := mem_iUnion₂.mp hcover
  refine mem_iUnion₂.mpr ⟨toHolderBesov η (g ⟨y, hy⟩), ⟨⟨y, hy⟩, rfl⟩, ?_⟩
  change dist (toHolderBesov η f) (toHolderBesov η (g ⟨y, hy⟩)) < ε
  rw [dist_eq_norm, ← toHolderBesov_sub]
  apply lt_of_le_of_lt (norm_toHolderBesov_le_max_heatOp η γ hηγ hδ
    (f - g ⟨y, hy⟩) ?_) (max_lt hsmall ?_)
  · rw [toHolderBesov_sub]
    exact (norm_sub_le _ _).trans (by linarith [hg ⟨y, hy⟩])
  · rw [heatOp_sub, ← dist_eq_norm, hgg]
    exact (show dist (heatOp δ f) y < ε / 2 from hnear).trans (by linarith)

end GlobalPhi43
