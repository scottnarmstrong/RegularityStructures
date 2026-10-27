module

public import GlobalPhi43.Flow.StoppedPathComparison
public import Mathlib.Topology.Order.Compact

public noncomputable section

open MeasureTheory Set Filter Topology RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {η : NegExponent}
  {τ : Ω → ℝ≥0∞} {v g : Ω → ℝ → HolderBesov η}

/-- Countable positive rational horizons identify all real times before the
lifetime. This null-set assertion is for the fixed deterministic start under
consideration; it does not alter the reference event. -/
theorem ae_before_lifetime_of_compact_eq
    (hcompact : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P, ENNReal.ofReal T < τ ω →
      ∀ t ∈ Icc (0 : ℝ) T, v ω t = g ω t) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ENNReal.ofReal t < τ ω → v ω t = g ω t := by
  have hQ : ∀ᵐ ω ∂P, ∀ q : {q : ℚ // 0 < q}, ENNReal.ofReal (q.val : ℝ) < τ ω →
      ∀ t ∈ Icc (0 : ℝ) (q.val : ℝ), v ω t = g ω t :=
    ae_all_iff.mpr (fun q => hcompact (q.val : ℝ) (by exact_mod_cast q.property))
  filter_upwards [hQ] with ω hω t ht htτ
  obtain ⟨q, _, htq, hqτ⟩ := ENNReal.lt_iff_exists_rat_btwn.1 htτ
  have htq' : t < (q : ℝ) := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).1 htq
  have hq : (0 : ℚ) < q := by exact_mod_cast ht.trans_lt htq'
  exact hω ⟨q, hq⟩ hqτ t ⟨ht, htq'.le⟩

/-- A2 rules out finite lifetime after identification with a globally
continuous path. No exit event of the constructed limit path is used. -/
theorem ae_lifetime_top_of_global_path {x : C(Torus3, ℝ)}
    {U : ℝ → Ω → ℝ → C(Torus3, ℝ)} (h : IsPhi43Limit P η x U τ v)
    (hg : ∀ ω, ContinuousOn (g ω) (Ici (0 : ℝ)))
    (heq : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ENNReal.ofReal t < τ ω → v ω t = g ω t) :
    ∀ᵐ ω ∂P, τ ω = ⊤ := by
  filter_upwards [heq] with ω heq
  by_contra hτ
  have hc : ContinuousOn (fun t => ‖g ω t‖) (Icc (0 : ℝ) (τ ω).toReal) :=
    (hg ω).norm.mono (fun _ ht => ht.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc
  apply h.explosion ω (lt_top_iff_ne_top.mpr hτ)
  refine ⟨C, ?_⟩
  rintro _ ⟨t, ⟨ht, htτ⟩, rfl⟩
  change ‖v ω t‖ ≤ C
  rw [heq t ht htτ]
  exact hC ⟨t, ⟨ht, ((ENNReal.ofReal_lt_iff_lt_toReal ht hτ).1 htτ).le⟩, rfl⟩

theorem ae_global_identification {x : C(Torus3, ℝ)}
    {U : ℝ → Ω → ℝ → C(Torus3, ℝ)} (h : IsPhi43Limit P η x U τ v)
    (hg : ∀ ω, ContinuousOn (g ω) (Ici (0 : ℝ)))
    (hcompact : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P, ENNReal.ofReal T < τ ω →
      ∀ t ∈ Icc (0 : ℝ) T, v ω t = g ω t) :
    (∀ᵐ ω ∂P, τ ω = ⊤) ∧ ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → v ω t = g ω t := by
  have hpre := ae_before_lifetime_of_compact_eq hcompact
  have htop := ae_lifetime_top_of_global_path h hg hpre
  refine ⟨htop, ?_⟩
  filter_upwards [htop, hpre] with ω htop hpre t ht
  exact hpre t ht (by simpa only [htop] using ENNReal.ofReal_lt_top (r := t))

end GlobalPhi43.Flow
