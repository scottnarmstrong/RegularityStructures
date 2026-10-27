module

public import GlobalPhi43.Flow.RoughWindowMeasurable
public import GlobalPhi43.Compactness.Embedding

/-! # Target embeddings commute with limits of the same classical family -/

public noncomputable section

open Set Filter Topology RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- The smooth identity is passed through the actual two producer limits.
Forcing and constants may agree across different lift orders or losses. -/
theorem FiniteLimitSystem.smooth_target_compatibility
    {N M : ℕ} {κ κ' : Kappa} {η γ : NegExponent} (hηγ : (η : ℝ) ≤ γ)
    {a : ℕ → LiftData N κ} {b : ℕ → LiftData M κ'}
    (u : FiniteLimitSystem η a) (v : FiniteLimitSystem γ b)
    (hf : ∀ n, (a n).forcing = (b n).forcing)
    (hc : ∀ n, (a n).constants = (b n).constants)
    (s q : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q)
    (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) :
    u.value s q (toHolderBesov η x) =
      holderBesovEmbed η γ hηγ (v.value s q (toHolderBesov γ x)) := by
  have hl := u.tendsto_smooth_value s q hs hq x hx
  have hr := (continuous_holderBesovEmbed η γ hηγ).continuousAt.tendsto.comp
    (v.tendsto_smooth_value s q hs hq x hx)
  have he (n : ℕ) :
      holderBesovEmbed η γ hηγ (toHolderBesov γ
        (smoothSolution (3 * (b n).constants.1 - 9 * (b n).constants.2)
          (shiftForcing s (b n).forcing) ((b n).shiftSmooth s) x hx q)) =
      toHolderBesov η (smoothSolution (3 * (a n).constants.1 - 9 * (a n).constants.2)
        (shiftForcing s (a n).forcing) ((a n).shiftSmooth s) x hx q) := by
    rw [holderBesovEmbed_toHolderBesov]
    simp only [hf n, hc n]
  simp only [Function.comp_def] at hr
  simp_rw [he] at hr
  exact tendsto_nhds_unique hl hr

/-- Physical comparison for 0<=s<=t, proved from actual common classical
endpoints before any use of the total map's negative-start fallback. -/
theorem EventFlow.nonnegative_target_compatibility {Ω : Type*} {N M : ℕ} {κ κ' : Kappa}
    {η γ : NegExponent} (hηγ : (η : ℝ) ≤ γ)
    {E F : Set Ω} {a : E → ℕ → LiftData N κ} {b : F → ℕ → LiftData M κ'}
    (u : EventFlow E η a) (v : EventFlow F γ b) (ω : Ω) (hE : ω ∈ E) (hF : ω ∈ F)
    (hf : ∀ n, (a ⟨ω, hE⟩ n).forcing = (b ⟨ω, hF⟩ n).forcing)
    (hc : ∀ n, (a ⟨ω, hE⟩ n).constants = (b ⟨ω, hF⟩ n).constants)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (x : HolderBesov γ) :
    u.value ω t s (holderBesovEmbed η γ hηγ x) =
      holderBesovEmbed η γ hηγ (v.value ω t s x) := by
  have he (f : C(Torus3, ℝ)) (hf' : IsSmoothOnTorus f) :
      u.value ω t s (holderBesovEmbed η γ hηγ (toHolderBesov γ f)) =
        holderBesovEmbed η γ hηγ (v.value ω t s (toHolderBesov γ f)) := by
    rw [holderBesovEmbed_toHolderBesov, u.value_on ⟨ω, hE⟩, v.value_on ⟨ω, hF⟩]
    exact (u.system ⟨ω, hE⟩).smooth_target_compatibility hηγ (v.system ⟨ω, hF⟩)
      hf hc s (t - s) hs (sub_nonneg.mpr hst) f hf'
  obtain ⟨f, hsm, hlim⟩ := exists_smooth_sequence γ x
  have hl := ((u.continuous_datum ω hs hst).comp
    (continuous_holderBesovEmbed η γ hηγ)).continuousAt.tendsto.comp hlim
  have hr := ((continuous_holderBesovEmbed η γ hηγ).comp
    (v.continuous_datum ω hs hst)).continuousAt.tendsto.comp hlim
  have hEq : (fun n => u.value ω t s (holderBesovEmbed η γ hηγ (toHolderBesov γ (f n)))) =
      (fun n => holderBesovEmbed η γ hηγ (v.value ω t s (toHolderBesov γ (f n)))) :=
    funext fun n => he (f n) (hsm n)
  simp only [Function.comp_def] at hl hr
  rw [hEq] at hl
  exact tendsto_nhds_unique hl hr

/-- Negative starts of the current producer are exactly its datum fallback.
This is not a negative-start PDE construction. -/
theorem EventFlow.value_negative_start {Ω : Type*} {N : ℕ} {κ : Kappa}
    {η : NegExponent} {E : Set Ω} {a : E → ℕ → LiftData N κ}
    (u : EventFlow E η a) (ω : Ω) (t s : ℝ) (hs : s < 0) (x : HolderBesov η) :
    u.value ω t s x = x := by
  by_cases hω : ω ∈ E
  · rw [u.value_on ⟨ω, hω⟩]
    simp only [FiniteLimitSystem.evolution, FiniteLimitSystem.value]
    exact dite_eq_right (show ¬(0 ≤ s ∧ 0 ≤ t - s) from fun h => (not_le.mpr hs) h.1)
  · exact u.value_off hω t s x

/-- All-real comparison of the exported total maps. Negative starts use only
the already defined identity branch, not a negative-start PDE solution. -/
theorem EventFlow.target_compatibility {Ω : Type*} {N M : ℕ} {κ κ' : Kappa}
    {η γ : NegExponent} (hηγ : (η : ℝ) ≤ γ)
    {E F : Set Ω} {a : E → ℕ → LiftData N κ} {b : F → ℕ → LiftData M κ'}
    (u : EventFlow E η a) (v : EventFlow F γ b) (ω : Ω) (hE : ω ∈ E) (hF : ω ∈ F)
    (hf : ∀ n, (a ⟨ω, hE⟩ n).forcing = (b ⟨ω, hF⟩ n).forcing)
    (hc : ∀ n, (a ⟨ω, hE⟩ n).constants = (b ⟨ω, hF⟩ n).constants)
    (s t : ℝ) (hst : s ≤ t) (x : HolderBesov γ) :
    u.value ω t s (holderBesovEmbed η γ hηγ x) =
      holderBesovEmbed η γ hηγ (v.value ω t s x) := by
  by_cases hs : 0 ≤ s
  · exact u.nonnegative_target_compatibility hηγ v ω hE hF hf hc s t hs hst x
  · rw [u.value_negative_start ω t s (lt_of_not_ge hs),
      v.value_negative_start ω t s (lt_of_not_ge hs)]

end GlobalPhi43.Flow
