module

public import GlobalPhi43.Assembly.WindowDense
public import GlobalPhi43.Invariant.FiniteProbabilityTransfer
public import GlobalPhi43Statements.Defs.IsConsistentWithTheoremA
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Consistency implies convergence in probability of positive-time samples -/

public noncomputable section

open MeasureTheory RegularityStructures RegularityStructures.Phi43 Set Filter Topology

namespace GlobalPhi43.Assembly

/-- A fixed reference sequence, independent of the probability space and all probes. -/
def referenceScale (n : ℕ) : ℝ := (1 / 2) ^ n

theorem referenceScale_mem (n : ℕ) : referenceScale n ∈ Ioc (0 : ℝ) 1 :=
  ⟨pow_pos (by norm_num) n, pow_le_one₀ (by norm_num) (by norm_num)⟩

theorem referenceScale_tendsto : Tendsto referenceScale atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
    Eventually.of_forall fun n => (referenceScale_mem n).1⟩

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- The consistency event controls a fixed evaluation; no stronger almost-sure consistency
premise, moment estimate or measurability of the regularised solution is assumed. -/
theorem sample_tendstoInMeasure_of_B3
    (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ) (a : ℝ)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hcons : IsConsistentWithTheoremA P W a η u)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x)
    (uε : ℝ → Ω → ℝ → C(Torus3, ℝ))
    (hsol : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsClassicalSolution
      (a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε) (ξ ε ω) x (uε ε ω))
    (t : Ioc (0 : ℝ) 1) :
    TendstoInMeasure P (fun n ω => toHolderBesov η (uε (referenceScale n) ω t)) atTop
      (fun ω => u t 0 (toHolderBesov η x) ω) := by
  rw [tendstoInMeasure_iff_norm]
  intro δ hδ
  have hc := ((hcons ρ hρ ξ hξ x hx uε hsol).1 1 zero_lt_one (δ / 2)
    (by linarith)).comp referenceScale_tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
  · intro n
    exact bot_le
  · intro n
    apply measure_mono
    intro ω hω
    exact ⟨t, ⟨t.property.1.le, t.property.2⟩, by dsimp at hω ⊢; linarith⟩

end GlobalPhi43.Assembly
