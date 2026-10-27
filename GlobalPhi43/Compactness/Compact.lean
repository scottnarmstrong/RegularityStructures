module

public import GlobalPhi43.Compactness.TotalBounded
public import GlobalPhi43.Compactness.Lifting

@[expose] public noncomputable section

open Set RegularityStructures
open scoped ENNReal

namespace GlobalPhi43

/-- total boundedness of the continuous stronger-norm ball, with no lower bound on η. -/
theorem totallyBounded_strongerNorm_ball (η γ : NegExponent) (hηγ : (η : ℝ) < γ)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) :
    TotallyBounded (toHolderBesov η '' {f : C(Torus3, ℝ) | holderBesovENorm γ f ≤ M}) := by
  have he : {f : C(Torus3, ℝ) | holderBesovENorm γ f ≤ M} =
      {f : C(Torus3, ℝ) | ‖toHolderBesov γ f‖ ≤ M.toReal} := by
    ext f
    rw [mem_ofPred_eq, mem_ofPred_eq, norm_toHolderBesov]
    exact (ENNReal.toReal_le_toReal (holderBesovENorm_lt_top γ.2.le f).ne hM).symm
  rw [he]
  exact totallyBounded_toHolderBesov_stronger_ball η γ hηγ ENNReal.toReal_nonneg

/-- Finite stronger extended-norm sublevels are compact in the weaker little completion. -/
theorem isCompact_extNorm_sublevel (η γ : NegExponent) (hηγ : (η : ℝ) < γ)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) :
    IsCompact {z : HolderBesov η | extNorm η γ z ≤ M} := by
  rw [extNorm_sublevel_eq_closure]
  exact (totallyBounded_strongerNorm_ball η γ hηγ hM).closure.isCompact_of_isClosed isClosed_closure

/-- The canonical embedding at equal exponents is the identity. -/
theorem holderBesovEmbed_refl (η : NegExponent) (z : HolderBesov η) :
    holderBesovEmbed η η le_rfl z = z := by
  have hh := holderBesovEmbed_unique η η le_rfl id continuous_id (fun _ => rfl)
  exact congrFun hh.symm z

/-- Finite stronger sublevels lie in every intermediate little completion, including β = η. -/
theorem exists_holderBesovEmbed_eq_of_extNorm_le_finite_le (η β γ : NegExponent)
    (hηβ : (η : ℝ) ≤ β) (hβγ : (β : ℝ) < γ)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) {z : HolderBesov η} (hz : extNorm η γ z ≤ M) :
    ∃ w : HolderBesov β, holderBesovEmbed η β hηβ w = z ∧ ‖w‖ₑ ≤ M := by
  by_cases hstrict : (η : ℝ) < β
  · exact exists_holderBesovEmbed_eq_of_extNorm_le_finite η β γ hstrict hβγ hM hz
  · have he : η = β := Subtype.ext (le_antisymm hηβ (le_of_not_gt hstrict))
    subst β
    refine ⟨z, holderBesovEmbed_refl η z, ?_⟩
    rw [← extNorm_self]
    exact (extNorm_mono η hβγ.le z).trans hz

/-- Every preimage of a stronger sublevel satisfies the literal intermediate norm bound. -/
theorem enorm_le_of_extNorm_holderBesovEmbed_le (η β γ : NegExponent)
    (hηβ : (η : ℝ) ≤ β) (hβγ : (β : ℝ) < γ)
    {M : ℝ≥0∞} {w : HolderBesov β}
    (hw : extNorm η γ (holderBesovEmbed η β hηβ w) ≤ M) : ‖w‖ₑ ≤ M := by
  rw [extNorm_holderBesovEmbed] at hw
  rw [← extNorm_self]
  exact (extNorm_mono β hβγ.le w).trans hw

/-- Compact finite sublevels and containment in the stronger space with bound M. -/
theorem compact_strongerNorm_sublevel (η β γ : NegExponent)
    (hηβ : (η : ℝ) ≤ β) (hβγ : (β : ℝ) < γ)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) :
    IsCompact {z : HolderBesov η | extNorm η γ z ≤ M} ∧
      (∀ z : HolderBesov η, extNorm η γ z ≤ M →
        ∃ w : HolderBesov β, holderBesovEmbed η β hηβ w = z ∧ ‖w‖ₑ ≤ M) ∧
      ∀ w : HolderBesov β, extNorm η γ (holderBesovEmbed η β hηβ w) ≤ M → ‖w‖ₑ ≤ M :=
  ⟨isCompact_extNorm_sublevel η γ (lt_of_le_of_lt hηβ hβγ) hM,
    (fun _ hz => exists_holderBesovEmbed_eq_of_extNorm_le_finite_le η β γ hηβ hβγ hM hz),
    fun _ hw => enorm_le_of_extNorm_holderBesovEmbed_le η β γ hηβ hβγ hw⟩

end GlobalPhi43
