module

public import GlobalPhi43.Flow.RoughLocal

public noncomputable section

open Set Metric RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

/-- The completion agrees with the classical curve for every smooth representative,
not only the representative selected in its definition. -/
theorem curveOnSmooth_eq {η : NegExponent} {R : ℝ} (τ c : ℝ) (f : SpaceTime → ℝ)
    (hf : IsSmoothOnSpaceTime f) (z : smoothBall η R)
    (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) (he : toHolderBesov η x = z.val.val) :
    curveOnSmooth τ c f hf z = smoothCurve η τ c f hf x hx := by
  have hr : smoothRepresentative z = x := toHolderBesov_injective η
    ((smoothRepresentative_spec z).2.trans he.symm)
  simp only [curveOnSmooth, hr]

theorem ballExtension_initial {η : NegExponent} {R τ c : ℝ} (hτ : 0 ≤ τ)
    (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f)
    (U : StateBall η R → C(Icc (0 : ℝ) τ, HolderBesov η)) (hU : Continuous U)
    (hm : ∀ x : smoothBall η R, U x.val = curveOnSmooth τ c f hf x) :
    ∀ x : StateBall η R, U x ⟨0, le_rfl, hτ⟩ = x.val := by
  let r : Icc (0 : ℝ) τ := ⟨0, le_rfl, hτ⟩
  have hc : IsClosed {x : StateBall η R | U x r = x.val} :=
    isClosed_eq ((continuous_eval_const r).comp hU) continuous_subtype_val
  have hd : Dense {x : StateBall η R | U x r = x.val} :=
    (dense_smoothBall η R).mono (by
      intro x hx
      change U x r = x.val
      rw [hm ⟨x, hx⟩]
      change toHolderBesov η (smoothSolution c f hf _ _ 0) = x.val
      rw [(smoothSolution_spec c f hf _ _).initial]
      exact (smoothRepresentative_spec ⟨x, hx⟩).2)
  intro x
  have hh := hd x
  rw [hc.closure_eq] at hh
  exact hh

end GlobalPhi43.Flow
