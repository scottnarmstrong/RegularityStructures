module

public import GlobalPhi43.Flow.LocalConsistency

public noncomputable section

open Set Metric RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

@[expose] def stateInclusion {η : NegExponent} {R L : ℝ} (h : R ≤ L)
    (x : StateBall η R) : StateBall η L := ⟨x.val, x.property.trans h⟩

theorem continuous_stateInclusion {η : NegExponent} {R L : ℝ} (h : R ≤ L) :
    Continuous (stateInclusion (η := η) h) := continuous_subtype_val.subtype_mk _

@[expose] def timeInclusion {ρ τ : ℝ} (h : ρ ≤ τ) (r : Icc (0 : ℝ) ρ) :
    Icc (0 : ℝ) τ := ⟨r.val, r.property.1, r.property.2.trans h⟩

/-- General overlap, including crossed choices of ball radius and time length. -/
theorem LocalChart.overlap_eq {N : ℕ} {κ : Kappa} {η : NegExponent}
    {L R A τ ρ θ s : ℝ} {K K' : ℝ≥0} {a : LiftData N κ}
    (u : LocalChart η L τ K a s) (v : LocalChart η R ρ K' a s)
    (hAL : A ≤ L) (hAR : A ≤ R) (hθτ : θ ≤ τ) (hθρ : θ ≤ ρ)
    (x : StateBall η A) (r : Icc (0 : ℝ) θ) :
    u.path (stateInclusion hAL x) (timeInclusion hθτ r) =
      v.path (stateInclusion hAR x) (timeInclusion hθρ r) := by
  have hc : IsClosed {z : StateBall η A |
      u.path (stateInclusion hAL z) (timeInclusion hθτ r) =
        v.path (stateInclusion hAR z) (timeInclusion hθρ r)} :=
    isClosed_eq ((continuous_eval_const _).comp
      (u.lipschitz.continuous.comp (continuous_stateInclusion hAL)))
      ((continuous_eval_const _).comp
        (v.lipschitz.continuous.comp (continuous_stateInclusion hAR)))
  have hd : Dense {z : StateBall η A |
      u.path (stateInclusion hAL z) (timeInclusion hθτ r) =
        v.path (stateInclusion hAR z) (timeInclusion hθρ r)} :=
    (dense_smoothBall η A).mono (by
      intro z hz
      let za : smoothBall η A := ⟨z, hz⟩
      let zl : smoothBall η L := ⟨stateInclusion hAL z,
        smoothRepresentative za, (smoothRepresentative_spec za).1,
        (smoothRepresentative_spec za).2⟩
      let zr : smoothBall η R := ⟨stateInclusion hAR z,
        smoothRepresentative za, (smoothRepresentative_spec za).1,
        (smoothRepresentative_spec za).2⟩
      change u.path zl.val (timeInclusion hθτ r) = v.path zr.val (timeInclusion hθρ r)
      rw [u.smooth_agreement zl, v.smooth_agreement zr,
        curveOnSmooth_eq τ _ _ _ zl (smoothRepresentative za)
          (smoothRepresentative_spec za).1 (smoothRepresentative_spec za).2,
        curveOnSmooth_eq ρ _ _ _ zr (smoothRepresentative za)
          (smoothRepresentative_spec za).1 (smoothRepresentative_spec za).2]
      rfl)
  have hh := hd x
  rw [hc.closure_eq] at hh
  exact hh

end GlobalPhi43.Flow
