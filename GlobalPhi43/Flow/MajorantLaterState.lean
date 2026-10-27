module

public import GlobalPhi43.Flow.WindowMajorantEnvelope
public import GlobalPhi43.Flow.FinitePersistence
public import GlobalPhi43.Flow.ClassicalTranslation
public import GlobalPhi43Statements.Defs.Characterisations

@[expose] public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

/-- The every-start unit-time majorant for the chosen classical solutions of all
smooth initial data, without a later-state radius assumption. -/
def EveryStartMajorant {N : ℕ} {κ : Kappa} (c : ℝ) (A : ℕ → LiftData N κ) : Prop :=
  ∀ n (r : ℝ), 0 ≤ r → ∀ (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x),
    ∀ τ ∈ Ioc (0 : ℝ) 1,
      ENNReal.ofReal (Real.sqrt τ) * holderBesovENorm (lossExponent κ)
        (smoothSolution (3 * (A n).constants.1 - 9 * (A n).constants.2)
          (shiftForcing r (A n).forcing) ((A n).shiftSmooth r) x hx τ) ≤
        windowMajorantRhs c κ (A n).model (A n).potential r

/-- Classical uniqueness applies the literal majorant to a restarted actual path. -/
theorem EveryStartMajorant.apply_classical {N : ℕ} {κ : Kappa} {c : ℝ}
    {A : ℕ → LiftData N κ} (h : EveryStartMajorant c A) (n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) (u : ℝ → C(Torus3, ℝ))
    (hu : IsClassicalSolution (3 * (A n).constants.1 - 9 * (A n).constants.2)
      (shiftForcing r (A n).forcing) x u) (τ : ℝ) (hτ : τ ∈ Ioc (0 : ℝ) 1) :
    ENNReal.ofReal (Real.sqrt τ) * holderBesovENorm (lossExponent κ) (u τ) ≤
      windowMajorantRhs c κ (A n).model (A n).potential r := by
  have he := smoothSolution_eq_classical _ _ ((A n).shiftSmooth r) x hx hu hτ.1.le
  simpa only [he] using h n r hr x hx τ hτ

/-- Cancel a positive square-root weight without converting a possibly infinite norm toReal. -/
theorem le_of_sqrt_weight {V : ℝ≥0∞} {h₀ τ M : ℝ} (hh₀ : 0 < h₀)
    (hτ : h₀ / 2 ≤ τ)
    (h : ENNReal.ofReal (Real.sqrt τ) * V ≤ ENNReal.ofReal M) :
    V ≤ ENNReal.ofReal (Real.sqrt (2 / h₀) * M) := by
  have hd : 0 < Real.sqrt (h₀ / 2) := Real.sqrt_pos.2 (by positivity)
  have he : Real.sqrt (2 / h₀) = (Real.sqrt (h₀ / 2))⁻¹ := by
    rw [← Real.sqrt_inv, inv_div]
  have hf : 1 ≤ Real.sqrt (2 / h₀) * Real.sqrt τ := by
    rw [he]
    calc 1 = (Real.sqrt (h₀ / 2))⁻¹ * Real.sqrt (h₀ / 2) := (inv_mul_cancel₀ hd.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hτ) (by positivity)
  have hf' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.sqrt (2 / h₀)) * ENNReal.ofReal (Real.sqrt τ) := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hf
  calc V = 1 * V := (one_mul V).symm
    _ ≤ (ENNReal.ofReal (Real.sqrt (2 / h₀)) * ENNReal.ofReal (Real.sqrt τ)) * V :=
      mul_le_mul' hf' le_rfl
    _ = ENNReal.ofReal (Real.sqrt (2 / h₀)) * (ENNReal.ofReal (Real.sqrt τ) * V) := mul_assoc _ _ _
    _ ≤ ENNReal.ofReal (Real.sqrt (2 / h₀)) * ENNReal.ofReal M := mul_le_mul' le_rfl h
    _ = _ := (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm

/-- The q -> (min(q,1),s+q-min(q,1)) physical application, including both endpoints.
The uniform envelope bounds only the majorant's RHS, not a solution or later radius. -/
theorem laterStateBound_of_majorant {N : ℕ} {κ : Kappa} (η : NegExponent)
    (hη : (η : ℝ) ≤ lossExponent κ) (c : ℝ) (A : ℕ → LiftData N κ)
    (hmajorant : EveryStartMajorant c A) (S T L h₀ M : ℝ)
    (hh₀ : 0 < h₀) (hh₀1 : h₀ ≤ 1)
    (henvelope : ∀ n (r : ℝ), 0 ≤ r → r ≤ S + T →
      windowMajorantRhs c κ (A n).model (A n).potential r ≤ ENNReal.ofReal M) :
    ∃ Rlater : ℝ, 1 ≤ Rlater ∧ ∀ n (s : ℝ), s ∈ Icc (0 : ℝ) S →
      LaterStateBound η L T h₀ Rlater (A n) s := by
  refine ⟨max 1 (Real.sqrt (2 / h₀) * M), le_max_left _ _, ?_⟩
  intro n s hs x q hq
  let τ := min q 1
  let d := q - τ
  let r := s + d
  have hqpos : 0 < q := lt_of_lt_of_le (by linarith : 0 < h₀ / 2) hq.1
  have hτpos : 0 < τ := lt_min hqpos one_pos
  have hτ1 : τ ≤ 1 := min_le_right _ _
  have hτlower : h₀ / 2 ≤ τ := le_min hq.1 (by linarith)
  have hd : 0 ≤ d := sub_nonneg.mpr (min_le_left _ _)
  have hr : 0 ≤ r := add_nonneg hs.1 hd
  have hrST : r ≤ S + T := by
    dsimp [r, d]
    linarith [hs.2, hq.2, hτpos]
  let u := liftSmoothPath (A n) s x
  have hu := liftSmoothPath_spec (A n) s x
  have hx : IsSmoothOnTorus (u d) := smoothSolution_smooth_state
    (3 * (A n).constants.1 - 9 * (A n).constants.2)
    (shiftForcing s (A n).forcing) ((A n).shiftSmooth s)
    (smoothRepresentative x) (smoothRepresentative_spec x).1 hd
  have hv := isClassicalSolution_shift hu hd
  change IsClassicalSolution _ (shiftForcing d (shiftForcing s (A n).forcing))
    (u d) (fun t => u (d + t)) at hv
  rw [shiftForcing_add] at hv
  have hweighted := hmajorant.apply_classical n r hr (u d) hx (fun t => u (d + t)) hv τ ⟨hτpos, hτ1⟩
  have hclock : d + τ = q := sub_add_cancel q τ
  rw [hclock] at hweighted
  have hb := le_of_sqrt_weight hh₀ hτlower (hweighted.trans (henvelope n r hr hrST))
  exact ((holderBesovENorm_mono hη (u q)).trans hb).trans
    (ENNReal.ofReal_le_ofReal (le_max_right _ _))

/-- On the same event E and dyadic family A, each chosen h0 in (0,1] yields a later
radius before all indices, starts and smooth data are quantified. The every-start
analytic majorant is assumed; the later-state bound is derived. -/
theorem reference_laterStateBound {Ω : Type*} (N : ℕ) (κ : Kappa)
    (ρ : ParabolicSpace → ℝ) (a : ℝ) (η : NegExponent)
    (hκη : κ.1 < -(1 / 2 : ℝ) - η) (c : ℝ) (hc : 0 ≤ c)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (ω : Ω) (hω : ω ∈ referenceEvent N κ ρ a η ξ hsmooth)
    (hmajorant : EveryStartMajorant c (dyadicLiftData N κ ρ a η ξ hsmooth ω hω))
    (S T L h₀ : ℝ) (hS : 0 ≤ S) (hT : 1 ≤ T) (hh₀ : 0 < h₀) (hh₀1 : h₀ ≤ 1) :
    ∃ Rlater : ℝ, 1 ≤ Rlater ∧ ∀ n (s : ℝ), s ∈ Icc (0 : ℝ) S →
      LaterStateBound η L T h₀ Rlater (dyadicLiftData N κ ρ a η ξ hsmooth ω hω n) s := by
  let Z := referenceAttachedModel N κ ρ a ξ hsmooth
  let ψ := referencePotential ξ hsmooth
  obtain ⟨k, hk⟩ := exists_nat_ge (S + T + 18)
  have hk18 : 18 ≤ k := by exact_mod_cast (show (18 : ℝ) ≤ k by linarith)
  have hwindow : ω ∈ windowEvent (lossExponent κ) Z ψ := hω.2
  apply laterStateBound_of_majorant η (by change (η : ℝ) ≤ -(1 / 2 : ℝ) - κ.1; linarith)
    c (dyadicLiftData N κ ρ a η ξ hsmooth ω hω) hmajorant S T L h₀
    (windowMajorantEnvelope c Z ψ k ω) hh₀ hh₀1
  intro n r hr hrST
  exact windowMajorantRhs_le_envelope c hc Z ψ k hk18 hwindow (n + 1) hr (by linarith)

end GlobalPhi43.Flow
