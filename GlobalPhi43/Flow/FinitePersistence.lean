module

public import GlobalPhi43.Flow.FiniteRestart

public noncomputable section

open Set Metric RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

/-- The already chosen classical solution for a smooth state and external start. -/
@[expose] def liftSmoothPath {N : ℕ} {κ : Kappa} {η : NegExponent} {L : ℝ}
    (a : LiftData N κ) (s : ℝ) (x : smoothBall η L) : ℝ → C(Torus3, ℝ) :=
  smoothSolution (3 * a.constants.1 - 9 * a.constants.2)
    (shiftForcing s a.forcing) (a.shiftSmooth s)
    (smoothRepresentative x) (smoothRepresentative_spec x).1

theorem liftSmoothPath_spec {N : ℕ} {κ : Kappa} {η : NegExponent} {L : ℝ}
    (a : LiftData N κ) (s : ℝ) (x : smoothBall η L) :
    IsClassicalSolution (3 * a.constants.1 - 9 * a.constants.2)
      (shiftForcing s a.forcing) (smoothRepresentative x) (liftSmoothPath a s x) :=
  smoothSolution_spec _ _ _ _ _

/-- A uniform later-time state bound on the chosen smooth paths, for every smooth
datum in the fixed closed ball. -/
@[expose] def LaterStateBound {N : ℕ} {κ : Kappa} (η : NegExponent)
    (L T h₀ R : ℝ) (a : LiftData N κ) (s : ℝ) : Prop :=
  ∀ x : smoothBall η L, ∀ r ∈ Icc (h₀ / 2) T,
    holderBesovENorm η (liftSmoothPath a s x r) ≤ ENNReal.ofReal R

/-- Persistence chooses the first time and radius before starts, lifts and data. -/
theorem exists_firstStateBound {κ : Kappa} (hκE : κ.1 ∉ Statements.excludedKappa)
    {N : ℕ} (hN : 5 ≤ N) {η : NegExponent}
    (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η)
    (T L B : ℝ) (hT : 1 ≤ T) (hL : 1 ≤ L) (hB : 1 ≤ B) :
    ∃ h₀ R₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ (S : ℝ), 0 ≤ S → ∀ (a : LiftData N κ) (s : Icc (0 : ℝ) S),
        Statements.phi43Size κ η (T + S) a.model a.potential ≤ ENNReal.ofReal B →
        ∀ (x : smoothBall η L) (r : ℝ), r ∈ Icc (0 : ℝ) h₀ →
          holderBesovENorm η (liftSmoothPath a s.val x r) ≤ ENNReal.ofReal R₀ := by
  obtain ⟨h₀, R₀, hh₀, hh₀1, hp⟩ :=
    Persistence.phi43_persistence κ hκE N hN η hη hκη L B hL hB
  refine ⟨h₀, R₀, hh₀, hh₀1, ?_⟩
  intro S _ a s hs x r hr
  have hx : holderBesovENorm η (smoothRepresentative x) ≤ ENNReal.ofReal L := by
    rw [← enorm_toHolderBesov, (smoothRepresentative_spec x).2, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [mem_closedBall, dist_zero_right] using x.val.property)
  have hs' := (Attachment.phi43Size_translate_le κ η T s.property.1 s.property.2
    a.model a.potential).trans hs
  have hu := liftSmoothPath_spec a s.val x
  exact hp _ _ _ _ _ _ T (moderateLift_time_translate a.moderate s.val) hu hT hs'
    0 ⟨le_rfl, by linarith⟩ (by simpa only [hu.initial] using hx) r (by simpa using hr)

/-- Joining the first persistence interval and the supplied later-time interval
leaves no gap and includes all terminal faces. Lift size is not the state radius. -/
theorem stateBound_first_later {η : NegExponent} {h₀ T R₀ R : ℝ}
    (hh₀ : 0 < h₀) (u : ℝ → C(Torus3, ℝ))
    (hfirst : ∀ r ∈ Icc (0 : ℝ) h₀, holderBesovENorm η (u r) ≤ ENNReal.ofReal R₀)
    (hlater : ∀ r ∈ Icc (h₀ / 2) T, holderBesovENorm η (u r) ≤ ENNReal.ofReal R) :
    ∀ r ∈ Icc (0 : ℝ) T,
      holderBesovENorm η (u r) ≤ ENNReal.ofReal (max 1 (max R₀ R)) := by
  intro r hr
  by_cases hh : r ≤ h₀
  · exact (hfirst r ⟨hr.1, hh⟩).trans (ENNReal.ofReal_le_ofReal
      ((le_max_left R₀ R).trans (le_max_right _ _)))
  · exact (hlater r ⟨by linarith, hr.2⟩).trans (ENNReal.ofReal_le_ofReal
      ((le_max_right R₀ R).trans (le_max_right _ _)))

end GlobalPhi43.Flow
