module

public import GlobalPhi43.Flow.FinitePersistence

public noncomputable section

open Set Metric RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

/-- Analytic inputs for a conditional finite chart: the model-size bound and the
later-state bound, without an iterated comparison or convergence assumption. -/
@[expose] def FiniteLiftCondition {N : ℕ} {κ : Kappa} (η : NegExponent)
    (L T B h₀ R S : ℝ) (a : LiftData N κ) (s : ℝ) : Prop :=
  Statements.phi43Size κ η (T + S) a.model a.potential ≤ ENNReal.ofReal B ∧
    LaterStateBound η L T h₀ R a s

/-- Conditional finite-horizon rough charts, built from the actual classical
paths. Persistence precedes the later radius, which precedes the common mesh;
all those witnesses precede starts, lifts and data. -/
theorem exists_conditionalFiniteCharts {κ : Kappa} (hκE : κ.1 ∉ Statements.excludedKappa)
    {N : ℕ} (hN : 5 ≤ N) {η : NegExponent}
    (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η)
    (T L B : ℝ) (hT : 1 ≤ T) (hL : 1 ≤ L) (hB : 1 ≤ B) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ R : ℝ, 1 ≤ R →
      ∃ h : ℝ, 0 < h ∧ ∃ K : ℝ≥0, 1 ≤ K ∧ ∃ mesh : RestartMesh T h,
        (∀ (S : ℝ), 0 ≤ S → ∀ (a : LiftData N κ) (s : Icc (0 : ℝ) S),
          FiniteLiftCondition η L T B h₀ R S a s.val →
          Nonempty (LocalChart η L T (finiteRestartFactor K mesh.count) a s.val)) ∧
        ∀ (S : ℝ), 0 ≤ S → ∀ (a b : LiftData N κ) (s : Icc (0 : ℝ) S),
          FiniteLiftCondition η L T B h₀ R S a s.val →
          FiniteLiftCondition η L T B h₀ R S b s.val →
          ∀ (u : LocalChart η L T (finiteRestartFactor K mesh.count) a s.val)
            (v : LocalChart η L T (finiteRestartFactor K mesh.count) b s.val)
            (x y : StateBall η L), edist (u.path x) (v.path y) ≤
            finiteRestartFactor K mesh.count * (edist x y +
              Statements.phi43Dist κ η (T + S) a.model b.model a.potential b.potential) := by
  obtain ⟨h₀, R₀, hh₀, hh₀1, hfirst⟩ :=
    exists_firstStateBound hκE hN hη hκη T L B hT hL hB
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro R _
  obtain ⟨h, hh, K, hK, mesh, hcompare⟩ := exists_finiteRestartEstimate hN hη hκη
    T (max 1 (max R₀ R)) B hT (le_max_left _ _) hB
  let H := finiteRestartFactor K mesh.count
  have hcurves (S : ℝ) (hS : 0 ≤ S) (a b : LiftData N κ) (s : Icc (0 : ℝ) S)
      (ha : FiniteLiftCondition η L T B h₀ R S a s.val)
      (hb : FiniteLiftCondition η L T B h₀ R S b s.val) (x y : smoothBall η L) :
      edist (curveOnSmooth T (3 * a.constants.1 - 9 * a.constants.2)
        (shiftForcing s.val a.forcing) (a.shiftSmooth s.val) x)
        (curveOnSmooth T (3 * b.constants.1 - 9 * b.constants.2)
        (shiftForcing s.val b.forcing) (b.shiftSmooth s.val) y) ≤
        H * (edist x.val y.val + Statements.phi43Dist κ η (T + S)
          a.model b.model a.potential b.potential) := by
    have hsa := stateBound_first_later hh₀ (liftSmoothPath a s.val x)
      (hfirst S hS a s ha.1 x) (ha.2 x)
    have hsb := stateBound_first_later hh₀ (liftSmoothPath b s.val y)
      (hfirst S hS b s hb.1 y) (hb.2 y)
    have he := hcompare S hS a b s (smoothRepresentative x) (smoothRepresentative y)
      _ _ (liftSmoothPath_spec a s.val x) (liftSmoothPath_spec b s.val y) ha.1 hb.1
      (fun r hr => ⟨hsa r hr, hsb r hr⟩)
    have he' := he.trans (finiteRestartFactor_bound K mesh.count _ _)
    have hxy : edist x.val y.val =
        holderBesovENorm η (smoothRepresentative x - smoothRepresentative y) := by
      change edist x.val.val y.val.val = _
      rw [← (smoothRepresentative_spec x).2, ← (smoothRepresentative_spec y).2,
        edist_toHolderBesov]
    rw [hxy, ContinuousMap.edist_eq_iSup]
    apply iSup_le
    intro r
    change edist (toHolderBesov η (liftSmoothPath a s.val x r.val))
      (toHolderBesov η (liftSmoothPath b s.val y r.val)) ≤ _
    rw [edist_toHolderBesov]
    exact (le_iSup₂ (f := fun q _ => holderBesovENorm η
      (liftSmoothPath a s.val x q - liftSmoothPath b s.val y q)) r.val r.property).trans he'
  have hex (S : ℝ) (hS : 0 ≤ S) (a : LiftData N κ) (s : Icc (0 : ℝ) S)
      (ha : FiniteLiftCondition η L T B h₀ R S a s.val) :
      Nonempty (LocalChart η L T H a s.val) := by
    let F := curveOnSmooth (η := η) (R := L) T (3 * a.constants.1 - 9 * a.constants.2)
      (shiftForcing s.val a.forcing) (a.shiftSmooth s.val)
    have hF : LipschitzWith H F := by
      intro x y
      change edist (F x) (F y) ≤ H * edist x.val y.val
      have he := hcurves S hS a a s ha ha x y
      simpa only [Statements.phi43Dist, Model.diffNormOn_self, phi43NoiseDist_self,
        zero_add, add_zero] using he
    obtain ⟨U, hU, hUF⟩ := exists_ballExtension F hF
    exact ⟨⟨U, hU, hUF⟩⟩
  refine ⟨h, hh, K, hK, mesh, hex, ?_⟩
  intro S hS a b s ha hb u v
  apply ballExtension_pair_bound u.lipschitz.continuous v.lipschitz.continuous
  intro x y
  rw [u.smooth_agreement, v.smooth_agreement]
  exact hcurves S hS a b s ha hb x y

end GlobalPhi43.Flow
