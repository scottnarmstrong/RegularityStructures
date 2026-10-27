module

public import GlobalPhi43.Flow.FiniteCharts
public import GlobalPhi43.Flow.LocalLimitProperties

public noncomputable section

open Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

/-- Conditional finite-horizon lift limit. The only additional analytic input is
the named later-state bound on actual smooth solutions. Neither an iterated
estimate nor a Cauchy/convergence property of the paths is assumed. Uniformity
includes every start, every datum in the closed ball, and both time endpoints.
Smooth approximation is given by `localLimit_smooth_approx` with interval length
`T`; the limit is independent of the selections and approximations. The
conclusion concerns the finite-horizon limit, rather than a global majorant or cocycle. -/
theorem exists_conditionalFiniteLimit {κ : Kappa} (hκE : κ.1 ∉ Statements.excludedKappa)
    {N : ℕ} (hN : 5 ≤ N) {η : NegExponent}
    (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η)
    (T L B : ℝ) (hT : 1 ≤ T) (hL : 1 ≤ L) (hB : 1 ≤ B) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ R : ℝ, 1 ≤ R →
      ∃ h : ℝ, 0 < h ∧ ∃ K : ℝ≥0, 1 ≤ K ∧ ∃ mesh : RestartMesh T h,
        ∀ (S : ℝ), 0 ≤ S → ∀ a : ℕ → LiftData N κ,
          (∀ n (s : Icc (0 : ℝ) S), FiniteLiftCondition η L T B h₀ R S (a n) s.val) →
          (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
            Statements.phi43Dist κ η (T + S) (a n).model (a m).model
              (a n).potential (a m).potential ≤ ENNReal.ofReal ε) →
          ∃ U : ∀ n : ℕ, ∀ s : Icc (0 : ℝ) S,
              LocalChart η L T (finiteRestartFactor K mesh.count) (a n) s.val,
            ∃ F : Icc (0 : ℝ) S × StateBall η L → C(Icc (0 : ℝ) T, HolderBesov η),
              (∀ n m (s : Icc (0 : ℝ) S) (x y : StateBall η L),
                edist ((U n s).path x) ((U m s).path y) ≤
                  finiteRestartFactor K mesh.count * (edist x y +
                    Statements.phi43Dist κ η (T + S) (a n).model (a m).model
                      (a n).potential (a m).potential)) ∧
              TendstoUniformlyOn (fun n p => (U n p.1).path p.2) F atTop univ ∧
              (∀ s : Icc (0 : ℝ) S,
                LipschitzWith (finiteRestartFactor K mesh.count) (fun x => F (s, x))) ∧
              (∀ (s : Icc (0 : ℝ) S) (x : StateBall η L),
                F (s, x) ⟨0, le_rfl, by linarith⟩ = x.val) ∧
              ∀ s : Icc (0 : ℝ) S,
                Continuous (fun p : Icc (0 : ℝ) T × StateBall η L => F (s, p.2) p.1) := by
  obtain ⟨h₀, hh₀, hh₀1, hcharts⟩ :=
    exists_conditionalFiniteCharts hκE hN hη hκη T L B hT hL hB
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro R hR
  obtain ⟨h, hh, K, hK, mesh, hex, hp⟩ := hcharts R hR
  refine ⟨h, hh, K, hK, mesh, ?_⟩
  intro S hS a ha hD
  let H := finiteRestartFactor K mesh.count
  let U : ∀ n : ℕ, ∀ s : Icc (0 : ℝ) S, LocalChart η L T H (a n) s.val :=
    fun n s => Classical.choice (hex S hS (a n) s (ha n s))
  have hpair (n m : ℕ) (s : Icc (0 : ℝ) S) (x y : StateBall η L) :=
    hp S hS (a n) (a m) s (ha n s) (ha m s) (U n s) (U m s) x y
  let P := Icc (0 : ℝ) S × StateBall η L
  let A : ℕ → P → C(Icc (0 : ℝ) T, HolderBesov η) := fun n p => (U n p.1).path p.2
  have hc : UniformCauchySeqOn A atTop univ := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    have hden : 0 < (H : ℝ) + 1 := by positivity
    obtain ⟨n₀, hn₀⟩ := hD (ε / ((H : ℝ) + 1)) (div_pos hε hden)
    refine ⟨n₀, ?_⟩
    intro n hn m hm p _
    have he := hpair n m p.1 p.2 p.2
    rw [edist_self, zero_add] at he
    have he' : edist (A n p) (A m p) ≤
        ENNReal.ofReal ((H : ℝ) * (ε / ((H : ℝ) + 1))) := by
      refine (he.trans (mul_le_mul' le_rfl (hn₀ n hn m hm))).trans_eq ?_
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_mul H.property).symm
    have hr : dist (A n p) (A m p) ≤ (H : ℝ) * (ε / ((H : ℝ) + 1)) := by
      rw [edist_dist] at he'
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he'
    refine hr.trans_lt ?_
    rw [mul_div_assoc', div_lt_iff₀ hden]
    nlinarith
  let F : P → C(Icc (0 : ℝ) T, HolderBesov η) := fun p => limUnder atTop (fun n => A n p)
  have hpoint (p : P) : Tendsto (fun n => A n p) atTop (𝓝 (F p)) :=
    (hc.cauchySeq (mem_univ p)).tendsto_limUnder
  have hLip (s : Icc (0 : ℝ) S) : LipschitzWith H (fun x => F (s, x)) := by
    intro x y
    exact le_of_tendsto ((hpoint (s, x)).edist (hpoint (s, y)))
      (Eventually.of_forall fun n => (U n s).lipschitz x y)
  refine ⟨U, F, hpair, hc.tendstoUniformlyOn_of_tendsto (fun p _ => hpoint p), hLip, ?_, ?_⟩
  · intro s x
    have ht : 0 ≤ T := by linarith
    have he := (continuous_eval_const (⟨0, le_rfl, ht⟩ : Icc (0 : ℝ) T)).tendsto (F (s, x))
    have he' := he.comp (hpoint (s, x))
    change Tendsto (fun n => A n (s, x) ⟨0, le_rfl, ht⟩) atTop _ at he'
    have heq : (fun n => A n (s, x) ⟨0, le_rfl, ht⟩) = fun _ : ℕ => x.val := by
      funext n
      exact (U n s).initial ht x
    rw [heq] at he'
    exact tendsto_nhds_unique he' tendsto_const_nhds
  · intro s
    exact ((hLip s).continuous.comp continuous_snd).eval continuous_fst

end GlobalPhi43.Flow
