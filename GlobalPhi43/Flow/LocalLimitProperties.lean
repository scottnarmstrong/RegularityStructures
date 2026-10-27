module

public import GlobalPhi43.Flow.LocalRestriction
public import Mathlib.Topology.UniformSpace.UniformApproximation

public noncomputable section

open Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

/-- Smooth approximations to the datum can be taken simultaneously with the lift limit.
Convergence is in continuous path space, hence uniform over the local time interval. -/
theorem localLimit_smooth_approx {N : ℕ} {κ : Kappa} {η : NegExponent} {L τ S : ℝ}
    {K : ℝ≥0} {a : ℕ → LiftData N κ}
    (U : ∀ n, ∀ s : Icc (0 : ℝ) S, LocalChart η L τ K (a n) s.val)
    {F : Icc (0 : ℝ) S × StateBall η L → C(Icc (0 : ℝ) τ, HolderBesov η)}
    (hF : TendstoUniformlyOn (fun n p => (U n p.1).path p.2) F atTop univ)
    (hLip : ∀ s : Icc (0 : ℝ) S, LipschitzWith K (fun x => F (s, x)))
    (s : Icc (0 : ℝ) S) (x : StateBall η L) (q : ℕ → smoothBall η L)
    (hq : Tendsto (fun n => (q n).val) atTop (𝓝 x)) :
    Tendsto (fun n => curveOnSmooth τ (3 * (a n).constants.1 - 9 * (a n).constants.2)
      (shiftForcing s.val (a n).forcing) ((a n).shiftSmooth s.val) (q n))
      atTop (𝓝 (F (s, x))) := by
  have hu : TendstoUniformlyOn (fun n z => (U n s).path z) (fun z => F (s, z)) atTop univ := by
    simpa only [Function.comp_def, preimage_univ] using hF.comp (fun z => (s, z))
  have hq' : Tendsto (fun n => (q n).val) atTop (𝓝[univ] x) := by simpa using hq
  exact (hu.tendsto_comp (hLip s).continuous.continuousAt.continuousWithinAt hq').congr
    (fun n => (U n s).smooth_agreement (q n))

end GlobalPhi43.Flow
