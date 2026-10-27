module

public import GlobalPhi43.Attachment.ProbeSpatialCutoff
public import GlobalPhi43.Attachment.SpatialPeriodisation
public import Mathlib.Algebra.Order.Round
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! A single smooth, unit-supported integer partition for folding the large
Gaussian annuli, constructed before every model and stochastic input. -/

@[expose] public noncomputable section

open RegularityStructures Set Metric
open scoped ContDiff

namespace GlobalPhi43.Attachment

def probeFoldBump : ContDiffBump (0 : ProbeSpace) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def probeFoldDenominator : ProbeSpace → ℝ := spatialPeriodisationLift probeFoldBump

theorem probeFoldBump_support : tsupport (probeFoldBump : ProbeSpace → ℝ) ⊆ closedBall 0 1 := by
  rw [probeFoldBump.tsupport_eq]
  exact Subset.rfl

theorem probeFoldDenominator_smooth : ContDiff ℝ ∞ probeFoldDenominator :=
  spatialPeriodisationLift_contDiff probeFoldBump.contDiff probeFoldBump_support

theorem probeFoldDenominator_integer (m : Fin 3 → ℤ) (x : ProbeSpace) :
    probeFoldDenominator (x + fun i => (m i : ℝ)) = probeFoldDenominator x :=
  spatialPeriodisationLift_add_integer probeFoldBump m x

/-- The nearest integer vector supplies an actual term equal to one. -/
theorem probeFoldDenominator_one_le (x : ProbeSpace) : 1 ≤ probeFoldDenominator x := by
  classical
  let m : Fin 3 → ℤ := fun i => -round (x i)
  have hm : ‖x + fun i => (m i : ℝ)‖ ≤ (1 / 2 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    simpa only [m, Pi.add_apply, Int.cast_neg, ← sub_eq_add_neg, Real.norm_eq_abs] using abs_sub_round (x i)
  have hone : probeFoldBump (x + fun i => (m i : ℝ)) = 1 :=
    probeFoldBump.one_of_mem_closedBall (by
      simpa only [mem_closedBall, dist_zero_right, probeFoldBump] using hm)
  obtain ⟨F, hF⟩ := spatial_periodisation_local_finite probeFoldBump 1 probeFoldBump_support x
  have hsum : Summable (fun k : Fin 3 → ℤ => probeFoldBump (x + fun i => (k i : ℝ))) :=
    summable_of_ne_finset_zero (fun k hk => hF x (mem_ball_self (by norm_num)) k hk)
  rw [← hone]
  exact hsum.le_tsum m (fun _ _ => probeFoldBump.nonneg)

/-- The normalized compact profile, with the actual periodisation denominator. -/
def probeFoldPartition (x : ProbeSpace) : ℝ := probeFoldBump x / probeFoldDenominator x

theorem probeFoldPartition_smooth : ContDiff ℝ ∞ probeFoldPartition :=
  probeFoldBump.contDiff.div probeFoldDenominator_smooth
    (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (probeFoldDenominator_one_le x)))
theorem probeFoldPartition_support : tsupport probeFoldPartition ⊆ closedBall 0 1 := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hb : probeFoldBump x ≠ 0 := by
    intro he
    exact hx (by simp only [probeFoldPartition, he, zero_div])
  exact probeFoldBump_support (subset_closure hb)

theorem probeFoldPartition_compact : HasCompactSupport probeFoldPartition :=
  (isCompact_closedBall (0 : ProbeSpace) 1).of_isClosed_subset (isClosed_tsupport _) probeFoldPartition_support

/-- The exact integer partition, before restricting to the finite annulus cells. -/
theorem probeFoldPartition_sum (x : ProbeSpace) :
    (∑' m : Fin 3 → ℤ, probeFoldPartition (x + fun i => (m i : ℝ))) = 1 := by
  simp_rw [probeFoldPartition, probeFoldDenominator_integer]
  rw [tsum_div_const]
  change probeFoldDenominator x / probeFoldDenominator x = 1
  exact div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one (probeFoldDenominator_one_le x)))

/-- A fixed C4 bound for periodised test functions. -/
theorem probeFoldPartition_C4 : ∃ B : ℝ, 0 ≤ B ∧ ∀ k ≤ 4, ∀ x,
    ‖iteratedFDeriv ℝ k probeFoldPartition x‖ ≤ B :=
  probeFoldPartition_compact.exists_bound_iteratedFDeriv probeFoldPartition_smooth 4

end GlobalPhi43.Attachment
