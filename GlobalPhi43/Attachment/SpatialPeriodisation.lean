module

public import RegularityStructures.PDE.TorusLift
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval

/-! Lattice periodisation of compact spatial profiles. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.PDE Set Filter Topology

/-- The periodised spatial lift, before descent to the torus. -/
def spatialPeriodisationLift (φ : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑' k : Fin 3 → ℤ, φ (x + fun i => (k i : ℝ))

/-- On a neighbourhood of any point only finitely many lattice translates can contribute. -/
theorem spatial_periodisation_local_finite (φ : (Fin 3 → ℝ) → ℝ) (R : ℝ)
    (hφ : tsupport φ ⊆ Metric.closedBall 0 R) (x : Fin 3 → ℝ) :
    ∃ s : Finset (Fin 3 → ℤ), ∀ y ∈ Metric.ball x 1, ∀ k ∉ s,
      φ (y + fun i => (k i : ℝ)) = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (R + (‖x‖ + 1))
  let s : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-(n : ℤ)) n)
  refine ⟨s, ?_⟩
  intro y hy k hk
  by_contra hne
  have hw : ‖y + fun i => (k i : ℝ)‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hφ (subset_closure hne)
  have hyb : ‖y‖ < ‖x‖ + 1 := by
    have ht := norm_add_le (y - x) x
    rw [sub_add_cancel] at ht
    have hy' : ‖y - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    linarith
  apply hk
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi : |(k i : ℝ)| < n := by
    calc |(k i : ℝ)| = |(y + fun i => (k i : ℝ)) i - y i| := by simp
      _ ≤ |(y + fun i => (k i : ℝ)) i| + |y i| := abs_sub _ _
      _ ≤ ‖y + fun i => (k i : ℝ)‖ + ‖y‖ := by
        simpa only [Real.norm_eq_abs] using
          add_le_add (norm_le_pi_norm (y + fun i => (k i : ℝ)) i) (norm_le_pi_norm y i)
      _ < n := by linarith
  have hl : -(n : ℝ) ≤ (k i : ℝ) := (abs_lt.mp hi).1.le
  have hr : (k i : ℝ) ≤ n := (abs_lt.mp hi).2.le
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hl, by exact_mod_cast hr⟩

/-- Finite local sums preserve exactly the source profile's differentiability order. -/
theorem spatialPeriodisationLift_contDiff {n : WithTop ℕ∞} {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ n φ) {R : ℝ} (hs : tsupport φ ⊆ Metric.closedBall 0 R) :
    ContDiff ℝ n (spatialPeriodisationLift φ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨s, ht⟩ := spatial_periodisation_local_finite φ R hs x
  have hc : ContDiff ℝ n (fun y => ∑ k ∈ s, φ (y + fun i => (k i : ℝ))) :=
    ContDiff.sum fun k _ => hφ.comp (contDiff_id.add contDiff_const)
  have he : spatialPeriodisationLift φ =ᶠ[𝓝 x]
      (fun y => ∑ k ∈ s, φ (y + fun i => (k i : ℝ))) := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    exact tsum_eq_sum fun k hk => ht y hy k hk
  exact hc.contDiffAt.congr_of_eventuallyEq he

/-- Integer lattice translations preserve the actual periodised lift. -/
theorem spatialPeriodisationLift_add_integer (φ : (Fin 3 → ℝ) → ℝ)
    (m : Fin 3 → ℤ) (x : Fin 3 → ℝ) :
    spatialPeriodisationLift φ (x + fun i => (m i : ℝ)) = spatialPeriodisationLift φ x := by
  have h := (Equiv.addLeft m).tsum_eq (fun k : Fin 3 → ℤ => φ (x + fun i => (k i : ℝ)))
  simpa only [spatialPeriodisationLift, Equiv.coe_addLeft, Pi.add_apply, Int.cast_add,
    Pi.add_def, add_assoc] using h

end GlobalPhi43.Attachment
