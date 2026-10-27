module

public import GlobalPhi43.Assembly.WindowDense
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! Fixed first-index smooth selectors, chosen before any noise space. -/

public noncomputable section

open MeasureTheory Set Filter Topology RegularityStructures

namespace GlobalPhi43.Flow

/-- A smooth sequence whose image is dense in the state space. -/
@[expose] def denseSmoothData (η : NegExponent) : ℕ → C(Torus3, ℝ) :=
  (Assembly.exists_dense_smooth_seq η).choose

theorem denseSmoothData_smooth (η : NegExponent) (i : ℕ) :
    IsSmoothOnTorus (denseSmoothData η i) :=
  (Assembly.exists_dense_smooth_seq η).choose_spec.1 i

theorem denseSmoothData_dense (η : NegExponent) :
    DenseRange (fun i => toHolderBesov η (denseSmoothData η i)) :=
  (Assembly.exists_dense_smooth_seq η).choose_spec.2

theorem exists_smooth_index (η : NegExponent) (j : ℕ) (x : HolderBesov η) :
    ∃ i, dist (toHolderBesov η (denseSmoothData η i)) x < (2⁻¹ : ℝ) ^ j := by
  obtain ⟨i, hi⟩ := (denseSmoothData_dense η).exists_dist_lt x
    (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) j)
  exact ⟨i, by rwa [dist_comm]⟩

/-- First dense smooth datum within the prescribed dyadic error. -/
@[expose] def smoothApproxIndex (η : NegExponent) (j : ℕ) (x : HolderBesov η) : ℕ :=
  Nat.find (exists_smooth_index η j x)

@[expose] def smoothApprox (η : NegExponent) (j : ℕ) (x : HolderBesov η) : C(Torus3, ℝ) :=
  denseSmoothData η (smoothApproxIndex η j x)

theorem smoothApprox_smooth (η : NegExponent) (j : ℕ) (x : HolderBesov η) :
    IsSmoothOnTorus (smoothApprox η j x) := denseSmoothData_smooth η _

theorem smoothApprox_dist (η : NegExponent) (j : ℕ) (x : HolderBesov η) :
    dist (toHolderBesov η (smoothApprox η j x)) x < (2⁻¹ : ℝ) ^ j :=
  Nat.find_spec (exists_smooth_index η j x)

theorem smoothApprox_tendsto (η : NegExponent) (x : HolderBesov η) :
    Tendsto (fun j => toHolderBesov η (smoothApprox η j x)) atTop (𝓝 x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun _ => dist_nonneg) (fun j => (smoothApprox_dist η j x).le)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

end GlobalPhi43.Flow
