module

public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! A finite smooth test partition chosen before all noise and model data. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures Set
open scoped Manifold

open scoped ContDiff in
/-- Every compact test-support set has a finite smooth partition into arbitrarily small balls,
with one uniform bound for all derivatives of orders at most four of all cutoffs. -/
theorem exists_finite_test_partition {K : Set ParabolicSpace} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (s : Finset K) (χ : s → ParabolicSpace → ℝ) (B : ℝ), 0 ≤ B ∧
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ Metric.ball (i.1 : ParabolicSpace) δ) ∧
      (∀ z ∈ K, ∑ i, χ i z = 1) ∧
      (∀ i k, k ≤ 4 → ∀ z, ‖iteratedFDeriv ℝ k (χ i) z‖ ≤ B) := by
  classical
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun i : K => Metric.ball (i : ParabolicSpace) δ)
    (fun _ => Metric.isOpen_ball) (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self hδ⟩)
  let U : s → Set ParabolicSpace := fun i => Metric.ball (i.1 : ParabolicSpace) δ
  have hcover : K ⊆ ⋃ i : s, U i := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hs hz)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ParabolicSpace)) hK.isClosed U (fun _ => Metric.isOpen_ball) hcover
  have hsm (i : s) : ContDiff ℝ ∞ (ρ i) := (contMDiff_iff_contDiff).mp (ρ i).contMDiff
  have hc (i : s) : HasCompactSupport (ρ i) :=
    (isCompact_closedBall (i.1 : ParabolicSpace) δ).of_isClosed_subset isClosed_closure
      ((hρ i).trans Metric.ball_subset_closedBall)
  have hb (i : s) := (hc i).exists_bound_iteratedFDeriv (hsm i) 4
  choose B hB0 hB using hb
  refine ⟨s, (fun i => ρ i), ∑ i, B i, Finset.sum_nonneg (fun i _ => hB0 i), hsm, hρ, ?_, ?_⟩
  · intro z hz
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hz
  · intro i k hk z
    exact (hB i k hk z).trans (Finset.single_le_sum (fun j _ => hB0 j) (Finset.mem_univ i))

/-- Euclidean norm control implies the parabolic sum-norm control needed for test pieces. -/
theorem parabolicNorm_le_of_norm_le {z : ParabolicSpace} {δ : ℝ} (hz : ‖z‖ ≤ δ) :
    parabolicNorm z ≤ Real.sqrt δ + 3 * δ := by
  have ht : |z.1| ≤ δ := (Real.norm_eq_abs _ ▸ norm_fst_le z).trans hz
  have hx (i : Fin 3) : |z.2 i| ≤ δ := by
    have h := (norm_le_pi_norm z.2 i).trans ((norm_snd_le z).trans hz)
    simpa only [Real.norm_eq_abs] using h
  unfold parabolicNorm
  have hsum : ∑ i : Fin 3, |z.2 i| ≤ 3 * δ := by
    calc _ ≤ ∑ _i : Fin 3, δ := Finset.sum_le_sum fun i _ => hx i
      _ = _ := by simp
  exact add_le_add (Real.sqrt_le_sqrt ht) hsum

open scoped ContDiff in
/-- A fixed finite partition into small parabolic balls, with all four derivative bounds
chosen before any noise, model, scale or test function. -/
theorem exists_parabolic_test_partition {K : Set ParabolicSpace} (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ (s : Finset K) (χ : s → ParabolicSpace → ℝ) (B : ℝ), 0 ≤ B ∧
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ {z | parabolicNorm (z - (i.1 : ParabolicSpace)) < r}) ∧
      (∀ z ∈ K, ∑ i, χ i z = 1) ∧
      (∀ i k, k ≤ 4 → ∀ z, ‖iteratedFDeriv ℝ k (χ i) z‖ ≤ B) := by
  let δ : ℝ := (r / 16) ^ 2
  have hδ : 0 < δ := sq_pos_of_pos (div_pos hr (by norm_num))
  obtain ⟨s, χ, B, hB, hsm, hsupport, hsum, hder⟩ := exists_finite_test_partition hK hδ
  refine ⟨s, χ, B, hB, hsm, ?_, hsum, hder⟩
  intro i z hz
  have hz' : ‖z - (i.1 : ParabolicSpace)‖ ≤ δ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using (hsupport i hz).le
  have hnorm := parabolicNorm_le_of_norm_le hz'
  have hsqrt : Real.sqrt δ = r / 16 := by
    dsimp [δ]
    rw [Real.sqrt_sq (div_nonneg hr.le (by norm_num))]
  rw [hsqrt] at hnorm
  have hr2 : r ^ 2 ≤ r := by nlinarith
  change parabolicNorm (z - (i.1 : ParabolicSpace)) < r
  dsimp [δ] at hnorm
  nlinarith

end GlobalPhi43.Attachment
