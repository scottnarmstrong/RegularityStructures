module

public import GlobalPhi43.Attachment.ProbeCompactPairing

/-! Exact finite folding of each physical Gaussian piece. The contributing
lattice set is finite by the compact support of the test function. -/

@[expose] public noncomputable section

open RegularityStructures MeasureTheory Set
open scoped ContDiff

namespace GlobalPhi43.Attachment

theorem probe_fold_partition_finite {j : ℕ} {r : ℝ} (hr : r ≤ 1)
    {K : ParabolicSpace → ℝ}
    (hK : ∀ a, K a ≠ 0 → ‖a.2‖ ≤ (2 : ℝ)^(j+1)*r) (a : ParabolicSpace) :
    (∑ m ∈ probeFoldCells j, K a * probeFoldPartition (a.2-probeIntegerVector m)) = K a := by
  classical
  by_cases ha : K a = 0
  · simp only [ha, zero_mul, Finset.sum_const_zero]
  have he : ∀ m ∉ probeFoldCells j, probeFoldPartition (a.2-probeIntegerVector m) = 0 := by
    intro m hm
    by_contra hn
    have hh := probeFoldPartition_support (subset_closure hn)
    have hy : ‖a.2-probeIntegerVector m‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hh
    apply hm
    apply probeFoldCells_of_support hr hy
    change ‖a.2-probeIntegerVector m+probeIntegerVector m‖ ≤ _
    rw [sub_add_cancel]
    exact hK a ha
  have hs : (∑' m : Fin 3 → ℤ, probeFoldPartition (a.2-probeIntegerVector m)) =
      ∑ m ∈ probeFoldCells j, probeFoldPartition (a.2-probeIntegerVector m) := tsum_eq_sum he
  rw [← Finset.mul_sum, ← hs, probeFoldPartition_sum_sub, mul_one]

/-- Each summand is integrable from continuity and the actual compact folded
profile. No model estimate, growth bound, or integrability input is needed. -/
theorem probe_fold_summand_integrable {f K : ParabolicSpace → ℝ} (hf : Continuous f)
    (hK : ContDiff ℝ ∞ K) (ht : tsupport K ⊆ {a | a.1 ∈ Icc (0 : ℝ) 1})
    (z : ParabolicSpace) (m : Fin 3 → ℤ) :
    Integrable (fun w => f w*K (z-w)*probeFoldPartition (z.2-w.2-probeIntegerVector m)) := by
  let H := Homeomorph.addRight (probeIntegerShift m-z)
  have hc := (probeFoldedProfile_compact ht m).comp_homeomorph H
  have he : (fun w => f w*K (z-w)*probeFoldPartition (z.2-w.2-probeIntegerVector m)) =
      f * (probeFoldedProfile K m ∘ H) := by
    funext w
    have ha : -(w+(probeIntegerShift m-z))+probeIntegerShift m = z-w := by abel
    have hb : -(w+(probeIntegerShift m-z)).2 = z.2-w.2-probeIntegerVector m := by
      change -(w.2+(probeIntegerVector m-z.2)) = _
      abel
    change f w*K (z-w)*probeFoldPartition _ = f w*(K _*probeFoldPartition _)
    change f w*K (z-w)*probeFoldPartition _ =
      f w*(K (-(w+(probeIntegerShift m-z))+probeIntegerShift m)*
        probeFoldPartition (-(w+(probeIntegerShift m-z)).2))
    rw [ha, hb, mul_assoc]
  rw [he]
  exact (hf.mul ((probeFoldedProfile_smooth hK m).continuous.comp H.continuous)).integrable_of_hasCompactSupport
    hc.mul_left

/-- Folding keeps the original base point, with unit-scale model tests. -/
theorem probe_fold_pairing_sum {f K : ParabolicSpace → ℝ} (hf : Continuous f)
    (hK : ContDiff ℝ ∞ K) (ht : tsupport K ⊆ {a | a.1 ∈ Icc (0 : ℝ) 1})
    (hp : ∀ m : Fin 3 → ℤ, ∀ w, f (w+probeIntegerShift m) = f w)
    {j : ℕ} {r : ℝ} (hr : r ≤ 1)
    (hs : ∀ a, K a ≠ 0 → ‖a.2‖ ≤ (2 : ℝ)^(j+1)*r) (z : ParabolicSpace) :
    (∫ w, f w*K (z-w)) = ∑ m ∈ probeFoldCells j,
      ∫ w, f w*rescaledTestFunction (probeFoldedProfile K m) 1 z w := by
  classical
  have he : (fun w => f w*K (z-w)) = fun w => ∑ m ∈ probeFoldCells j,
      f w*K (z-w)*probeFoldPartition (z.2-w.2-probeIntegerVector m) := by
    funext w
    have hh := congrArg (fun a : ℝ => f w*a) (probe_fold_partition_finite hr hs (z-w))
    simpa only [Finset.mul_sum, mul_assoc, Prod.snd_sub] using hh.symm
  rw [he, integral_finsetSum _ (fun m _ => probe_fold_summand_integrable hf hK ht z m)]
  apply Finset.sum_congr rfl
  intro m _
  exact probe_periodic_pairing_fold f K hp z m

end GlobalPhi43.Attachment
