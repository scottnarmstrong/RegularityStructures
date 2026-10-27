module

public import GlobalPhi43.Attachment.ProbeJetCoordinates
public import RegularityStructures.Abstract.Singular.TaylorKernel.IterDeriv
public import RegularityStructures.Analysis.Heat.Decay.Remainder

/-! Uniform spatial decay for full Gaussian remainder jets, obtained from the
directional-derivative estimates by a finite coordinate argument. -/

public noncomputable section

open RegularityStructures

namespace GlobalPhi43.Attachment

/-- Fixed derivative order and decay degree: all constants precede spacetime.
No directional or Frechet derivative bound is a supplied premise. -/
theorem probeHeatRemainder_jet_decay (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ParabolicSpace, z.1 ≤ 1 →
      ‖iteratedFDeriv ℝ k heatRemainder z‖ ≤ C * (1 + sqNorm3 z.2)⁻¹ ^ m := by
  classical
  obtain ⟨D, hD, hd⟩ := probeJet_coordinate_bound k
  have hex (p : Fin k → ProbeDirection) :=
    exists_abs_lineIter_heatRemainder_le_of_list
      (List.ofFn (fun i => probeDirectionBasis (p i))) m (T₀ := 1)
  choose A hA ha using hex
  let B := ∑ p : Fin k → ProbeDirection, A p
  have hB : 0 ≤ B := Finset.sum_nonneg (fun p _ => hA p)
  refine ⟨D * B, mul_nonneg hD.le hB, ?_⟩
  intro z hz
  have hdec : 0 ≤ (1 + sqNorm3 z.2)⁻¹ ^ m := by
    have hs : 0 ≤ sqNorm3 z.2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  have hb : ‖iteratedFDeriv ℝ k heatRemainder z‖ ≤ D * (B * (1 + sqNorm3 z.2)⁻¹ ^ m) := by
    apply hd _ _ (mul_nonneg hB hdec)
    intro p
    rw [iteratedFDeriv_apply_eq_lineIter contDiff_heatRemainder]
    exact (ha p z hz).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun q _ => hA q) (Finset.mem_univ p)) hdec)
  exact hb.trans_eq (mul_assoc _ _ _).symm

/-- One actual C4 allowance for each prescribed decay degree. -/
theorem probeHeatRemainder_C4_decay (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ 4, ∀ z : ParabolicSpace, z.1 ≤ 1 →
      ‖iteratedFDeriv ℝ k heatRemainder z‖ ≤ C * (1 + sqNorm3 z.2)⁻¹ ^ m := by
  classical
  choose A hA ha using fun k : Fin 5 => probeHeatRemainder_jet_decay k.val m
  refine ⟨∑ k : Fin 5, A k, Finset.sum_nonneg (fun k _ => hA k), ?_⟩
  intro k hk z hz
  have hs : 0 ≤ sqNorm3 z.2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact (ha ⟨k, Nat.lt_succ_iff.mpr hk⟩ z hz).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun q _ => hA q) (Finset.mem_univ _)) (by positivity))

end GlobalPhi43.Attachment
