module

public import GlobalPhi43.Attachment.ProbeFoldCells
public import GlobalPhi43.Attachment.ProbeDyadicKernel
public import Mathlib.MeasureTheory.Group.Integral

/-! Integer folding preserves the actual periodic pairing and produces
literal unit-scale compact tests at the original spacetime base point. -/

@[expose] public noncomputable section

open RegularityStructures MeasureTheory Set
open scoped ContDiff

namespace GlobalPhi43.Attachment

def probeIntegerVector (m : Fin 3 → ℤ) : ProbeSpace := fun i => (m i : ℝ)
def probeIntegerShift (m : Fin 3 → ℤ) : ParabolicSpace := (0, probeIntegerVector m)

theorem probeIntegerShift_neg (m : Fin 3 → ℤ) : probeIntegerShift (-m) = -probeIntegerShift m := by
  ext i <;> simp [probeIntegerShift, probeIntegerVector]

/-- The same partition in the subtraction convention of the source proof. -/
theorem probeFoldPartition_sum_sub (x : ProbeSpace) :
    (∑' m : Fin 3 → ℤ, probeFoldPartition (x - probeIntegerVector m)) = 1 := by
  have hh := (Equiv.neg (Fin 3 → ℤ)).tsum_eq
    (fun m => probeFoldPartition (x + probeIntegerVector m))
  have he (m : Fin 3 → ℤ) : x + probeIntegerVector (-m) = x - probeIntegerVector m := by
    ext i
    simp [probeIntegerVector, sub_eq_add_neg]
  simp only [Equiv.neg_apply, he] at hh
  exact hh.trans (probeFoldPartition_sum x)

def probeFoldedProfile (K : ParabolicSpace → ℝ) (m : Fin 3 → ℤ) (v : ParabolicSpace) : ℝ :=
  K (-v + probeIntegerShift m) * probeFoldPartition (-v.2)

theorem probeFoldedProfile_smooth {K : ParabolicSpace → ℝ} (hK : ContDiff ℝ ∞ K)
    (m : Fin 3 → ℤ) : ContDiff ℝ ∞ (probeFoldedProfile K m) := by
  unfold probeFoldedProfile
  exact (hK.comp (by fun_prop)).mul (probeFoldPartition_smooth.comp (by fun_prop))

theorem probeFoldedProfile_support {K : ParabolicSpace → ℝ}
    (hK : tsupport K ⊆ {w | w.1 ∈ Icc (0 : ℝ) 1}) (m : Fin 3 → ℤ) :
    tsupport (probeFoldedProfile K m) ⊆ {v | Local.pdist 0 v ≤ 1} := by
  apply closure_minimal _ (isCompact_pdist_ball (by norm_num : (0 : ℝ) ≤ 1)).isClosed
  intro v hv
  have hk : K (-v + probeIntegerShift m) ≠ 0 := by
    intro he
    exact hv (by simp only [probeFoldedProfile, he, zero_mul])
  have ht := hK (subset_closure hk)
  change 0 ≤ -v.1 + 0 ∧ -v.1 + 0 ≤ 1 at ht
  have hθ : probeFoldPartition (-v.2) ≠ 0 := by
    intro he
    exact hv (by simp only [probeFoldedProfile, he, mul_zero])
  have hx := probeFoldPartition_support (subset_closure hθ)
  have hx' : ‖v.2‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using hx
  have ht' : |v.1| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [ht.1, ht.2]
  change max (Real.sqrt |0-v.1|) ‖0-v.2‖ ≤ 1
  simp only [zero_sub, abs_neg, norm_neg]
  exact max_le ((Real.sqrt_le_left zero_le_one).mpr (by simpa only [one_pow] using ht')) hx'

theorem probeFoldedProfile_compact {K : ParabolicSpace → ℝ}
    (hK : tsupport K ⊆ {w | w.1 ∈ Icc (0 : ℝ) 1}) (m : Fin 3 → ℤ) :
    HasCompactSupport (probeFoldedProfile K m) :=
  (isCompact_pdist_ball (by norm_num : (0 : ℝ) ≤ 1)).of_isClosed_subset
    (isClosed_tsupport _) (probeFoldedProfile_support hK m)

/-- Exact unit-scale profile identity, keeping the original base point z. -/
theorem probeFoldedProfile_rescaled (K : ParabolicSpace → ℝ) (m : Fin 3 → ℤ)
    (z w : ParabolicSpace) :
    rescaledTestFunction (probeFoldedProfile K m) 1 z w =
      K (z-w+probeIntegerShift m) * probeFoldPartition (z.2-w.2) := by
  simp only [rescaledTestFunction, inv_one, parabolicDilate_one, one_pow, one_mul,
    probeFoldedProfile, neg_sub]
  congr 2
  change -(w.2-z.2) = z.2-w.2
  exact neg_sub _ _

/-- Translation of the actual integral, without changing the field or its
periodicity convention. Integrability is preserved by Haar translation. -/
theorem probe_periodic_pairing_fold (f K : ParabolicSpace → ℝ)
    (hf : ∀ m : Fin 3 → ℤ, ∀ w, f (w + probeIntegerShift m) = f w)
    (z : ParabolicSpace) (m : Fin 3 → ℤ) :
    (∫ w, f w * K (z-w) * probeFoldPartition (z.2-w.2-probeIntegerVector m)) =
      ∫ w, f w * rescaledTestFunction (probeFoldedProfile K m) 1 z w := by
  have : (volume : Measure ParabolicSpace).IsAddHaarMeasure :=
    (inferInstance : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure)
  let F := fun w => f w * K (z-w) * probeFoldPartition (z.2-w.2-probeIntegerVector m)
  calc (∫ w, F w) = ∫ w, F (w + -probeIntegerShift m) :=
      (integral_add_right_eq_self F (-probeIntegerShift m)).symm
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro w
      have he : f (w + -probeIntegerShift m) = f w := by
        rw [← probeIntegerShift_neg]
        exact hf (-m) w
      have harg : z - (w + -probeIntegerShift m) = z-w+probeIntegerShift m := by abel
      have hspace : z.2-(w + -probeIntegerShift m).2-probeIntegerVector m = z.2-w.2 := by
        change z.2-(w.2 + -probeIntegerVector m)-probeIntegerVector m = _
        abel
      dsimp only [F]
      rw [he, harg, hspace, probeFoldedProfile_rescaled, mul_assoc]

end GlobalPhi43.Attachment
