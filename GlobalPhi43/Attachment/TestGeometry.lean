module

public import GlobalPhi43.Local.RadiusGeometry
public import RegularityStructures.Analysis.Parabolic.GeneratorScaling

/-! The max-metric geometry used by compact model-to-test conversion. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures GlobalPhi43.Local Set

/-- The parabolic maximum metric is bounded by the base parabolic sum norm. -/
theorem pdist_le_parabolicNorm (x y : ParabolicSpace) : pdist x y ≤ parabolicNorm (x - y) := by
  have hsum : 0 ≤ ∑ i : Fin 3, |(x - y).2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsqrt : 0 ≤ Real.sqrt |(x - y).1| := Real.sqrt_nonneg _
  have hspace : ‖(x - y).2‖ ≤ ∑ i : Fin 3, |(x - y).2 i| := by
    apply (pi_norm_le_iff_of_nonneg hsum).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun j _ => abs_nonneg ((x - y).2 j)) (Finset.mem_univ i)
  change max (Real.sqrt |(x - y).1|) ‖(x - y).2‖ ≤
    Real.sqrt |(x - y).1| + ∑ i, |(x - y).2 i|
  exact max_le (by linarith) (by linarith)

/-- The comparison between the parabolic maximum metric and the sum norm in dimension four. -/
theorem parabolicNorm_le_four_pdist (x y : ParabolicSpace) : parabolicNorm (x - y) ≤ 4 * pdist x y := by
  have ht : Real.sqrt |(x - y).1| ≤ pdist x y := le_max_left _ _
  have hs : ‖(x - y).2‖ ≤ pdist x y := le_max_right _ _
  have hi (i : Fin 3) : |(x - y).2 i| ≤ pdist x y := by
    have h := (norm_le_pi_norm (x - y).2 i).trans hs
    simpa only [Real.norm_eq_abs] using h
  have hsum : ∑ i : Fin 3, |(x - y).2 i| ≤ 3 * pdist x y := by
    calc _ ≤ ∑ _i : Fin 3, pdist x y := Finset.sum_le_sum fun i _ => hi i
      _ = _ := by simp
  unfold parabolicNorm
  linarith

/-- A closed max-metric ball is the compact rectangular parabolic box. -/
theorem pdist_zero_le_iff {r : ℝ} (hr : 0 ≤ r) (z : ParabolicSpace) :
    pdist 0 z ≤ r ↔ z ∈ Icc (-r ^ 2) (r ^ 2) ×ˢ pi univ (fun _ : Fin 3 => Icc (-r) r) := by
  simp only [pdist, Prod.fst_zero, Prod.snd_zero, zero_sub, abs_neg, norm_neg,
    max_le_iff, Real.sqrt_le_left hr, abs_le, mem_prod, mem_Icc, mem_pi, mem_univ,
    forall_true_left, pi_norm_le_iff_of_nonneg hr, Real.norm_eq_abs]

/-- Compactness of the closed max-metric ball. -/
theorem isCompact_pdist_ball {r : ℝ} (hr : 0 ≤ r) : IsCompact {z : ParabolicSpace | pdist 0 z ≤ r} := by
  have he : {z : ParabolicSpace | pdist 0 z ≤ r} =
      Icc (-r ^ 2) (r ^ 2) ×ˢ pi univ (fun _ : Fin 3 => Icc (-r) r) := by
    ext z; exact pdist_zero_le_iff hr z
  rw [he]
  exact isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)

/-- Translation invariance of the max metric, with the same orientation as model translation. -/
theorem pdist_add_right (x y a : ParabolicSpace) : pdist (x + a) (y + a) = pdist x y := by
  simp only [pdist, Prod.fst_add, Prod.snd_add, add_sub_add_right_eq_sub]

/-- A compact set enlarged by the closed max-metric ball remains compact. -/
theorem isCompact_parabolic_enlargement {S : Set ParabolicSpace} (hS : IsCompact S)
    {r : ℝ} (hr : 0 ≤ r) : IsCompact {y | ∃ x ∈ S, pdist x y ≤ r} := by
  have he : {y | ∃ x ∈ S, pdist x y ≤ r} =
      (fun p : ParabolicSpace × ParabolicSpace => p.1 + p.2) ''
        (S ×ˢ {v | pdist 0 v ≤ r}) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      refine ⟨(x, y - x), ⟨hx, ?_⟩, by
        change x + (y - x) = y
        rw [add_comm, sub_add_cancel]⟩
      have h : pdist x y = pdist 0 (y - x) := by
        simpa only [zero_add, sub_add_cancel] using pdist_add_right 0 (y - x) x
      exact h.symm.trans_le hxy
    · rintro ⟨⟨x, v⟩, ⟨hx, hv⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      have h := pdist_add_right 0 v x
      simpa only [zero_add, add_comm v x] using h.le.trans hv
  rw [he]
  exact (hS.prod (isCompact_pdist_ball hr)).image (continuous_fst.add continuous_snd)

/-- Exact max-metric scaling of a translated test center. -/
theorem pdist_scaled_center {T : ℝ} (hT : 0 ≤ T) (x w : ParabolicSpace) :
    pdist x (x + parabolicDilate T w) = T * pdist 0 w := by
  have he : pdist x (x + parabolicDilate T w) = pdist 0 (parabolicDilate T w) := by
    simpa only [zero_add, add_comm (parabolicDilate T w) x] using
      pdist_add_right 0 (parabolicDilate T w) x
  rw [he]
  have ht : Real.sqrt |T ^ 2 * w.1| = T * Real.sqrt |w.1| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg T), Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT]
  have hs : ‖T • w.2‖ = T * ‖w.2‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hT]
  simp only [pdist, Prod.fst_zero, Prod.snd_zero, zero_sub, abs_neg, norm_neg,
    parabolicDilate, ht, hs]
  exact (mul_max_of_nonneg _ _ hT).symm

end GlobalPhi43.Attachment
