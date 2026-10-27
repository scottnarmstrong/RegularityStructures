module

public import GlobalPhi43.Flow.WindowGeometry

/-! Exact radius-four regions of cover, slice and the common majorant. -/

public noncomputable section

open Set RegularityStructures GlobalPhi43.Local
open scoped Pointwise

namespace GlobalPhi43.Attachment

/-- The source closed max-metric enlargement, with its literal existential formula. -/
@[expose] def radiusFourRegion (S : Set ParabolicSpace) : Set ParabolicSpace :=
  {y | ∃ z ∈ S, pdist z y ≤ 4}

theorem radiusFourRegion_subset_majorant {S : Set ParabolicSpace} {s : ℝ}
    (hS : S ⊆ Flow.coverRegion s ∪ Flow.sliceRegion s) :
    radiusFourRegion S ⊆ Flow.majorantRegion s := by
  rintro y ⟨z, hz, hd⟩
  refine ⟨z, hS hz, y-z, ?_, by abel_nf⟩
  have he : pdist 0 (y-z) = pdist z y := by
    simp only [pdist, Prod.fst_zero, Prod.snd_zero, Prod.fst_sub, Prod.snd_sub,
      zero_sub, abs_neg, norm_neg, abs_sub_comm, norm_sub_rev]
  change pdist 0 (y-z) ≤ 4
  rwa [he]

theorem coverRadiusFour_subset_majorant (s : ℝ) :
    radiusFourRegion (Flow.coverRegion s) ⊆ Flow.majorantRegion s :=
  radiusFourRegion_subset_majorant (fun _ h => Or.inl h)

theorem sliceRadiusFour_subset_majorant (s : ℝ) :
    radiusFourRegion (Flow.sliceRegion s) ⊆ Flow.majorantRegion s :=
  radiusFourRegion_subset_majorant (fun _ h => Or.inr h)

theorem isCompact_coverRegion (s : ℝ) : IsCompact (Flow.coverRegion s) :=
  isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)

theorem isCompact_sliceRegion (s : ℝ) : IsCompact (Flow.sliceRegion s) :=
  isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)

end GlobalPhi43.Attachment
