module

public import GlobalPhi43.Attachment.DefectSupBounds
public import GlobalPhi43.Attachment.MajorantRegions
public import GlobalPhi43.Attachment.SliceDuhamelAverage
public import GlobalPhi43.Attachment.ProbePsiAverage
public import RegularityStructures.Torus.KernelBoundsBasic

public section

namespace GlobalPhi43.Attachment

open MeasureTheory RegularityStructures RegularityStructures.Phi43 RegularityStructures.PDE Set MW20

/-- The actual source E_s, kept extended until its finiteness is proved. -/
@[expose] noncomputable def sliceDefectSup (N : ℕ) (f : SpaceTime → ℝ)
    (C : RenormalisationConstants) (s : ℝ) : ENNReal :=
  localScalarSup (defectField N f C 0) (Flow.sliceRegion s)

@[expose] noncomputable def sliceDefectSize (N : ℕ) (f : SpaceTime → ℝ)
    (C : RenormalisationConstants) (s : ℝ) : ℝ := (sliceDefectSup N f C s).toReal

/-- Uniform defect bounds on C'_s plus the radius-four ball. -/
theorem slice_defect_size_bound (N : ℕ) (κ : Kappa) :
    ∃ c : ℝ, 0<c ∧ ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsSmoothOnSpaceTime f → Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z → ∀ s : ℝ,
      sliceDefectSup N f C s ≠ ⊤ ∧ sliceDefectSize N f C s ≤
        c*(1+(Z.normOn (gamma κ) (radiusFourRegion (Flow.sliceRegion s))).toReal)^3 := by
  obtain ⟨c,hc,h⟩ := defect_sup_bounds N κ
  refine ⟨c,hc,?_⟩
  intro f C Z hf hg hZ s
  have hb := h f C Z hf hg hZ (Flow.sliceRegion s) (isCompact_sliceRegion s) 0
  have hn : 0 ≤ c*(1+(Z.normOn (gamma κ) (radiusFourRegion (Flow.sliceRegion s))).toReal)^3 := by positivity
  have he : sliceDefectSup N f C s ≤
      ENNReal.ofReal (c*(1+(Z.normOn (gamma κ) (radiusFourRegion (Flow.sliceRegion s))).toReal)^3) := hb
  refine ⟨ne_of_lt (he.trans_lt ENNReal.ofReal_lt_top),?_⟩
  exact ENNReal.toReal_le_of_le_ofReal hn he

/-- The supplied potential is bundled without changing any of its values. -/
@[expose] noncomputable def slicePotentialPath {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) {ψ : ℝ → C(Torus3, ℝ)}
    (hψ : IsMassivePotential f ψ) : C(ℝ,C(Torus3,ℝ)) :=
  ⟨ψ,(massivePotential_regular hf hg hψ).2⟩

/-- The signed forcing differs from psi by exactly the first defect;
the source compact spatial region covers every torus point. -/
theorem slice_forcing_defect_bound {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    {ψ : ℝ → C(Torus3, ℝ)} (hψ : IsMassivePotential f ψ)
    (C : RenormalisationConstants) (s a r : ℝ) (hr : a+r ∈ Icc s (s+1))
    (hfin : sliceDefectSup N f C s ≠ ⊤) :
    ‖sliceDuhamelForcing (N := N) hf hg hψ a r-ψ (a+r)‖ ≤ sliceDefectSize N f C s := by
  have hE : 0 ≤ sliceDefectSize N f C s := ENNReal.toReal_nonneg
  apply (ContinuousMap.norm_le _ hE).mpr
  intro x
  have hx : (a+r,torusRep x) ∈ Flow.sliceRegion s := by
    refine ⟨hr,fun i _ => ?_⟩
    have hh := torusRep_mem_Ico x i
    constructor <;> linarith [hh.1,hh.2]
  have hb := localScalarSup_bound (defectField N f C 0) (Flow.sliceRegion s) hE
    (le_of_eq (ENNReal.ofReal_toReal hfin).symm) hx
  have he := sliceDuhamelForcing_apply (N := N) hf hg hψ C a r (torusRep x)
  rw [torusProj_torusRep] at he
  simpa only [ContinuousMap.sub_apply,he,add_sub_cancel_left,Real.norm_eq_abs] using hb

end GlobalPhi43.Attachment
