module

public import GlobalPhi43.Attachment.SlicePotentialWindow
public import GlobalPhi43.Attachment.SlicePowerAssembly
public import GlobalPhi43.Attachment.ProbeJAverageBound
public import GlobalPhi43.Attachment.AttachmentFunctionalBound

@[expose] public noncomputable section
namespace GlobalPhi43.Attachment
open MeasureTheory Set RegularityStructures RegularityStructures.Phi43 RegularityStructures.PDE

/-- Identification of the initial term with the time average of the heat evolution. -/
theorem sliceInitialJAverage_eq_probe (N : ℕ) {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (s t : ℝ) :
    sliceInitialJAverage N hf s t = probeJAverage N f hf s t := by
  have he : smoothNoiseJ N ⟨f,hf⟩ = probeJPath N f hf := by
    funext r
    ext x
    simp [smoothNoiseJ,probeJPath]
  unfold sliceInitialJAverage probeJAverage probePsiAverage
  rw [he]

/-- Time slices of J at the original loss exponent and exact source
radius-four enlargement. One constant precedes every source datum. -/
theorem slice_radius_four (N : ℕ) (κ : Kappa) :
    ∃ c : ℝ, 0<c ∧ ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
      (hf : IsSmoothOnSpaceTime f), Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
      ∀ (ψ : ℝ → C(Torus3,ℝ)), IsMassivePotential f ψ → ∀ (s t : ℝ),
      t ∈ Ioc (0:ℝ) 1 →
      ENNReal.ofReal (Real.sqrt t) * holderBesovENorm (Flow.lossExponent κ)
        (smoothNoiseJ N ⟨f,hf⟩ (s+t)) ≤
      ENNReal.ofReal c * (Flow.unitPotentialSize (Flow.lossExponent κ) s ψ +
        (1+Z.normOn (gamma κ) (radiusFourRegion (Flow.sliceRegion s)))^3) := by
  obtain ⟨j,hj,hJ⟩ := probeJ_average_bound N κ
  obtain ⟨p,hp,hP⟩ := probePsiAverage_bound (Flow.lossExponent κ)
  obtain ⟨e,he,hE⟩ := slice_defect_size_bound N κ
  let β := (Flow.lossExponent κ : ℝ)/2+1
  let c := 1+j+p+β⁻¹+e
  have hβ : 0<β := by
    change 0 < (Flow.lossExponent κ : ℝ)/2+1
    change 0 < (-(1/2:ℝ)-κ.1)/2+1
    linarith [κ.2.2]
  refine ⟨c,by dsimp [c]; positivity,?_⟩
  intro f C Z hf hg hZ ψ hψ s t ht
  let Y := ‖probePotentialWindow (Flow.lossExponent κ) (slicePotentialPath hf hg hψ) s‖
  let X := Z.normOn (gamma κ) (radiusFourRegion (Flow.sliceRegion s))
  let M := (1+X.toReal)^3
  have hX : X ≠ ⊤ := by
    obtain ⟨noise,hn,hm⟩ := hZ
    exact hm.2.2.1 _ (isCompact_parabolic_enlargement (isCompact_sliceRegion s) (by norm_num))
  have h34 : (Z.normOn (gamma κ) {y | ∃ z ∈ probeModelWindow s, Local.pdist z y ≤ 3}).toReal ≤ X.toReal :=
    ENNReal.toReal_mono hX (attachment_normOn_mono Z (by
      rintro y ⟨z,hz,hd⟩
      refine ⟨z,⟨hz.1,fun i _ => ⟨hz.2.1 i,hz.2.2 i⟩⟩,?_⟩
      linarith))
  have hJb : ‖sliceInitialJAverage N hf s t‖ ≤ j*M*t^((Flow.lossExponent κ : ℝ)/2) := by
    rw [sliceInitialJAverage_eq_probe]
    have hh := hJ f C Z hf hg hZ s t ht
    have hη : (Flow.lossExponent κ : ℝ) = -1/2-(κ:ℝ) := by
      change -(1/2:ℝ)-κ.1 = _
      ring
    rw [hη]
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.1.le _)
    apply mul_le_mul_of_nonneg_left _ hj.le
    dsimp [M]
    gcongr
  have hPb := hP (slicePotentialPath hf hg hψ) s t ht
  have hEb := (hE f C Z hf hg hZ s).2
  have hII := sliceDuhamelRemainder_bound κ hf hg hψ C Z hZ
    (Flow.lossExponent κ) (slice_time_power_bounds κ ht).1 s ht
  have hW : ‖sliceDifferencePath (N := N) hf hg hψ (s+t)‖ ≤
      j*M*t^((Flow.lossExponent κ : ℝ)/2) + p*t^((Flow.lossExponent κ : ℝ)/2)*Y +
      t^((Flow.lossExponent κ : ℝ)/2+1)/β*Y + t*e*M := by
    have hnorm : ‖sliceDifferencePath (N := N) hf hg hψ (s+t)‖ ≤
        ‖sliceInitialJAverage N hf s t‖ +
        ‖probePsiAverage (slicePotentialPath hf hg hψ) s t‖ +
        ‖sliceDuhamelRemainder (N := N) hf hg hψ s t‖ := by
      rw [slice_averaged_duhamel_split hf hg hψ s ht.1]
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    have hte := mul_le_mul_of_nonneg_left hEb ht.1.le
    dsimp only [M,X,β,Y] at *
    nlinarith [hJb,hPb,hII,hte]
  have hreal := slice_power_assembly κ ht j p e Y M
    ‖sliceDifferencePath (N := N) hf hg hψ (s+t)‖ hj.le hp.le he.le (norm_nonneg _)
    (by dsimp [M]; positivity) hW
  have hnorm : ENNReal.ofReal (Real.sqrt t) *
      holderBesovENorm (Flow.lossExponent κ) (smoothNoiseJ N ⟨f,hf⟩ (s+t)) ≤
      ENNReal.ofReal (Real.sqrt t) * ENNReal.ofReal
        (‖sliceDifferencePath (N := N) hf hg hψ (s+t)‖+Y) := by
    simpa only [mul_comm] using mul_le_mul_left
      (slice_holderBesov_le_difference (N := N) hf hg hψ (Flow.lossExponent κ) s ht)
      (ENNReal.ofReal (Real.sqrt t))
  have hscalar : ENNReal.ofReal (Real.sqrt t) * ENNReal.ofReal
      (‖sliceDifferencePath (N := N) hf hg hψ (s+t)‖+Y) ≤
      ENNReal.ofReal c*(ENNReal.ofReal Y+(1+X)^3) := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg t)]
    apply (ENNReal.ofReal_le_ofReal hreal).trans
    have hm : ENNReal.ofReal M = (1+X)^3 := by
      rw [show M = (1+X.toReal)^3 from rfl,ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_add (by norm_num) ENNReal.toReal_nonneg,
        ENNReal.ofReal_one,ENNReal.ofReal_toReal hX]
    rw [ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add (norm_nonneg _) (by dsimp [M]; positivity),hm]
  have hfinal := hnorm.trans hscalar
  dsimp only [Y] at hfinal
  rw [probePotentialWindow_ofReal_norm] at hfinal
  exact hfinal

end GlobalPhi43.Attachment
