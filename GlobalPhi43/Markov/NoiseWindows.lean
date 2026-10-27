module

public import GlobalPhi43.Markov.Independence
public import GlobalPhi43.Markov.WhiteNoiseIndependence
public import GlobalPhi43Statements.Defs.NoiseWindowSigma

public noncomputable section

open MeasureTheory ProbabilityTheory Set
open RegularityStructures

namespace GlobalPhi43.Markov

/-- The completed window sigma-algebra is a sub-sigma-algebra of the ambient space. -/
theorem noiseWindowSigma_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W) (s t : ℝ) :
    noiseWindowSigma P W s t ≤ mΩ := by
  apply sup_le
  · exact MeasurableSpace.generateFrom_le fun _ h => h.1
  · apply iSup_le
    intro h
    apply iSup_le
    intro hh
    exact (hW.1 h hh.1).comap_le

/-- Inclusion of deterministic time windows gives inclusion of their completed sigma-algebras. -/
theorem noiseWindowSigma_mono {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ) {s t s' t' : ℝ}
    (hs : s' ≤ s) (ht : t ≤ t') : noiseWindowSigma P W s t ≤ noiseWindowSigma P W s' t' := by
  unfold noiseWindowSigma
  apply sup_le_sup le_rfl
  apply iSup_mono
  intro h
  apply iSup_mono'
  intro hh
  have hsupp : Function.support h ⊆ Ioc s' t' ×ˢ univ := by
    intro z hz
    have hzt := (hh.2 hz).1
    exact ⟨⟨lt_of_le_of_lt hs hzt.1, hzt.2.trans ht⟩, trivial⟩
  exact ⟨⟨hh.1, hsupp⟩, le_rfl⟩

/-- Disjoint deterministic white-noise windows are independent after adjoining ambient null sets. -/
theorem indep_noiseWindowSigma {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {s t s' t' : ℝ} (hsep : t ≤ s') :
    Indep (noiseWindowSigma P W s t) (noiseWindowSigma P W s' t') P := by
  let I := {h : SpaceTime → ℝ // MemLp h 2 ∧ Function.support h ⊆ Ioc s t ×ˢ univ}
  let J := {h : SpaceTime → ℝ // MemLp h 2 ∧ Function.support h ⊆ Ioc s' t' ×ˢ univ}
  have horth (h : I) (g : J) : (∫ z, h.val z * g.val z) = 0 := by
    apply integral_eq_zero_of_ae
    apply ae_of_all
    intro z
    change h.val z * g.val z = 0
    by_cases hh : h.val z = 0
    · rw [hh, zero_mul]
    · have ht := (h.property.2 (Function.mem_support.mpr hh)).1.2
      have hg : g.val z = 0 := by
        by_contra hg
        have hs := (g.property.2 (Function.mem_support.mpr hg)).1.1
        linarith
      rw [hg, mul_zero]
  have hInd := whiteNoise_indep_processes P hW (fun h : I => h.val) (fun g : J => g.val)
    (fun h => h.property.1) (fun g => g.property.1) horth
  have hleft : (⨆ (h : SpaceTime → ℝ) (_ : MemLp h 2 ∧ Function.support h ⊆ Ioc s t ×ˢ univ),
      MeasurableSpace.comap (W h) inferInstance) ≤
      MeasurableSpace.comap (fun ω (h : I) => W h.val ω) inferInstance := by
    apply iSup_le
    intro h
    apply iSup_le
    intro hh
    have hp : @Measurable Ω (I → ℝ)
        (MeasurableSpace.comap (fun ω (h : I) => W h.val ω) inferInstance) inferInstance
        (fun ω (h : I) => W h.val ω) := Measurable.of_comap_le le_rfl
    exact ((measurable_pi_apply (⟨h, hh⟩ : I)).comp hp).comap_le
  have hright : (⨆ (h : SpaceTime → ℝ) (_ : MemLp h 2 ∧ Function.support h ⊆ Ioc s' t' ×ˢ univ),
      MeasurableSpace.comap (W h) inferInstance) ≤
      MeasurableSpace.comap (fun ω (h : J) => W h.val ω) inferInstance := by
    apply iSup_le
    intro h
    apply iSup_le
    intro hh
    have hp : @Measurable Ω (J → ℝ)
        (MeasurableSpace.comap (fun ω (h : J) => W h.val ω) inferInstance) inferInstance
        (fun ω (h : J) => W h.val ω) := Measurable.of_comap_le le_rfl
    exact ((measurable_pi_apply (⟨h, hh⟩ : J)).comp hp).comap_le
  exact indep_adjoin_null P (indep_of_indep_of_le hInd hleft hright)

end GlobalPhi43.Markov
