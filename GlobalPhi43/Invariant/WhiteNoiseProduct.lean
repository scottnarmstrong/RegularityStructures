module

public import GlobalPhi43.Markov.NoiseWindows
public import Mathlib.Probability.Independence.Basic

/-! # The literal product-space lift preserves the white-noise property -/

public noncomputable section

open MeasureTheory ProbabilityTheory RegularityStructures

namespace GlobalPhi43.Invariant

variable {Ω A E : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace E]

/-- A measurable map preserving the whole source law preserves all finite Gaussian
vectors, their means and covariances, hence the exact RS white-noise predicate. -/
theorem isWhiteNoise_of_map (P : Measure Ω) (Q : Measure A)
    (f : A → Ω) (hf : Measurable f) (hmap : Q.map f = P)
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W) :
    IsWhiteNoise Q (fun h a => W h (f a)) := by
  constructor
  · exact fun h hh => (hW.1 h hh).comp hf
  · intro n h hh
    rcases hW.2 n h hh with ⟨_, hG, hmean, hcov⟩
    have hx : Measurable (fun ω (i : Fin n) => W (h i) ω) :=
      Measurable.of_eval fun i => hW.1 (h i) (hh i)
    have hlaw : Q.map (fun a (i : Fin n) => W (h i) (f a)) =
        P.map (fun ω (i : Fin n) => W (h i) ω) := by
      change Q.map ((fun ω (i : Fin n) => W (h i) ω) ∘ f) = _
      rw [← Measure.map_map hx hf, hmap]
    refine ⟨(hx.comp hf).aemeasurable, hlaw.symm ▸ hG, ?_, ?_⟩
    · intro i
      have he := integral_map (μ := Q) hf.aemeasurable
        (hW.1 (h i) (hh i)).aestronglyMeasurable
      rw [hmap] at he
      exact he.symm.trans (hmean i)
    · intro i j
      have he := integral_map (μ := Q) hf.aemeasurable
        ((hW.1 (h i) (hh i)).mul (hW.1 (h j) (hh j))).aestronglyMeasurable
      rw [hmap] at he
      exact he.symm.trans (hcov i j)

/-- Wbar(h)(omega,z)=W(h)(omega), on precisely P.prod mu. -/
theorem isWhiteNoise_product (P : Measure Ω) (μ : Measure E) [IsProbabilityMeasure μ]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W) :
    IsWhiteNoise (P.prod μ) (fun h p => W h p.1) :=
  isWhiteNoise_of_map P (P.prod μ) Prod.fst measurable_fst
    measurePreserving_fst.map_eq W hW

/-- Independence holds for the whole L2-test-indexed noise family, not only
for one scalar sample or one finite tuple. The index carries the source MemLp condition. -/
theorem initial_indep_l2Noise_product (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W) :
    IndepFun (fun p : Ω × E => p.2)
      (fun p : Ω × E => fun h : {h : SpaceTime → ℝ // MemLp h 2} => W h.val p.1)
      (P.prod μ) := by
  exact (indepFun_prod (μ := P) (ν := μ)
    (Measurable.of_eval fun h : {h : SpaceTime → ℝ // MemLp h 2 volume} => hW.1 h.val h.property)
    (measurable_id : Measurable (fun x : E => x))).symm

/-- The literal initial coordinate has the given probability law. -/
theorem initial_product_law (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure E) [SFinite μ] :
    (P.prod μ).map Prod.snd = μ := measurePreserving_snd.map_eq

end GlobalPhi43.Invariant
