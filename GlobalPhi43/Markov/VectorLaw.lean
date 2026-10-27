module

public import GlobalPhi43.Markov.ConditionalProducts
public import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-! # Finite-vector laws are determined by bounded cylinder products -/

public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace GlobalPhi43.Markov

variable {E : Type*} [MeasurableSpace E]

/-- Product tests are a generating class only: the conclusion is equality of measures
on the full finite vector sigma-algebra. -/
theorem measure_eq_of_vectorProducts (n : ℕ) (μ ν : Measure (Fin n → E))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ f : ℕ → E → ℝ, (∀ i, Measurable (f i)) →
      (∀ i y, ‖f i y‖ ≤ 1) →
      (∫ v, vectorProduct f n v ∂μ) = ∫ v, vectorProduct f n v ∂ν) : μ = ν := by
  classical
  apply ext_of_generate_finite
    (pi univ '' pi univ (fun _ : Fin n => {s : Set E | MeasurableSet s}))
    generateFrom_pi.symm (IsPiSystem.pi (fun _ => fun _ hs _ ht _ => hs.inter ht))
  · rintro _ ⟨s, hs, rfl⟩
    have hsm : ∀ i, MeasurableSet (s i) := by
      intro i
      exact (mem_univ_pi.mp hs) i
    let f : ℕ → E → ℝ := fun i => if hi : i < n then
      (s ⟨i, hi⟩).indicator (fun _ => 1) else fun _ => 1
    have hfm (i : ℕ) : Measurable (f i) := by
      dsimp only [f]
      split_ifs with hi
      · exact measurable_const.indicator (hsm ⟨i, hi⟩)
      · exact measurable_const
    have hfb (i : ℕ) (y : E) : ‖f i y‖ ≤ 1 := by
      dsimp only [f]
      split_ifs with hi
      · by_cases hy : y ∈ s ⟨i, hi⟩ <;> simp [hy]
      · simp
    have hp (v : Fin n → E) : vectorProduct f n v = (pi univ s).indicator (fun _ => 1) v := by
      by_cases hv : v ∈ pi univ s
      · rw [indicator_of_mem hv]
        apply Finset.prod_eq_one
        intro i _
        have hi := (mem_univ_pi.mp hv) i
        simp [f, i.isLt, hi]
      · obtain ⟨i, hi⟩ : ∃ i, v i ∉ s i := by simpa only [mem_univ_pi, not_forall] using hv
        rw [indicator_of_notMem hv]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [f, i.isLt, hi])
    have he := h f hfm hfb
    simp_rw [hp, integral_indicator (MeasurableSet.univ_pi hsm), setIntegral_const,
      smul_eq_mul, mul_one, measureReal_def] at he
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp he
  · simp

/-- The scalar conditional Markov identity determines the actual future-vector law.
The initial state is fixed once, and no joint-law premise is taken. -/
theorem map_future_eq_finiteChain {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℕ → Kernel E E) [∀ i, IsMarkovKernel (κ i)]
    (X : ℕ → Ω → E) (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ i, m i ≤ mΩ) (hmono : Monotone m)
    (hX : ∀ i, Measurable[m i] (X i)) (x : E) (h0 : X 0 =ᵐ[P] fun _ => x)
    (hMarkov : ∀ i (g : E → ℝ), Measurable g → (∀ y, ‖g y‖ ≤ 1) →
      P[fun ω => g (X (i + 1) ω) | m i] =ᵐ[P]
        fun ω => ∫ y, g y ∂κ i (X i ω)) (n : ℕ) :
    P.map (fun ω (i : Fin n) => X (i.val + 1) ω) = finiteChain κ n x := by
  have hv : Measurable (fun ω (i : Fin n) => X (i.val + 1) ω) :=
    Measurable.of_eval fun i => (hX (i.val + 1)).mono (hm _) le_rfl
  have : IsProbabilityMeasure (P.map (fun ω (i : Fin n) => X (i.val + 1) ω)) :=
    (Measure.isProbabilityMeasure_map_iff hv.aemeasurable).mpr inferInstance
  apply measure_eq_of_vectorProducts
  intro f hf hb
  rw [integral_map hv.aemeasurable (measurable_vectorProduct f hf n).aestronglyMeasurable]
  have hc := condExp_future_product P κ X m hm hmono hX hMarkov f hf hb n
  rw [← integral_condExp (hm 0), integral_congr_ae hc]
  calc
    _ = ∫ _, chainProduct κ f n x ∂P := integral_congr_ae
      (h0.mono fun ω hω => congrArg (chainProduct κ f n) hω)
    _ = _ := by simp [chainProduct]

end GlobalPhi43.Markov
