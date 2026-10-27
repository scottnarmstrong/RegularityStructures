module

public import GlobalPhi43.Markov.FiniteProducts
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Iteration of scalar conditional Markov identities -/

public noncomputable section

open MeasureTheory ProbabilityTheory

namespace GlobalPhi43.Markov

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]

/-- Future cylinder products are obtained from scalar Markov identities, adaptedness
and the increasing filtration. No finite-dimensional law is assumed. -/
theorem condExp_future_product (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℕ → Kernel E E) [∀ i, IsMarkovKernel (κ i)]
    (X : ℕ → Ω → E) (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ i, m i ≤ mΩ) (hmono : Monotone m)
    (hX : ∀ i, Measurable[m i] (X i))
    (hMarkov : ∀ i (g : E → ℝ), Measurable g → (∀ y, ‖g y‖ ≤ 1) →
      P[fun ω => g (X (i + 1) ω) | m i] =ᵐ[P]
        fun ω => ∫ y, g y ∂κ i (X i ω))
    (f : ℕ → E → ℝ) (hf : ∀ i, Measurable (f i)) (hb : ∀ i y, ‖f i y‖ ≤ 1)
    (n : ℕ) :
    P[fun ω => vectorProduct f n (fun i => X (i.val + 1) ω) | m 0] =ᵐ[P]
      fun ω => chainProduct κ f n (X 0 ω) := by
  induction n generalizing κ X m f with
  | zero =>
    have he : (fun ω => vectorProduct f 0 (fun i => X (i.val + 1) ω)) =
        (fun _ : Ω => (1 : ℝ)) := by funext ω; simp [vectorProduct]
    rw [he]
    simp only [chainProduct_zero]
    exact Filter.Eventually.of_forall fun ω => congrFun (condExp_const (μ := P) (hm 0) (1 : ℝ)) ω
  | succ n ih =>
    let B : Ω → ℝ := fun ω => vectorProduct (fun i => f (i + 1)) n
      (fun i => X (i.val + 2) ω)
    let H : E → ℝ := chainProduct (fun i => κ (i + 1)) (fun i => f (i + 1)) n
    have hB : Integrable B P := by
      apply Integrable.of_bound _ 1 (ae_of_all _ fun ω =>
        norm_vectorProduct_le_one _ (fun i => hb (i + 1)) n _)
      exact ((measurable_vectorProduct _ (fun i => hf (i + 1)) n).comp
        (Measurable.of_eval (fun i => (hX (i.val + 2)).mono (hm _) le_rfl))).aestronglyMeasurable
    have hH : Measurable H := measurable_chainProduct _ _ (fun i => hf (i + 1)) n
    have hHbound : ∀ y, ‖H y‖ ≤ 1 := norm_chainProduct_le_one _ _ (fun i => hb (i + 1)) n
    have htail : P[B | m 1] =ᵐ[P] fun ω => H (X 1 ω) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using
        ih (fun i => κ (i + 1)) (fun i => X (i + 1)) (fun i => m (i + 1))
          (fun i => hm (i + 1)) (fun _ _ h => hmono (Nat.add_le_add_right h 1))
          (fun i => hX (i + 1)) (fun i => hMarkov (i + 1))
          (fun i => f (i + 1)) (fun i => hf (i + 1)) (fun i => hb (i + 1))
    let A : Ω → ℝ := fun ω => f 0 (X 1 ω)
    have hA : StronglyMeasurable[m 1] A := ((hf 0).comp (hX 1)).stronglyMeasurable
    have hprod : (fun ω => vectorProduct f (n + 1) (fun i => X (i.val + 1) ω)) = A * B := by
      funext ω
      simp [A, B, vectorProduct, Fin.prod_univ_succ, Nat.add_assoc]
    have hpull : P[A * B | m 1] =ᵐ[P] fun ω => f 0 (X 1 ω) * H (X 1 ω) := by
      exact (condExp_stronglyMeasurable_mul_of_bound (hm 1) hA hB 1
        (ae_of_all _ fun ω => hb 0 (X 1 ω))).trans
          (htail.mono fun ω h => by simp only [Pi.mul_apply, h]; rfl)
    let g : E → ℝ := fun y => f 0 y * H y
    have hg : Measurable g := (hf 0).mul hH
    have hgb : ∀ y, ‖g y‖ ≤ 1 := by
      intro y
      dsimp only [g]
      rw [norm_mul]
      simpa using mul_le_mul (hb 0 y) (hHbound y) (norm_nonneg _) zero_le_one
    rw [hprod]
    have htower := (condExp_condExp_of_le (hmono (show 0 ≤ 1 by omega)) (hm 1)
      (f := A * B) (μ := P)).symm
    refine htower.trans ((condExp_congr_ae hpull).trans ((hMarkov 0 g hg hgb).trans ?_))
    exact ae_of_all _ fun ω => (chainProduct_succ κ f hf hb n (X 0 ω)).symm

end GlobalPhi43.Markov
