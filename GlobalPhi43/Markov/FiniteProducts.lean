module

public import GlobalPhi43.Markov.FiniteChain

/-! # Bounded product tests for finite kernel-law determination -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace GlobalPhi43.Markov

variable {E : Type*} [MeasurableSpace E]

/-- Cylinder product test; used only as the generating class for the full vector law. -/
def vectorProduct (f : ℕ → E → ℝ) (n : ℕ) (v : Fin n → E) : ℝ :=
  ∏ i : Fin n, f i (v i)

omit [MeasurableSpace E] in
theorem vectorProduct_cons (f : ℕ → E → ℝ) (n : ℕ) (y : E) (v : Fin n → E) :
    vectorProduct f (n + 1) (Fin.cons y v) =
      f 0 y * vectorProduct (fun i => f (i + 1)) n v := by
  simp [vectorProduct, Fin.prod_univ_succ]

theorem measurable_vectorProduct (f : ℕ → E → ℝ) (hf : ∀ i, Measurable (f i)) (n : ℕ) :
    Measurable (vectorProduct f n) :=
  Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)

omit [MeasurableSpace E] in
/-- Unit-bounded scalar tests give a unit-bounded whole-vector product. -/
theorem norm_vectorProduct_le_one (f : ℕ → E → ℝ)
    (hf : ∀ i y, ‖f i y‖ ≤ 1) (n : ℕ) (v : Fin n → E) :
    ‖vectorProduct f n v‖ ≤ 1 := by
  induction n generalizing f with
  | zero => simp [vectorProduct]
  | succ n ih =>
    have he : v = Fin.cons (v 0) (fun i => v i.succ) := by ext i; exact Fin.cases rfl (fun _ => rfl) i
    rw [he, vectorProduct_cons, norm_mul]
    simpa only [one_mul] using mul_le_mul (hf 0 (v 0))
      (ih (fun i => f (i + 1)) (fun i => hf (i + 1)) _) (norm_nonneg _) zero_le_one

/-- Integrating a cylinder product against the actual finite chain. -/
def chainProduct (κ : ℕ → Kernel E E) (f : ℕ → E → ℝ) (n : ℕ) (x : E) : ℝ :=
  ∫ v, vectorProduct f n v ∂finiteChain κ n x

theorem measurable_chainProduct (κ : ℕ → Kernel E E) [∀ i, IsMarkovKernel (κ i)]
    (f : ℕ → E → ℝ) (hf : ∀ i, Measurable (f i)) (n : ℕ) :
    Measurable (chainProduct κ f n) :=
  measurable_integral_finiteChain κ n (measurable_vectorProduct f hf n)

theorem norm_chainProduct_le_one (κ : ℕ → Kernel E E) [∀ i, IsMarkovKernel (κ i)]
    (f : ℕ → E → ℝ) (hf : ∀ i y, ‖f i y‖ ≤ 1) (n : ℕ) (x : E) :
    ‖chainProduct κ f n x‖ ≤ 1 := by
  simpa only [chainProduct, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const (μ := finiteChain κ n x)
      (ae_of_all _ (norm_vectorProduct_le_one f hf n))

theorem chainProduct_zero (κ : ℕ → Kernel E E) (f : ℕ → E → ℝ) (x : E) :
    chainProduct κ f 0 x = 1 := by
  rw [chainProduct, integral_finiteChain_zero]
  simp [vectorProduct]

theorem chainProduct_succ (κ : ℕ → Kernel E E) [∀ i, IsMarkovKernel (κ i)]
    (f : ℕ → E → ℝ) (hm : ∀ i, Measurable (f i)) (hb : ∀ i y, ‖f i y‖ ≤ 1)
    (n : ℕ) (x : E) :
    chainProduct κ f (n + 1) x =
      ∫ y, f 0 y * chainProduct (fun i => κ (i + 1)) (fun i => f (i + 1)) n y ∂κ 0 x := by
  rw [chainProduct, integral_finiteChain_succ κ n x (measurable_vectorProduct f hm _) 1
    (norm_vectorProduct_le_one f hb _)]
  congr 1
  funext y
  simp_rw [vectorProduct_cons]
  exact integral_const_mul _ _

end GlobalPhi43.Markov
