module

public import GlobalPhi43.Markov.Semigroup
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Finite chains of probability transition kernels -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GlobalPhi43.Markov

variable {E : Type*} [MeasurableSpace E]

/-- Appending the first observation to the remaining finite vector is measurable. -/
theorem measurable_finCons (n : ℕ) :
    Measurable (fun p : E × (Fin n → E) => (Fin.cons p.1 p.2 : Fin (n + 1) → E)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

/-- The first kernel observes the first coordinate, and each later kernel starts at
the preceding observation. Length zero is the unique empty-vector probability. -/
def finiteChain (κ : ℕ → Kernel E E) : (n : ℕ) → Kernel E (Fin n → E)
  | 0 => Kernel.deterministic (fun _ => Fin.elim0) measurable_const
  | n + 1 => ((κ 0) ⊗ₖ ((finiteChain (fun i => κ (i + 1)) n).comap
      Prod.snd measurable_snd)).map (fun p => Fin.cons p.1 p.2)

instance finiteChain_isMarkov (κ : ℕ → Kernel E E) [∀ i, IsMarkovKernel (κ i)]
    (n : ℕ) : IsMarkovKernel (finiteChain κ n) := by
  induction n generalizing κ with
  | zero => dsimp [finiteChain]; infer_instance
  | succ n ih =>
    have := ih (fun i => κ (i + 1))
    dsimp only [finiteChain]
    exact Kernel.IsMarkovKernel.map _ (measurable_finCons n)

/-- Borel tests of the entire vector have Borel expectation in the starting state. -/
theorem measurable_integral_finiteChain (κ : ℕ → Kernel E E)
    [∀ i, IsMarkovKernel (κ i)] (n : ℕ) {F : (Fin n → E) → ℝ} (hF : Measurable F) :
    Measurable (fun x => ∫ v, F v ∂finiteChain κ n x) :=
  hF.stronglyMeasurable.integral_kernel.measurable

/-- The recursive integral identity holds for every bounded Borel vector test,
without restricting to products of scalar tests. -/
theorem integral_finiteChain_succ (κ : ℕ → Kernel E E)
    [∀ i, IsMarkovKernel (κ i)] (n : ℕ) (x : E)
    {F : (Fin (n + 1) → E) → ℝ} (hF : Measurable F)
    (C : ℝ) (hC : ∀ v, ‖F v‖ ≤ C) :
    (∫ v, F v ∂finiteChain κ (n + 1) x) =
      ∫ y, ∫ v, F (Fin.cons y v) ∂finiteChain (fun i => κ (i + 1)) n y ∂κ 0 x := by
  let η : Kernel (E × E) (Fin n → E) :=
    (finiteChain (fun i => κ (i + 1)) n).comap Prod.snd measurable_snd
  have hm : Measurable (fun p : E × (Fin n → E) => F (Fin.cons p.1 p.2)) :=
    hF.comp (measurable_finCons n)
  have hi : Integrable (fun p : E × (Fin n → E) => F (Fin.cons p.1 p.2))
      ((κ 0 ⊗ₖ η) x) := Integrable.of_bound hm.aestronglyMeasurable C
        (ae_of_all _ fun p => hC _)
  rw [finiteChain, Kernel.map_apply _ (measurable_finCons n),
    integral_map (measurable_finCons n).aemeasurable hF.aestronglyMeasurable]
  exact ProbabilityTheory.integral_compProd hi

/-- The empty-vector base case used when expanding the recursion. -/
theorem integral_finiteChain_zero (κ : ℕ → Kernel E E) (x : E)
    (F : (Fin 0 → E) → ℝ) : (∫ v, F v ∂finiteChain κ 0 x) = F Fin.elim0 := by
  simp [finiteChain, Kernel.deterministic_apply]

end GlobalPhi43.Markov
