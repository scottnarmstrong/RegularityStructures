module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Tactic

/-!
# Finite MW20 convolution blocks as actual measures

This is the measure-level finite factorisation in (2.7). Factors are probability
measures, not a postulated associative operation. The smooth densities and the
infinite-convolution limit are not constructed in this module.
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory

variable {G : Type*} [AddMonoid G] [MeasurableSpace G]

/-- Consecutive finite convolution block, with the zero-fold block a Dirac mass. -/
@[expose] noncomputable def kernelMeasure (K : ℕ → Measure G) (s : ℕ) : ℕ → Measure G
  | 0 => Measure.dirac 0
  | n + 1 => (kernelMeasure K s n).conv (K (s + n))

@[simp] theorem kernelMeasure_succ (K : ℕ → Measure G) (s n : ℕ) :
    kernelMeasure K s (n + 1) = (kernelMeasure K s n).conv (K (s + n)) := rfl

variable [MeasurableAdd₂ G]

/-- All finite convolution blocks have mass one. -/
instance kernelMeasure_probability (K : ℕ → Measure G) [∀ j, IsProbabilityMeasure (K j)]
    (s n : ℕ) : IsProbabilityMeasure (kernelMeasure K s n) := by
  induction n with
  | zero => simp only [kernelMeasure]; infer_instance
  | succ n ih =>
    rw [kernelMeasure_succ]
    have := ih
    infer_instance

/-- Factorisation (2.7) at the level of actual finite probability measures. -/
theorem kernelMeasure_add (K : ℕ → Measure G) [∀ j, IsProbabilityMeasure (K j)]
    (s n m : ℕ) :
    kernelMeasure K s (n + m) = (kernelMeasure K s n).conv (kernelMeasure K (s + n) m) := by
  induction m with
  | zero => simp [kernelMeasure]
  | succ m ih =>
    simp only [Nat.add_succ, kernelMeasure_succ, ih, Nat.add_assoc]
    exact Measure.conv_assoc _ _ _

omit [MeasurableAdd₂ G] in
/-- Scale-index shift for finite measure blocks. -/
theorem kernelMeasure_shift (K : ℕ → Measure G) (s n : ℕ) :
    kernelMeasure K s n = kernelMeasure (fun j => K (s + j)) 0 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [kernelMeasure_succ, ih, Nat.zero_add]

end GlobalPhi43.MW20
