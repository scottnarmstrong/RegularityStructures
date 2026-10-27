module

public import GlobalPhi43.Invariant.StationaryProduct
public import Mathlib.Data.Fin.Tuple.Sort

/-! # Stationarity for every finite observation tuple, including empty and repeated times -/

public noncomputable section

open MeasureTheory
open scoped NNReal

namespace GlobalPhi43.Invariant

/-- Sorting and a measurable inverse permutation remove the order restriction.
The empty vector is literally the unique function on Fin 0. -/
theorem stationary_finite_tuples {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (Q : Measure A) (X : ℝ≥0 → A → E) (hX : ∀ t, Measurable (X t))
    (hordered : ∀ n (t : Fin (n + 1) → ℝ≥0), Monotone t → ∀ r : ℝ≥0,
      Q.map (fun a i => X (r + t i) a) = Q.map (fun a i => X (t i) a))
    (k : ℕ) (t : Fin k → ℝ≥0) (r : ℝ≥0) :
    Q.map (fun a i => X (r + t i) a) = Q.map (fun a i => X (t i) a) := by
  classical
  cases k with
  | zero =>
    congr 1
    funext a i
    exact Fin.elim0 i
  | succ n =>
    let e := Tuple.sort t
    let undo : (Fin (n + 1) → E) → (Fin (n + 1) → E) := fun v i => v (e.symm i)
    have hm : Measurable undo := Measurable.of_eval fun i => measurable_pi_apply _
    have h := congrArg (Measure.map undo) (hordered n (t ∘ e) (Tuple.monotone_sort t) r)
    rw [Measure.map_map hm (Measurable.of_eval fun i => hX _),
      Measure.map_map hm (Measurable.of_eval fun i => hX _)] at h
    simpa only [undo, Function.comp_def, Equiv.apply_symm_apply] using h

/-- Stationarity for real-valued nonnegative observation tuples and shifts. -/
theorem stationary_real_tuples {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (Q : Measure A) (X : ℝ≥0 → A → E) (hX : ∀ t, Measurable (X t))
    (hordered : ∀ n (t : Fin (n + 1) → ℝ≥0), Monotone t → ∀ r : ℝ≥0,
      Q.map (fun a i => X (r + t i) a) = Q.map (fun a i => X (t i) a))
    (k : ℕ) (t : Fin k → ℝ) (ht : ∀ i, 0 ≤ t i) (r : ℝ) (hr : 0 ≤ r) :
    Q.map (fun a i => X ⟨t i + r, add_nonneg (ht i) hr⟩ a) =
      Q.map (fun a i => X ⟨t i, ht i⟩ a) := by
  have h := stationary_finite_tuples Q X hX hordered k (fun i => ⟨t i, ht i⟩) ⟨r, hr⟩
  convert h using 1
  congr 1
  funext a i
  congr 1
  exact Subtype.ext (add_comm _ _)

end GlobalPhi43.Invariant
