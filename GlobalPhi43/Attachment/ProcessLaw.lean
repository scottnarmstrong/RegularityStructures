module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Probability.IdentDistrib

/-! Equality of process laws from finite-dimensional marginals. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory

/-- Finite-dimensional laws determine the law on the coordinate sigma algebra. -/
theorem process_map_eq_of_finite_law {Ω Ω' I : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {X : Ω → I → ℝ} {Y : Ω' → I → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hfin : ∀ (n : ℕ) (i : Fin n → I),
      P.map (fun ω j => X ω (i j)) = P'.map (fun ω j => Y ω (i j))) :
    P.map X = P'.map Y := by
  classical
  let F (s : Finset I) := (P.map X).map s.restrict
  have hprojX : IsProjectiveLimit (P.map X) F := fun _ => rfl
  have hprojY : IsProjectiveLimit (P'.map Y) F := by
    intro s
    let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
    let restore : (Fin (Fintype.card s) → ℝ) → (s → ℝ) := fun v i => v (e.symm i)
    have hm : Measurable restore := by fun_prop
    have h := congrArg (fun μ => μ.map restore) (hfin _ (fun j => (e j).1))
    have hmeasX : Measurable (fun ω j => X ω (e j).1) := by fun_prop
    have hmeasY : Measurable (fun ω j => Y ω (e j).1) := by fun_prop
    rw [Measure.map_map hm hmeasX, Measure.map_map hm hmeasY] at h
    have hx : (restore ∘ fun ω j => X ω (e j).1) = (s.restrict ∘ X) := by
      funext ω i
      simp [restore, Finset.restrict_def]
    have hy : (restore ∘ fun ω j => Y ω (e j).1) = (s.restrict ∘ Y) := by
      funext ω i
      simp [restore, Finset.restrict_def]
    rw [hx, hy] at h
    change (P'.map Y).map s.restrict = (P.map X).map s.restrict
    rw [Measure.map_map (by fun_prop) hX, Measure.map_map (by fun_prop) hY]
    exact h.symm
  exact hprojX.unique hprojY

end GlobalPhi43.Attachment
