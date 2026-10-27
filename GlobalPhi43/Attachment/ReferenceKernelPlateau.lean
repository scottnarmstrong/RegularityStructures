module

public import GlobalPhi43.MW20.TestKernelOfProfile
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! An actual smooth plateau in the literal past unit ball. -/

public noncomputable section
namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures Set
open scoped ContDiff

@[expose] def referenceBump : ContDiffBump (0 : ℝ) :=
  ⟨3/4, 7/8, by norm_num, by norm_num⟩

@[expose] def referenceKernelPlateau (z : ParabolicSpace) : ℝ :=
  referenceBump (2*z.1+1) * ∏ i : Fin 3, referenceBump (z.2 i)

@[expose] def referenceKernelOuter : Set ParabolicSpace :=
  Icc (-(15/16 : ℝ), fun _ => -(7/8 : ℝ)) (-(1/16 : ℝ), fun _ => (7/8 : ℝ))

@[expose] def referenceKernelInner : Set ParabolicSpace :=
  Icc (-(7/8 : ℝ), fun _ => -(3/4 : ℝ)) (-(1/8 : ℝ), fun _ => (3/4 : ℝ))

theorem referenceKernelPlateau_smooth : ContDiff ℝ ∞ referenceKernelPlateau :=
  (referenceBump.contDiff.comp (by fun_prop)).mul
    (contDiff_prod fun i _ => referenceBump.contDiff.comp (by fun_prop))

theorem referenceKernelPlateau_nonneg (z : ParabolicSpace) : 0 ≤ referenceKernelPlateau z :=
  mul_nonneg referenceBump.nonneg (Finset.prod_nonneg fun _ _ => referenceBump.nonneg)

theorem referenceKernelPlateau_le_one (z : ParabolicSpace) : referenceKernelPlateau z ≤ 1 := by
  exact (mul_le_mul referenceBump.le_one
    (Finset.prod_le_one₀ (fun _ _ => referenceBump.nonneg) (fun _ _ => referenceBump.le_one))
    (Finset.prod_nonneg fun _ _ => referenceBump.nonneg) (by norm_num)).trans_eq (one_mul 1)

theorem referenceKernelPlateau_support : tsupport referenceKernelPlateau ⊆ referenceKernelOuter := by
  apply closure_minimal _ isClosed_Icc
  intro z hz
  have ht : referenceBump (2*z.1+1) ≠ 0 := (mul_ne_zero_iff.mp hz).1
  have hx : ∀ i : Fin 3, referenceBump (z.2 i) ≠ 0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).2) i (Finset.mem_univ i)
  have htime : |2*z.1+1| < 7/8 := by
    have hh : 2*z.1+1 ∈ Function.support referenceBump := ht
    simpa [ContDiffBump.support_eq, Metric.mem_ball, Real.dist_eq, referenceBump] using hh
  have hspace (i : Fin 3) : |z.2 i| < 7/8 := by
    have hh : z.2 i ∈ Function.support referenceBump := hx i
    simpa [ContDiffBump.support_eq, Metric.mem_ball, Real.dist_eq, referenceBump] using hh
  exact ⟨⟨by linarith [(abs_lt.mp htime).1], fun i => (by linarith [(abs_lt.mp (hspace i)).1])⟩,
    ⟨by linarith [(abs_lt.mp htime).2], fun i => (by linarith [(abs_lt.mp (hspace i)).2])⟩⟩

theorem referenceKernelPlateau_compact : HasCompactSupport referenceKernelPlateau :=
  isCompact_Icc.of_isClosed_subset isClosed_closure referenceKernelPlateau_support

theorem referenceKernelPlateau_integrable : Integrable referenceKernelPlateau :=
  referenceKernelPlateau_smooth.continuous.integrable_of_hasCompactSupport referenceKernelPlateau_compact

theorem referenceKernelPlateau_one {z : ParabolicSpace} (hz : z ∈ referenceKernelInner) :
    referenceKernelPlateau z = 1 := by
  have ht : referenceBump (2*z.1+1) = 1 := referenceBump.one_of_mem_closedBall (by
    change |2*z.1+1-0| ≤ (3/4 : ℝ)
    rw [sub_zero, abs_le]
    exact ⟨by linarith [hz.1.1], by linarith [hz.2.1]⟩)
  have hx (i : Fin 3) : referenceBump (z.2 i) = 1 := referenceBump.one_of_mem_closedBall (by
    change |z.2 i-0| ≤ (3/4 : ℝ)
    rw [sub_zero, abs_le]
    exact ⟨hz.1.2 i, hz.2.2 i⟩)
  simp only [referenceKernelPlateau, ht, hx, Finset.prod_const_one, mul_one]

theorem referenceKernelPlateau_even (t : ℝ) (x : Fin 3 → ℝ) :
    referenceKernelPlateau (t,-x) = referenceKernelPlateau (t,x) := by
  simp only [referenceKernelPlateau, Pi.neg_apply, referenceBump.neg]

end GlobalPhi43.Attachment
