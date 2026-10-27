module

public import GlobalPhi43.Flow.FiniteRecurrence
public import GlobalPhi43.Flow.FiniteSubdivision

public section

open Set
open scoped ENNReal

namespace GlobalPhi43.Flow

/-- Iterates the local comparison over every closed mesh interval, including
its last partial interval. -/
theorem finite_mesh_estimate {T h : ℝ} (mesh : RestartMesh T h)
    {K D : ℝ≥0∞} (hK : 1 ≤ K) (d : ℝ → ℝ≥0∞)
    (hstep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ s + h → t ≤ T →
      d t ≤ K * (d s + D)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      d t ≤ K ^ mesh.count * d 0 + restartError K mesh.count * D := by
  have hg (j : ℕ) :
      d (mesh.point j) ≤ K ^ j * d 0 + restartError K j * D := by
    have hh := finite_restart_recurrence K D (fun i => d (mesh.point i)) j
      (fun i _ => hstep _ _ (mesh.nonneg i) (mesh.mono (Nat.le_succ i))
        (mesh.step i) (mesh.bounded (i + 1)))
    simpa only [mesh.initial] using hh
  intro t ht
  obtain ⟨j, hj, hleft, hright⟩ := mesh.covers t ht
  calc
    d t ≤ K * (d (mesh.point j) + D) :=
      hstep _ _ (mesh.nonneg j) hleft (hright.trans (mesh.step j)) ht.2
    _ ≤ K * ((K ^ j * d 0 + restartError K j * D) + D) := by
      exact mul_le_mul' le_rfl (add_le_add (hg j) le_rfl)
    _ = K ^ (j + 1) * d 0 + restartError K (j + 1) * D := by
      simp only [restartError_succ, pow_succ', mul_add, add_mul, mul_one, mul_assoc, add_assoc]
    _ ≤ K ^ mesh.count * d 0 + restartError K mesh.count * D :=
      restart_bound_mono hK (d 0) D (by omega)

end GlobalPhi43.Flow
