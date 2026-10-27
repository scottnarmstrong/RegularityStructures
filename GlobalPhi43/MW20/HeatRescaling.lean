module

public import GlobalPhi43.MW20.AffineDerivatives
public import GlobalPhi43.MW20.LocalMaximum

/-!
# Exact parabolic rescaling of the source cubic equation
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures

/-- The parabolic pullback with the cubic amplitude normalization. -/
@[expose] def sourceCubicPullback (w : ParabolicSpace → ℝ) (b : ParabolicSpace)
    (c : ℝ) (z : ParabolicSpace) : ℝ := c * w (b + parabolicDilate c z)

/-- Exact source heat rescaling, including the c³ amplitude. -/
theorem sourceHeat_cubicPullback (w : ParabolicSpace → ℝ) (b : ParabolicSpace)
    (c : ℝ) (z : ParabolicSpace) :
    sourceHeat (sourceCubicPullback w b c) z = c ^ 3 * sourceHeat w (b + parabolicDilate c z) := by
  let p := b + parabolicDilate c z
  have htime : (fun t => sourceCubicPullback w b c (t, z.2)) =
      (fun t => c * w (b.1 + c ^ 2 * t, p.2)) := rfl
  have hspace (i : Fin 3) : (fun a => sourceCubicPullback w b c (z.1, Function.update z.2 i a)) =
      (fun a => c * w (p.1, Function.update p.2 i (b.2 i + c * a))) := by
    funext a
    change c * w (b + parabolicDilate c (z.1, Function.update z.2 i a)) = _
    congr 2
    apply Prod.ext
    · rfl
    · funext j
      by_cases hj : j = i
      · subst j
        simp only [p, parabolicDilate, Prod.snd_add,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.update_self]
      · simp only [p, parabolicDilate, Prod.snd_add,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.update_of_ne hj]
  have ht : deriv (fun t => sourceCubicPullback w b c (t, z.2)) z.1 =
      c ^ 3 * deriv (fun t => w (t, p.2)) p.1 := by
    rw [htime, deriv_affine_pullback (fun t => w (t, p.2)) c b.1 (c ^ 2) z.1]
    rw [show p.1 = b.1 + c ^ 2 * z.1 from rfl]
    ring
  have hs (i : Fin 3) : deriv (deriv (fun a =>
      sourceCubicPullback w b c (z.1, Function.update z.2 i a))) (z.2 i) =
      c ^ 3 * deriv (deriv (fun a => w (p.1, Function.update p.2 i a))) (p.2 i) := by
    rw [hspace i, second_deriv_affine_pullback
      (fun a => w (p.1, Function.update p.2 i a)) c (b.2 i) c (z.2 i)]
    rw [show p.2 i = b.2 i + c * z.2 i from rfl]
    ring
  rw [sourceHeat, ht]
  simp only [hs, ← Finset.mul_sum]
  change c ^ 3 * _ - c ^ 3 * _ = c ^ 3 * (_ - _)
  ring

end GlobalPhi43.MW20
