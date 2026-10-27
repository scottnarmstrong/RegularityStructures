module

public import GlobalPhi43.Local.ParabolicTransport
public import GlobalPhi43.MW20.HeatRescaling

public section

namespace GlobalPhi43.MW20

open RegularityStructures

/-- Exact heat transport with independent field amplitude and coordinate scale. -/
theorem sourceHeat_parabolicPullback (A : ℝ) (w : ParabolicSpace → ℝ) (b : ParabolicSpace)
    (c : ℝ) (z : ParabolicSpace) :
    sourceHeat (Local.parabolicPullback A w b c) z = A * c ^ 2 * sourceHeat w (b + parabolicDilate c z) := by
  let p := b + parabolicDilate c z
  have htime : (fun t => Local.parabolicPullback A w b c (t, z.2)) =
      (fun t => A * w (b.1 + c ^ 2 * t, p.2)) := rfl
  have hspace (i : Fin 3) : (fun a => Local.parabolicPullback A w b c (z.1, Function.update z.2 i a)) =
      (fun a => A * w (p.1, Function.update p.2 i (b.2 i + c * a))) := by
    funext a
    change A * w (b + parabolicDilate c (z.1, Function.update z.2 i a)) = _
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
  have ht : deriv (fun t => Local.parabolicPullback A w b c (t, z.2)) z.1 =
      A * c ^ 2 * deriv (fun t => w (t, p.2)) p.1 := by
    rw [htime, deriv_affine_pullback (fun t => w (t, p.2)) A b.1 (c ^ 2) z.1]
    rw [show p.1 = b.1 + c ^ 2 * z.1 from rfl]
  have hs (i : Fin 3) : deriv (deriv (fun a =>
      Local.parabolicPullback A w b c (z.1, Function.update z.2 i a))) (z.2 i) =
      A * c ^ 2 * deriv (deriv (fun a => w (p.1, Function.update p.2 i a))) (p.2 i) := by
    rw [hspace i, second_deriv_affine_pullback
      (fun a => w (p.1, Function.update p.2 i a)) A (b.2 i) c (z.2 i)]
    rw [show p.2 i = b.2 i + c * z.2 i from rfl]
  rw [sourceHeat, ht]
  simp only [hs, ← Finset.mul_sum]
  change A * c ^ 2 * _ - A * c ^ 2 * _ = A * c ^ 2 * (_ - _)
  ring


end GlobalPhi43.MW20
