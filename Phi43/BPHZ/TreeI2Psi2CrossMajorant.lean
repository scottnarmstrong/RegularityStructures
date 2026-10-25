/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2CrossPointwise
public import Phi43.BPHZ.TreeI2Psi2DifferenceMajorant

/-!
# The second difference of the chaos kernels at two mollifiers is dominated by the diagram majorants

For `θ ∈ (0, 1]`, scales `a, b ∈ (0, 1]` and the kernel increments `A, A'` of `TreeI2Psi2Field`,
`abs_i2Psi2DiffChaos4Two_le` and `abs_i2Psi2DiffChaos2Two_le` bound `|A A' Δ|` by
`C (max a b)^(2θ)` times the eight-monomial majorants `i2Psi2Maj4`, `i2Psi2Maj2`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem rpow_two_theta_i2 {M θ : ℝ} (hM : 0 < M) : (M ^ θ) ^ 2 = M ^ (2 * θ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
  congr 1
  push_cast
  ring

/-- **Chaos `4`: pointwise domination of the second difference.** -/
theorem abs_i2Psi2DiffChaos4Two_le (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b : ℝ}, 0 < a → a ≤ 1 → 0 < b → b ≤ 1 → ∀ x y y' w w' : SpaceTime,
      0 < torusParabolicSize (w' - w) → 0 < torusParabolicSize (y' - w) →
      0 < torusParabolicSize (y - w') → 0 < torusParabolicSize (y - y') →
        |hairerI2Psi2Kernel N x y w * hairerI2Psi2Kernel N x y' w' *
            i2Psi2DiffChaos4Two N ρ ρ' a b y y' w w'| ≤
          C * (max a b) ^ (2 * θ) * i2Psi2Maj4 θ (hairerKernelTorus N) x y y' (w, w') := by
  obtain ⟨A, hA, h⟩ := i2Psi2CrossTwo_tables_bd N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨65536 * A ^ 4, by positivity, ?_⟩
  intro a b ha ha1 hb hb1 x y y' w w' p02 p03 p12 p13
  obtain ⟨hn, hf⟩ := h ha ha1 hb hb1
  have hμ : 0 ≤ (max a b) ^ θ := Real.rpow_nonneg (le_max_of_le_left ha.le) _
  have f02 := (hf (w - w') (by rwa [neg_sub])).1
  have f03 := (hf (w - y') (by rwa [neg_sub])).1
  rw [neg_sub] at f02 f03
  have n12 := (hn (y - w') p12).1
  have n13 := (hn (y - y') p13).1
  have nq : ∀ u : SpaceTime, 0 ≤ torusParabolicSize u ^ (-θ) := fun u =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have key := abs_i2Psi2Dm_chaos4_le (T02 := i2Psi2Tab1Two N ρ ρ' a b (w - w'))
    (T03 := i2Psi2Tab1Two N ρ ρ' a b (w - y')) (T12 := i2Psi2Tab1Two N ρ ρ' a b (y - w'))
    (T13 := i2Psi2Tab1Two N ρ ρ' a b (y - y')) hμ (nq _) (nq _) (nq _) (nq _) f02 f03 n12 n13
  rw [← i2Psi2DiffChaos4Two_eq] at key
  have hmax : 0 < max a b := lt_max_of_lt_left ha
  calc |hairerI2Psi2Kernel N x y w * hairerI2Psi2Kernel N x y' w' *
          i2Psi2DiffChaos4Two N ρ ρ' a b y y' w w'|
      = |hairerI2Psi2Kernel N x y w| * |hairerI2Psi2Kernel N x y' w'| *
          |i2Psi2DiffChaos4Two N ρ ρ' a b y y' w w'| := by rw [abs_mul, abs_mul]
    _ ≤ |hairerI2Psi2Kernel N x y w| * |hairerI2Psi2Kernel N x y' w'| *
          (65536 * A ^ 4 * ((max a b) ^ θ) ^ 2 * i2Psi2Mon4 (torusParabolicSize (w' - w) ^ (-(1 : ℝ)))
          (torusParabolicSize (y' - w) ^ (-(1 : ℝ))) (torusParabolicSize (y - w') ^ (-(1 : ℝ)))
          (torusParabolicSize (y - y') ^ (-(1 : ℝ))) (torusParabolicSize (w' - w) ^ (-θ))
          (torusParabolicSize (y' - w) ^ (-θ)) (torusParabolicSize (y - w') ^ (-θ))
          (torusParabolicSize (y - y') ^ (-θ))) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
        rw [i2Psi2Maj4_eq hθ, rpow_two_theta_i2 hmax]
        unfold hairerI2Psi2Kernel
        ring

/-- **Chaos `2`: pointwise domination of the second difference.** -/
theorem abs_i2Psi2DiffChaos2Two_le (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b : ℝ}, 0 < a → a ≤ 1 → 0 < b → b ≤ 1 → ∀ x y y' w w' : SpaceTime,
      0 < torusParabolicSize (y - w) → 0 < torusParabolicSize (y' - w') →
      0 < torusParabolicSize (w' - w) → 0 < torusParabolicSize (y' - w) →
      0 < torusParabolicSize (y - w') → 0 < torusParabolicSize (y - y') →
        |hairerI2Psi2Kernel N x y w * hairerI2Psi2Kernel N x y' w' *
            i2Psi2DiffChaos2Two N ρ ρ' a b y y' w w'| ≤
          C * (max a b) ^ (2 * θ) * i2Psi2Maj2 θ (hairerKernelTorus N) x y y' (w, w') := by
  obtain ⟨A, hA, h⟩ := i2Psi2CrossTwo_tables_bd N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨65536 * A ^ 4, by positivity, ?_⟩
  intro a b ha ha1 hb hb1 x y y' w w' p01 p23 p02 p03 p12 p13
  obtain ⟨hn, hf⟩ := h ha ha1 hb hb1
  have hμ : 0 ≤ (max a b) ^ θ := Real.rpow_nonneg (le_max_of_le_left ha.le) _
  have f01 := (hf (w - y) (by rwa [neg_sub])).2.1
  have f23 := (hf (w' - y') (by rwa [neg_sub])).2.2
  have f02 := (hf (w - w') (by rwa [neg_sub])).1
  have f03 := (hf (w - y') (by rwa [neg_sub])).1
  rw [neg_sub] at f01 f23 f02 f03
  have n12 := (hn (y - w') p12).1
  have n13 := (hn (y - y') p13).1
  have nq : ∀ u : SpaceTime, 0 ≤ torusParabolicSize u ^ (-θ) := fun u =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have key := abs_i2Psi2Dm_chaos2_le (T01 := i2Psi2Tab2Two N ρ ρ' a b (w - y))
    (T23 := i2Psi2Tab3Two N ρ ρ' a b (w' - y')) (T02 := i2Psi2Tab1Two N ρ ρ' a b (w - w'))
    (T03 := i2Psi2Tab1Two N ρ ρ' a b (w - y')) (T12 := i2Psi2Tab1Two N ρ ρ' a b (y - w'))
    (T13 := i2Psi2Tab1Two N ρ ρ' a b (y - y')) hμ (nq _) (nq _) (nq _) (nq _) (nq _) (nq _) f01 f23 f02
    f03 n12 n13
  rw [← i2Psi2DiffChaos2Two_eq] at key
  have hmax : 0 < max a b := lt_max_of_lt_left ha
  calc |hairerI2Psi2Kernel N x y w * hairerI2Psi2Kernel N x y' w' *
          i2Psi2DiffChaos2Two N ρ ρ' a b y y' w w'|
      = |hairerI2Psi2Kernel N x y w| * |hairerI2Psi2Kernel N x y' w'| *
          |i2Psi2DiffChaos2Two N ρ ρ' a b y y' w w'| := by rw [abs_mul, abs_mul]
    _ ≤ |hairerI2Psi2Kernel N x y w| * |hairerI2Psi2Kernel N x y' w'| *
          (65536 * A ^ 4 * ((max a b) ^ θ) ^ 2 * i2Psi2Mon2 (torusParabolicSize (y - w) ^ (-(1 : ℝ)))
          (torusParabolicSize (y' - w') ^ (-(1 : ℝ))) (torusParabolicSize (w' - w) ^ (-(1 : ℝ)))
          (torusParabolicSize (y' - w) ^ (-(1 : ℝ))) (torusParabolicSize (y - w') ^ (-(1 : ℝ)))
          (torusParabolicSize (y - y') ^ (-(1 : ℝ))) (torusParabolicSize (y - w) ^ (-θ))
          (torusParabolicSize (y' - w') ^ (-θ)) (torusParabolicSize (w' - w) ^ (-θ))
          (torusParabolicSize (y' - w) ^ (-θ)) (torusParabolicSize (y - w') ^ (-θ))
          (torusParabolicSize (y - y') ^ (-θ))) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
        rw [i2Psi2Maj2_eq hθ, rpow_two_theta_i2 hmax]
        unfold hairerI2Psi2Kernel
        ring

end RegularityStructures.Phi43

end
