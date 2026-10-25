/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2ChaosOneIdentity

/-!
# The chaos-`1` identity for a pair of kernels

For two kernels `J_a`, `J_b` with covariances `Q_aa = J_a ⋆ J_a`, `Q_bb = J_b ⋆ J_b`,
`Q_ab(x) = ∫ J_a(x + w) J_b(w) dw`, `Q_ba(x) = ∫ J_b(x + w) J_a(w) dw` and constants `c_a`, `c_b`,
the chaos-`1` part of the covariance `E[F_a(z) F_b(z')]` of the fields of `I(Ψ³)Ψ²` together with
the counterterm cross terms equals
`36 ∫ D^a_z D^b_{z'} dy`, `D^a_z = smear J_a (ρ^a_z) - (c_a/2) J_a(z - ·)`.
For the second difference (the four pairs `(a,a)`, `(a,b)`, `(b,a)`, `(b,b)`) this is
`36 ∫ (D^a_z - D^b_z)(D^a_{z'} - D^b_{z'}) dy` by bilinearity (`integral_sub_mul_sub_eq`).
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

/-- The chaos-`1` kernel `36 c₀₁² c₀₂ c₂₃²` with the entries `Q_aa(w - z)`, `Q_bb(v - z')`,
`Q_ab(w - v)`. -/
def i3Psi2Chaos1Gen (Qaa Qbb Qab : SpaceTime → ℝ) (z z' w v : SpaceTime) : ℝ :=
  i3Psi2Kernel1 (Qaa (w - z)) (Qbb (v - z')) (Qab (w - v))

/-- The chaos-`1` part of `E[F_a(z) F_b(z')]` together with the counterterm cross terms. -/
def i3Psi2Chaos1TotalPair (K Qaa Qab Qba Qbb : SpaceTime → ℝ) (ca cb : ℝ) (z z' : SpaceTime) : ℝ :=
  i3Psi2Double K (i3Psi2Chaos1Gen Qaa Qbb Qab) z z' -
    3 * cb * (∫ w, i3Psi2dK K z w * (6 * Qaa (w - z) ^ 2 * Qab (w - z'))) -
    3 * ca * (∫ w, i3Psi2dK K z' w * (6 * Qbb (w - z') ^ 2 * Qba (w - z))) +
    9 * ca * cb * Qab (z - z')

/-- The function `D^a_z(y) = smear J_a (ρ^a_z) (y) - (c_a/2) J_a(z - y)`. -/
def i3Psi2D (K Q J : SpaceTime → ℝ) (c : ℝ) (z y : SpaceTime) : ℝ :=
  i3Psi2Smear J (i3Psi2Rho K Q z) y - c / 2 * J (z - y)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

/-- `∫ J₁(a - y) J₂(b - y) dy = Q(a - b)` for `Q(x) = ∫ J₁(x + w) J₂(w) dw`. -/
theorem integral_J_mul_J_pair {J₁ J₂ Q : SpaceTime → ℝ}
    (hQ : ∀ x, Q x = ∫ w, J₁ (x + w) * J₂ w) (a b : SpaceTime) :
    ∫ y, J₁ (a - y) * J₂ (b - y) = Q (a - b) := by
  have h := integral_comp_sub_left_spaceTime (fun y => J₁ (a - y) * J₂ (b - y)) b
  rw [← h, hQ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have e1 : a - (b - w) = a - b + w := by abel
  have e2 : b - (b - w) = w := by abel
  simp only [e1, e2]

/-- `Q_ba(x) = Q_ab(-x)`. -/
theorem Q_swap_of_hQJ {Ja Jb Qab Qba : SpaceTime → ℝ}
    (hQab : ∀ x, Qab x = ∫ w, Ja (x + w) * Jb w) (hQba : ∀ x, Qba x = ∫ w, Jb (x + w) * Ja w)
    (x : SpaceTime) : Qba x = Qab (-x) := by
  rw [hQba, hQab]
  have h := integral_add_right_eq_self (μ := (volume : Measure SpaceTime))
    (fun w => Ja (-x + w) * Jb w) x
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have e : -x + (w + x) = w := by abel
  show Jb (x + w) * Ja w = Ja (-x + (w + x)) * Jb (w + x)
  rw [e, add_comm x w, mul_comm]

/-- `∫ smear J_s h (y) J_e(p - y) dy = ∫ h(w) Q(w - p) dw` for `Q(x) = ∫ J_s(x + u) J_e(u) du`. -/
theorem integral_smear_mul_J_pair {Js Je Q h : SpaceTime → ℝ} {M : ℝ}
    (hJeb : ∀ x, |Je x| ≤ M) (hJsi : Integrable Js) (hJei : Integrable Je)
    (hQ : ∀ x, Q x = ∫ w, Js (x + w) * Je w) (hh : Integrable h) (p : SpaceTime) :
    ∫ y, i3Psi2Smear Js h y * Je (p - y) = ∫ w, h w * Q (w - p) := by
  rw [integral_smear_mul hJsi hh (integrable_comp_sub_left_spaceTime hJei p) (fun y => hJeb _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  beta_reduce
  rw [integral_J_mul_J_pair hQ]

/-- `∫ smear J_a h₁ · smear J_b h₂ = ∫ h₁(w) ∫ h₂(w') Q_ab(w - w') dw' dw`. -/
theorem integral_smear_mul_smear_pair {Ja Jb Qab Qba h₁ h₂ : SpaceTime → ℝ} {Ma Mb : ℝ}
    (hJbm : Measurable Jb) (hJab : ∀ x, |Ja x| ≤ Ma) (hJbb : ∀ x, |Jb x| ≤ Mb)
    (hJai : Integrable Ja) (hJbi : Integrable Jb)
    (hQab : ∀ x, Qab x = ∫ w, Ja (x + w) * Jb w) (hQba : ∀ x, Qba x = ∫ w, Jb (x + w) * Ja w)
    (hh₁ : Integrable h₁) (hh₂ : Integrable h₂) :
    ∫ y, i3Psi2Smear Ja h₁ y * i3Psi2Smear Jb h₂ y =
      ∫ w, h₁ w * ∫ w', h₂ w' * Qab (w - w') := by
  rw [integral_smear_mul hJai hh₁ (integrable_i3Psi2Smear hh₂ hJbi)
    (fun y => abs_i3Psi2Smear_le hJbm hJbb hh₂ y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  beta_reduce
  congr 1
  have h1 := integral_smear_mul_J_pair hJab hJbi hJai hQba hh₂ w
  calc ∫ y, Ja (w - y) * i3Psi2Smear Jb h₂ y = ∫ y, i3Psi2Smear Jb h₂ y * Ja (w - y) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        beta_reduce; ring
    _ = ∫ w', h₂ w' * Qba (w' - w) := h1
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun w' => ?_)
        beta_reduce
        rw [Q_swap_of_hQJ hQab hQba, neg_sub]

end RegularityStructures

end
