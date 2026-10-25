/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiCrossChain

/-!
# The principal piece of the cross-mollifier difference diagram of `I(Ψ³)Ψ`

`δK(z,w) δK(z',v) D2(w - v, z - z')` with `D2 = Q_{e₁e₂}(x₁)³ Q_{e₁e₂}(x₂)` differenced over the
two scales/mollifiers is absolutely integrable and bounded by
`C (max ε ε')^(2θ) (s(z - z')^(-1) s(z')^(1-δ-2θ) + s(z - z')^(-(1+2θ)) s(z')^(1-δ))`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **The principal piece of the difference diagram.** -/
theorem i3PsiDiffPiece2Cross_bound (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ z z' : SpaceTime, 0 < torusParabolicSize (z - z') → torusParabolicSize z ≤ 1 →
        torusParabolicSize z' ≤ 1 →
        Integrable (Function.uncurry (i3PsiDiffPiece2Cross N ρ ρ' ε ε' z z')) (volume.prod volume) ∧
          |∫ w, ∫ v, i3PsiDiffPiece2Cross N ρ ρ' ε ε' z z' w v| ≤
            C * (max ε ε') ^ (2 * θ) *
              (torusParabolicSize (z - z') ^ (-(1 : ℝ)) * torusParabolicSize z' ^ (1 - δ - 2 * θ) +
                torusParabolicSize (z - z') ^ (-(1 + 2 * θ)) * torusParabolicSize z' ^ (1 - δ)) := by
  obtain ⟨B, hB, hKm, hKs, hK, hinc⟩ := hairerKernelTorus_diagram_data N
  obtain ⟨K2, hK2, hD⟩ := i3PsiDiff_piece_two_abs_le_cross N ρ ρ' hρ hρ' hθ (by linarith)
  obtain ⟨Ca, hCa, hPa⟩ := twoLevelLe_principalMajorant (θ := 1 - δ - 2 * θ) (τ := 2 * θ)
    (by linarith) (by linarith) (by linarith)
  obtain ⟨Cb, hCb, hPb⟩ := twoLevelLe_principalMajorant (θ := 1 - δ) (τ := 0)
    (by linarith) le_rfl (by linarith)
  refine ⟨12 * B ^ 2 * K2 * (Ca + Cb), by positivity, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 z z' hzz hz1 hz1'
  have hM : 0 < max ε ε' := lt_max_of_lt_left hε
  have hm2 : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg hM.le _
  set m2 : ℝ := (max ε ε') ^ (2 * θ) with hm2def
  set X : ℝ := torusParabolicSize (z - z') ^ (-(1 : ℝ)) * torusParabolicSize z' ^ (1 - δ - 2 * θ)
    with hX
  set Y : ℝ := torusParabolicSize (z - z') ^ (-(1 + 2 * θ)) * torusParabolicSize z' ^ (1 - δ)
    with hY
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have hY0 : 0 ≤ Y := mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have TLa := hPa z z' hz1 hz1'
  have TLb := hPb z z' hz1 hz1'
  have hca : 0 ≤ 12 * B ^ 2 * K2 * m2 * X := by positivity
  have hcb : 0 ≤ 12 * B ^ 2 * K2 * m2 * Y := by positivity
  have TL := (TLa.const_mul hca).add (TLb.const_mul hcb)
  have hmeas : Measurable (fun p : SpaceTime × SpaceTime =>
      i3PsiDiffPiece2Cross N ρ ρ' ε ε' z z' p.1 p.2) := by
    unfold i3PsiDiffPiece2Cross i3PsiDiffD2Cross
    have h11 := measurable_hairerCrossCovarianceTwo N hρ hρ
    have h12 := measurable_hairerCrossCovarianceTwo N hρ hρ'
    have h21 := measurable_hairerCrossCovarianceTwo N hρ' hρ
    have h22 := measurable_hairerCrossCovarianceTwo N hρ' hρ'
    fun_prop
  obtain ⟨hint, hbd⟩ := TL.integrable_bound (F := i3PsiDiffPiece2Cross N ρ ρ' ε ε' z z')
    hmeas.aestronglyMeasurable (by
    filter_upwards [ae_ae_chain_pos z z' z z'] with w hw
    obtain ⟨⟨a, b, c⟩, hw2⟩ := hw
    filter_upwards [hw2] with v hv
    obtain ⟨⟨a', b', c'⟩, d'⟩ := hv
    have hd := hD hε hε1 hε' hε'1 (w - v) (z - z') d' hzz
    have e : |i3PsiDiffPiece2Cross N ρ ρ' ε ε' z z' w v| =
        |hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
          |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| *
          |i3PsiDiffD2Cross N ρ ρ' ε ε' (w - v) (z - z')| := by
      unfold i3PsiDiffPiece2Cross
      rw [abs_mul, abs_mul]
    rw [e]
    have nK : 0 ≤ |hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
        |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have pa := abs_dK_dK_principal_le (K := hairerKernelTorus N) (θ := 1 - δ - 2 * θ) (τ := 2 * θ)
      (w := w) (v := v) hB (by linarith) (by linarith) hK hinc hKs hz1 a b a' b'
    have pb := abs_dK_dK_principal_le (K := hairerKernelTorus N) (θ := 1 - δ) (τ := 0)
      (w := w) (v := v) hB (by linarith) (by linarith) hK hinc hKs hz1 a b a' b'
    rw [show (3 : ℝ) + 0 = 3 by norm_num] at pb
    calc _ ≤ _ := mul_le_mul_of_nonneg_left hd nK
      _ = K2 * m2 * (|hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
            |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| *
            torusParabolicSize (w - v) ^ (-(3 + 2 * θ)) * torusParabolicSize (z - z') ^ (-(1 : ℝ)) +
          |hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
            |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| *
            torusParabolicSize (w - v) ^ (-(3 : ℝ)) *
              torusParabolicSize (z - z') ^ (-(1 + 2 * θ))) := by ring
      _ ≤ K2 * m2 * ((12 * B ^ 2 * torusParabolicSize z' ^ (1 - δ - 2 * θ) *
            i3PsiPrincipalMajorant (1 - δ - 2 * θ) (2 * θ) z z' w v) *
              torusParabolicSize (z - z') ^ (-(1 : ℝ)) +
          (12 * B ^ 2 * torusParabolicSize z' ^ (1 - δ) *
            i3PsiPrincipalMajorant (1 - δ) 0 z z' w v) *
              torusParabolicSize (z - z') ^ (-(1 + 2 * θ))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
        · exact mul_le_mul_of_nonneg_right pa (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        · exact mul_le_mul_of_nonneg_right pb (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      _ = _ := by rw [hX, hY]; ring)
  refine ⟨hint, hbd.trans ?_⟩
  have hsum : 0 ≤ Ca + Cb := by linarith
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 12 * B ^ 2) hK2) hm2)
    (mul_nonneg hCa hY0), mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 12 * B ^ 2)
    hK2) hm2) (mul_nonneg hCb hX0)]

end RegularityStructures.Phi43

end
