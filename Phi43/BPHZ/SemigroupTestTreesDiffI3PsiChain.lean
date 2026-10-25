/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI3PsiDom
public import Phi43.BPHZ.TreeI3PsiCrossChainBound

/-!
# Global bounds for the chain pieces of the cross-mollifier difference diagram of `I(Ψ³)Ψ`

`i3PsiDiffPiece1Cross_bound_global`, `i3PsiDiffPiece3Cross_bound_global`: for `θ ∈ (0, 1/8]`,
`δ ∈ (0, 1/4]`, arbitrary `z, z'` (no smallness) and `D` bounding `s(w - v)` on the slab
`|w.1| ≤ |z.1| + 1`, `|v.1| ≤ |z'.1| + 1`, the chain pieces are absolutely integrable and
`|∫∫ δK δK D| ≤ C (max ε ε')^(2θ) D^δ (s(z - z')^(-(2θ+δ)) + s(z)^(-(2θ+δ)) + s(z')^(-(2θ+δ)))`,
uniformly in `ε, ε' ∈ (0, 1]`.  These are the global versions of `i3PsiDiffPiece1Cross_bound` and
`i3PsiDiffPiece3Cross_bound`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **The first chain piece of the difference diagram.** -/
theorem i3PsiDiffPiece1Cross_bound_global (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ z z' : SpaceTime, ∀ {D : ℝ}, 0 ≤ D →
        (∀ w v : SpaceTime, |w.1| ≤ |z.1| + 1 → |v.1| ≤ |z'.1| + 1 →
          torusParabolicSize (w - v) ≤ D) →
        0 < torusParabolicSize (z - z') → 0 < torusParabolicSize z →
        0 < torusParabolicSize z' →
        Integrable (Function.uncurry (i3PsiDiffPiece1Cross N ρ ρ' ε ε' z z')) (volume.prod volume) ∧
          |∫ w, ∫ v, i3PsiDiffPiece1Cross N ρ ρ' ε ε' z z' w v| ≤
            C * (max ε ε') ^ (2 * θ) * D ^ δ * (torusParabolicSize (z - z') ^ (-(2 * θ + δ)) +
              torusParabolicSize z ^ (-(2 * θ + δ)) + torusParabolicSize z' ^ (-(2 * θ + δ))) := by
  obtain ⟨B, hB, hKm, hKs, hK, hinc⟩ := hairerKernelTorus_diagram_data N
  obtain ⟨K1, hK1, hD⟩ := i3PsiDiff_piece_one_abs_le_cross N ρ ρ' hρ hρ' hθ (by linarith)
  obtain ⟨Ca, hCa, hCha⟩ := twoLevelLe_chainMajorant_of_eq (α := 2 * θ) (β := δ) (γ := 0)
    (η := 2 * θ + δ) (by linarith) le_rfl (by norm_num) hδ (by linarith) (by ring) (by linarith)
    (by linarith) (by linarith)
  obtain ⟨Cb, hCb, hChb⟩ := twoLevelLe_chainMajorant_of_eq (α := 0) (β := 2 * θ + δ) (γ := 0)
    (η := 2 * θ + δ) (by norm_num) le_rfl (by norm_num) (by linarith) (by linarith) (by ring)
    (by linarith) (by linarith) (by linarith)
  obtain ⟨Cc, hCc, hChc⟩ := twoLevelLe_chainMajorant_of_eq (α := 0) (β := δ) (γ := 2 * θ)
    (η := 2 * θ + δ) (by norm_num) (by linarith) (by linarith) hδ (by linarith) (by ring)
    (by linarith) (by linarith) (by linarith)
  refine ⟨16 * B ^ 2 * K1 * (Ca + Cb + Cc), by positivity, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 z z' D hD0 hDs hzz hz hz'
  have n3 : (0 : ℝ) ≤ D ^ δ := Real.rpow_nonneg hD0 _
  have hM : 0 < max ε ε' := lt_max_of_lt_left hε
  have hm2 : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg hM.le _
  set m2 : ℝ := (max ε ε') ^ (2 * θ) with hm2def
  set S : ℝ := torusParabolicSize (z - z') ^ (-(2 * θ + δ)) +
    torusParabolicSize z ^ (-(2 * θ + δ)) + torusParabolicSize z' ^ (-(2 * θ + δ)) with hS
  have TLa := hCha z z' z z' hzz hz hz' (Or.inl ⟨rfl, rfl⟩)
  have TLb := hChb z z' z z' hzz hz hz' (Or.inl ⟨rfl, rfl⟩)
  have TLc := hChc z z' z z' hzz hz hz' (Or.inl ⟨rfl, rfl⟩)
  have hc0 : 0 ≤ 16 * B ^ 2 * D ^ δ * K1 * m2 := by positivity
  have TL := ((TLa.add TLb).add TLc).const_mul hc0
  have hmeas : Measurable (fun p : SpaceTime × SpaceTime =>
      i3PsiDiffPiece1Cross N ρ ρ' ε ε' z z' p.1 p.2) := by
    unfold i3PsiDiffPiece1Cross i3PsiDiffD1Cross
    have h11 := measurable_hairerCrossCovarianceTwo N hρ hρ
    have h12 := measurable_hairerCrossCovarianceTwo N hρ hρ'
    have h21 := measurable_hairerCrossCovarianceTwo N hρ' hρ
    have h22 := measurable_hairerCrossCovarianceTwo N hρ' hρ'
    fun_prop
  obtain ⟨hint, hbd⟩ := TL.integrable_bound (F := i3PsiDiffPiece1Cross N ρ ρ' ε ε' z z')
    hmeas.aestronglyMeasurable (by
    filter_upwards [ae_ae_chain_pos z z' z z'] with w hw
    obtain ⟨⟨a, b, c⟩, hw2⟩ := hw
    filter_upwards [hw2] with v hv
    obtain ⟨⟨a', b', c'⟩, d'⟩ := hv
    have p1 : 0 < torusParabolicSize (w - z) := torusParabolicSize_sub_pos_symm a
    have p3 : 0 < torusParabolicSize (v - z') := torusParabolicSize_sub_pos_symm a'
    have hd := hD hε hε1 hε' hε'1 (w - z) (w - v) (v - z') p1 d' p3
    have e : |i3PsiDiffPiece1Cross N ρ ρ' ε ε' z z' w v| =
        |hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
          |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| *
          |i3PsiDiffD1Cross N ρ ρ' ε ε' (w - z) (w - v) (v - z')| := by
      unfold i3PsiDiffPiece1Cross
      rw [abs_mul, abs_mul]
    rw [e]
    have nK : 0 ≤ |hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
        |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have ca := abs_dK_dK_chain_flip_le_global_i3Psi (K := hairerKernelTorus N) (α := 2 * θ) (β₀ := 0) (β := δ)
      (γ := 0) (a := 1 + 2 * θ) (b := 2) (c := 1) hB hδ.le (by linarith) (by linarith) le_rfl (by norm_num) hD0 rfl (by norm_num) (by ring) (by norm_num) hK hKs hDs a b c a' b' c' d'
    have cb := abs_dK_dK_chain_flip_le_global_i3Psi (K := hairerKernelTorus N) (α := 0) (β₀ := 2 * θ)
      (β := 2 * θ + δ) (γ := 0) (a := 1) (b := 2 + 2 * θ) (c := 1) hB hδ.le le_rfl (by norm_num) le_rfl (by norm_num) hD0 (by norm_num) rfl (by ring) (by norm_num) hK hKs hDs
      a b c a' b' c' d'
    have cc := abs_dK_dK_chain_flip_le_global_i3Psi (K := hairerKernelTorus N) (α := 0) (β₀ := 0) (β := δ)
      (γ := 2 * θ) (a := 1) (b := 2) (c := 1 + 2 * θ) hB hδ.le le_rfl (by norm_num) (by linarith) (by linarith) hD0 (by norm_num) (by norm_num) (by ring) rfl hK hKs hDs a b c a' b' c' d'
    calc _ ≤ _ := mul_le_mul_of_nonneg_left hd nK
      _ = K1 * m2 * (|hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
            |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| *
            (torusParabolicSize (w - z) ^ (-(1 + 2 * θ)) * torusParabolicSize (w - v) ^ (-(2 : ℝ)) *
              torusParabolicSize (v - z') ^ (-(1 : ℝ))) +
          |hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
            |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| *
            (torusParabolicSize (w - z) ^ (-(1 : ℝ)) * torusParabolicSize (w - v) ^ (-(2 + 2 * θ)) *
              torusParabolicSize (v - z') ^ (-(1 : ℝ))) +
          |hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
            |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| *
            (torusParabolicSize (w - z) ^ (-(1 : ℝ)) * torusParabolicSize (w - v) ^ (-(2 : ℝ)) *
              torusParabolicSize (v - z') ^ (-(1 + 2 * θ)))) := by ring
      _ ≤ K1 * m2 * (16 * B ^ 2 * D ^ δ * i3PsiChainMajorant (2 * θ) δ 0 z z' z z' w v +
          16 * B ^ 2 * D ^ δ * i3PsiChainMajorant 0 (2 * θ + δ) 0 z z' z z' w v +
          16 * B ^ 2 * D ^ δ * i3PsiChainMajorant 0 δ (2 * θ) z z' z z' w v) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add ca cb) cc) (by positivity)
      _ = _ := by ring)
  refine ⟨hint, hbd.trans (le_of_eq ?_)⟩
  rw [hS]
  ring

/-- **The secondary chain piece of the difference diagram.** -/
theorem i3PsiDiffPiece3Cross_bound_global (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ z z' : SpaceTime, ∀ {D : ℝ}, 0 ≤ D →
        (∀ w v : SpaceTime, |w.1| ≤ |z.1| + 1 → |v.1| ≤ |z'.1| + 1 →
          torusParabolicSize (w - v) ≤ D) →
        0 < torusParabolicSize (z - z') → 0 < torusParabolicSize z →
        0 < torusParabolicSize z' →
        Integrable (Function.uncurry (i3PsiDiffPiece3Cross N ρ ρ' ε ε' z z')) (volume.prod volume) ∧
          |∫ w, ∫ v, i3PsiDiffPiece3Cross N ρ ρ' ε ε' z z' w v| ≤
            C * (max ε ε') ^ (2 * θ) * D ^ δ * (torusParabolicSize (z - z') ^ (-(2 * θ + δ)) +
              torusParabolicSize z ^ (-(2 * θ + δ)) + torusParabolicSize z' ^ (-(2 * θ + δ))) := by
  obtain ⟨B, hB, hKm, hKs, hK, hinc⟩ := hairerKernelTorus_diagram_data N
  obtain ⟨K1, hK1, hD⟩ := i3PsiDiff_piece_three_abs_le_cross N ρ ρ' hρ hρ' hθ (by linarith)
  obtain ⟨Ca, hCa, hCha⟩ := twoLevelLe_chainMajorant_of_eq (α := 2 * θ) (β := δ) (γ := 0)
    (η := 2 * θ + δ) (by linarith) le_rfl (by norm_num) hδ (by linarith) (by ring) (by linarith)
    (by linarith) (by linarith)
  obtain ⟨Cb, hCb, hChb⟩ := twoLevelLe_chainMajorant_of_eq (α := 0) (β := 2 * θ + δ) (γ := 0)
    (η := 2 * θ + δ) (by norm_num) le_rfl (by norm_num) (by linarith) (by linarith) (by ring)
    (by linarith) (by linarith) (by linarith)
  obtain ⟨Cc, hCc, hChc⟩ := twoLevelLe_chainMajorant_of_eq (α := 0) (β := δ) (γ := 2 * θ)
    (η := 2 * θ + δ) (by norm_num) (by linarith) (by linarith) hδ (by linarith) (by ring)
    (by linarith) (by linarith) (by linarith)
  refine ⟨4 * B ^ 2 * K1 * (Ca + Cb + Cc), by positivity, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 z z' D hD0 hDs hzz hz hz'
  have n3 : (0 : ℝ) ≤ D ^ δ := Real.rpow_nonneg hD0 _
  have hM : 0 < max ε ε' := lt_max_of_lt_left hε
  have hm2 : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg hM.le _
  set m2 : ℝ := (max ε ε') ^ (2 * θ) with hm2def
  set S : ℝ := torusParabolicSize (z - z') ^ (-(2 * θ + δ)) +
    torusParabolicSize z ^ (-(2 * θ + δ)) + torusParabolicSize z' ^ (-(2 * θ + δ)) with hS
  have TLa := hCha z z' z' z hzz hz hz' (Or.inr ⟨rfl, rfl⟩)
  have TLb := hChb z z' z' z hzz hz hz' (Or.inr ⟨rfl, rfl⟩)
  have TLc := hChc z z' z' z hzz hz hz' (Or.inr ⟨rfl, rfl⟩)
  have hc0 : 0 ≤ 4 * B ^ 2 * D ^ δ * K1 * m2 := by positivity
  have TL := ((TLa.add TLb).add TLc).const_mul hc0
  have hmeas : Measurable (fun p : SpaceTime × SpaceTime =>
      i3PsiDiffPiece3Cross N ρ ρ' ε ε' z z' p.1 p.2) := by
    unfold i3PsiDiffPiece3Cross i3PsiDiffD3Cross
    have h11 := measurable_hairerCrossCovarianceTwo N hρ hρ
    have h12 := measurable_hairerCrossCovarianceTwo N hρ hρ'
    have h21 := measurable_hairerCrossCovarianceTwo N hρ' hρ
    have h22 := measurable_hairerCrossCovarianceTwo N hρ' hρ'
    fun_prop
  obtain ⟨hint, hbd⟩ := TL.integrable_bound (F := i3PsiDiffPiece3Cross N ρ ρ' ε ε' z z')
    hmeas.aestronglyMeasurable (by
    filter_upwards [ae_ae_chain_pos z z' z' z] with w hw
    obtain ⟨⟨a, b, c⟩, hw2⟩ := hw
    filter_upwards [hw2] with v hv
    obtain ⟨⟨a', b', c'⟩, d'⟩ := hv
    have p2 : 0 < torusParabolicSize (w - z') := torusParabolicSize_sub_pos_symm c
    have hd := hD hε hε1 hε' hε'1 (w - v) (w - z') (z - v) d' p2 c'
    have e : |i3PsiDiffPiece3Cross N ρ ρ' ε ε' z z' w v| =
        |hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
          |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| *
          |i3PsiDiffD3Cross N ρ ρ' ε ε' (w - v) (w - z') (z - v)| := by
      unfold i3PsiDiffPiece3Cross
      rw [abs_mul, abs_mul]
    rw [e]
    have nK : 0 ≤ |hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
        |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have ca := abs_dK_dK_chain_flip_left_le_global_i3Psi (K := hairerKernelTorus N) (α := 0) (β₀ := 2 * θ)
      (β := 2 * θ + δ) (γ := 0) (a := 1) (b := 2 + 2 * θ) (c := 1) hB hδ.le le_rfl (by norm_num) le_rfl hD0 (by norm_num) rfl (by ring) (by norm_num) hK hKs hDs
      a b c a' b' c' d'
    have cb := abs_dK_dK_chain_flip_left_le_global_i3Psi (K := hairerKernelTorus N) (α := 2 * θ) (β₀ := 0)
      (β := δ) (γ := 0) (a := 1 + 2 * θ) (b := 2) (c := 1) hB hδ.le (by linarith) (by linarith) le_rfl hD0 rfl (by norm_num) (by norm_num) (by norm_num) hK hKs hDs a b c a' b' c' d'
    have cc := abs_dK_dK_chain_flip_left_le_global_i3Psi (K := hairerKernelTorus N) (α := 0) (β₀ := 0) (β := δ)
      (γ := 2 * θ) (a := 1) (b := 2) (c := 1 + 2 * θ) hB hδ.le le_rfl (by norm_num) (by linarith) hD0 (by norm_num) (by norm_num) (by ring) rfl hK hKs hDs a b c a' b' c' d'
    calc _ ≤ _ := mul_le_mul_of_nonneg_left hd nK
      _ = K1 * m2 * (|hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
            |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| *
            (torusParabolicSize (w - z') ^ (-(1 : ℝ)) * torusParabolicSize (w - v) ^ (-(2 + 2 * θ)) *
              torusParabolicSize (z - v) ^ (-(1 : ℝ))) +
          |hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
            |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| *
            (torusParabolicSize (w - z') ^ (-(1 + 2 * θ)) * torusParabolicSize (w - v) ^ (-(2 : ℝ)) *
              torusParabolicSize (z - v) ^ (-(1 : ℝ))) +
          |hairerKernelTorus N (z - w) - hairerKernelTorus N (-w)| *
            |hairerKernelTorus N (z' - v) - hairerKernelTorus N (-v)| *
            (torusParabolicSize (w - z') ^ (-(1 : ℝ)) * torusParabolicSize (w - v) ^ (-(2 : ℝ)) *
              torusParabolicSize (z - v) ^ (-(1 + 2 * θ)))) := by ring
      _ ≤ K1 * m2 * (4 * B ^ 2 * D ^ δ * i3PsiChainMajorant 0 (2 * θ + δ) 0 z z' z' z w v +
          4 * B ^ 2 * D ^ δ * i3PsiChainMajorant (2 * θ) δ 0 z z' z' z w v +
          4 * B ^ 2 * D ^ δ * i3PsiChainMajorant 0 δ (2 * θ) z z' z' z w v) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add ca cb) cc) (by positivity)
      _ = _ := by ring)
  refine ⟨hint, hbd.trans (le_of_eq ?_)⟩
  rw [hS]
  ring

end RegularityStructures.Phi43

end
