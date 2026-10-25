/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Commute.KRegular

/-!
# Linearity of `Λ ↦ K ∗ Λ` on regular distributions

For finitely many `KRegular` families `Λ_j` (at the same base point `x`), the pairing with the
shell `K_n(z - ·)` and hence `kConv N` is linear:
`kConv N (∑_j c_j Λ_j) = ∑_j c_j kConv N Λ_j` (`kConv_finset_sum`), used for the basis expansion of
`Γ_{xy} e_i` in [Hai14, Lemma 5.16]. The only extra input beyond `tendsto_and_abs_pairing_scaledShell_centre_le`
is the integrability of `Λ_s K_n(z - ·)` for `0 < s ≤ 1` (`KRegular.integrable_mul_annShell`).
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace RegularityStructures

namespace KRegular

variable {Λ : ℝ → ParabolicSpace → ℝ} {x : ParabolicSpace}

theorem integrable_mul_annShell (hΛ : KRegular Λ x) (N n : ℕ) (z : ParabolicSpace) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun w => Λ s w * annShell N n (z - w)) := by
  obtain ⟨h1, h2, α, C, A, hA, hC, hloc⟩ := hΛ
  have hLD : parabolicSemigroup.LocalData Λ x α A C :=
    ⟨h1, h2, hC, fun a ha => (hA a ha).2, hloc⟩
  have hg := contDiff_scaledShell (contDiff_annKernel0 N) n
  set q : ℝ := (2 : ℝ)⁻¹ ^ n with hq
  have hq0 : 0 < q := by positivity
  set d : ℝ := parabolicNorm (z - x) with hd
  have hc1 : Continuous fun w => annShell N n (z - w) :=
    hg.continuous.comp (continuous_const.sub continuous_id)
  have hsupp : ∀ w, q < parabolicNorm (w - z) → annShell N n (z - w) = 0 := fun w hw => by
    refine scaledShell_eq_zero (fun _ hz => annKernel0_eq_zero N hz) ?_
    rwa [parabolicNorm_sub_comm]
  have hcs : HasCompactSupport fun w => annShell N n (z - w) :=
    hasCompactSupport_of_eq_zero (c := q) hq0 z hsupp
  exact hLD.integrable_mul hs (lam := q + d) ⟨hc1.measurable,
    hc1.integrable_of_hasCompactSupport hcs, fun w hw => by
      have h3 : parabolicNorm (w - x) ≤ parabolicNorm (w - z) + parabolicNorm (z - x) := by
        simpa using parabolicNorm_add_le (w - z) (z - x)
      refine hsupp w ?_
      change q + d < parabolicNorm (w - x) at hw
      linarith⟩

end KRegular

variable {J : Type*} {x : ParabolicSpace}

/-- Linearity of the pairing with a shell on finitely many regular families. -/
theorem pairing_annShell_finset_sum (s : Finset J) (Λj : J → ℝ → ParabolicSpace → ℝ) (c : J → ℝ)
    (hΛ : ∀ j ∈ s, KRegular (Λj j) x) (N n : ℕ) (z : ParabolicSpace) :
    parabolicSemigroup.pairing (fun t w => ∑ j ∈ s, c j * Λj j t w)
        (fun w => annShell N n (z - w)) =
      ∑ j ∈ s, c j * parabolicSemigroup.pairing (Λj j) (fun w => annShell N n (z - w)) := by
  have hT : ∀ j ∈ s, Tendsto (fun r => ∫ w, Λj j r w * annShell N n (z - w))
      (𝓝[>] 0) (𝓝 (parabolicSemigroup.pairing (Λj j) (fun w => annShell N n (z - w)))) := by
    intro j hj
    obtain ⟨h1, h2, α, C, A, hA, hC, hloc⟩ := hΛ j hj
    exact (tendsto_and_abs_pairing_scaledShell_centre_le h1 h2 (contDiff_annKernel0 N)
      (fun _ hz => annKernel0_eq_zero N hz) (y := z) (A := A)
      (fun a ha => ⟨by linarith [(hA a ha).1], (hA a ha).2⟩) hC hloc n).1
  refine parabolicSemigroup.pairing_eq_of_tendsto ((tendsto_finsetSum s fun j hj =>
    (hT j hj).const_mul (c j)).congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with r hr
  have hr' : r ∈ Ioc (0 : ℝ) 1 := ⟨hr.1, hr.2.le⟩
  simp only [← integral_const_mul]
  rw [← integral_finsetSum]
  · refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · intro j hj
    exact ((hΛ j hj).integrable_mul_annShell N n z hr').const_mul (c j)

/-- **Linearity of `kConv`** on finitely many regular families. -/
theorem kConv_finset_sum (s : Finset J) (Λj : J → ℝ → ParabolicSpace → ℝ) (c : J → ℝ)
    (hΛ : ∀ j ∈ s, KRegular (Λj j) x) (N : ℕ) (z : ParabolicSpace) :
    kConv N (fun t w => ∑ j ∈ s, c j * Λj j t w) z = ∑ j ∈ s, c j * kConv N (Λj j) z := by
  unfold kConv
  simp only [pairing_annShell_finset_sum s Λj c hΛ N _ z]
  rw [Summable.tsum_finsetSum]
  · exact Finset.sum_congr rfl fun j _ => tsum_mul_left
  · intro j hj
    exact ((hΛ j hj).summable_pairing N z).mul_left (c j)

end RegularityStructures

end
