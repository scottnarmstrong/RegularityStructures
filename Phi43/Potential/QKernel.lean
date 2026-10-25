/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.HeatEq
public import RegularityStructures.Analysis.Heat.Causal.Support

/-!
# The kernel `Q = (∂_t - Δ) R` of bounded lag

For the smooth causal remainder `R = annRemainderC N` of the heat kernel `G = K + R` (`K` the sum of
the causal shells, supported in the unit parabolic ball), the function
`potQ N = (∂_t - Δ) R` is smooth, vanishes for `t ≤ 0` and, by the heat equation for `G` off the
origin, vanishes outside the closed unit parabolic ball (`potQ_eq_zero_of_one_lt`).  Hence `potQ N`
and all its derivatives are supported in `{0 ≤ t ≤ 1} × [-1, 1]³`: `Q` has lag at most `1`.
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Potential

open RegularityStructures.Inhomogeneity

/-- The kernel `Q = (∂_t - Δ) R` of the smooth causal remainder `R = annRemainderC N`. -/
def potQ (N : ℕ) (z : ParabolicSpace) : ℝ :=
  ddv 0 (annRemainderC N) z - ∑ j : Fin 3, ddv j.succ (ddv j.succ (annRemainderC N)) z

end RegularityStructures.Potential

end

public section

open Filter Topology Set

namespace RegularityStructures.Potential

open RegularityStructures.Inhomogeneity

theorem contDiff_ddv {F : ParabolicSpace → ℝ} (hF : ContDiff ℝ ∞ F) (j : Fin 4) :
    ContDiff ℝ ∞ (ddv j F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_ddA {F : ParabolicSpace → ℝ} (hF : ContDiff ℝ ∞ F) :
    ∀ l : List (Fin 4), ContDiff ℝ ∞ (ddA l F)
  | [] => hF
  | j :: l => contDiff_ddv (contDiff_ddA hF l) j

theorem contDiff_potQ (N : ℕ) : ContDiff ℝ ∞ (potQ N) := by
  have hR := contDiff_annRemainderC N
  unfold potQ
  refine (contDiff_ddv hR 0).sub (ContDiff.sum fun j _ => ?_)
  exact contDiff_ddv (contDiff_ddv hR _) _

/-- A function vanishing near `z` has vanishing derivative at `z`. -/
theorem ddv_eq_zero_of_eventuallyEq {F : ParabolicSpace → ℝ} {z : ParabolicSpace}
    (h : F =ᶠ[𝓝 z] fun _ => (0 : ℝ)) (j : Fin 4) : ddv j F z = 0 := by
  simp [ddv, h.fderiv_eq]

theorem ddv_eventuallyEq {F G : ParabolicSpace → ℝ} {z : ParabolicSpace} (h : F =ᶠ[𝓝 z] G)
    (j : Fin 4) : ddv j F =ᶠ[𝓝 z] ddv j G := by
  filter_upwards [h.eventuallyEq_nhds] with w hw
  simp only [ddv, hw.fderiv_eq]

/-- A smooth function vanishing on `{t ≤ 0}` has its derivatives vanishing there. -/
theorem ddv_eq_zero_of_nonpos {F : ParabolicSpace → ℝ} (hF : ContDiff ℝ ∞ F)
    (h0 : ∀ z : ParabolicSpace, z.1 ≤ 0 → F z = 0) (j : Fin 4) {z : ParabolicSpace}
    (hz : z.1 ≤ 0) : ddv j F z = 0 := by
  have hopen : IsOpen {w : ParabolicSpace | w.1 < 0} := isOpen_lt continuous_fst continuous_const
  have hlt : ∀ w : ParabolicSpace, w.1 < 0 → ddv j F w = 0 := fun w hw =>
    ddv_eq_zero_of_eventuallyEq (Filter.eventuallyEq_of_mem (hopen.mem_nhds hw)
      fun v hv => h0 v hv.le) j
  have hclosed : IsClosed {w : ParabolicSpace | ddv j F w = 0} :=
    isClosed_eq (contDiff_ddv hF j).continuous continuous_const
  have hcl : closure {w : ParabolicSpace | w.1 < 0} = {w : ParabolicSpace | w.1 ≤ 0} := by
    have := (isOpenMap_fst (X := ℝ) (Y := Fin 3 → ℝ)).preimage_closure_eq_closure_preimage
      continuous_fst (Set.Iio (0 : ℝ))
    rw [closure_Iio] at this
    exact this.symm
  have : z ∈ closure {w : ParabolicSpace | w.1 < 0} := by rw [hcl]; exact hz
  exact (hclosed.closure_subset_iff.2 (fun w hw => hlt w hw)) this

theorem ddA_eq_zero_of_nonpos {F : ParabolicSpace → ℝ} (hF : ContDiff ℝ ∞ F)
    (h0 : ∀ z : ParabolicSpace, z.1 ≤ 0 → F z = 0) :
    ∀ (l : List (Fin 4)) {z : ParabolicSpace}, z.1 ≤ 0 → ddA l F z = 0
  | [], _, hz => h0 _ hz
  | j :: l, _, hz =>
    ddv_eq_zero_of_nonpos (contDiff_ddA hF l) (fun _ hw => ddA_eq_zero_of_nonpos hF h0 l hw) j hz

theorem potQ_eq_zero_of_nonpos (N : ℕ) {z : ParabolicSpace} (hz : z.1 ≤ 0) : potQ N z = 0 := by
  have hR := contDiff_annRemainderC N
  have h0 : ∀ w : ParabolicSpace, w.1 ≤ 0 → annRemainderC N w = 0 :=
    fun _ hw => annRemainderC_eq_zero_of_nonpos N hw
  have := ddA_eq_zero_of_nonpos hR h0 [0] hz
  have h2 := fun j : Fin 3 => ddA_eq_zero_of_nonpos hR h0 [j.succ, j.succ] hz
  unfold potQ
  simp only [ddA] at this h2
  simp [this, h2]

theorem annRemainderC_eq_heatKernelR4 (N : ℕ) {z : ParabolicSpace} (hz : 1 < parabolicNorm z) :
    annRemainderC N z = heatKernelR4 z := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    norm_num [parabolicNorm_zero] at hz
  have h := heatKernelR4_eq_tsum_annShellC (N := N) hz0
  have hs : ∑' n : ℕ, annShellC N n z = 0 := by
    refine (tsum_congr fun n => annShellC_eq_zero (N := N) (n := n) ?_).trans tsum_zero
    exact lt_of_le_of_lt (pow_le_one₀ (by norm_num) (by norm_num)) hz
  rw [h, hs, zero_add]

theorem annRemainderC_eventuallyEq_heatKernelR4 (N : ℕ) {z : ParabolicSpace}
    (hz : 1 < parabolicNorm z) : annRemainderC N =ᶠ[𝓝 z] heatKernelR4 := by
  have ho : IsOpen {w : ParabolicSpace | 1 < parabolicNorm w} :=
    isOpen_lt continuous_const continuous_parabolicNorm
  filter_upwards [ho.mem_nhds hz] with w hw
  exact annRemainderC_eq_heatKernelR4 N hw

theorem potQ_eq_zero_of_one_lt (N : ℕ) {z : ParabolicSpace} (hz : 1 < parabolicNorm z) :
    potQ N z = 0 := by
  by_cases ht : z.1 ≤ 0
  · exact potQ_eq_zero_of_nonpos N ht
  · have ht' : 0 < z.1 := not_le.1 ht
    have hev := annRemainderC_eventuallyEq_heatKernelR4 N hz
    have e0 : ddv 0 (annRemainderC N) z = ddv 0 heatKernelR4 z := by
      simp only [ddv, hev.fderiv_eq]
    have e1 : ∀ j : Fin 3, ddv j.succ (ddv j.succ (annRemainderC N)) z =
        ddv j.succ (ddv j.succ heatKernelR4) z := fun j => by
      simp only [ddv, (ddv_eventuallyEq hev j.succ).fderiv_eq]
    unfold potQ
    rw [e0, Finset.sum_congr rfl fun j _ => e1 j]
    exact heatEq_heatKernelR4 ht'

theorem one_lt_parabolicNorm_of_not_mem_closedBall {z : ParabolicSpace}
    (h : z ∉ Metric.closedBall (0 : ParabolicSpace) 1) : 1 < parabolicNorm z := by
  rw [mem_closedBall_zero_iff, not_le, Prod.norm_def, lt_max_iff] at h
  have h1 : 0 ≤ ∑ i, |z.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 := Real.sqrt_nonneg |z.1|
  unfold parabolicNorm
  rcases h with h | h
  · have : 1 < |z.1| := by simpa using h
    have : 1 < Real.sqrt |z.1| := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt zero_le_one this
    linarith
  · have : ∃ i, 1 < |z.2 i| := by
      by_contra hc
      push Not at hc
      exact absurd ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simpa using hc i)
        (not_le.2 h)
    obtain ⟨i, hi⟩ := this
    have := Finset.single_le_sum (f := fun j => |z.2 j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
    linarith

theorem ddA_potQ_eventuallyEq_zero (N : ℕ) (l : List (Fin 4)) {z : ParabolicSpace}
    (hz : 1 < parabolicNorm z) : ddA l (potQ N) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
  have ho : IsOpen {w : ParabolicSpace | 1 < parabolicNorm w} :=
    isOpen_lt continuous_const continuous_parabolicNorm
  induction l with
  | nil => filter_upwards [ho.mem_nhds hz] with w hw using potQ_eq_zero_of_one_lt N hw
  | cons j l ih =>
    refine (ddv_eventuallyEq ih j).trans (Eventually.of_forall fun w => ?_)
    simp [ddv]

theorem ddA_potQ_eq_zero_of_one_lt (N : ℕ) (l : List (Fin 4)) {z : ParabolicSpace}
    (hz : 1 < parabolicNorm z) : ddA l (potQ N) z = 0 :=
  (ddA_potQ_eventuallyEq_zero N l hz).self_of_nhds

theorem hasCompactSupport_ddA_potQ (N : ℕ) (l : List (Fin 4)) :
    HasCompactSupport (ddA l (potQ N)) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ParabolicSpace) 1) fun _ hx =>
    ddA_potQ_eq_zero_of_one_lt N l (one_lt_parabolicNorm_of_not_mem_closedBall hx)

end RegularityStructures.Potential

end
