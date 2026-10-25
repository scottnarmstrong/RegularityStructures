/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.Main
public import RegularityStructures.Abstract.Integration.Theorem512.ReconId

/-!
# Hairer's Theorem 5.12, (5.17): `R 𝒦_γ f = K ∗ Rf`

`Model.reconstruct_kGamma`: for `f ∈ D^γ` with values in `V` (a `SchauderSetting`, joint
measurability of `(x, z) ↦ (Q_t Π_x e_i)(z)`, the non-integrality conditions, and the model bound
`PiBoundOn (γ + 2)`), the reconstruction of `𝒦_γ f ∈ D^{γ+2}` is the `Q`-family
`t ↦ Q_t (K ∗ Rf)` (zero for `t ≤ 0`).  By `Model.eq_reconstruct` at level `γ + 2` it suffices
that `|Q_t(K ∗ Rf)(x) − Q_t Π_x 𝒦_γ f(x)(x)| ≲ t^{(γ+2)/4}`; by `apply_kConv_reconstruct_sub_regPi`
this is `|Q_t g_x (x)|` for `g_x = K ∗ (Rf − Π_x f(x))` minus its Taylor polynomial, and
`|g_x(w)| ≲ ‖w − x‖^{γ+2}` (`exists_abs_kConv_sub_taylor_le`), whence the kernel moment bound
gives the claim.

Here `K = ∑_n K_n` with `K_n = annShell N n` is the singular part of the heat kernel
`G`, the remainder `G - K` being smooth; `K` depends on `N`, and (5.17) is stated for this `K`,
not for `G` (the smooth remainder acts on `Rf` classically).

Source: [Hai14, Theorem 5.12, (5.17)].
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

theorem abs_apply_le_of_bound {g : ParabolicSpace → ℝ} {B r : ℝ} (hB : 0 ≤ B) (hr : 0 ≤ r)
    {x : ParabolicSpace} (hg : ∀ w, |g w| ≤ B * parabolicSemigroup.scaleDist w x ^ r) {t : ℝ}
    (ht : 0 < t) :
    |parabolicSemigroup.apply t g x| ≤
      B * parabolicSemigroup.momentConst r * t ^ (r / parabolicSemigroup.order) := by
  unfold RegularisingSemigroup.apply
  calc |∫ w, parabolicSemigroup.kernel t x w * g w|
      ≤ ∫ w, |parabolicSemigroup.kernel t x w * g w| := abs_integral_le_integral_abs
    _ ≤ ∫ w, B * (|parabolicSemigroup.kernel t x w| * parabolicSemigroup.scaleDist w x ^ r) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => abs_nonneg _)
          ((parabolicSemigroup.integrable_moment ht hr x).const_mul B)
          (Filter.Eventually.of_forall fun w => ?_)
        show |parabolicSemigroup.kernel t x w * g w| ≤ _
        rw [abs_mul]
        calc |parabolicSemigroup.kernel t x w| * |g w|
            ≤ |parabolicSemigroup.kernel t x w| * (B * parabolicSemigroup.scaleDist w x ^ r) :=
              mul_le_mul_of_nonneg_left (hg w) (abs_nonneg _)
          _ = _ := by ring
    _ = B * ∫ w, |parabolicSemigroup.kernel t x w| * parabolicSemigroup.scaleDist w x ^ r :=
        integral_const_mul _ _
    _ ≤ B * (parabolicSemigroup.momentConst r * t ^ (r / parabolicSemigroup.order)) :=
        mul_le_mul_of_nonneg_left (parabolicSemigroup.moment_le ht hr x) hB
    _ = _ := by ring

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {N : ℕ} {γ CPi CGam CI : ℝ} {P : PolynomialSector 𝒯 N'}
  {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}

theorem polyBounded_kConv_reconstruct (S : SchauderSetting M N γ P I V CPi CGam CI)
    {f : ParabolicSpace → ι → ℝ} {Cf : ℝ} (hf : f ∈ M.modelledDistributions γ)
    (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf) :
    PolyBounded (kConv N (M.reconstruct f)) := by
  have hK0 := kRegular_reconstructSubAt S.pos S.deg_gt S.piBound S.piBound_nonneg hf hfb hCf 0
  have hKi : ∀ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
      PolyBounded (kConv N (fun t w => M.regPi 0 (Pi.single i 1) t w)) := fun i hi =>
    (M.kRegular_regPi_single S.deg_gt S.piBound S.gammaBound S.piBound_nonneg
      (Finset.mem_filter.1 hi).2 0).polyBounded_kConv N
  have h := (hK0.polyBounded_kConv N).add
    (PolyBounded.finsetSum _ (fun i => f 0 i) _ hKi)
  have e : kConv N (M.reconstruct f) = fun w => kConv N (M.reconstructSubAt f 0) w +
      ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
        f 0 i * kConv N (fun t w => M.regPi 0 (Pi.single i 1) t w) w := by
    funext w
    exact kConv_reconstruct_eq S hf hfb hCf 0 w
  rw [e]
  exact h

/-- **Hairer's Theorem 5.12, (5.17)**: `R 𝒦_γ f = K ∗ Rf`, i.e. `(Q_t R 𝒦_γ f)(z) = Q_t (K ∗ Rf)(z)`
for `t > 0`. -/
theorem reconstruct_kGamma (S : SchauderSetting M N γ P I V CPi CGam CI)
    (hNN : N' ≤ N) (hn : SchauderNonIntegral 𝒯 γ N' P) (hnat : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) ≠ γ + 2)
    (hJ : M.IsJointMeasurable) {CPi' : ℝ} (hPi' : M.PiBoundOn (γ + 2) CPi' univ)
    (hCPi' : 0 ≤ CPi') {f : ParabolicSpace → ι → ℝ} {Cf : ℝ} (hf : f ∈ M.modelledDistributions γ)
    (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf) (hfV : ∀ x, f x ∈ V) :
    M.reconstruct (fun x => kGamma M N P I γ f x) =
      fun t z => if 0 < t then parabolicSemigroup.apply t (kConv N (M.reconstruct f)) z else 0 := by
  obtain ⟨c, hc0, hc⟩ := kGamma_mem_modelledDistributions S.pos S.deg_gt N P hNN hn
  obtain ⟨hmem, hbd⟩ := hc M I V S hJ hf hfb hCf hfV
  have hCf' : 0 ≤ c * max 1 CI * max 1 CPi * max CGam 1 * Cf :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc0 (le_trans zero_le_one (le_max_left _ _)))
      (le_trans zero_le_one (le_max_left _ _))) (le_trans zero_le_one (le_max_right _ _))) hCf
  -- the constant of the Taylor bound
  have hA : ∀ a ∈ insert γ (𝒯.degreesBelow γ), -2 < a ∧ a ≤ γ := by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact ⟨by linarith [S.pos], le_rfl⟩
    · obtain ⟨i, hi, rfl⟩ := (𝒯.mem_degreesBelow).1 ha
      exact ⟨S.deg_gt i hi, hi.le⟩
  obtain ⟨cT, hcT0, hcT⟩ := exists_abs_kConv_sub_taylor_le N hA (by linarith [S.pos]) hnat
  set CL : ℝ := (modelReconstructionConst 𝒯 parabolicSemigroup γ + Fintype.card ι) * CPi * Cf
    with hCL
  have hCL0 : 0 ≤ CL :=
    mul_nonneg (mul_nonneg (add_nonneg (modelReconstructionConst_nonneg 𝒯 _ S.pos.le)
      (Nat.cast_nonneg _)) S.piBound_nonneg) hCf
  have hpb := polyBounded_kConv_reconstruct S hf hfb hCf
  have hΛ : (fun t z => if 0 < t then parabolicSemigroup.apply t (kConv N (M.reconstruct f)) z
      else 0) ∈ parabolicSemigroup.distributions := mem_distributions_ite_apply hpb
  refine (M.eq_reconstruct (f := fun x => kGamma M N P I γ f x) (by linarith [S.pos]) hPi' hCPi'
    hmem hbd hCf' hΛ (C' := cT * CL * parabolicSemigroup.momentConst (γ + 2)) ?_).symm
  intro t ht x
  simp only [ht.1, ↓reduceIte]
  rw [apply_kConv_reconstruct_sub_regPi S hf hfb hCf hfV x ht.1 x]
  have hg := hcT (x := x) (M.reconstructSubAt_mem S.pos S.piBound S.piBound_nonneg hf hfb hCf x)
    (fun _ hu => M.measurable_reconstructSubAt S.pos S.piBound S.piBound_nonneg hf hfb hCf x hu)
    hCL0 (M.isLocalOrder_reconstructSubAt S.pos S.piBound S.piBound_nonneg hf hfb hCf x)
  exact abs_apply_le_of_bound (mul_nonneg hcT0 hCL0) (by linarith [S.pos]) hg ht.1
