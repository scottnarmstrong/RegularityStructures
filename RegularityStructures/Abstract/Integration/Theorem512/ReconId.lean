/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.Helpers
public import RegularityStructures.Abstract.Integration.Theorem512.PolyHelpers
public import RegularityStructures.Abstract.Integration.Theorem512.KConvTaylor
public import RegularityStructures.Abstract.Integration.Theorem512.Sup
public import RegularityStructures.Abstract.Integration.Theorem512.SupBound

/-!
# `Q_t (K ∗ Rf) − Q_t Π_x 𝒦_γ f(x) = Q_t g_x`

For `f ∈ D^γ` with values in `V` and a `SchauderSetting`, write `Λ_x = Rf − Π_x f(x)`
(`reconstructSubAt`).  Then `K ∗ Λ_x` is the function `kConv N Λ_x`, and for every `x`, `t > 0`

  `(Q_t (K ∗ Rf))(z) − (Q_t Π_x 𝒦_γ f(x))(z) = (Q_t g_x)(z)`,
  `g_x(w) = kConv N Λ_x (w) − ∑_{|k|_𝔰 < γ + 2} (w − x)^k/k! · nCoeff M N f x k`
  (`apply_kConv_reconstruct_sub_regPi`).  This combines Hairer's Lemma 5.16
  (`regPi_integral_add_jMap`: `Q_t Π_x (I + J(x)) e_i = Q_t (K ∗ Π_x e_i)`), the polynomial
  `Π_x N_γ f(x)` (`IsPolyCompatible`) and the linearity of `K ∗ ·` (`kConv_finset_sum`).

Source: [Hai14, proof of Theorem 5.12, (5.17)].
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {N : ℕ} {γ CPi CGam CI : ℝ} {P : PolynomialSector 𝒯 N'}
  {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}

theorem kRegular_reconstructSubAt {Cf : ℝ} (hγ : 0 < γ) (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hPi : M.PiBoundOn γ CPi univ) (hCPi : 0 ≤ CPi) {f : ParabolicSpace → ι → ℝ}
    (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf)
    (x : ParabolicSpace) : KRegular (M.reconstructSubAt f x) x := by
  refine ⟨M.reconstructSubAt_mem hγ hPi hCPi hf hfb hCf x,
    fun _ hu => M.measurable_reconstructSubAt hγ hPi hCPi hf hfb hCf x hu, γ,
    (modelReconstructionConst 𝒯 parabolicSemigroup γ + Fintype.card ι) * CPi * Cf,
    insert γ (𝒯.degreesBelow γ), ?_,
    mul_nonneg (mul_nonneg (add_nonneg (modelReconstructionConst_nonneg 𝒯 _ hγ.le)
      (Nat.cast_nonneg _)) hCPi) hCf,
    M.isLocalOrder_reconstructSubAt hγ hPi hCPi hf hfb hCf x⟩
  intro a ha
  rcases Finset.mem_insert.1 ha with rfl | ha
  · exact ⟨by linarith, le_rfl⟩
  · obtain ⟨i, hi, rfl⟩ := (𝒯.mem_degreesBelow).1 ha
    exact ⟨hdeg i hi, hi.le⟩

/-- `K ∗ Rf = K ∗ (Rf − Π_x f(x)) + ∑_i f(x)_i K ∗ Π_x e_i`. -/
theorem kConv_reconstruct_eq (S : SchauderSetting M N γ P I V CPi CGam CI)
    {f : ParabolicSpace → ι → ℝ} {Cf : ℝ} (hf : f ∈ M.modelledDistributions γ)
    (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf) (x z : ParabolicSpace) :
    kConv N (M.reconstruct f) z = kConv N (M.reconstructSubAt f x) z +
      ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
        f x i * kConv N (fun t w => M.regPi x (Pi.single i 1) t w) z := by
  classical
  set F : Finset ι := Finset.univ.filter (fun i => 𝒯.deg i < γ) with hF
  have hK0 := kRegular_reconstructSubAt S.pos S.deg_gt S.piBound S.piBound_nonneg hf hfb hCf x
  have hKi : ∀ i ∈ F, KRegular (fun t w => M.regPi x (Pi.single i 1) t w) x := fun i hi =>
    M.kRegular_regPi_single S.deg_gt S.piBound S.gammaBound S.piBound_nonneg
      (Finset.mem_filter.1 hi).2 x
  set Λj : Option ι → ℝ → ParabolicSpace → ℝ := fun o t w =>
    Option.elim o (M.reconstructSubAt f x t w) (fun i => M.regPi x (Pi.single i 1) t w) with hΛj
  set c : Option ι → ℝ := fun o => Option.elim o 1 (fun i => f x i) with hc
  have hΛ : ∀ j ∈ Finset.insertNone F, KRegular (Λj j) x := by
    rintro (_ | i) hj
    · exact hK0
    · exact hKi i (Finset.mem_insertNone.1 hj i rfl)
  have h := kConv_finset_sum (Finset.insertNone F) Λj c hΛ N z
  simp only [Finset.sum_insertNone] at h
  have hΛj1 : (fun t w => c none * Λj none t w + ∑ i ∈ F, c (some i) * Λj (some i) t w) =
      M.reconstruct f := by
    funext t w
    have e := M.regPi_eq_sum_filter (hf.2.1 x) x t w
    simp only [hc, hΛj, Option.elim_none, Option.elim_some, one_mul]
    rw [← hF] at e
    simp only [Model.reconstructSubAt, e]
    ring
  rw [hΛj1] at h
  rw [h]
  simp [hc, hΛj]

/-- `Q_t Π_x 𝒦_γ f(x) = ∑_i f(x)_i Q_t (K ∗ Π_x e_i) + Q_t (the polynomial `N_γ f(x)`)`. -/
theorem regPi_kGamma_eq (S : SchauderSetting M N γ P I V CPi CGam CI)
    {f : ParabolicSpace → ι → ℝ} (hfl : ∀ x, f x ∈ lowerSubspace 𝒯.deg γ)
    (hfV : ∀ x, f x ∈ V) (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    M.regPi x (kGamma M N P I γ f x) t z =
      ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ), f x i *
        parabolicSemigroup.apply t (kConv N (fun t w => M.regPi x (Pi.single i 1) t w)) z +
      parabolicSemigroup.apply t (polyEval x (fun k : PolyIndex N' =>
        if polyDeg N' k < γ + 2 then nCoeff M N f x k.1 / multiFactorial k.1 else 0)) z := by
  classical
  have e1 : I (f x) + jMap M N P x (f x) =
      ∑ i, f x i • (I (Pi.single i 1) + jMap M N P x (Pi.single i 1)) := by
    conv_lhs => rw [eq_sum_single (f x)]
    simp only [map_sum, map_smul, ← Finset.sum_add_distrib, smul_add]
  have e2 : kGamma M N P I γ f x = (∑ i, f x i • (I (Pi.single i 1) + jMap M N P x (Pi.single i 1))) +
      P.polyEmbed (fun k : PolyIndex N' =>
        if polyDeg N' k < γ + 2 then nCoeff M N f x k.1 / multiFactorial k.1 else 0) := by
    rw [← nVec_eq_polyEmbed, ← e1]; rfl
  rw [e2, M.regPi_add, regPi_finset_sum, regPi_polyEmbed S.realising.poly,
    polyReg_of_pos _ _ ht, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hfi : f x i = 0
  · simp [hfi]
  · have hi : 𝒯.deg i < γ := by
      by_contra hge; exact hfi (hfl x i (not_lt.1 hge))
    simp only [hi, ↓reduceIte]
    rw [regPi_integral_add_jMap S.realising S.deg_gt S.piBound S.gammaBound
      S.piBound_nonneg hi (S.basis_mem _ (hfV x) i hfi) (S.poly_large i hi) x ht z]

/-- **The identity behind (5.17)**: for `x`, `t > 0`,
`Q_t (K ∗ Rf)(z) − Q_t Π_x 𝒦_γ f(x)(z) = Q_t g_x (z)`, `g_x = K ∗ (Rf − Π_x f(x))` minus its Taylor
polynomial of order `γ + 2` at `x`. -/
theorem apply_kConv_reconstruct_sub_regPi (S : SchauderSetting M N γ P I V CPi CGam CI)
    {f : ParabolicSpace → ι → ℝ} {Cf : ℝ} (hf : f ∈ M.modelledDistributions γ)
    (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf) (hfV : ∀ x, f x ∈ V)
    (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    parabolicSemigroup.apply t (kConv N (M.reconstruct f)) z -
        M.regPi x (kGamma M N P I γ f x) t z =
      parabolicSemigroup.apply t (fun w => kConv N (M.reconstructSubAt f x) w -
        ∑ k ∈ taylorIdx (γ + 2),
          (evalParabolic (MvPolynomial.monomial k 1) (w - x) / multiFact k) *
            nCoeff M N f x k) z := by
  classical
  set F : Finset ι := Finset.univ.filter (fun i => 𝒯.deg i < γ) with hF
  have hK0 := kRegular_reconstructSubAt S.pos S.deg_gt S.piBound S.piBound_nonneg hf hfb hCf x
  have hKi : ∀ i ∈ F, KRegular (fun t w => M.regPi x (Pi.single i 1) t w) x := fun i hi =>
    M.kRegular_regPi_single S.deg_gt S.piBound S.gammaBound S.piBound_nonneg
      (Finset.mem_filter.1 hi).2 x
  have hPB0 := hK0.polyBounded_kConv N
  have hPBi : ∀ i ∈ F, PolyBounded (kConv N (fun t w => M.regPi x (Pi.single i 1) t w)) :=
    fun i hi => (hKi i hi).polyBounded_kConv N
  have hPBs := PolyBounded.finsetSum F (fun i => f x i)
    (fun i => kConv N (fun t w => M.regPi x (Pi.single i 1) t w)) hPBi
  have hpe : ∀ w, polyEval x (fun k : PolyIndex N' =>
      if polyDeg N' k < γ + 2 then nCoeff M N f x k.1 / multiFactorial k.1 else 0) w =
      ∑ k ∈ taylorIdx (γ + 2),
        (evalParabolic (MvPolynomial.monomial k 1) (w - x) / multiFact k) * nCoeff M N f x k :=
    fun w => polyEval_coeffPoly x (γ + 2) (fun k => nCoeff M N f x k) S.poly_large' w
  have hPBp := polyBounded_polyEval x (fun k : PolyIndex N' =>
      if polyDeg N' k < γ + 2 then nCoeff M N f x k.1 / multiFactorial k.1 else 0)
  have hkc : kConv N (M.reconstruct f) = fun w => kConv N (M.reconstructSubAt f x) w +
      ∑ i ∈ F, f x i * kConv N (fun t w => M.regPi x (Pi.single i 1) t w) w := by
    funext w
    exact kConv_reconstruct_eq S hf hfb hCf x w
  rw [hkc, PolyBounded.apply_add hPB0 hPBs ht,
    PolyBounded.apply_finsetSum F (fun i => f x i) _ hPBi ht,
    regPi_kGamma_eq S hf.2.1 hfV x ht z]
  have hsub := PolyBounded.apply_sub hPB0 hPBp ht z
  have hfun : (fun w => kConv N (M.reconstructSubAt f x) w - ∑ k ∈ taylorIdx (γ + 2),
      (evalParabolic (MvPolynomial.monomial k 1) (w - x) / multiFact k) * nCoeff M N f x k) =
      fun w => kConv N (M.reconstructSubAt f x) w - polyEval x (fun k : PolyIndex N' =>
        if polyDeg N' k < γ + 2 then nCoeff M N f x k.1 / multiFactorial k.1 else 0) w := by
    funext w; rw [hpe w]
  rw [hfun, hsub]
  ring

end Model

end RegularityStructures

end
