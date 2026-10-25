/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Profile.Growth.KConv
public import RegularityStructures.Abstract.Profile.Growth.Coeff
public import RegularityStructures.Abstract.Integration.Growth.Commute
public import RegularityStructures.Abstract.Integration.Commute.Reg
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Integration.SectorLocalOrder
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.Germ
public import RegularityStructures.Abstract.Profile.JMap
public import RegularityStructures.Abstract.Profile.KConv
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Hairer's Lemma 5.16 under weighted bounds, for a general shell profile

Profile-generic version of `RegularityStructures.Abstract.Integration.Growth.Commute`: for a
kernel profile `h`
(`ShellProfile h N`), a model `M` realising `K = ∑_n scaledShell h n` for `I`
(`Model.IsRealisingP`) and compatible with the polynomials, satisfying the weighted bounds
`Model.GrowthModel`, and a sector `V` of degrees `> -2`,

  `Γ_{xy} (I + J(y)) a = (I + J(x)) Γ_{xy} a`   for `a ∈ V ∩ T_{<γ}`,  `J = jMapP M h P`

(`Model.gammaMap_integral_add_jMap_of_mem_inP_growth`).  The germ identity with growth is
`realGerm_eq_growthP`.  `Π_x e_i` is `KRegularG` (`Model.GrowthModel.kRegularG_regPi_single`,
reused).
Source: [Hai14] = arXiv:1303.5113v4, proof of Lemma 5.16.
-/
public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}

/-- **Germ identity** for `e_i ∈ V`: `realGerm = K ∗ Π_x e_i - ∑_k (z - x)^k/k! · jCoeff`. -/
theorem realGerm_eq_growthP (M : Model 𝒯 parabolicSemigroup) (hh : ShellProfile h N) {γ CPi CGam p qG : ℝ}
    {ρP ρG : ParabolicSpace → ℝ} (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j) {i : ι}
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (hi : 𝒯.deg i < γ)
    (x z : ParabolicSpace) :
    realGermP M h x i z = kConvP h (fun t w => M.regPi x (Pi.single i 1) t w) z -
      ∑ k ∈ taylorIdx (𝒯.deg i + 2),
        (evalParabolic (MvPolynomial.monomial k 1) (z - x) / multiFact k) * jCoeffP M h x i k := by
  have hR := G.kRegularG_regPi_single hV hVb hdeg hVi hi x
  have hdeg4 : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -4 < 𝒯.deg j :=
    fun j hjV hj => by linarith [hdeg j hjV hj]
  have hloc := G.localGrowth_regPi hV hVb hdeg4 hVi hi x
  have hA : ∀ a ∈ 𝒯.degreesBelowLeIn V γ (𝒯.deg i), -4 < a ∧ a ≤ 𝒯.deg i := fun a ha =>
    ⟨by linarith [(degreesBelowLeIn_bounds_two hdeg i a ha).1],
      (degreesBelowLeIn_bounds_two hdeg i a ha).2⟩
  have hterm : ∀ n : ℕ, parabolicSemigroup.pairing (fun t w => M.regPi x (Pi.single i 1) t w)
      (taylorKernel h n (𝒯.deg i + 2) x z) =
      parabolicSemigroup.pairing (fun t w => M.regPi x (Pi.single i 1) t w)
        (fun w => scaledShell h n (z - w)) -
      ∑ k ∈ taylorIdx (𝒯.deg i + 2),
        (evalParabolic (MvPolynomial.monomial k 1) (z - x) / multiFact k) *
          parabolicSemigroup.pairing (fun t w => M.regPi x (Pi.single i 1) t w)
            (fun w => lineIter (multiDirs k) (scaledShell h n) (x - w)) := fun n =>
    pairing_taylorKernel_eq_growth (regPi_single_mem_distributions M x i)
      (fun _ hu => M.measurable_pi x i hu) hh.contDiff
      hh.eq_zero hA hloc.nonneg hloc.nonneg_exp hloc.loc
      (𝒯.deg i + 2) n
  unfold realGermP kConvP
  simp only [hterm]
  have hs1 := hR.summable_pairing_growthP hh z
  have hsk : ∀ k ∈ taylorIdx (𝒯.deg i + 2), Summable fun n : ℕ =>
      (evalParabolic (MvPolynomial.monomial k 1) (z - x) / multiFact k) *
        parabolicSemigroup.pairing (fun t w => M.regPi x (Pi.single i 1) t w)
          (fun w => lineIter (multiDirs k) (scaledShell h n) (x - w)) := fun k hk =>
    (summable_jCoeff_terms_growthP M hh G x i k hV hVb hVi hi hdeg4
      ((mem_taylorIdx_iff k).1 hk)).mul_left _
  rw [Summable.tsum_sub hs1 (summable_sum hsk), Summable.tsum_finsetSum hsk]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tsum_mul_left]
  rfl

namespace Model

/-- **Target 3** [Hai14, proof of Lemma 5.16] for `e_i ∈ V` (sector version of
`regPi_integral_add_jMap`). -/
theorem regPi_integral_add_jMap_inP_growth {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}
    {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    (hh : ShellProfile h N) (hreal : M.IsRealisingP h γ P I V) (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    {i : ι} (hi : 𝒯.deg i < γ) (hVi : (Pi.single i 1 : ι → ℝ) ∈ V)
    (hN' : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg i + 2 → multiDeg k < N')
    (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    M.regPi x (I (Pi.single i 1) + jMapP M h P x (Pi.single i 1)) t z =
      parabolicSemigroup.apply t (kConvP h (fun t w => M.regPi x (Pi.single i 1) t w)) z := by
  have hR := G.kRegularG_regPi_single hV hVb hdeg hVi hi x
  have hK := hR.polyBounded_kConv_growthP hh
  have hσ := polyBounded_polyEval x (jPolyCoeffP (N' := N') M h x i)
  have hG : PolyBounded (realGermP M h x i) := by
    have e : realGermP M h x i = fun w => kConvP h (fun t w => M.regPi x (Pi.single i 1) t w) w -
        polyEval x (jPolyCoeffP (N' := N') M h x i) w := by
      funext w
      rw [realGerm_eq_growthP M hh G hV hVb hdeg hVi hi x w,
        polyEval_jPolyCoeffP M h x i hN' w]
    rw [e]
    exact hK.sub hσ
  rw [M.regPi_add, hreal.realises x i hi hVi t ht z, realRegP_of_pos M h x i ht,
    jMapP_single, jVec_eq_polyEmbedP, regPi_polyEmbed hreal.poly, polyReg_of_pos _ _ ht,
    ← hG.apply_add hσ ht z]
  congr 1
  funext w
  rw [realGerm_eq_growthP M hh G hV hVb hdeg hVi hi x w,
    polyEval_jPolyCoeffP M h x i hN' w]
  ring

variable {M : Model 𝒯 parabolicSemigroup}

/-- **Hairer's Lemma 5.16** [Hai14] for a sector `V` of degrees `> -2` (sector version of
`gammaMap_integral_add_jMap`): `Γ_{xy} (I + J(y)) e_i = (I + J(x)) Γ_{xy} e_i` for `e_i ∈ V`. -/
theorem gammaMap_integral_add_jMap_inP_growth {γ CPi CGam p qG : ℝ}
    {ρP ρG : ParabolicSpace → ℝ} {P : PolynomialSector 𝒯 N'}
    {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    (hh : ShellProfile h N) (hreal : M.IsRealisingP h γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hN' : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ →
      ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N')
    {i : ι} (hi : 𝒯.deg i < γ) (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (x y : ParabolicSpace) :
    M.gammaMap x y (I (Pi.single i 1) + jMapP M h P y (Pi.single i 1)) =
      I (M.gammaMap x y (Pi.single i 1)) + jMapP M h P x (M.gammaMap x y (Pi.single i 1)) := by
  set τ : ι → ℝ := M.gammaMap x y (Pi.single i 1) with hτ
  have hτV : τ ∈ V := hV.invariant _ (M.gamma x y).2 _ hVi
  have hτlow : τ ∈ lowerSubspace 𝒯.deg γ :=
    (M.isGradedUnipotent_gammaMap x y).map_lowerSubspace (single_mem_lowerSubspace hi 1)
  -- the difference lies in `T̄`
  have hD : M.gammaMap x y (I (Pi.single i 1) + jMapP M h P y (Pi.single i 1)) -
      (I τ + jMapP M h P x τ) ∈ P.subspace := by
    have h1 : I τ - M.gammaMap x y (I (Pi.single i 1)) ∈ P.subspace :=
      hI.comm _ (M.gamma x y).2 _ hVi
    have h2 : M.gammaMap x y (jMapP M h P y (Pi.single i 1)) ∈ P.subspace :=
      P.invariant _ (M.gamma x y).2 _ (jMapP_mem_subspace M h P y _)
    have h3 := jMapP_mem_subspace M h P x τ
    have e : M.gammaMap x y (I (Pi.single i 1) + jMapP M h P y (Pi.single i 1)) -
        (I τ + jMapP M h P x τ) = -(I τ - M.gammaMap x y (I (Pi.single i 1))) +
        M.gammaMap x y (jMapP M h P y (Pi.single i 1)) - jMapP M h P x τ := by
      rw [map_add]; abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ h1) h2) h3
  refine sub_eq_zero.1 (eq_zero_of_regPi_eq_zero hreal.poly x hD fun t ht z => ?_)
  -- the support `S` of the expansion
  set S : Finset ι := 𝒯.sectorBelow V γ with hS
  have hKR : ∀ j ∈ S, KRegularG (fun t w => M.regPi x (Pi.single j 1) t w) x := fun j hj =>
    G.kRegularG_regPi_single hV hVb hdeg ((𝒯.mem_sectorBelow V).1 hj).1
      ((𝒯.mem_sectorBelow V).1 hj).2 x
  have hτsum : τ = ∑ j ∈ S, τ j • (Pi.single j 1 : ι → ℝ) := by
    funext l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single l]
    · simp only [Pi.single_eq_same, mul_one]
    · intro j _ hj
      simp [hj.symm]
    · intro hl
      by_cases h0 : τ l = 0
      · simp [h0]
      · exact absurd ((𝒯.mem_sectorBelow V).2 ⟨hVb τ hτV l h0, by
          by_contra hlt
          exact h0 (hτlow l (not_lt.1 hlt))⟩) hl
  have hvec : I τ + jMapP M h P x τ =
      ∑ j ∈ S, τ j • (I (Pi.single j 1) + jMapP M h P x (Pi.single j 1)) := by
    conv_lhs => rw [hτsum]
    simp only [map_sum, map_smul, smul_add, Finset.sum_add_distrib]
  rw [M.regPi_sub, M.regPi_gammaMap, hvec, regPi_finsetSum_smul,
    regPi_integral_add_jMap_inP_growth hh hreal hV hVb hdeg G hi hVi (hN' i hVi hi) y ht z,
    sub_eq_zero]
  have hterm : ∀ j ∈ S, τ j * M.regPi x (I (Pi.single j 1) + jMapP M h P x (Pi.single j 1)) t z =
      τ j * parabolicSemigroup.apply t (kConvP h (fun t w => M.regPi x (Pi.single j 1) t w)) z := by
    intro j hj
    by_cases h0 : τ j = 0
    · rw [h0, zero_mul, zero_mul]
    · exact congrArg _ (regPi_integral_add_jMap_inP_growth hh hreal hV hVb hdeg G
        ((𝒯.mem_sectorBelow V).1 hj).2 ((𝒯.mem_sectorBelow V).1 hj).1
        (hN' j ((𝒯.mem_sectorBelow V).1 hj).1 ((𝒯.mem_sectorBelow V).1 hj).2) x ht z)
  rw [Finset.sum_congr rfl hterm]
  have hfam : (fun t w => M.regPi y (Pi.single i 1) t w) =
      fun t w => ∑ j ∈ S, τ j * M.regPi x (Pi.single j 1) t w := by
    funext t' w
    rw [← M.regPi_gammaMap x y, M.regPi_eq_sum_sectorBelow hVb hτV hτlow]
  have hk : kConvP h (fun t w => M.regPi y (Pi.single i 1) t w) =
      fun w => ∑ j ∈ S, τ j * kConvP h (fun t w => M.regPi x (Pi.single j 1) t w) w := by
    rw [hfam]
    funext w
    exact kConv_finset_sum_growthP S (fun j t w => M.regPi x (Pi.single j 1) t w) τ hKR hh w
  rw [hk, PolyBounded.apply_finsetSum S τ _ (fun j hj => (hKR j hj).polyBounded_kConv_growthP hh) ht z]

variable {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}
  {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}

/-- Lemma 5.16 for every `a ∈ V ∩ T_{<γ}`: `Γ_{xy}(I + J(y)) a = (I + J(x)) Γ_{xy} a`. -/
theorem gammaMap_integral_add_jMap_of_mem_inP_growth
    (hh : ShellProfile h N) (hreal : M.IsRealisingP h γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hN' : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 →
      multiDeg k < N')
    {a : ι → ℝ} (haV : a ∈ V) (hal : a ∈ lowerSubspace 𝒯.deg γ) (x y : ParabolicSpace) :
    M.gammaMap x y (I a + jMapP M h P y a) =
      I (M.gammaMap x y a) + jMapP M h P x (M.gammaMap x y a) := by
  have hterm : ∀ i, M.gammaMap x y (I (a i • Pi.single i 1) + jMapP M h P y (a i • Pi.single i 1))
      = I (M.gammaMap x y (a i • Pi.single i 1)) +
        jMapP M h P x (M.gammaMap x y (a i • Pi.single i 1)) := by
    intro i
    by_cases hai : a i = 0
    · simp [hai]
    · have hi : 𝒯.deg i < γ := by
        by_contra hge
        exact hai (hal i (not_lt.1 hge))
      have h := M.gammaMap_integral_add_jMap_inP_growth hh hreal hI hV hVb hdeg G hN' hi
        (hVb a haV i hai) x y
      simp only [map_smul, ← smul_add, h]
  conv_lhs => rw [eq_sum_single a]
  conv_rhs => rw [eq_sum_single a]
  simp only [map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hterm i

end Model

end RegularityStructures

end
