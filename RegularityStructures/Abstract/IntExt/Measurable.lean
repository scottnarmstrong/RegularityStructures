/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.Model
public import RegularityStructures.Abstract.Singular.KGamma.MeasJG
public import RegularityStructures.Abstract.Integration.Growth.LocalOrder
public import RegularityStructures.Abstract.Profile.KConv
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs

/-!
# Joint measurability of the planted regularisations

Under `Model.IsJointMeasurable`, the germ `(x, y) ↦ realGermP M h x d y` of a planted symbol
`d ∈ D` is jointly measurable, hence so is `(x, z) ↦ realRegP M h x d t z` (`t > 0`), which is the
hypothesis `IntExtMeas` of `IntExtHyp.intExtend` (`intExtMeas_of_isJointMeasurable`).

The germ is `K ∗ Π_x e_d` minus the Taylor polynomial with coefficients `jCoeffP M h x d k`
(`realGerm_eq_growthP`); the weighted pairings `⟨Π_x e_d, scaledShell h n (y − ·)⟩` and
`⟨Π_x e_d, D^k scaledShell h n (x − ·)⟩` are jointly measurable as limits of the integrals at times
`1 / (m + 1)` (Fubini).
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace RegularityStructures

section Pairings

variable {h : ParabolicSpace → ℝ} {N : ℕ}

/-- `(x, y) ↦ ⟨Λ_x, scaledShell h n (y − ·)⟩` is jointly measurable. -/
theorem measurable_pairing_shell_joint {Λ : ParabolicSpace → ℝ → ParabolicSpace → ℝ}
    (hΛm : ∀ s, 0 < s → Measurable fun p : ParabolicSpace × ParabolicSpace => Λ p.1 s p.2)
    (hKR : ∀ x, KRegularG (Λ x) x) (hh : ShellProfile h N) (n : ℕ) :
    Measurable fun p : ParabolicSpace × ParabolicSpace =>
      parabolicSemigroup.pairing (Λ p.1) (fun w => scaledShell h n (p.2 - w)) := by
  have hg := contDiff_scaledShell hh.contDiff n
  have hF : ∀ m : ℕ, Measurable fun p : ParabolicSpace × ParabolicSpace =>
      ∫ w, Λ p.1 (1 / ((m : ℝ) + 1)) w * scaledShell h n (p.2 - w) := by
    intro m
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hm : Measurable fun q : (ParabolicSpace × ParabolicSpace) × ParabolicSpace =>
        Λ q.1.1 (1 / ((m : ℝ) + 1)) q.2 * scaledShell h n (q.1.2 - q.2) :=
      ((hΛm _ hpos).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
        (hg.continuous.measurable.comp ((measurable_snd.comp measurable_fst).sub measurable_snd))
    exact (hm.stronglyMeasurable.integral_prod_right (ν := volume)).measurable
  refine measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.2 fun p => ?_)
  obtain ⟨h1, h2, α, C, q, A, hA, hC, hq, hloc⟩ := hKR p.1
  have hA' : ∀ a ∈ A, -4 < a ∧ a ≤ α := fun a ha => ⟨by linarith [(hA a ha).1], (hA a ha).2⟩
  have hseq : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun m => by
        show (0 : ℝ) < 1 / ((m : ℝ) + 1)
        positivity⟩
  have key := (tendsto_and_abs_pairing_scaledShell_centre_le_growth h1 h2 hh.contDiff
    hh.eq_zero (y := p.2) hA' hC hq hloc n).1
  exact key.comp hseq

/-- `(x, y) ↦ (K ∗ Λ_x)(y)` is jointly measurable. -/
theorem measurable_kConv_joint {Λ : ParabolicSpace → ℝ → ParabolicSpace → ℝ}
    (hΛm : ∀ s, 0 < s → Measurable fun p : ParabolicSpace × ParabolicSpace => Λ p.1 s p.2)
    (hKR : ∀ x, KRegularG (Λ x) x) (hh : ShellProfile h N) :
    Measurable fun p : ParabolicSpace × ParabolicSpace => kConvP h (Λ p.1) p.2 :=
  measurable_tsum_of_summable (fun n => measurable_pairing_shell_joint hΛm hKR hh n)
    fun p => (hKR p.1).summable_pairing_growthP hh p.2

/-- Weighted version of `measurable_derivShellPairing`. -/
theorem measurable_derivShellPairing_growth {Λ : ParabolicSpace → ℝ → ParabolicSpace → ℝ}
    (hΛ : ∀ x, Λ x ∈ parabolicSemigroup.distributions)
    (hΛm : ∀ s, 0 < s → Measurable fun p : ParabolicSpace × ParabolicSpace => Λ p.1 s p.2)
    (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    {γ q : ℝ} {C : ParabolicSpace → ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ)
    (hC : ∀ x, 0 ≤ C x) (hq : 0 ≤ q)
    (hloc : ∀ x, parabolicSemigroup.IsLocalOrderGrowth (Λ x) x γ A (C x) q) (k : Fin 4 →₀ ℕ)
    (n : ℕ) : Measurable fun x => derivShellPairing (Λ x) h k x n := by
  have hg : ContDiff ℝ ∞ (lineIter (multiDirs k) (scaledShell h n)) :=
    contDiff_lineIter (contDiff_scaledShell h0 n) _
  have hF : ∀ m : ℕ, Measurable fun x => ∫ z, Λ x (1 / ((m : ℝ) + 1)) z *
      lineIter (multiDirs k) (scaledShell h n) (x - z) := by
    intro m
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hm : Measurable fun p : ParabolicSpace × ParabolicSpace =>
        Λ p.1 (1 / ((m : ℝ) + 1)) p.2 *
          lineIter (multiDirs k) (scaledShell h n) (p.1 - p.2) :=
      (hΛm _ hpos).mul (hg.continuous.comp (continuous_fst.sub continuous_snd)).measurable
    exact (hm.stronglyMeasurable.integral_prod_right (ν := volume)).measurable
  refine measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.2 fun x => ?_)
  have key := (tendsto_and_abs_pairing_word_scaledShell_le_growth (hΛ x)
    (fun u hu => (hΛm u hu).comp measurable_prodMk_left) h0 hs hA (hC x) hq (hloc x)
    (Finsupp.toMultiset k).toList n).1
  have hseq : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun m => by
        show (0 : ℝ) < 1 / ((m : ℝ) + 1)
        positivity⟩
  exact key.comp hseq

end Pairings

namespace IntExtHyp

open IntExt

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} {M : Model 𝒯 parabolicSemigroup} {E : IntegrationExtension 𝒯 𝒯' P P' I D}
  {h : ParabolicSpace → ℝ} {N : ℕ} {γ : ℝ} {V : Submodule ℝ (ι → ℝ)}
  (H : IntExtHyp M E h N γ V)

include H in
/-- The coefficients `x ↦ jCoeffP M h x d k` of the planted symbols are measurable. -/
theorem measurable_jCoeffP_ext (hJ : M.IsJointMeasurable) {d : ι} (hd : d ∈ D) {k : Fin 4 →₀ ℕ}
    (hk : (multiDeg k : ℝ) < 𝒯.deg d + 2) : Measurable fun x => jCoeffP M h x d k := by
  obtain ⟨C, C', p, q, ρP, ρG, G⟩ := H.growth
  have hVi := H.single_mem_ext_of_mem_D hd
  have hi := H.deg_D d hd
  have hdeg4 : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ extSector V D → 𝒯.deg j < γ → -4 < 𝒯.deg j :=
    fun j hj hjγ => by linarith [H.deg_gt_ext j hj hjγ]
  have hC : ∀ x, 0 ≤ max C' 1 * C * Fintype.card ι * (ρP x * ρG x) := fun x =>
    mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _))
      G.piBound_nonneg) (Nat.cast_nonneg _))
      (mul_nonneg (G.moderateP.pos x).le (G.moderateG.pos x).le)
  exact measurable_tsum_of_summable
    (fun n => measurable_derivShellPairing_growth
      (Λ := fun x t y => M.regPi x (Pi.single d 1) t y)
      (fun x => regPi_single_mem_distributions M x d) (fun s hs => hJ d s hs)
      H.profile.contDiff H.profile.eq_zero (degreesBelowLeIn_bounds 𝒯 _ hdeg4 d) hC
      (add_nonneg G.moderateP.nonneg_exp G.nonnegG)
      (fun x => M.isLocalOrderGrowth_regPi_single_in H.isSector_ext H.coord_ext G.moderateP
        G.moderateG.one_le G.nonnegG G.piBound G.gammaBound G.piBound_nonneg hVi hi x) k n)
    fun x => summable_jCoeff_terms_growthP M H.profile G x d k H.isSector_ext H.coord_ext hVi
      hi hdeg4 hk

include H in
/-- The germ `(x, y) ↦ realGermP M h x d y` of a planted symbol is jointly measurable. -/
theorem measurable_realGermP_joint (hJ : M.IsJointMeasurable) {d : ι} (hd : d ∈ D) :
    Measurable fun p : ParabolicSpace × ParabolicSpace => realGermP M h p.1 d p.2 := by
  obtain ⟨C, C', p, q, ρP, ρG, G⟩ := H.growth
  have hVi := H.single_mem_ext_of_mem_D hd
  have hi := H.deg_D d hd
  have hKR : ∀ x, KRegularG (fun t w => M.regPi x (Pi.single d 1) t w) x := fun x =>
    G.kRegularG_regPi_single H.isSector_ext H.coord_ext H.deg_gt_ext hVi hi x
  have hK : Measurable fun p : ParabolicSpace × ParabolicSpace =>
      kConvP h (fun t w => M.regPi p.1 (Pi.single d 1) t w) p.2 :=
    measurable_kConv_joint (Λ := fun x t w => M.regPi x (Pi.single d 1) t w)
      (fun s hs => hJ d s hs) hKR H.profile
  have hT : Measurable fun p : ParabolicSpace × ParabolicSpace =>
      ∑ k ∈ taylorIdx (𝒯.deg d + 2),
        (evalParabolic (MvPolynomial.monomial k 1) (p.2 - p.1) / multiFact k) *
          jCoeffP M h p.1 d k := by
    refine Finset.measurable_sum _ fun k hk => ?_
    have h1 : Measurable fun p : ParabolicSpace × ParabolicSpace =>
        evalParabolic (MvPolynomial.monomial k 1) (p.2 - p.1) / multiFact k :=
      (((continuous_evalParabolic _).comp (continuous_snd.sub continuous_fst)).measurable).div_const _
    exact h1.mul ((H.measurable_jCoeffP_ext hJ hd ((mem_taylorIdx_iff k).1 hk)).comp
      measurable_fst)
  have e : ∀ p : ParabolicSpace × ParabolicSpace, realGermP M h p.1 d p.2 =
      kConvP h (fun t w => M.regPi p.1 (Pi.single d 1) t w) p.2 -
        ∑ k ∈ taylorIdx (𝒯.deg d + 2),
          (evalParabolic (MvPolynomial.monomial k 1) (p.2 - p.1) / multiFact k) *
            jCoeffP M h p.1 d k := fun p =>
    realGerm_eq_growthP M H.profile G H.isSector_ext H.coord_ext H.deg_gt_ext hVi hi p.1 p.2
  have e' : (fun p : ParabolicSpace × ParabolicSpace => realGermP M h p.1 d p.2) = _ := funext e
  rw [e']
  exact hK.sub hT

end IntExtHyp

theorem realRegP_eq_integral {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
    (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (d : ι) {t : ℝ} (ht : 0 < t)
    (x z : ParabolicSpace) :
    realRegP M h x d t z = ∫ y, parabolicKernel t (z - y) * realGermP M h x d y := by
  rw [realRegP_of_pos M h x d ht]
  rfl

theorem measurable_integral_parabolicKernel_mul {g : ParabolicSpace × ParabolicSpace → ℝ}
    (hg : Measurable g) (t : ℝ) :
    Measurable fun p : ParabolicSpace × ParabolicSpace =>
      ∫ y, parabolicKernel t (p.2 - y) * g (p.1, y) := by
  have hm : Measurable fun q : (ParabolicSpace × ParabolicSpace) × ParabolicSpace =>
      parabolicKernel t (q.1.2 - q.2) * g (q.1.1, q.2) :=
    ((measurable_parabolicKernel t).comp ((measurable_snd.comp measurable_fst).sub
      measurable_snd)).mul (hg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right (ν := volume)).measurable

namespace IntExtHyp

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} {M : Model 𝒯 parabolicSemigroup} {E : IntegrationExtension 𝒯 𝒯' P P' I D}
  {h : ParabolicSpace → ℝ} {N : ℕ} {γ : ℝ} {V : Submodule ℝ (ι → ℝ)}
  (H : IntExtHyp M E h N γ V)

include H in
/-- Joint measurability of `M` gives joint measurability of the planted regularisations. -/
theorem intExtMeas_of_isJointMeasurable (hJ : M.IsJointMeasurable) : IntExtMeas M h D := by
  intro d hd t ht
  have hint := measurable_integral_parabolicKernel_mul (H.measurable_realGermP_joint hJ hd) t
  have e : (fun p : ParabolicSpace × ParabolicSpace => realRegP M h p.1 d t p.2) =
      fun p => ∫ y, parabolicKernel t (p.2 - y) * realGermP M h p.1 d y :=
    funext fun p => realRegP_eq_integral M h d ht p.1 p.2
  rw [e]
  exact hint

end IntExtHyp

end RegularityStructures

end

@[expose] public noncomputable section

namespace RegularityStructures

namespace IntExtHyp

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} {M : Model 𝒯 parabolicSemigroup} {E : IntegrationExtension 𝒯 𝒯' P P' I D}
  {h : ParabolicSpace → ℝ} {N : ℕ} {γ : ℝ} {V : Submodule ℝ (ι → ℝ)}

/-- The extended model of a jointly measurable model: `intExtend` with the measurability of the
planted regularisations proved from `M.IsJointMeasurable`. -/
def intExtendOfJoint (H : IntExtHyp M E h N γ V) (hJ : M.IsJointMeasurable) :
    Model 𝒯' parabolicSemigroup :=
  H.intExtend (H.intExtMeas_of_isJointMeasurable hJ)

end IntExtHyp

end RegularityStructures

end
