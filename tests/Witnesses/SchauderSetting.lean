/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.Setting
public import RegularityStructures.Abstract.Integration.Theorem512.ReconMain
public import RegularityStructures.Abstract.Polynomial.Model.Bounds
public import RegularityStructures.Abstract.Polynomial.Structure
public import RegularityStructures.Abstract.Polynomial.Bound

/-!
# A non-degenerate instance of the hypotheses of Theorem 5.12

The hypotheses `SchauderSetting M N γ P I V CPi CGam CI` and `SchauderNonIntegral 𝒯 γ N' P` of the
multilevel Schauder theorems `Model.kGamma_mem_modelledDistributions` and
`Model.reconstruct_kGamma` hold simultaneously with a nonzero sector `V` on which `I` is nonzero.

The regularity structure has basis `{X^k : |k|_𝔰 < N'} ⊔ {Ξ, IΞ}`, indexed by
`PolyIndex N' ⊕ Fin 2`, with degrees `|X^k| = |k|_𝔰`, `|Ξ| = -1/2` and `|IΞ| = 3/2`. The structure
group consists of the block maps acting as the polynomial translation `Γ_h` on the polynomial block
and as the identity on `Ξ`, `IΞ`. The model is the polynomial model `Π_x X^k = (· - x)^k`,
`Γ_{xy} = Γ_{x - y}` on the polynomial block, together with `Π_x Ξ = Π_x IΞ = 0`. The sector is
`V = ℝ Ξ`, the abstract integration map is `I Ξ = IΞ` (zero on the other basis vectors), the
polynomial sector is the polynomial block and `γ = 7/4`.

The model realises the kernel for `I` because the realised germ of the zero distribution `Π_x Ξ`
vanishes, so that `Π_x I Ξ = 0` is the required distribution.

* `schauderSetting_blockModel`, `schauderNonIntegral_blockModel`,
  `isJointMeasurable_blockModel`: the concrete instance;
* `xiConst_mem_modelledDistributions`: the constant `f(x) = Ξ` is a nonzero modelled distribution
  of order `7/4` with values in `V`;
* `schauderSetting_witness`: the existential summary of the full hypothesis set of
  `Model.kGamma_mem_modelledDistributions` and `Model.reconstruct_kGamma`, with `N' ≤ N`,
  `V ≠ ⊥`, `I ≠ 0`, an element `a ∈ V` with `I a ≠ 0` and a nonzero `f ∈ D^γ` with values in `V`;
* `kGamma_xiConst_mem_modelledDistributions`, `reconstruct_kGamma_xiConst`: the two theorems
  applied to the block model and `f(x) = Ξ`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.SchauderWitness

variable {N : ℕ}

/-- The basis `{X^k : |k|_𝔰 < N} ⊔ {Ξ, IΞ}`; `Sum.inr 0 = Ξ`, `Sum.inr 1 = IΞ`. -/
abbrev Idx (N : ℕ) : Type := PolyIndex N ⊕ Fin 2

/-- The degrees of `Ξ` and `IΞ`: `-1/2` and `3/2`. -/
def xiDeg : Fin 2 → ℝ := ![-1 / 2, 3 / 2]

/-- The block map: the translation `Γ_h` on the polynomial block, the identity on `Ξ`, `IΞ`. -/
def blockTranslate (h : Fin 4 → ℝ) : (Idx N → ℝ) →ₗ[ℝ] (Idx N → ℝ) where
  toFun τ := Sum.elim (polyTranslate h (τ ∘ Sum.inl)) (τ ∘ Sum.inr)
  map_add' τ σ := by
    funext i
    cases i with
    | inl k =>
      rw [Pi.add_apply, Sum.elim_inl, Sum.elim_inl, Sum.elim_inl, Pi.add_comp, map_add,
        Pi.add_apply]
    | inr m =>
      rw [Pi.add_apply, Sum.elim_inr, Sum.elim_inr, Sum.elim_inr, Function.comp_apply,
        Function.comp_apply, Function.comp_apply, Pi.add_apply]
  map_smul' c τ := by
    funext i
    cases i with
    | inl k =>
      rw [Pi.smul_apply, Sum.elim_inl, Sum.elim_inl, Pi.smul_comp, map_smul, Pi.smul_apply,
        RingHom.id_apply]
    | inr m =>
      rw [Pi.smul_apply, Sum.elim_inr, Sum.elim_inr, Function.comp_apply, Function.comp_apply,
        Pi.smul_apply, RingHom.id_apply]

theorem blockTranslate_inl (h : Fin 4 → ℝ) (τ : Idx N → ℝ) (k : PolyIndex N) :
    blockTranslate h τ (Sum.inl k) = polyTranslate h (τ ∘ Sum.inl) k := rfl

theorem blockTranslate_inr (h : Fin 4 → ℝ) (τ : Idx N → ℝ) (m : Fin 2) :
    blockTranslate h τ (Sum.inr m) = τ (Sum.inr m) := rfl

theorem blockTranslate_comp_inl (h : Fin 4 → ℝ) (τ : Idx N → ℝ) :
    blockTranslate h τ ∘ Sum.inl = polyTranslate h (τ ∘ Sum.inl) := rfl

/-- A vector with no polynomial component is fixed by every block map. -/
theorem blockTranslate_of_comp_inl {τ : Idx N → ℝ} (hτ : τ ∘ Sum.inl = 0) (h : Fin 4 → ℝ) :
    blockTranslate h τ = τ := by
  funext i
  cases i with
  | inl k =>
    rw [blockTranslate_inl, hτ, map_zero]
    exact (congrFun hτ k).symm
  | inr m => rw [blockTranslate_inr]

theorem single_inl_comp_inl (k : PolyIndex N) (c : ℝ) :
    (Pi.single (Sum.inl k) c : Idx N → ℝ) ∘ Sum.inl = Pi.single k c := by
  funext l
  simp [Pi.single_apply]

theorem single_inr_comp_inl (m : Fin 2) (c : ℝ) :
    (Pi.single (Sum.inr m) c : Idx N → ℝ) ∘ Sum.inl = 0 := by
  funext l
  simp

theorem blockTranslate_zero : (blockTranslate 0 : (Idx N → ℝ) →ₗ[ℝ] (Idx N → ℝ)) = LinearMap.id := by
  refine LinearMap.ext fun τ => funext fun i => ?_
  cases i with
  | inl k =>
    rw [blockTranslate_inl, polyTranslate_zero, LinearMap.id_apply, LinearMap.id_apply,
      Function.comp_apply]
  | inr m => rw [blockTranslate_inr, LinearMap.id_apply]

theorem blockTranslate_add (h h' : Fin 4 → ℝ) :
    (blockTranslate h ∘ₗ blockTranslate h' : (Idx N → ℝ) →ₗ[ℝ] (Idx N → ℝ)) =
      blockTranslate (h + h') := by
  refine LinearMap.ext fun τ => funext fun i => ?_
  cases i with
  | inl k =>
    rw [LinearMap.comp_apply, blockTranslate_inl, blockTranslate_comp_inl, blockTranslate_inl,
      ← polyTranslate_add, LinearMap.comp_apply]
  | inr m =>
    rw [LinearMap.comp_apply, blockTranslate_inr, blockTranslate_inr, blockTranslate_inr]

/-- The block map `Γ_h` as an element of `GL(T)`, with inverse `Γ_{-h}`. -/
def blockUnit (h : Fin 4 → ℝ) : LinearMap.GeneralLinearGroup ℝ (Idx N → ℝ) where
  val := blockTranslate h
  inv := blockTranslate (-h)
  val_inv := by
    rw [Module.End.mul_eq_comp, blockTranslate_add, add_neg_cancel, blockTranslate_zero,
      Module.End.one_eq_id]
  inv_val := by
    rw [Module.End.mul_eq_comp, blockTranslate_add, neg_add_cancel, blockTranslate_zero,
      Module.End.one_eq_id]

/-- The group homomorphism `h ↦ Γ_h`. -/
def blockHom (N : ℕ) :
    Multiplicative (Fin 4 → ℝ) →* LinearMap.GeneralLinearGroup ℝ (Idx N → ℝ) where
  toFun h := blockUnit (Multiplicative.toAdd h)
  map_one' := Units.ext blockTranslate_zero
  map_mul' a b := Units.ext (by
    rw [Units.val_mul, Module.End.mul_eq_comp]
    exact (blockTranslate_add _ _).symm)

/-- The structure group of block maps. -/
def blockGroup (N : ℕ) : Subgroup (LinearMap.GeneralLinearGroup ℝ (Idx N → ℝ)) :=
  (blockHom N).range

/-- The degrees: `|X^k| = |k|_𝔰`, `|Ξ| = -1/2`, `|IΞ| = 3/2`. -/
def blockDeg (N : ℕ) : Idx N → ℝ := Sum.elim (polyDeg N) xiDeg

theorem isGradedUnipotent_blockTranslate (h : Fin 4 → ℝ) :
    IsGradedUnipotent (blockDeg N) (blockTranslate h) := by
  intro i j hij
  cases i with
  | inl k =>
    cases j with
    | inl l =>
      have := isGradedUnipotent_polyTranslate (N := N) h k l hij
      simpa [blockTranslate_inl, single_inl_comp_inl, Pi.single_apply] using this
    | inr m => simp [blockTranslate_inr]
  | inr m =>
    rw [blockTranslate_of_comp_inl (single_inr_comp_inl m 1) h, sub_self]
    exact Pi.zero_apply j

/-- The regularity structure with basis `{X^k} ⊔ {Ξ, IΞ}`. -/
def blockStructure (N : ℕ) : RegularityStructure (Idx N) where
  deg := blockDeg N
  group := blockGroup N
  isGradedUnipotent := by
    rintro g ⟨h, rfl⟩
    exact isGradedUnipotent_blockTranslate _

theorem blockGroup_val {g : LinearMap.GeneralLinearGroup ℝ (Idx N → ℝ)}
    (hg : g ∈ (blockStructure N).group) :
    ∃ h : Fin 4 → ℝ, (g : (Idx N → ℝ) →ₗ[ℝ] (Idx N → ℝ)) = blockTranslate h := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨Multiplicative.toAdd h, rfl⟩

/-! ## The model -/

/-- `Γ_{xy} = Γ_{x - y}`. -/
def blockGamma (N : ℕ) (x y : ParabolicSpace) : (blockStructure N).group :=
  ⟨blockUnit (parabolicCoords (x - y)), ⟨Multiplicative.ofAdd _, rfl⟩⟩

theorem blockGamma_val (x y : ParabolicSpace) :
    (((blockGamma N x y : (blockStructure N).group) :
      LinearMap.GeneralLinearGroup ℝ (Idx N → ℝ)) : (Idx N → ℝ) →ₗ[ℝ] (Idx N → ℝ))
      = blockTranslate (parabolicCoords (x - y)) := rfl

theorem polyReg_diag (x : ParabolicSpace) (τ : PolyIndex N → ℝ) {t : ℝ} (ht : 0 < t) :
    polyReg x τ t x = polyReg 0 τ t 0 := by
  rw [polyReg_of_pos x τ ht, polyReg_of_pos 0 τ ht]
  simp only [RegularisingSemigroup.apply, parabolicSemigroup]
  have e : ∀ z : ParabolicSpace, parabolicKernel t (x - z) * polyEval x τ z =
      (fun w => parabolicKernel t (-w) * polyEval 0 τ w) (z - x) := by
    intro z
    simp only [neg_sub, polyEval, sub_zero]
  have e0 : ∀ z : ParabolicSpace, parabolicKernel t (0 - z) * polyEval 0 τ z =
      (fun w => parabolicKernel t (-w) * polyEval 0 τ w) z := by
    intro z
    simp
  simp_rw [e, e0]
  rw [Measure.volume_eq_prod]
  exact integral_sub_right_eq_self (fun w : ParabolicSpace =>
    parabolicKernel t (-w) * polyEval 0 τ w) x

theorem polyReg_zero (x : ParabolicSpace) : polyReg x (0 : PolyIndex N → ℝ) = 0 :=
  congrArg Subtype.val ((polyRegLin N x).map_zero)

/-- Translation invariance: `(Q_t (· - x)^τ)(z) = (Q_t (·)^τ)(z - x)`. -/
theorem polyReg_shift (x : ParabolicSpace) (τ : PolyIndex N → ℝ) {t : ℝ} (ht : 0 < t)
    (z : ParabolicSpace) : polyReg x τ t z = polyReg 0 τ t (z - x) := by
  rw [polyReg_of_pos x τ ht, polyReg_of_pos 0 τ ht]
  simp only [RegularisingSemigroup.apply, parabolicSemigroup]
  have e : ∀ y : ParabolicSpace, parabolicKernel t (z - y) * polyEval x τ y =
      (fun w => parabolicKernel t (z - x - w) * polyEval 0 τ w) (y - x) := by
    intro y
    simp only [polyEval, sub_zero, sub_sub_sub_cancel_right]
  simp_rw [e]
  rw [Measure.volume_eq_prod]
  exact integral_sub_right_eq_self (fun w : ParabolicSpace =>
    parabolicKernel t (z - x - w) * polyEval 0 τ w) x

/-- The model: the polynomial model on the polynomial block, `Π_x Ξ = Π_x IΞ = 0`. -/
def blockModel (N : ℕ) : Model (blockStructure N) parabolicSemigroup where
  pi x := (polyRegLin N x).comp (LinearMap.funLeft ℝ ℝ Sum.inl)
  gamma := blockGamma N
  pi_gamma x y τ := by
    refine Subtype.ext ?_
    change polyReg x (blockTranslate (parabolicCoords (x - y)) τ ∘ Sum.inl) =
      polyReg y (τ ∘ Sum.inl)
    rw [blockTranslate_comp_inl]
    funext t z
    by_cases ht : 0 < t
    · rw [polyReg_of_pos _ _ ht, polyReg_of_pos _ _ ht]
      have : polyEval x (polyTranslate (parabolicCoords (x - y)) (τ ∘ Sum.inl)) =
          polyEval y (τ ∘ Sum.inl) :=
        funext (polyEval_polyTranslate x y _)
      rw [this]
    · simp [polyReg_of_nonpos _ _ (not_lt.1 ht)]
  gamma_self x := by
    refine Subtype.ext (Units.ext ?_)
    change (blockTranslate (parabolicCoords (x - x)) : (Idx N → ℝ) →ₗ[ℝ] (Idx N → ℝ)) = _
    have : parabolicCoords (x - x) = 0 := by
      funext i; fin_cases i <;> simp [parabolicCoords]
    rw [this, blockTranslate_zero]
    rfl
  gamma_mul x y z := by
    refine Subtype.ext (Units.ext ?_)
    change (blockTranslate (parabolicCoords (x - y)) ∘ₗ blockTranslate (parabolicCoords (y - z)) :
      (Idx N → ℝ) →ₗ[ℝ] (Idx N → ℝ)) = blockTranslate (parabolicCoords (x - z))
    rw [blockTranslate_add, ← parabolicCoords_add]
    congr 2
    abel
  measurable_diag i t ht := by
    have : (fun x => (((polyRegLin N x).comp (LinearMap.funLeft ℝ ℝ Sum.inl)
        (Pi.single i 1 : Idx N → ℝ) : parabolicSemigroup.distributions) :
          ℝ → ParabolicSpace → ℝ) t x) =
        fun _ => polyReg 0 ((Pi.single i 1 : Idx N → ℝ) ∘ Sum.inl) t 0 :=
      funext fun x => polyReg_diag x _ ht
    rw [this]
    exact measurable_const
  measurable_pi x i t ht := by
    change Measurable (polyReg x ((Pi.single i 1 : Idx N → ℝ) ∘ Sum.inl) t)
    rw [polyReg_of_pos x _ ht]
    exact parabolicSemigroup.measurable_apply t (measurable_polyEval x _)

theorem blockModel_regPi (x : ParabolicSpace) (τ : Idx N → ℝ) :
    (blockModel N).regPi x τ = polyReg x (τ ∘ Sum.inl) := rfl

theorem blockModel_gammaMap (x y : ParabolicSpace) :
    (blockModel N).gammaMap x y = blockTranslate (parabolicCoords (x - y)) := rfl

/-- `Π_x` vanishes on vectors with no polynomial component, in particular on `Ξ` and `IΞ`. -/
theorem blockModel_regPi_of_comp_inl {τ : Idx N → ℝ} (hτ : τ ∘ Sum.inl = 0) (x : ParabolicSpace) :
    (blockModel N).regPi x τ = 0 := by
  rw [blockModel_regPi, hτ, polyReg_zero]

/-! ## The model bounds -/

theorem blockModel_piBoundOn (N : ℕ) (γ : ℝ) :
    (blockModel N).PiBoundOn γ (polyPiConst N) univ := by
  intro i _ t ht x _
  have hC0 : 0 ≤ polyPiConst N := Finset.sum_nonneg fun k _ => parabolicMomentConst_nonneg _
  cases i with
  | inl k =>
    rw [blockModel_regPi, single_inl_comp_inl]
    have h := abs_polyReg_single_le k ht.1 x
    have hC : parabolicMomentConst (polyDeg N k) ≤ polyPiConst N :=
      Finset.single_le_sum (f := fun k : PolyIndex N => parabolicMomentConst (polyDeg N k))
        (fun j _ => parabolicMomentConst_nonneg _) (Finset.mem_univ k)
    exact h.trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg ht.1.le _))
  | inr m =>
    rw [blockModel_regPi_of_comp_inl (single_inr_comp_inl m 1)]
    simpa using mul_nonneg hC0 (Real.rpow_nonneg ht.1.le _)

/-- The constant of `blockModel_gammaBoundOn`. -/
def blockGammaConst (N : ℕ) : ℝ := max (Classical.choose (polyTranslate_single_le N)) 0

theorem blockModel_gammaBoundOn (N : ℕ) (γ : ℝ) :
    (blockModel N).GammaBoundOn γ (blockGammaConst N) univ := by
  intro i j _ hj x _ y _
  have hd : 0 ≤ parabolicSemigroup.scaleDist y x ^
      ((blockStructure N).deg i - (blockStructure N).deg j) :=
    Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg y x) _
  have h0 : 0 ≤ blockGammaConst N * parabolicSemigroup.scaleDist y x ^
      ((blockStructure N).deg i - (blockStructure N).deg j) := mul_nonneg (le_max_right _ _) hd
  rw [blockModel_gammaMap]
  cases i with
  | inl k =>
    cases j with
    | inl l =>
      rw [blockTranslate_inl, single_inl_comp_inl]
      exact (Classical.choose_spec (polyTranslate_single_le N) (y - x) k l hj).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)
    | inr m =>
      rw [blockTranslate_inr]
      simpa using h0
  | inr m =>
    rw [blockTranslate_of_comp_inl (single_inr_comp_inl m 1)]
    have hne : j ≠ Sum.inr m := by
      rintro rfl
      exact lt_irrefl _ hj
    simpa [Pi.single_apply, hne] using h0

/-! ## The sectors and the integration map -/

/-- The polynomial block as a polynomial sector. -/
def blockSector (N : ℕ) : PolynomialSector (blockStructure N) N where
  emb := Sum.inl
  emb_injective := Sum.inl_injective
  deg_emb _ := rfl
  invariant g hg τ hτ i hi := by
    obtain ⟨h, hh⟩ := blockGroup_val hg
    rw [hh]
    cases i with
    | inl k => exact absurd ⟨k, rfl⟩ hi
    | inr m => exact hτ _ hi

/-- The sector `V = ℝ Ξ`. -/
def xiSector (N : ℕ) : Submodule ℝ (Idx N → ℝ) where
  carrier := {τ | ∀ i, i ≠ Sum.inr 0 → τ i = 0}
  add_mem' {τ σ} hτ hσ i hi := by simp [hτ i hi, hσ i hi]
  zero_mem' _ _ := rfl
  smul_mem' c τ hτ i hi := by simp [hτ i hi]

theorem single_xi_mem_xiSector : (Pi.single (Sum.inr 0) 1 : Idx N → ℝ) ∈ xiSector N := by
  intro i hi
  simp [hi]

theorem comp_inl_of_mem_xiSector {τ : Idx N → ℝ} (hτ : τ ∈ xiSector N) : τ ∘ Sum.inl = 0 :=
  funext fun k => hτ (Sum.inl k) (by simp)

/-- The abstract integration map `I τ = τ_Ξ IΞ`: `I Ξ = IΞ`, zero on the other basis vectors. -/
def xiIntegration (N : ℕ) : (Idx N → ℝ) →ₗ[ℝ] (Idx N → ℝ) :=
  (LinearMap.single ℝ (fun _ => ℝ) (Sum.inr 1)).comp (LinearMap.proj (Sum.inr 0))

theorem xiIntegration_apply (τ : Idx N → ℝ) :
    xiIntegration N τ = Pi.single (Sum.inr 1) (τ (Sum.inr 0)) := rfl

theorem xiIntegration_xi :
    xiIntegration N (Pi.single (Sum.inr 0) 1) = Pi.single (Sum.inr 1) 1 := by
  simp [xiIntegration_apply]

theorem xiIntegration_ne_zero : xiIntegration N ≠ 0 := by
  intro h
  have := congrFun (xiIntegration_xi (N := N)) (Sum.inr 1)
  rw [h] at this
  simp at this

theorem xiSector_ne_bot : xiSector N ≠ ⊥ := by
  intro h
  have := single_xi_mem_xiSector (N := N)
  rw [h, Submodule.mem_bot] at this
  have := congrFun this (Sum.inr 0)
  simp at this

theorem isSector_xiSector : (blockStructure N).IsSector (xiSector N) where
  graded α a ha i hi := by
    rw [homogeneousProj_apply, ha i hi, ite_self]
  invariant g hg a ha := by
    obtain ⟨h, hh⟩ := blockGroup_val hg
    rw [hh, blockTranslate_of_comp_inl (comp_inl_of_mem_xiSector ha)]
    exact ha

theorem isAbstractIntegration_xiIntegration :
    IsAbstractIntegration (blockSector N) (xiSector N) (xiIntegration N) 2 where
  pos := by norm_num
  map_homogeneous α a _ ha := by
    rw [xiIntegration_apply]
    by_cases h0 : a (Sum.inr 0) = 0
    · rw [h0, Pi.single_zero]
      exact Submodule.zero_mem _
    · have hα : α = -1 / 2 := by
        by_contra hne
        exact h0 (ha _ fun h => hne (by rw [← h]; rfl))
      intro i hi
      have hne : i ≠ Sum.inr 1 := by
        rintro rfl
        exact hi (by rw [hα]; norm_num [blockStructure, blockDeg, xiDeg])
      simp [hne]
  map_poly a _ ha := by
    rw [xiIntegration_apply, ha (Sum.inr 0) (by rintro ⟨k, hk⟩; cases hk), Pi.single_zero]
  comm g hg a _ := by
    obtain ⟨h, hh⟩ := blockGroup_val hg
    rw [hh, xiIntegration_apply, xiIntegration_apply, blockTranslate_inr,
      blockTranslate_of_comp_inl (single_inr_comp_inl 1 _), sub_self]
    exact Submodule.zero_mem _

/-! ## Realising the kernel -/

/-- The realised germ of `Π_x Ξ = 0` vanishes. -/
theorem realReg_xi (N₀ : ℕ) (x : ParabolicSpace) (t : ℝ) (z : ParabolicSpace) :
    realReg (blockModel N) N₀ x (Sum.inr 0) t z = 0 := by
  by_cases ht : 0 < t
  · rw [realReg_of_pos _ _ _ _ ht]
    have hg : realGerm (blockModel N) N₀ x (Sum.inr 0) = 0 := by
      funext y
      simp only [realGerm, blockModel_regPi_of_comp_inl (single_inr_comp_inl 0 1),
        Pi.zero_apply, RegularisingSemigroup.pairing, zero_mul, integral_zero]
      rw [tendsto_const_nhds.limUnder_eq, tsum_zero]
    simp [hg, RegularisingSemigroup.apply]
  · simp [realReg, ht]

theorem isRealising_blockModel (N₀ : ℕ) (γ : ℝ) :
    (blockModel N).IsRealising N₀ γ (blockSector N) (xiIntegration N) (xiSector N) where
  realises x i _ hi t _ z := by
    have hi0 : i = Sum.inr 0 := by
      by_contra hne
      have := hi i hne
      simp at this
    subst hi0
    rw [realReg_xi, xiIntegration_xi,
      blockModel_regPi_of_comp_inl (single_inr_comp_inl 1 1)]
    rfl
  poly x k t z := by
    change (blockModel N).regPi x (Pi.single (Sum.inl k) 1) t z = _
    rw [blockModel_regPi, single_inl_comp_inl]

/-! ## The hypotheses of Theorem 5.12 -/

theorem multiDeg_eq (k : Fin 4 →₀ ℕ) : multiDeg k = 2 * k 0 + k 1 + k 2 + k 3 :=
  weight_parabolicWeight k

theorem multiDeg_lt_of_lt {k : Fin 4 →₀ ℕ} (hk : (multiDeg k : ℝ) < 7 / 4 + 2) :
    multiDeg k < 4 := by
  have : (multiDeg k : ℝ) < 4 := by linarith
  exact_mod_cast this

theorem blockDeg_lt_imp (j : Idx N) (hj : blockDeg N j < 7 / 4) :
    -2 < blockDeg N j ∧ blockDeg N j + 2 < 7 / 4 + 2 := by
  refine ⟨?_, by linarith⟩
  cases j with
  | inl k =>
    have : (0 : ℝ) ≤ polyDeg N k := Nat.cast_nonneg _
    change -2 < polyDeg N k
    linarith
  | inr m => fin_cases m <;> norm_num [blockDeg, xiDeg]

/-- The block model, the polynomial sector `X^k`, the sector `V = ℝ Ξ` and the integration map
`I Ξ = IΞ` satisfy the standing hypotheses of Theorem 5.12 with `γ = 7/4`. -/
theorem schauderSetting_blockModel (N₀ : ℕ) {N : ℕ} (hN : 4 ≤ N) :
    SchauderSetting (blockModel N) N₀ (7 / 4) (blockSector N) (xiIntegration N) (xiSector N)
      (polyPiConst N) (blockGammaConst N) 1 where
  pos := by norm_num
  realising := isRealising_blockModel N₀ _
  integration := isAbstractIntegration_xiIntegration
  sector := isSector_xiSector
  basis_mem a ha j hj := by
    have : j = Sum.inr 0 := by
      by_contra hne
      exact hj (ha j hne)
    subst this
    exact single_xi_mem_xiSector
  deg_gt j hj := (blockDeg_lt_imp j hj).1
  piBound := blockModel_piBoundOn N _
  gammaBound := blockModel_gammaBoundOn N _
  piBound_nonneg := Finset.sum_nonneg fun k _ => parabolicMomentConst_nonneg _
  poly_large j hj k hk := by
    have := multiDeg_lt_of_lt (hk.trans (blockDeg_lt_imp j hj).2)
    omega
  poly_large' l hl := by
    have := multiDeg_lt_of_lt hl
    omega
  integration_poly a _ k := by
    change xiIntegration N a (Sum.inl k) = 0
    simp [xiIntegration_apply]
  entry_bound i j := by
    rw [xiIntegration_apply, Pi.single_apply, Pi.single_apply]
    split_ifs <;> norm_num

/-- `γ = 7/4` satisfies the non-integrality conditions of Theorem 5.12: `γ + 2 − |k|_𝔰 ∉ ℕ`, and
`|k|_𝔰 ≠ |Ξ| + 2 = 3/2`, `|k|_𝔰 ≠ |IΞ| + 2 = 7/2`. -/
theorem schauderNonIntegral_blockModel (N : ℕ) :
    SchauderNonIntegral (blockStructure N) (7 / 4) N (blockSector N) where
  nonint₁ k _ l h := by
    have h2 : (4 : ℝ) * ((multiDeg l + multiDeg k.1 : ℕ) : ℝ) = 15 := by push_cast; linarith
    norm_cast at h2
    omega
  nonint₂ k _ i hi _ h := by
    cases i with
    | inl l => exact hi ⟨l, rfl⟩
    | inr m =>
      fin_cases m
      · have h2 : (2 : ℝ) * (multiDeg k.1 : ℝ) = 3 := by
          rw [h]; norm_num [blockStructure, blockDeg, xiDeg]
        norm_cast at h2
        omega
      · have h2 : (2 : ℝ) * (multiDeg k.1 : ℝ) = 7 := by
          rw [h]; norm_num [blockStructure, blockDeg, xiDeg]
        norm_cast at h2
        omega

/-! ## Joint measurability and a modelled distribution -/

theorem isJointMeasurable_blockModel (N : ℕ) : (blockModel N).IsJointMeasurable := by
  intro i t ht
  have e : (fun p : ParabolicSpace × ParabolicSpace =>
      (blockModel N).regPi p.1 (Pi.single i 1) t p.2) =
      (fun w => polyReg 0 ((Pi.single i 1 : Idx N → ℝ) ∘ Sum.inl) t w) ∘
        fun p : ParabolicSpace × ParabolicSpace => p.2 - p.1 :=
    funext fun p => polyReg_shift p.1 _ ht p.2
  rw [e, polyReg_of_pos 0 _ ht]
  exact (parabolicSemigroup.measurable_apply t (measurable_polyEval 0 _)).comp
    (measurable_snd.sub measurable_fst)

/-- The constant modelled distribution `f(x) = Ξ`. -/
def xiConst (N : ℕ) : ParabolicSpace → Idx N → ℝ := fun _ => Pi.single (Sum.inr 0) 1

theorem xiConst_ne_zero : xiConst N ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) (Sum.inr 0)
  simp [xiConst] at this

theorem xiConst_mem_xiSector (x : ParabolicSpace) : xiConst N x ∈ xiSector N :=
  single_xi_mem_xiSector

theorem modelledBoundOn_xiConst (γ : ℝ) :
    (blockModel N).ModelledBoundOn γ 1 univ (xiConst N) := by
  refine ⟨fun x _ i _ => ?_, fun x _ y _ j _ => ?_⟩
  · simp only [xiConst, Pi.single_apply]
    split_ifs <;> norm_num
  · simp only [xiConst]
    rw [blockModel_gammaMap, blockTranslate_of_comp_inl (single_inr_comp_inl 0 1), sub_self, Pi.zero_apply, abs_zero]
    exact mul_nonneg zero_le_one (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg y x) _)

theorem xiConst_mem_modelledDistributions :
    xiConst N ∈ (blockModel N).modelledDistributions (7 / 4) := by
  refine ⟨measurable_const, fun _ => single_mem_lowerSubspace ?_ 1, 1,
    modelledBoundOn_xiConst _⟩
  norm_num [blockStructure, blockDeg, xiDeg]

/-- `7/4 + 2 = 15/4` is not a parabolic degree. -/
theorem multiDeg_ne (k : Fin 4 →₀ ℕ) : (multiDeg k : ℝ) ≠ 7 / 4 + 2 := by
  intro h
  have h2 : (4 : ℝ) * (multiDeg k : ℝ) = 15 := by rw [h]; norm_num
  norm_cast at h2
  omega

/-! ## The full hypothesis set and the two theorems -/

/-- The hypotheses of the multilevel Schauder theorems `Model.kGamma_mem_modelledDistributions`
and `Model.reconstruct_kGamma` are jointly satisfiable with `N' ≤ N`, a nonzero sector `V`, an
integration map `I` that is nonzero on `V`, and a nonzero modelled distribution `f ∈ D^γ` with
values in `V`. -/
theorem schauderSetting_witness :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (𝒯 : RegularityStructure ι)
      (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (γ : ℝ) (N' : ℕ) (P : PolynomialSector 𝒯 N')
      (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ)) (CPi CGam CI : ℝ),
      SchauderSetting M N γ P I V CPi CGam CI ∧ M.IsJointMeasurable ∧
        SchauderNonIntegral 𝒯 γ N' P ∧ N' ≤ N ∧ (∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) ≠ γ + 2) ∧
        (∃ CPi' : ℝ, 0 ≤ CPi' ∧ M.PiBoundOn (γ + 2) CPi' univ) ∧
        V ≠ ⊥ ∧ I ≠ 0 ∧ (∃ a ∈ V, I a ≠ 0) ∧
        ∃ (f : ParabolicSpace → ι → ℝ) (Cf : ℝ), f ∈ M.modelledDistributions γ ∧
          M.ModelledBoundOn γ Cf univ f ∧ 0 ≤ Cf ∧ (∀ x, f x ∈ V) ∧ f ≠ 0 :=
  ⟨Idx 4, inferInstance, inferInstance, blockStructure 4, blockModel 4, 4, 7 / 4, 4,
    blockSector 4, xiIntegration 4, xiSector 4, _, _, _, schauderSetting_blockModel 4 le_rfl,
    isJointMeasurable_blockModel 4, schauderNonIntegral_blockModel 4, le_rfl, multiDeg_ne,
    ⟨_, Finset.sum_nonneg fun k _ => parabolicMomentConst_nonneg _,
      blockModel_piBoundOn 4 _⟩,
    xiSector_ne_bot, xiIntegration_ne_zero,
    ⟨_, single_xi_mem_xiSector, by
      rw [xiIntegration_xi]
      intro h
      have := congrFun h (Sum.inr 1)
      simp at this⟩,
    xiConst 4, 1, xiConst_mem_modelledDistributions, modelledBoundOn_xiConst _, zero_le_one,
    xiConst_mem_xiSector, xiConst_ne_zero⟩

/-- [Hai14, Theorem 5.12] applied to the block model and `f(x) = Ξ`: `𝒦_γ f ∈ D^{γ+2}`. -/
theorem kGamma_xiConst_mem_modelledDistributions {N : ℕ} (hN : 4 ≤ N) :
    (fun x => kGamma (blockModel N) N (blockSector N) (xiIntegration N) (7 / 4)
      (xiConst N) x) ∈ (blockModel N).modelledDistributions (7 / 4 + 2) := by
  have S := schauderSetting_blockModel N hN
  obtain ⟨c, -, hc⟩ := Model.kGamma_mem_modelledDistributions S.pos S.deg_gt N (blockSector N)
    le_rfl (schauderNonIntegral_blockModel N)
  exact (hc (blockModel N) (xiIntegration N) (xiSector N) S (isJointMeasurable_blockModel N)
    xiConst_mem_modelledDistributions (modelledBoundOn_xiConst _) zero_le_one
    xiConst_mem_xiSector).1

/-- [Hai14, Theorem 5.12, (5.17)] applied to the block model and `f(x) = Ξ`:
`ℛ 𝒦_γ f = K * ℛ f`. -/
theorem reconstruct_kGamma_xiConst {N : ℕ} (hN : 4 ≤ N) :
    (blockModel N).reconstruct (fun x => kGamma (blockModel N) N (blockSector N)
      (xiIntegration N) (7 / 4) (xiConst N) x) =
      fun t z => if 0 < t then
        parabolicSemigroup.apply t (kConv N ((blockModel N).reconstruct (xiConst N))) z else 0 :=
  Model.reconstruct_kGamma (schauderSetting_blockModel N hN) le_rfl
    (schauderNonIntegral_blockModel N) multiDeg_ne (isJointMeasurable_blockModel N)
    (blockModel_piBoundOn N _) (Finset.sum_nonneg fun _ _ => parabolicMomentConst_nonneg _)
    xiConst_mem_modelledDistributions (modelledBoundOn_xiConst _) zero_le_one xiConst_mem_xiSector

end RegularityStructures.SchauderWitness

end
