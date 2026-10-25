/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.Symbols
public import Mathlib.Data.Finsupp.Single
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The finite graded model space and structure group

The model space is the free real vector space on the finite symbol sector.  Its
product is the linear extension of the product table in `Phi43.Structure.Symbols`, with
unlisted products set to zero as in Hairer's construction after (8.4).

The structure-group action is defined on the primitive generators and on the
Taylor products by multiplication in this algebra.  Thus the formulas for
`XᵢΨ`, `XᵢXⱼ`, `XᵢΨ²`, and the products entering `U³` are derived from the
generator action; they are not an independently listed action table.  The
non-trivial parameter cocycle is the spatial Taylor term in the action of
`I(Ψ)Ψ` and `I(Ψ)Ψ²`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open scoped BigOperators

/-- The free model space on the finite symbol basis. -/
abbrev T : Type := Symbol →₀ ℝ

/-- The basis vector associated with a symbol. -/
def basis (τ : Symbol) : T := Finsupp.single τ 1

/-- The bilinear basis product, with absent finite products equal to zero. -/
def basisProduct (a b : Symbol) : T :=
  match productSymbol a b with
  | some c => basis c
  | none => 0

/-- The bilinear product on `T`, obtained by linear extension of `basisProduct`. -/
def basisProductLinear (a : Symbol) : T →ₗ[ℝ] T :=
  Finsupp.linearCombination ℝ (fun b => basisProduct a b)

def multiply (v w : T) : T :=
  Finsupp.linearCombination ℝ (fun a => basisProductLinear a w) v

instance mulT : Mul T := ⟨multiply⟩

@[simp]
theorem basisProduct_eq (a b : Symbol) : basisProduct a b =
    match productSymbol a b with
    | some c => basis c
    | none => 0 := by
  rfl

@[simp]
theorem multiply_basis (a b : Symbol) : basis a * basis b = basisProduct a b := by
  change Finsupp.linearCombination ℝ (fun a => basisProductLinear a (basis b))
    (Finsupp.single a 1) = basisProduct a b
  rw [Finsupp.linearCombination_single]
  simp [basisProductLinear, basis]

@[simp]
theorem multiply_zero_left (v : T) : 0 * v = 0 := by
  change Finsupp.linearCombination ℝ (fun a => basisProductLinear a v) 0 = 0
  exact (Finsupp.linearCombination ℝ (fun a => basisProductLinear a v)).map_zero

@[simp]
theorem multiply_zero_right (v : T) : v * 0 = 0 := by
  change Finsupp.linearCombination ℝ (fun a => basisProductLinear a 0) v = 0
  have h : (fun a => basisProductLinear a 0) = (fun _ : Symbol => 0) := by
    funext a
    exact (basisProductLinear a).map_zero
  rw [h]
  exact Finsupp.linearCombination_zero_apply ℝ v

theorem multiply_add_left (v w z : T) : (v + w) * z = v * z + w * z := by
  change Finsupp.linearCombination ℝ (fun a => basisProductLinear a z) (v + w) = _
  exact (Finsupp.linearCombination ℝ (fun a => basisProductLinear a z)).map_add v w

theorem multiply_add_right (v w z : T) : v * (w + z) = v * w + v * z := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w ihv ihw =>
      simp only [multiply_add_left, ihv, ihw, add_add_add_comm]
  | single a r =>
      change multiply (Finsupp.single a r) (w + z) =
        multiply (Finsupp.single a r) w + multiply (Finsupp.single a r) z
      change Finsupp.linearCombination ℝ (fun a => basisProductLinear a (w + z))
          (Finsupp.single a r) =
        Finsupp.linearCombination ℝ (fun a => basisProductLinear a w)
            (Finsupp.single a r) +
          Finsupp.linearCombination ℝ (fun a => basisProductLinear a z)
            (Finsupp.single a r)
      rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single,
        Finsupp.linearCombination_single]
      rw [(basisProductLinear a).map_add, smul_add]

theorem multiply_sum_right {α : Type*} (s : Finset α) (v : T) (w : α → T) :
    v * ∑ i ∈ s, w i = ∑ i ∈ s, v * w i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, multiply_add_right, ih]

theorem multiply_sum_left {α : Type*} (s : Finset α) (v : T) (w : α → T) :
    (∑ i ∈ s, w i) * v = ∑ i ∈ s, w i * v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, multiply_add_left, ih]

theorem multiply_fintype_sum_left {α : Type*} [Fintype α] (v : T) (w : α → T) :
    (∑ i, w i) * v = ∑ i, w i * v := by
  simpa using multiply_sum_left (Finset.univ : Finset α) v w

theorem multiply_smul_left (r : ℝ) (v w : T) : (r • v) * w = r • (v * w) := by
  change Finsupp.linearCombination ℝ (fun a => basisProductLinear a w) (r • v) = _
  exact (Finsupp.linearCombination ℝ (fun a => basisProductLinear a w)).map_smul r v

theorem multiply_smul_right (r : ℝ) (v w : T) : v * (r • w) = r • (v * w) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w ihv ihw =>
      simp only [multiply_add_left, ihv, ihw, smul_add]
  | single a s =>
      change multiply (Finsupp.single a s) (r • w) =
        r • multiply (Finsupp.single a s) w
      change Finsupp.linearCombination ℝ (fun a => basisProductLinear a (r • w))
          (Finsupp.single a s) =
        r • Finsupp.linearCombination ℝ (fun a => basisProductLinear a w)
          (Finsupp.single a s)
      rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
      rw [(basisProductLinear a).map_smul, smul_smul, smul_smul, mul_comm]

theorem multiply_neg_left (v w : T) : (-v) * w = -(v * w) := by
  rw [← neg_one_smul ℝ v, multiply_smul_left, neg_one_smul]

theorem multiply_neg_right (v w : T) : v * (-w) = -(v * w) := by
  rw [← neg_one_smul ℝ w, multiply_smul_right, neg_one_smul]

attribute [simp] multiply_add_left multiply_add_right multiply_smul_left multiply_smul_right
  multiply_neg_left multiply_neg_right

@[simp]
theorem multiply_single (a b : Symbol) (r s : ℝ) :
    Finsupp.single a r * Finsupp.single b s = (r * s) • basisProduct a b := by
  calc
    Finsupp.single a r * Finsupp.single b s =
        (r • basis a) * (s • basis b) := by
          change Finsupp.single a r * Finsupp.single b s =
            (r • Finsupp.single a 1) * (s • Finsupp.single b 1)
          rw [Finsupp.smul_single_one, Finsupp.smul_single_one]
    _ = r • (s • (basis a * basis b)) := by
      rw [multiply_smul_left, multiply_smul_right]
    _ = (r * s) • basisProduct a b := by
      rw [multiply_basis, smul_smul]

@[simp]
theorem multiply_one_left (v : T) : basis .one * v = v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w ihv ihw => rw [multiply_add_right, ihv, ihw]
  | single a r =>
      rw [← Finsupp.smul_single_one, multiply_smul_right]
      change r • (basis .one * basis a) = r • basis a
      rw [multiply_basis]
      cases a <;> rfl

@[simp]
theorem multiply_one_right (v : T) : v * basis .one = v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w ihv ihw => rw [multiply_add_left, ihv, ihw]
  | single a r =>
      rw [← Finsupp.smul_single_one, multiply_smul_left]
      change r • (basis a * basis .one) = r • basis a
      rw [multiply_basis]
      cases a <;> rfl

/-- A polynomial shift together with the positive Taylor characters which
occur in the finite sector.  The `cPsi` character is the constant Taylor
coefficient of `J(Ψ)`, while `cPsiGrad` stores the independent spatial
coefficients of `J_i(Ψ)`; the positive symbol `I(Ψ)` is retained. -/
structure StructureParameters where
  shift : Fin 4 → ℝ
  cPsi : ℝ
  cPsiGrad : Fin 3 → ℝ
  cPsiSq : ℝ
  cPsiCube : ℝ

abbrev G := StructureParameters

instance : Zero StructureParameters :=
  ⟨0, 0, 0, 0, 0⟩

@[simp]
theorem zero_shift (i : Fin 4) : (0 : G).shift i = 0 := rfl

@[simp]
theorem zero_cPsi : (0 : G).cPsi = 0 := rfl

@[simp]
theorem zero_cPsiGrad (i : Fin 3) : (0 : G).cPsiGrad i = 0 := rfl

@[simp]
theorem zero_cPsiSq : (0 : G).cPsiSq = 0 := rfl

@[simp]
theorem zero_cPsiCube : (0 : G).cPsiCube = 0 := rfl

/-- Composition of structure-group parameters. -/
def structureGroupMul (g h : G) : G :=
  { shift := g.shift + h.shift
    cPsi := g.cPsi + h.cPsi + ∑ i : Fin 3, g.shift i.succ * h.cPsiGrad i
    cPsiGrad := g.cPsiGrad + h.cPsiGrad
    cPsiSq := g.cPsiSq + h.cPsiSq
    cPsiCube := g.cPsiCube + h.cPsiCube }

instance : Mul G := ⟨structureGroupMul⟩

@[simp]
theorem structureGroupMul_shift (g h : G) : (g * h).shift = g.shift + h.shift := rfl

@[simp]
theorem structureGroupMul_cPsi (g h : G) :
    (g * h).cPsi = g.cPsi + h.cPsi + ∑ i : Fin 3, g.shift i.succ * h.cPsiGrad i := rfl

@[simp]
theorem structureGroupMul_cPsiGrad (g h : G) :
    (g * h).cPsiGrad = g.cPsiGrad + h.cPsiGrad := rfl

@[simp]
theorem structureGroupMul_cPsiSq (g h : G) :
    (g * h).cPsiSq = g.cPsiSq + h.cPsiSq := rfl

@[simp]
theorem structureGroupMul_cPsiCube (g h : G) :
    (g * h).cPsiCube = g.cPsiCube + h.cPsiCube := rfl

/-- The inverse parameter, including the Taylor cocycle correction. -/
def structureGroupInv (g : G) : G :=
  { shift := -g.shift
    cPsi := -g.cPsi + ∑ i : Fin 3, g.shift i.succ * g.cPsiGrad i
    cPsiGrad := -g.cPsiGrad
    cPsiSq := -g.cPsiSq
    cPsiCube := -g.cPsiCube }

def primitiveAction (g : G) : Symbol → T
  | .one => basis .one
  | .noise => basis .noise
  | .x0 => basis .x0 + g.shift 0 • basis .one
  | .x i => basis (.x i) + g.shift i.succ • basis .one
  | .psi => basis .psi
  | .iPsi => basis .iPsi + g.cPsi • basis .one +
      ∑ i : Fin 3, g.cPsiGrad i • basis (.x i)
  | .iPsiSq => basis .iPsiSq + g.cPsiSq • basis .one
  | .iPsiCube => basis .iPsiCube + g.cPsiCube • basis .one
  | _ => 0

/-- Taylor expansion of the two products containing the positive coefficient
`I(Ψ)`.  Since `|I(Ψ)|=3/2-κ<2`, only the constant and spatial linear Taylor
terms occur. -/
def integratedPsiProductAction (g : G) : Bool → T
  | false => basis .iPsiPsi + g.cPsi • basis .psi +
      ∑ i : Fin 3, g.cPsiGrad i • basis (.psiX i)
  | true => basis .iPsiPsiSq + g.cPsi • basis .psiSq +
      ∑ i : Fin 3, g.cPsiGrad i • basis (.psiSqX i)

/-- The multiplicative action on a commutative quadratic polynomial monomial. -/
def xMulAction (g : G) : Sym2 (Fin 3) → T :=
  Sym2.lift ⟨fun i j => primitiveAction g (.x i) * primitiveAction g (.x j), by
    intro i j
    simp [primitiveAction, multiply_basis, basisProduct, productSymbol,
      Sym2.sound (Sym2.Rel.swap i j)]
    module⟩

@[simp]
theorem xMulAction_mk (g : G) (i j : Fin 3) :
    xMulAction g s(i, j) = primitiveAction g (.x i) * primitiveAction g (.x j) := by
  rfl

@[simp]
theorem xMulAction_zero (p : Sym2 (Fin 3)) : xMulAction 0 p = basis (.xMul p) := by
  induction p using Sym2.inductionOn with
  | _ i j =>
      simp [xMulAction, primitiveAction, multiply_basis, basisProduct, productSymbol]

/-- The structure-group action on basis symbols, derived from primitive action
and the product in `T`. -/
def structureBasisAction (g : G) : Symbol → T
  | .one => primitiveAction g .one
  | .noise => primitiveAction g .noise
  | .x0 => primitiveAction g .x0
  | .x i => primitiveAction g (.x i)
  | .xMul p => xMulAction g p
  | .psi => primitiveAction g .psi
  | .iPsi => primitiveAction g .iPsi
  | .psiSq => primitiveAction g .psi * primitiveAction g .psi
  | .psiCube => (primitiveAction g .psi * primitiveAction g .psi) * primitiveAction g .psi
  | .psiX i => primitiveAction g .psi * primitiveAction g (.x i)
  | .psiSqX i => primitiveAction g (.x i) *
      (primitiveAction g .psi * primitiveAction g .psi)
  | .iPsiSq => primitiveAction g .iPsiSq
  | .iPsiCube => primitiveAction g .iPsiCube
  | .iPsiPsi => integratedPsiProductAction g false
  | .iPsiPsiSq => integratedPsiProductAction g true
  | .iPsiSqPsi => primitiveAction g .iPsiSq * primitiveAction g .psi
  | .iPsiSqPsiSq => primitiveAction g .iPsiSq *
      (primitiveAction g .psi * primitiveAction g .psi)
  | .iPsiCubePsi => primitiveAction g .iPsiCube * primitiveAction g .psi
  | .iPsiCubePsiSq => primitiveAction g .iPsiCube *
      (primitiveAction g .psi * primitiveAction g .psi)
  | .iPsiCubeSq => primitiveAction g .iPsiCube * primitiveAction g .iPsiCube

@[simp]
theorem structureBasisAction_zero (τ : Symbol) :
    structureBasisAction 0 τ = basis τ := by
  cases τ <;>
    simp [structureBasisAction, primitiveAction, integratedPsiProductAction,
      multiply_single, basisProduct, productSymbol, basis]

/-- The linear structure-group map. -/
def structureGroupMap (g : G) : T →ₗ[ℝ] T :=
  Finsupp.linearCombination ℝ (structureBasisAction g)

@[simp]
theorem structureGroupMap_basis (g : G) (τ : Symbol) :
    structureGroupMap g (basis τ) = structureBasisAction g τ := by
  simp [structureGroupMap, basis]

@[simp]
theorem structureGroupMap_single (g : G) (τ : Symbol) (r : ℝ) :
    structureGroupMap g (Finsupp.single τ r) = r • structureBasisAction g τ := by
  simp [structureGroupMap]

theorem structureGroup_one (g : G) :
    structureGroupMap g (basis .one) = basis .one := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction]

/-- The product action is multiplicative on every explicitly retained basis
product. -/
theorem structureGroupMap_product (g : G) (a b c : Symbol)
    (h : productSymbol a b = some c) :
    structureGroupMap g (basis c) =
      structureGroupMap g (basis a) * structureGroupMap g (basis b) := by
  cases a <;> cases b <;> simp [productSymbol] at h ⊢
  all_goals subst c
  all_goals
    simp [structureBasisAction, primitiveAction,
      integratedPsiProductAction,
      multiply_one_right, multiply_add_left, multiply_add_right,
      multiply_smul_left, multiply_smul_right, multiply_basis, basisProduct,
      productSymbol, multiply_sum_right]
  all_goals
    first | rw [multiply_fintype_sum_right] | rw [multiply_fintype_sum_left]
    simp [multiply_basis, basisProduct, productSymbol]

theorem structureGroupMap_zero : structureGroupMap 0 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro τ r
  simp [structureGroupMap_single, structureBasisAction_zero, basis]

theorem structureBasisAction_comp (g h : G) (τ : Symbol) :
    structureGroupMap g (structureBasisAction h τ) =
      structureBasisAction (g * h) τ := by
  cases τ <;>
    simp [structureBasisAction, primitiveAction,
      integratedPsiProductAction,
      multiply_one_right, multiply_add_left,
      multiply_add_right, multiply_smul_left, multiply_smul_right,
      multiply_basis, basisProduct, productSymbol]
  case xMul p =>
    induction p using Sym2.inductionOn with
    | _ i j =>
        simp [xMulAction, structureBasisAction, primitiveAction,
          basisProduct, productSymbol, basis]
        abel_nf
        simp [mul_comm]
        rw [add_comm]
  all_goals
    try simp only [Finset.sum_add_distrib, smul_add, smul_smul,
      mul_comm, add_smul]
  all_goals
    try rw [← Finset.sum_smul]
  all_goals try abel_nf
  all_goals try module

theorem structureGroupMap_comp (g h : G) :
    (structureGroupMap g).comp (structureGroupMap h) =
      structureGroupMap (g * h) := by
  apply Finsupp.lhom_ext
  intro τ r
  rw [← Finsupp.smul_single_one, map_smul, map_smul]
  change r • structureGroupMap g (structureGroupMap h (basis τ)) =
    r • structureGroupMap (g * h) (basis τ)
  rw [structureGroupMap_basis, structureBasisAction_comp, structureGroupMap_basis]

theorem structureGroupInv_mul (g : G) : structureGroupInv g * g = 0 := by
  cases g with
  | mk shift cPsi cPsiGrad cPsiSq cPsiCube =>
      change
        (⟨-shift + shift,
          (-cPsi + ∑ i : Fin 3, shift i.succ * cPsiGrad i) + cPsi +
            ∑ i : Fin 3, (-shift) i.succ * cPsiGrad i,
          -cPsiGrad + cPsiGrad,
          -cPsiSq + cPsiSq, -cPsiCube + cPsiCube⟩ : G) = (0 : G)
      congr
      · funext i
        simp
      · simp
      · funext i
        simp
      · simp
      · simp

theorem structureGroupMap_inverse (g : G) :
    (structureGroupMap (structureGroupInv g)).comp (structureGroupMap g) =
      LinearMap.id := by
  rw [structureGroupMap_comp]
  rw [structureGroupInv_mul, structureGroupMap_zero]

def strictlyLower (κ : Kappa) (τ : Symbol) (v : T) : Prop :=
  ∀ σ, v σ ≠ 0 → homogeneity κ σ < homogeneity κ τ

theorem structureGroup_triangular_one (κ : Kappa) (g : G) :
    strictlyLower κ .one (structureGroupMap g (basis .one) - basis .one) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, basis] at hσ ⊢

theorem structureGroup_triangular_noise (κ : Kappa) (g : G) :
    strictlyLower κ .noise (structureGroupMap g (basis .noise) - basis .noise) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, basis] at hσ ⊢

theorem structureGroup_triangular_x0 (κ : Kappa) (g : G) :
    strictlyLower κ .x0 (structureGroupMap g (basis .x0) - basis .x0) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, basis, homogeneity] at hσ ⊢

theorem structureGroup_triangular_x (κ : Kappa) (g : G) (i : Fin 3) :
    strictlyLower κ (.x i) (structureGroupMap g (basis (.x i)) - basis (.x i)) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, basis, homogeneity] at hσ ⊢

theorem structureGroup_triangular_xMul (κ : Kappa) (g : G)
    (p : Sym2 (Fin 3)) :
    strictlyLower κ (.xMul p)
      (structureGroupMap g (basis (.xMul p)) - basis (.xMul p)) := by
  induction p using Sym2.inductionOn with
  | _ i j =>
      rw [structureGroupMap_basis]
      unfold strictlyLower
      intro σ hσ
      cases σ <;>
        simp [structureBasisAction, xMulAction_mk, primitiveAction,
          basisProduct, productSymbol, basis, homogeneity] at hσ ⊢

theorem structureGroup_triangular_psi (κ : Kappa) (g : G) :
    strictlyLower κ .psi (structureGroupMap g (basis .psi) - basis .psi) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, basis] at hσ ⊢

theorem structureGroup_triangular_iPsi (κ : Kappa) (g : G) :
    strictlyLower κ .iPsi
      (structureGroupMap g (basis .iPsi) - basis .iPsi) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, basis, homogeneity] at hσ ⊢
  all_goals
    have hk₀ : κ.1 < 1 / 16 := by
      simpa [kappa₀] using kappa_lt_kappa₀ κ
    linarith

theorem structureGroup_triangular_psiSq (κ : Kappa) (g : G) :
    strictlyLower κ .psiSq (structureGroupMap g (basis .psiSq) - basis .psiSq) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, multiply_single,
      basisProduct, productSymbol, basis] at hσ ⊢

theorem structureGroup_triangular_psiCube (κ : Kappa) (g : G) :
    strictlyLower κ .psiCube
      (structureGroupMap g (basis .psiCube) - basis .psiCube) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, multiply_single,
      basisProduct, productSymbol, basis] at hσ ⊢

theorem structureGroup_triangular_psiX (κ : Kappa) (g : G) (i : Fin 3) :
    strictlyLower κ (.psiX i)
      (structureGroupMap g (basis (.psiX i)) - basis (.psiX i)) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, multiply_single,
      multiply_add_right, basisProduct, productSymbol, basis, homogeneity] at hσ ⊢
  all_goals
    have hk₀ : κ.1 < 1 / 16 := by
      simpa [kappa₀] using kappa_lt_kappa₀ κ
    linarith

theorem structureGroup_triangular_psiSqX (κ : Kappa) (g : G) (i : Fin 3) :
    strictlyLower κ (.psiSqX i)
      (structureGroupMap g (basis (.psiSqX i)) - basis (.psiSqX i)) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, multiply_single,
      multiply_add_left, basisProduct, productSymbol, basis, homogeneity] at hσ ⊢
  all_goals
    have hk₀ : κ.1 < 1 / 16 := by
      simpa [kappa₀] using kappa_lt_kappa₀ κ
    linarith

theorem structureGroup_triangular_iPsiSq (κ : Kappa) (g : G) :
    strictlyLower κ .iPsiSq
      (structureGroupMap g (basis .iPsiSq) - basis .iPsiSq) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, basis, homogeneity] at hσ ⊢
  all_goals
    have hk₀ : κ.1 < 1 / 16 := by
      simpa [kappa₀] using kappa_lt_kappa₀ κ
    linarith

theorem structureGroup_triangular_iPsiCube (κ : Kappa) (g : G) :
    strictlyLower κ .iPsiCube
      (structureGroupMap g (basis .iPsiCube) - basis .iPsiCube) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, basis, homogeneity] at hσ ⊢
  all_goals
    have hk₀ : κ.1 < 1 / 16 := by
      simpa [kappa₀] using kappa_lt_kappa₀ κ
    linarith

theorem structureGroup_triangular_iPsiPsi (κ : Kappa) (g : G) :
    strictlyLower κ .iPsiPsi
      (structureGroupMap g (basis .iPsiPsi) - basis .iPsiPsi) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, integratedPsiProductAction,
      basis, homogeneity] at hσ ⊢
  all_goals
    have hk₀ : κ.1 < 1 / 16 := by
      simpa [kappa₀] using kappa_lt_kappa₀ κ
    linarith

theorem structureGroup_triangular_iPsiPsiSq (κ : Kappa) (g : G) :
    strictlyLower κ .iPsiPsiSq
      (structureGroupMap g (basis .iPsiPsiSq) - basis .iPsiPsiSq) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, integratedPsiProductAction,
      basis, homogeneity] at hσ ⊢
  all_goals
    have hk₀ : κ.1 < 1 / 16 := by
      simpa [kappa₀] using kappa_lt_kappa₀ κ
    linarith

theorem structureGroup_triangular_iPsiSqPsi (κ : Kappa) (g : G) :
    strictlyLower κ .iPsiSqPsi
      (structureGroupMap g (basis .iPsiSqPsi) - basis (.iPsiSqPsi)) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, multiply_single,
      basisProduct, productSymbol, basis, homogeneity] at hσ ⊢
  all_goals
    have hk₀ : κ.1 < 1 / 16 := by
      simpa [kappa₀] using kappa_lt_kappa₀ κ
    linarith

theorem structureGroup_triangular_iPsiSqPsiSq (κ : Kappa) (g : G) :
    strictlyLower κ .iPsiSqPsiSq
      (structureGroupMap g (basis .iPsiSqPsiSq) - basis (.iPsiSqPsiSq)) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, multiply_single,
      basisProduct, productSymbol, basis, homogeneity] at hσ ⊢
  all_goals
    have hk₀ : κ.1 < 1 / 16 := by
      simpa [kappa₀] using kappa_lt_kappa₀ κ
    linarith

theorem structureGroup_triangular_iPsiCubePsi (κ : Kappa) (g : G) :
    strictlyLower κ .iPsiCubePsi
      (structureGroupMap g (basis .iPsiCubePsi) - basis (.iPsiCubePsi)) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, multiply_single,
      basisProduct, productSymbol, basis, homogeneity] at hσ ⊢
  all_goals
    have hk₀ : κ.1 < 1 / 16 := by
      simpa [kappa₀] using kappa_lt_kappa₀ κ
    linarith

theorem structureGroup_triangular_iPsiCubePsiSq (κ : Kappa) (g : G) :
    strictlyLower κ .iPsiCubePsiSq
      (structureGroupMap g (basis .iPsiCubePsiSq) - basis (.iPsiCubePsiSq)) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, multiply_single,
      basisProduct, productSymbol, basis, homogeneity] at hσ ⊢
  all_goals
    have hk₀ : κ.1 < 1 / 16 := by
      simpa [kappa₀] using kappa_lt_kappa₀ κ
    linarith

theorem structureGroup_triangular_iPsiCubeSq (κ : Kappa) (g : G) :
    strictlyLower κ .iPsiCubeSq
      (structureGroupMap g (basis .iPsiCubeSq) - basis (.iPsiCubeSq)) := by
  rw [structureGroupMap_basis]
  unfold strictlyLower
  intro σ hσ
  cases σ <;>
    simp [structureBasisAction, primitiveAction, basisProduct,
      productSymbol, basis, homogeneity] at hσ ⊢
  all_goals
    have hk₀ : κ.1 < 1 / 16 := by
      simpa [kappa₀] using kappa_lt_kappa₀ κ
    linarith

theorem structureGroup_triangular_basis (κ : Kappa) (g : G) (τ : Symbol) :
    strictlyLower κ τ (structureGroupMap g (basis τ) - basis τ) := by
  cases τ with
  | one => exact structureGroup_triangular_one κ g
  | noise => exact structureGroup_triangular_noise κ g
  | x0 => exact structureGroup_triangular_x0 κ g
  | x i => exact structureGroup_triangular_x κ g i
  | xMul p => exact structureGroup_triangular_xMul κ g p
  | psi => exact structureGroup_triangular_psi κ g
  | iPsi => exact structureGroup_triangular_iPsi κ g
  | psiSq => exact structureGroup_triangular_psiSq κ g
  | psiCube => exact structureGroup_triangular_psiCube κ g
  | psiX i => exact structureGroup_triangular_psiX κ g i
  | psiSqX i => exact structureGroup_triangular_psiSqX κ g i
  | iPsiSq => exact structureGroup_triangular_iPsiSq κ g
  | iPsiCube => exact structureGroup_triangular_iPsiCube κ g
  | iPsiPsi => exact structureGroup_triangular_iPsiPsi κ g
  | iPsiPsiSq => exact structureGroup_triangular_iPsiPsiSq κ g
  | iPsiSqPsi => exact structureGroup_triangular_iPsiSqPsi κ g
  | iPsiSqPsiSq => exact structureGroup_triangular_iPsiSqPsiSq κ g
  | iPsiCubePsi => exact structureGroup_triangular_iPsiCubePsi κ g
  | iPsiCubePsiSq => exact structureGroup_triangular_iPsiCubePsiSq κ g
  | iPsiCubeSq => exact structureGroup_triangular_iPsiCubeSq κ g

end RegularityStructures.Phi43

end
