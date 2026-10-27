module

public import GlobalPhi43.Attachment.DefectTests
public import Phi43.Structure.CanonicalSmoothGrowth
public import Phi43.BPHZ.CanonicalBridgeConvolution

/-! The three actual source defects, with realisation and polynomial growth attached. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43
open RegularityStructures.Potential RegularityStructures.Inhomogeneity GlobalPhi43.Local
open scoped ContDiff

/-- The whole renormalised input to each of the three source defects. -/
def defectInput (N : ℕ) (f : SpaceTime → ℝ) (C : RenormalisationConstants)
    (i : Fin 3) (z : ParabolicSpace) : ℝ :=
  ![f, treeV N f (C₁ C), treeW N f (C₁ C)] i (spaceTimeProj z)

/-- Source `r * f`, since `potQ` is `L R` and `r = -L R`. -/
def defectField (N : ℕ) (f : SpaceTime → ℝ) (C : RenormalisationConstants)
    (i : Fin 3) : ParabolicSpace → ℝ :=
  -potConv (defectInput N f C i) (potQ N)

/-- No model bound or renormalisation bound is needed for polynomial growth of these inputs. -/
theorem defectInput_regular {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z) (i : Fin 3) :
    Continuous (defectInput N f C i) ∧ PolyBounded (defectInput N f C i) := by
  obtain ⟨noise, hn, _⟩ := hZ
  obtain ⟨Cg, q, hgr⟩ := hg
  have he : noise.zeta = fun z => f (spaceTimeProj z) := funext hn
  have hg' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q := by
    rw [he]
    exact hgr
  have hp : PolyBounded (fun z => f (spaceTimeProj z)) := by
    rw [← he]
    exact canonicalNoise_polyBounded_of_derivatives noise Cg q hg'
  have hJ : PolyBounded (fun z => treeJ N f (spaceTimeProj z)) := by
    have h := polyBounded_hairerConvolution N hf hp
    have hj : hairerConvolution N (fun z => f (spaceTimeProj z)) =
        fun z => treeJ N f (spaceTimeProj z) := by
      funext z
      exact hairerConvolution_comp_proj_eq N (IsSmoothOnSpaceTime.continuous hf) z
    rw [← hj]
    exact h
  have hconst (a : ℝ) : PolyBounded (fun _ : ParabolicSpace => a) :=
    ⟨measurable_const, |a|, 0, fun _ => by simp⟩
  have hV : PolyBounded (fun z => treeV N f (C₁ C) (spaceTimeProj z)) := by
    simpa only [treeV, pow_two, Pi.mul_apply] using
      (canonicalPolyBounded_mul hJ hJ).sub (hconst (C₁ C))
  have hW : PolyBounded (fun z => treeW N f (C₁ C) (spaceTimeProj z)) := by
    have hcube := canonicalPolyBounded_mul (canonicalPolyBounded_mul hJ hJ) hJ
    simpa only [treeW, pow_succ, pow_zero, one_mul, Pi.mul_apply] using
      hcube.sub (hJ.const_mul (3 * C₁ C))
  fin_cases i
  · exact ⟨hf.continuous, hp⟩
  · exact ⟨(continuous_treeV hf _).comp continuous_spaceTimeProj, hV⟩
  · exact ⟨(continuous_treeW hf _).comp continuous_spaceTimeProj, hW⟩

/-- The actual source defects are smooth on the whole lifted space. -/
theorem defectField_smooth {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z) (i : Fin 3) :
    ContDiff ℝ ∞ (defectField N f C i) :=
  (contDiff_potConv (defectInput_regular hf hg hZ i).1 (contDiff_potQ N)
    (by simpa only [ddA] using hasCompactSupport_ddA_potQ N [])).neg

/-- Exact Q-realisations for noise, the whole V and the whole W. -/
theorem defectInput_realise {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z) (i : Fin 3)
    (x : ParabolicSpace) {u : ℝ} (hu : 0 < u) (y : ParabolicSpace) :
    Z.regPi x (Pi.single (![Symbol.noise, .psiSq, .psiCube] i) 1) u y =
      parabolicSemigroup.apply u (defectInput N f C i) y := by
  have h := realise hf hg hZ x hu y
  fin_cases i
  · exact h.1
  · exact h.2.2.1
  · exact h.2.2.2.1

end GlobalPhi43.Attachment
