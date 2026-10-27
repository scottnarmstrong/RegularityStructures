module

public import GlobalPhi43.Flow.SmoothDensity
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.UniformSpace.UniformEmbedding

public noncomputable section

open Set Metric RegularityStructures
open Filter Topology
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

/-- The actual closed state ball, with its inherited eta metric. -/
abbrev StateBall (η : NegExponent) (R : ℝ) := closedBall (0 : HolderBesov η) R

/-- Smooth states inside the same closed ball. -/
@[expose] def smoothBall (η : NegExponent) (R : ℝ) : Set (StateBall η R) :=
  {z | ∃ f : C(Torus3, ℝ), IsSmoothOnTorus f ∧ toHolderBesov η f = z.val}

theorem dense_smoothBall (η : NegExponent) (R : ℝ) : Dense (smoothBall η R) := by
  apply Metric.dense_iff.mpr
  intro z ε hε
  obtain ⟨f, hf, hR, hd⟩ := exists_smooth_approx_ball η z.val
    (by simpa only [mem_closedBall, dist_zero_right] using z.property) hε
  let w : StateBall η R := ⟨toHolderBesov η f, by simpa only [mem_closedBall,
    dist_zero_right] using hR⟩
  exact ⟨w, hd, ⟨f, hf, rfl⟩⟩

/-- A uniform local solution map on smooth data extends to the whole closed eta-ball. -/
theorem exists_ballExtension {η : NegExponent} {R : ℝ} {Y : Type*}
    [MetricSpace Y] [CompleteSpace Y] {K : ℝ≥0}
    (F : smoothBall η R → Y) (hF : LipschitzWith K F) :
    ∃ G : StateBall η R → Y, LipschitzWith K G ∧
      ∀ z : smoothBall η R, G z.val = F z := by
  let hs := dense_smoothBall η R
  exact ⟨hs.extend F, hs.lipschitzWith_extend hF,
    fun z => hs.extend_eq hF.continuous z⟩

/-- The two-lift estimate survives completion with its unchanged model-distance term. -/
theorem ballExtension_pair_bound {η : NegExponent} {R : ℝ} {Y : Type*}
    [MetricSpace Y] {K : ℝ≥0} {δ : ℝ≥0∞}
    {G H : StateBall η R → Y} (hG : Continuous G) (hH : Continuous H)
    (h : ∀ x y : smoothBall η R,
      edist (G x.val) (H y.val) ≤ K * (edist x.val y.val + δ)) :
    ∀ x y : StateBall η R, edist (G x) (H y) ≤ K * (edist x y + δ) := by
  have hc : IsClosed {p : StateBall η R × StateBall η R |
      edist (G p.1) (H p.2) ≤ K * (edist p.1 p.2 + δ)} :=
    isClosed_le ((hG.comp continuous_fst).edist (hH.comp continuous_snd))
      ((ENNReal.continuous_const_mul (by simp)).comp
        ((continuous_fst.edist continuous_snd).add continuous_const))
  have hd : Dense {p : StateBall η R × StateBall η R |
      edist (G p.1) (H p.2) ≤ K * (edist p.1 p.2 + δ)} :=
    ((dense_smoothBall η R).prod (dense_smoothBall η R)).mono (by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      exact h ⟨x, hx⟩ ⟨y, hy⟩)
  intro x y
  have hp := hd (x, y)
  rw [hc.closure_eq] at hp
  exact hp

/-- A continuous extension is uniquely determined by its smooth values. -/
theorem ballExtension_unique {η : NegExponent} {R : ℝ} {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] {G H : StateBall η R → Y}
    (hG : Continuous G) (hH : Continuous H)
    (h : ∀ z : smoothBall η R, G z.val = H z.val) : G = H := by
  apply funext
  have hc : IsClosed {z | G z = H z} := isClosed_eq hG hH
  have hd : Dense {z | G z = H z} := (dense_smoothBall η R).mono fun z hz => h ⟨z, hz⟩
  intro z
  have hz := hd z
  rw [hc.closure_eq] at hz
  exact hz

end GlobalPhi43.Flow
