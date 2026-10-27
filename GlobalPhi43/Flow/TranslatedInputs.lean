module

public import GlobalPhi43.Flow.ModelHorizon
public import GlobalPhi43.Attachment.FlowCovariance

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

/-- The model-input bounds on the single reference event. The allowance precedes all
indices and real starts. Both the unshifted and translated distances retain the literal T+S
horizon; the integer horizon used internally never changes that conclusion. -/
theorem reference_translated_inputs {Ω : Type*} (N : ℕ) (κ : Kappa)
    (ρ : ParabolicSpace → ℝ) (a α : ℝ) (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (ω : Ω) (hω : ω ∈ referenceEvent N κ ρ a α ξ hsmooth)
    (S T : ℝ) (hS : 0 ≤ S) (hT : 1 ≤ T) :
    let A := dyadicLiftData N κ ρ a α ξ hsmooth ω hω
    ∃ B : ℝ, 1 ≤ B ∧
      (∀ n, Statements.phi43Size κ α (T + S) (A n).model (A n).potential ≤ ENNReal.ofReal B) ∧
      (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
        Statements.phi43Dist κ α (T + S) (A n).model (A m).model
          (A n).potential (A m).potential ≤ ENNReal.ofReal δ) ∧
      (∀ n (s : ℝ), s ∈ Icc (0 : ℝ) S →
        Statements.phi43Size κ α T ((A n).model.translate (s, 0))
          (fun r => (A n).potential (s + r)) ≤
            Statements.phi43Size κ α (T + S) (A n).model (A n).potential) ∧
      (∀ n m (s : ℝ), s ∈ Icc (0 : ℝ) S →
        Statements.phi43Dist κ α T ((A n).model.translate (s, 0)) ((A m).model.translate (s, 0))
          (fun r => (A n).potential (s + r)) (fun r => (A m).potential (s + r)) ≤
            Statements.phi43Dist κ α (T + S) (A n).model (A m).model
              (A n).potential (A m).potential) ∧
      ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
        (⨆ s : Icc (0 : ℝ) S,
          Statements.phi43Dist κ α T ((A n).model.translate (s.val, 0))
            ((A m).model.translate (s.val, 0))
            (fun r => (A n).potential (s.val + r)) (fun r => (A m).potential (s.val + r))) ≤
          ENNReal.ofReal δ := by
  let A := dyadicLiftData N κ ρ a α ξ hsmooth ω hω
  obtain ⟨B, hB, hb, hc⟩ := modelConvergenceEvent_realHorizon α
    (referenceAttachedModel N κ ρ a ξ hsmooth) (referencePotential ξ hsmooth) hω.1.1 (T + S) (by linarith)
  have hsize : ∀ n, Statements.phi43Size κ α (T + S) (A n).model (A n).potential ≤
      ENNReal.ofReal B := hb
  have hC : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
      Statements.phi43Dist κ α (T + S) (A n).model (A m).model
        (A n).potential (A m).potential ≤ ENNReal.ofReal δ := hc
  have hdist (n m : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) S) :=
    Attachment.phi43Dist_translate_le κ α T hs.1 hs.2
      (A n).model (A m).model (A n).potential (A m).potential
  refine ⟨B, hB, hsize, hC, ?_, hdist, ?_⟩
  · intro n s hs
    exact Attachment.phi43Size_translate_le κ α T hs.1 hs.2 (A n).model (A n).potential
  · intro δ hδ
    obtain ⟨n₀, hn₀⟩ := hC δ hδ
    refine ⟨n₀, fun n hn m hm => iSup_le fun s => ?_⟩
    exact (hdist n m s.val s.property).trans (hn₀ n hn m hm)

end GlobalPhi43.Flow
