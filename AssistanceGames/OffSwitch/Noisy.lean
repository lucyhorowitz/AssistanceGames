import AssistanceGames.OffSwitch.Basic
import AssistanceGames.OffSwitch.Policy
import AssistanceGames.Probability.Gaussian.Stein

section Gaussian

open MeasureTheory
open ProbabilityTheory

variable (G : offSwitchGame ℝ)
variable (μ : ℝ) (v : NNReal)

def HasGaussianBelief : Prop :=
  (G.p : Measure ℝ) = gaussianReal μ v

noncomputable def probCorrection : ℝ :=
  if μ ≥ 0 then (1 - G.p[G.π ∘ G.u]) else G.p[G.π ∘ G.u]

theorem gaussian_deferenceIncentive (G : offSwitchGame ℝ) (hdiff : IsDifferentiablePolicy G.π) (hgauss : HasGaussianBelief G μ v) :
    deferenceIncentive G = (v : ℝ) * G.p[deriv G.π ∘ G.u] - abs μ * probCorrection G μ := by
  sorry

theorem gradient_gt_of_deference_pos (G : offSwitchGame ℝ) (hdiff : IsDifferentiablePolicy G.π) (hgauss : HasGaussianBelief G μ v) :
    0 < deferenceIncentive G → ((abs μ / v : ℝ) * probCorrection G μ) < G.p[deriv G.π ∘ G.u] := by
  sorry

theorem deference_pos_of_gradient_gt (G : offSwitchGame ℝ) (hdiff : IsDifferentiablePolicy G.π) (hgauss : HasGaussianBelief G μ v) :
    ((abs μ / v : ℝ) * probCorrection G μ) < G.p[deriv G.π ∘ G.u] → 0 < deferenceIncentive G := by
  sorry

theorem deference_optimal_iff (G : offSwitchGame ℝ) (hdiff : IsDifferentiablePolicy G.π) (hgauss : HasGaussianBelief G μ v) :
    0 < deferenceIncentive G ↔ ((abs μ / v : ℝ) * probCorrection G μ) < G.p[deriv G.π ∘ G.u] := by
  constructor
  · exact fun a ↦ gradient_gt_of_deference_pos μ v G hdiff hgauss a
  · exact fun a ↦ deference_pos_of_gradient_gt μ v G hdiff hgauss a
