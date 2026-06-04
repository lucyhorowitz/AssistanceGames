import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory

noncomputable def rationalPolicy : ℝ → ℝ :=
  fun x ↦ (if x ≥ 0 then 1 else 0)

def IsRationalPolicy (f : ℝ → ℝ) : Prop :=
  ∀ r : ℝ, f r = rationalPolicy r

/-- A logistic noisy-rational policy with inverse-temperature/noise parameter `β`.

Given a utility gap `x`, this returns the probability of allowing the action. Larger positive
`x` makes allowing more likely, while `β` controls how sharply the policy approaches the
deterministic rational policy. Downstream results should usually assume `0 < β`. -/
noncomputable def noisilyRationalPolicy (β : ℝ) : ℝ → ℝ :=
  fun x ↦ (1 + Real.exp (-x / β))⁻¹

/-- `f` is exactly the noisy-rational policy for a fixed positive parameter `β`.

Use this version in theorem assumptions when proofs need to reason about the same `β`
throughout, especially for sign or monotonicity arguments. -/
def IsNoisilyRationalPolicyWith (β : ℝ) (f : ℝ → ℝ) : Prop :=
  0 < β ∧ ∀ r : ℝ, f r = noisilyRationalPolicy β r

/-- `f` is noisy-rational for some positive parameter `β`.

This existential wrapper is useful for classification statements, while
`IsNoisilyRationalPolicyWith` is usually more convenient inside proofs. -/
def IsNoisilyRationalPolicy (f : ℝ → ℝ) : Prop :=
  ∃ β : ℝ, IsNoisilyRationalPolicyWith β f

/-- `π` is differentiable with respect to its utility input. -/
def IsDifferentiablePolicy (π : ℝ → ℝ) : Prop :=
  Differentiable ℝ π

/-- The derivative of `π` is integrable under the distribution of utility values `u`. -/
def IsIntegrablePolicyDerivative
    {α : Type*} [MeasurableSpace α]
    (p : ProbabilityMeasure α) (u : α → ℝ) (π : ℝ → ℝ) : Prop :=
  Integrable (deriv π ∘ u) p
