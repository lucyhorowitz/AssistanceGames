import Mathlib.Analysis.SpecialFunctions.Exp

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
