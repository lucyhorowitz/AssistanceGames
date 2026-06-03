import Mathlib.Probability.ProbabilityMassFunction.Constructions


variable {α : Type*} [Fintype α]

def expectation (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑ x : α , ((p x).toReal * f x)

lemma expectation_pure (x : α) (f : α → ℝ) :
    expectation (PMF.pure x) f = f x := by
  simp_all [expectation, Finset.sum_eq_single x]
