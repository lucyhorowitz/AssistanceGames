import Mathlib.Probability.Notation

/-!
For an explicit probability measure or measure `P`, mathlib notation `P[X]` means the expectation
of the random variable `X` under `P`, i.e. the integral `∫ x, X x ∂P`.
-/

open MeasureTheory
open scoped ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

lemma sub_max_zero_eq_min_sub (a b : ℝ) :
    a - max b 0 = min (a - b) a := by
  by_cases! hb : 0 < b
  · rw [max_eq_left (Std.le_of_lt hb), min_eq_left ?_]
    linarith
  · rw [max_eq_right hb, min_eq_right, sub_zero]
    exact (le_sub_self_iff a).mpr hb

lemma expectation_mul_sub_eq_expectation_sub
    (p : Measure α) (u : α → ℝ) (π : ℝ → ℝ)
    (hπu : Integrable (fun x ↦ π (u x) * u x) p)
    (hu : Integrable u p) :
    p[fun x ↦ π (u x) * u x] - p[u] =
      p[fun x ↦ π (u x) * u x - u x] := by
  simp [integral_sub hπu hu]
