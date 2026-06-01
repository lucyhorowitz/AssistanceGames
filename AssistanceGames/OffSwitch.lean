import Mathlib.Probability.ProbabilityMassFunction.Constructions

variable {α : Type*} [Fintype α] -- states of the world

def expectation (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑ x : α , ((p x).toReal * f x)

/- Fix an "action" a that a robot might take. -/

structure offSwitchGame (α : Type*) [Fintype α] where
  p : PMF α -- probability that this is the true state of the world
  u : α → ℝ -- utility of the state of the world
  π : ℝ → ℝ -- human policy that sends a utility value to the probability of allowing the action
  hπ_ge_zero : ∀ x, 0 ≤ π x
  hπ_le_one : ∀ x, π x ≤ 1

def consent_incentive (G : offSwitchGame α) : ℝ :=
  expectation G.p (fun x ↦ G.π (G.u x) * G.u x) -
    max (expectation G.p G.u) 0

lemma sub_max_zero_eq_min_sub (a b : ℝ) :
    a - max b 0 = min (a - b) a := by
  by_cases! hb : 0 < b
  · rw [max_eq_left (Std.le_of_lt hb), min_eq_left ?_]
    linarith
  · rw [max_eq_right hb, min_eq_right, sub_zero]
    exact (le_sub_self_iff a).mpr hb

lemma expectation_mul_sub_eq_expectation_sub
    (p : PMF α) (u : α → ℝ) (π : ℝ → ℝ) :
    expectation p (fun x ↦ π (u x) * u x) - expectation p u =
      expectation p (fun x ↦ π (u x) * u x - u x) := by
  simp only [expectation]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem consent_incentive_eq_min (G : offSwitchGame α) :
    consent_incentive G =
      min
        (expectation G.p (fun x ↦ G.π (G.u x) * G.u x - G.u x))
        (expectation G.p (fun x ↦ G.π (G.u x) * G.u x)) := by
  rw [consent_incentive, sub_max_zero_eq_min_sub,
        expectation_mul_sub_eq_expectation_sub]

noncomputable def rationalPolicy : ℝ → ℝ :=
  fun x ↦ (if x ≥ 0 then 1 else 0)

def IsRationalPolicy (f : ℝ → ℝ) : Prop :=
  ∀ r : ℝ, f r = rationalPolicy r

theorem incentive_nonneg (G : offSwitchGame α) : IsRationalPolicy G.π → consent_incentive G ≥ 0 := by
  intro hrat
  unfold IsRationalPolicy at hrat
  rw [consent_incentive_eq_min, expectation, expectation]
  apply le_min
  · have hnonneg : ∀ x, 0 ≤ (G.p x).toReal * (G.π (G.u x) * G.u x - G.u x) := by
      intro x
      simp_all only [rationalPolicy]
      by_cases hx : G.u x ≥ 0
      · simp_all
      · simp only [hx, ↓reduceIte, zero_mul, zero_sub, mul_neg, Left.nonneg_neg_iff]
        have hx1 : G.u x < 0 := by exact Std.not_le.mp hx
        have hppos : (G.p x).toReal ≥ 0 := by exact ENNReal.toReal_nonneg
        exact mul_nonpos_of_nonneg_of_nonpos hppos (le_of_lt hx1)
    exact Fintype.sum_nonneg hnonneg
  · have hnonneg : ∀ x, 0 ≤ (G.p x).toReal * (G.π (G.u x) * G.u x) := by
      intro x
      simp_all only [rationalPolicy]
      by_cases hx : G.u x ≥ 0
      · simp only [hx, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
        have hpos : 0 ≤ (G.p x).toReal := by exact ENNReal.toReal_nonneg
        exact Left.mul_nonneg hpos hx
      · simp [hx]
    exact Fintype.sum_nonneg hnonneg

theorem nonempty_support_incentive_pos (G : offSwitchGame α) :
  IsRationalPolicy G.π → (∃ x, 0 < (G.p x).toReal ∧ 0 < G.u x) →
      (∃ x, 0 < (G.p x).toReal ∧ 0 > G.u x )→
      (consent_incentive G > 0) := by
  intro hrat hpos hneg
  unfold IsRationalPolicy at hrat
  rw [consent_incentive_eq_min, expectation, expectation]
  apply lt_min
  · apply Finset.sum_pos'
    · intro x hx
      rw [hrat (G.u x)]
      by_cases hu : 0 ≤ G.u x
      · simp [rationalPolicy, hu]
      · simp only [rationalPolicy, ge_iff_le, hu, ↓reduceIte, zero_mul, zero_sub, mul_neg,
        Left.nonneg_neg_iff]
        have hp : 0 ≤ (G.p x).toReal := ENNReal.toReal_nonneg
        have hu' : G.u x ≤ 0 := le_of_lt (lt_of_not_ge hu)
        exact mul_nonpos_of_nonneg_of_nonpos hp hu'
    · obtain ⟨x, hp, hu⟩ := hneg
      refine ⟨x, Finset.mem_univ x, ?_⟩
      apply mul_pos hp
      rw [hrat (G.u x)]
      simp [rationalPolicy, not_le_of_gt hu]
      linarith
  · apply Finset.sum_pos'
    · intro x hx
      rw [hrat (G.u x)]
      by_cases hu : 0 ≤ G.u x
      · simp only [rationalPolicy, ge_iff_le, hu, ↓reduceIte, one_mul]
        exact mul_nonneg ENNReal.toReal_nonneg hu
      · simp [rationalPolicy, hu]
    · obtain ⟨x, hp, hu⟩ := hpos
      refine ⟨x, Finset.mem_univ x, ?_⟩
      rw [hrat (G.u x)]
      simp only [rationalPolicy, ge_iff_le, le_of_lt hu, ↓reduceIte, one_mul]
      exact mul_pos hp hu
