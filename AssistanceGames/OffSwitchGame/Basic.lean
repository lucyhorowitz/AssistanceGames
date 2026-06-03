import AssistanceGames.Basic
/-!
This file formalizes a finite version of the off-switch game from the paper "The
 Off-Switch Game" by Hadfield-Menell et al. (https://arxiv.org/abs/1611.08219).
-/

variable {α : Type*} [Fintype α] -- states of the world

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

def IsRationalAt (G : offSwitchGame α) (x : α) : Prop :=
  G.π (G.u x) = rationalPolicy (G.u x)

theorem incentive_nonneg (G : offSwitchGame α) :
    IsRationalPolicy G.π → consent_incentive G ≥ 0 := by
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

lemma incentive_eq_piecewise (G : offSwitchGame α) (x : α) :
    (G.p = PMF.pure x) → consent_incentive G =
      if G.u x < 0 then G.π (G.u x) * G.u x else G.π (G.u x) * G.u x - G.u x := by
  intro hdirac
  rw [consent_incentive, hdirac, expectation_pure, expectation_pure]
  by_cases hu : G.u x < 0
  · simp_all only [↓reduceIte, sub_eq_self, sup_eq_right]
    exact Std.le_of_lt hu
  · simp_all

theorem rational_at_of_optimal_of_dirac (G : offSwitchGame α) (x : α) :
    G.p = PMF.pure x →
      G.u x ≠ 0 →
      consent_incentive G ≥ 0 →
      IsRationalAt G x := by
  intro hdirac hnonz hinc
  rw [IsRationalAt, rationalPolicy]
  rw [consent_incentive, hdirac, expectation_pure, expectation_pure] at hinc
  by_cases hu : G.u x ≥ 0
  · simp_all
    have hu_pos : 0 < G.u x := lt_of_le_of_ne' hu hnonz
    have hπ_ge_one : 1 ≤ G.π (G.u x) := by
      nlinarith [hinc, hu_pos]
    have hπ_le_one : G.π (G.u x) ≤ 1 := by exact G.hπ_le_one (G.u x)
    linarith
  · simp only [ge_iff_le]
    have hu_neg : G.u x < 0 := lt_of_not_ge hu
    simp only [ge_iff_le, sub_nonneg, sup_le_iff] at hinc
    have hπ_nonpos : G.π (G.u x) ≤ 0 := by
      rw [mul_comm] at hinc
      exact nonpos_of_mul_nonneg_right hinc.2 hu_neg
    simp only [hu, ↓reduceIte]
    exact le_antisymm hπ_nonpos (G.hπ_ge_zero (G.u x))

theorem optimal_of_rational_at_of_dirac (G : offSwitchGame α) (x : α) :
    G.p = PMF.pure x →
      IsRationalAt G x →
      consent_incentive G ≥ 0 := by
  intro hdirac hrat
  by_cases! hu : 0 ≤ G.u x
  · rw [consent_incentive, hdirac, expectation_pure, expectation_pure]
    simp [IsRationalAt, rationalPolicy] at hrat
    simp_all
  · have hpiece := incentive_eq_piecewise G x hdirac
    rw [hpiece]
    unfold IsRationalAt at hrat
    rw [hrat]
    simp [rationalPolicy, hu, not_le_of_gt hu]

theorem optimal_iff_rationalPolicy_of_dirac (G : offSwitchGame α) (x : α) :
    G.p = PMF.pure x →
      G.u x ≠ 0 →
      (IsRationalAt G x ↔ consent_incentive G ≥ 0) := by
  intro hdirac hne
  constructor
  · exact optimal_of_rational_at_of_dirac G x hdirac
  · exact rational_at_of_optimal_of_dirac G x hdirac hne
