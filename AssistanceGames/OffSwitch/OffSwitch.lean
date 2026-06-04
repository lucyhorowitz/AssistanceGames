import AssistanceGames.Basic
import AssistanceGames.OffSwitch.Policy
import Mathlib.MeasureTheory.Measure.DiracProba

open MeasureTheory
open ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

structure offSwitchGame (α : Type*) [MeasurableSpace α] where
  p : ProbabilityMeasure α
  u : α → ℝ
  hu : Measurable u
  π : ℝ → ℝ
  hπ_ge_zero : ∀ r, 0 ≤ π r
  hπ_le_one : ∀ r, π r ≤ 1

def HasFiniteExpectations (G : offSwitchGame α) : Prop :=
  Integrable G.u G.p ∧ Integrable (fun x ↦ G.π (G.u x) * G.u x) G.p

noncomputable def consent_incentive (G : offSwitchGame α) : ℝ :=
  G.p[fun x ↦ G.π (G.u x) * G.u x] - max G.p[G.u] 0

theorem consent_incentive_eq_min (G : offSwitchGame α) (hg : HasFiniteExpectations G) :
    consent_incentive G =
      min
        G.p[fun x ↦ G.π (G.u x) * G.u x - G.u x]
        G.p[fun x ↦ G.π (G.u x) * G.u x] := by
  obtain ⟨hu, hπu⟩ := hg
  rw [consent_incentive, sub_max_zero_eq_min_sub,
        expectation_mul_sub_eq_expectation_sub G.p G.u G.π hπu hu]

def IsRationalAt (G : offSwitchGame α) (x : α) : Prop :=
  G.π (G.u x) = rationalPolicy (G.u x)

theorem incentive_nonneg (G : offSwitchGame α) (hG : HasFiniteExpectations G) :
    IsRationalPolicy G.π → consent_incentive G ≥ 0 := by
  intro hrat
  unfold IsRationalPolicy at hrat
  rw [consent_incentive_eq_min G hG]
  apply le_min
  · have hnonneg : ∀ x, 0 ≤ G.π (G.u x) * G.u x - G.u x := by
      intro x
      simp_all only [rationalPolicy, ge_iff_le, ite_mul, one_mul, zero_mul, sub_nonneg]
      by_cases hx : G.u x ≥ 0
      · simp_all
      · simp only [hx, ↓reduceIte]
        have hx1 : G.u x < 0 := by exact Std.not_le.mp hx
        exact Std.le_of_not_ge hx
    exact integral_nonneg hnonneg
  · have hnonneg : ∀ x, 0 ≤ G.π (G.u x) * G.u x := by
      intro x
      simp_all only [rationalPolicy, ge_iff_le, ite_mul, one_mul, zero_mul]
      by_cases hx : G.u x ≥ 0
      · simp_all
      · simp only [hx, ↓reduceIte]
        have hx1 : G.u x < 0 := by exact Std.not_le.mp hx
        exact Std.IsPreorder.le_refl 0
    exact integral_nonneg hnonneg

theorem nonempty_support_incentive_pos
    (G : offSwitchGame α) (hG : HasFiniteExpectations G) :
    IsRationalPolicy G.π →
    0 < (G.p : Measure α) {x | 0 < G.u x} →
    0 < (G.p : Measure α) {x | G.u x < 0} →
    consent_incentive G > 0 := by
  intro hrat hpos hneg
  unfold IsRationalPolicy at hrat
  have hG' := hG
  obtain ⟨hu, hπu⟩ := hG
  rw [consent_incentive_eq_min G hG']
  apply lt_min
  · have hnonneg : ∀ x, 0 ≤ G.π (G.u x) * G.u x - G.u x := by
      intro x
      rw [hrat (G.u x)]
      by_cases hu : 0 ≤ G.u x
      · simp [rationalPolicy, hu]
      · simp only [rationalPolicy, ge_iff_le, hu, ↓reduceIte, zero_mul, zero_sub,
          Left.nonneg_neg_iff]
        exact le_of_lt (lt_of_not_ge hu)
    rw [integral_pos_iff_support_of_nonneg hnonneg (hπu.sub hu)]
    exact lt_of_lt_of_le hneg (measure_mono fun x hx ↦ by
      have hx' : G.u x < 0 := by simpa using hx
      rw [Function.mem_support]
      rw [hrat (G.u x)]
      simp [rationalPolicy, not_le_of_gt hx', hx'.ne])
  · have hnonneg : ∀ x, 0 ≤ G.π (G.u x) * G.u x := by
      intro x
      rw [hrat (G.u x)]
      by_cases hu : 0 ≤ G.u x
      · simp [rationalPolicy, hu]
      · simp [rationalPolicy, hu]
    rw [integral_pos_iff_support_of_nonneg hnonneg hπu]
    exact lt_of_lt_of_le hpos (measure_mono fun x hx ↦ by
      have hx' : 0 < G.u x := by simpa using hx
      rw [Function.mem_support]
      rw [hrat (G.u x)]
      simp [rationalPolicy, le_of_lt hx', hx'.ne'])

variable [MeasurableSingletonClass α]

lemma incentive_eq_piecewise (G : offSwitchGame α) (x : α) :
    (G.p = diracProba x) → consent_incentive G =
      if G.u x < 0 then G.π (G.u x) * G.u x else G.π (G.u x) * G.u x - G.u x := by
  intro hdirac
  rw [consent_incentive, hdirac]
  simp only [diracProba, ProbabilityMeasure.coe_mk, integral_dirac]
  by_cases hu : G.u x < 0
  · simp_all only [↓reduceIte, sub_eq_self, sup_eq_right]
    exact Std.le_of_lt hu
  · simp_all

theorem rational_at_of_optimal_of_dirac (G : offSwitchGame α) (x : α) :
    G.p = diracProba x →
      G.u x ≠ 0 →
      consent_incentive G ≥ 0 →
      IsRationalAt G x := by
  intro hdirac hnonz hinc
  rw [IsRationalAt, rationalPolicy]
  rw [consent_incentive, hdirac] at hinc
  simp only [diracProba, ProbabilityMeasure.coe_mk, integral_dirac] at hinc
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
    G.p = diracProba x →
      IsRationalAt G x →
      consent_incentive G ≥ 0 := by
  intro hdirac hrat
  by_cases! hu : 0 ≤ G.u x
  · rw [consent_incentive, hdirac]
    simp only [diracProba, ProbabilityMeasure.coe_mk, integral_dirac]
    simp [IsRationalAt, rationalPolicy] at hrat
    simp_all
  · have hpiece := incentive_eq_piecewise G x hdirac
    rw [hpiece]
    unfold IsRationalAt at hrat
    rw [hrat]
    simp [rationalPolicy, hu, not_le_of_gt hu]

theorem optimal_iff_rationalPolicy_of_dirac (G : offSwitchGame α) (x : α) :
    G.p = diracProba x →
      G.u x ≠ 0 →
      (IsRationalAt G x ↔ consent_incentive G ≥ 0) := by
  intro hdirac hne
  constructor
  · exact optimal_of_rational_at_of_dirac G x hdirac
  · exact rational_at_of_optimal_of_dirac G x hdirac hne
