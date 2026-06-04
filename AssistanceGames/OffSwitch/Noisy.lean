import AssistanceGames.OffSwitch.Basic
import AssistanceGames.OffSwitch.Policy
import AssistanceGames.Probability.Gaussian.Stein

section Gaussian

open MeasureTheory
open ProbabilityTheory

variable (G : offSwitchGame ℝ)
variable (μ : ℝ) (v : NNReal)

/-- The agent's belief about the *utility* `U_a = G.u` is a normal distribution `N(μ, σ²)`:
the pushforward of `G.p` along `G.u` is `gaussianReal μ v`. This matches the paper's
`Bᴿ(U_a) = N(U_a; μ, σ²)`. -/
def HasGaussianBelief : Prop :=
  (G.p : Measure ℝ).map G.u = gaussianReal μ v

noncomputable def probCorrection : ℝ :=
  if μ ≥ 0 then (1 - G.p[G.π ∘ G.u]) else G.p[G.π ∘ G.u]

/-- Applying Stein's lemma to `deferenceIncentive_eq_min` (Equation 1) turns each term of the
minimum into a piece that shares a common `σ² 𝔼[π̇ᴴ]` summand, which can be pulled out of the
minimum. This is the intermediate identity

  `Δ = min{ -μ 𝔼[1 - πᴴ], μ 𝔼[πᴴ] } + σ² 𝔼[π̇ᴴ]`

from the paper, with `πᴴ = G.π ∘ G.u` and `σ² = v`. -/
lemma deferenceIncentive_eq_plus' (G : offSwitchGame ℝ)
    (hdiff : IsDifferentiablePolicy G.π) (hv : v ≠ 0)
    (hgauss : HasGaussianBelief G μ v)
    (hint : IsIntegrablePolicyDerivative G.p G.u G.π) :
    deferenceIncentive G =
      min (- μ * G.p[fun x ↦ 1 - G.π (G.u x)]) (μ * G.p[fun x ↦ G.π (G.u x)])
        + (v : ℝ) * G.p[deriv G.π ∘ G.u] := by
  unfold HasGaussianBelief at hgauss
  unfold IsDifferentiablePolicy at hdiff
  unfold IsIntegrablePolicyDerivative at hint
  -- Measurability / strong measurability facts.
  have hu_aem : AEMeasurable G.u (G.p : Measure ℝ) := G.hu.aemeasurable
  have hπ_aesm : AEStronglyMeasurable G.π (gaussianReal μ v) :=
    hdiff.continuous.aestronglyMeasurable
  have hderiv_aesm : AEStronglyMeasurable (deriv G.π) (gaussianReal μ v) :=
    (measurable_deriv G.π).aestronglyMeasurable
  have hid_aesm : AEStronglyMeasurable (fun y : ℝ ↦ y) (gaussianReal μ v) :=
    measurable_id.aestronglyMeasurable
  -- `G.π` is bounded in `[0, 1]`.
  have hπ_abs_le : ∀ y : ℝ, |G.π y| ≤ 1 := by
    intro y
    rw [abs_le]
    exact ⟨by linarith [G.hπ_ge_zero y], G.hπ_le_one y⟩
  -- Change of variables along the pushforward `G.u`.
  have push : ∀ g : ℝ → ℝ, AEStronglyMeasurable g (gaussianReal μ v) →
      ∫ x, g (G.u x) ∂(G.p : Measure ℝ) = ∫ y, g y ∂(gaussianReal μ v) := by
    intro g hg
    have hg' : AEStronglyMeasurable g ((G.p : Measure ℝ).map G.u) := by rw [hgauss]; exact hg
    have hmap := integral_map hu_aem hg'
    rw [hgauss] at hmap
    exact hmap.symm
  -- Integrability of the relevant functions under the Gaussian.
  have hid_int : Integrable (fun y : ℝ ↦ y) (gaussianReal μ v) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)
  have hπ_int : Integrable G.π (gaussianReal μ v) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hπ_aesm ?_
    filter_upwards with y
    simpa using hπ_abs_le y
  have hderiv_int : Integrable (deriv G.π) (gaussianReal μ v) := by
    have haesm : AEStronglyMeasurable (deriv G.π) ((G.p : Measure ℝ).map G.u) := by
      rw [hgauss]; exact hderiv_aesm
    rw [← hgauss]
    exact (integrable_map_measure haesm hu_aem).mpr hint
  have hπid_int : Integrable (fun y : ℝ ↦ G.π y * y) (gaussianReal μ v) := by
    refine Integrable.mono' hid_int.norm (hπ_aesm.mul hid_aesm) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul]
    calc |G.π y| * |y| ≤ 1 * |y| :=
          mul_le_mul_of_nonneg_right (hπ_abs_le y) (abs_nonneg y)
      _ = ‖y‖ := by rw [one_mul, Real.norm_eq_abs]
  have hcent_int : Integrable (fun y : ℝ ↦ (y - μ) * G.π y) (gaussianReal μ v) := by
    have hsub : Integrable (fun y : ℝ ↦ y - μ) (gaussianReal μ v) :=
      hid_int.sub (integrable_const μ)
    refine Integrable.mono' hsub.norm
      ((hid_aesm.sub aestronglyMeasurable_const).mul hπ_aesm) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul]
    calc |y - μ| * |G.π y| ≤ |y - μ| * 1 :=
          mul_le_mul_of_nonneg_left (hπ_abs_le y) (abs_nonneg _)
      _ = ‖y - μ‖ := by rw [mul_one, Real.norm_eq_abs]
  -- Re-express Gaussian integrability as `pdf`-weighted Lebesgue integrability for Stein's lemma.
  have conv : ∀ g : ℝ → ℝ, Integrable g (gaussianReal μ v) →
      Integrable (fun x ↦ g x * gaussianPDFReal μ v x) := by
    intro g hg
    rw [gaussianReal_of_var_ne_zero μ hv,
      integrable_withDensity_iff (measurable_gaussianPDF μ v)
        (ae_of_all _ (fun _ ↦ gaussianPDF_lt_top))] at hg
    simpa only [toReal_gaussianPDF] using hg
  -- Stein's lemma.
  have hf : ∀ x, HasDerivAt G.π (deriv G.π x) x := fun x ↦ (hdiff x).hasDerivAt
  have h_centered_f_pdf :
      Integrable (fun x ↦ (x - μ) * G.π x * gaussianPDFReal μ v x) := by
    simpa only [mul_assoc] using conv _ hcent_int
  have hstein := stein_gaussianReal hv hf (conv _ hπ_int) (conv _ hderiv_int) h_centered_f_pdf
  -- Finiteness of the expectations needed for `deferenceIncentive_eq_min`.
  have hπu_comp_int : Integrable (fun x ↦ G.π (G.u x)) (G.p : Measure ℝ) := by
    have haesm : AEStronglyMeasurable G.π ((G.p : Measure ℝ).map G.u) := by
      rw [hgauss]; exact hπ_aesm
    exact (integrable_map_measure haesm hu_aem).mp (by rw [hgauss]; exact hπ_int)
  have hfin : HasFiniteExpectations G := by
    refine ⟨?_, ?_⟩
    · have haesm : AEStronglyMeasurable (fun y : ℝ ↦ y) ((G.p : Measure ℝ).map G.u) := by
        rw [hgauss]; exact hid_aesm
      simpa using (integrable_map_measure haesm hu_aem).mp (by rw [hgauss]; exact hid_int)
    · have haesm : AEStronglyMeasurable (fun y : ℝ ↦ G.π y * y) ((G.p : Measure ℝ).map G.u) := by
        rw [hgauss]; exact hπ_aesm.mul hid_aesm
      simpa [Function.comp] using
        (integrable_map_measure haesm hu_aem).mp (by rw [hgauss]; exact hπid_int)
  -- Mean of the utility.
  have hGu_mean : ∫ x, G.u x ∂(G.p : Measure ℝ) = μ := by
    rw [push (fun y ↦ y) hid_aesm, integral_id_gaussianReal]
  -- The two arguments of the minimum, computed via Stein's lemma.
  have e2 : ∫ x, G.π (G.u x) * G.u x ∂(G.p : Measure ℝ)
      = μ * (∫ x, G.π (G.u x) ∂(G.p : Measure ℝ))
        + (v : ℝ) * (∫ x, deriv G.π (G.u x) ∂(G.p : Measure ℝ)) := by
    calc ∫ x, G.π (G.u x) * G.u x ∂(G.p : Measure ℝ)
        = ∫ y, G.π y * y ∂(gaussianReal μ v) := push (fun y ↦ G.π y * y) (hπ_aesm.mul hid_aesm)
      _ = ∫ y, y * G.π y ∂(gaussianReal μ v) := by simp_rw [mul_comm]
      _ = μ * (∫ y, G.π y ∂(gaussianReal μ v))
            + (v : ℝ) * (∫ y, deriv G.π y ∂(gaussianReal μ v)) := hstein
      _ = μ * (∫ x, G.π (G.u x) ∂(G.p : Measure ℝ))
            + (v : ℝ) * (∫ x, deriv G.π (G.u x) ∂(G.p : Measure ℝ)) := by
          rw [← push G.π hπ_aesm, ← push (deriv G.π) hderiv_aesm]
  have hone : ∫ x, (1 - G.π (G.u x)) ∂(G.p : Measure ℝ)
      = 1 - ∫ x, G.π (G.u x) ∂(G.p : Measure ℝ) := by
    rw [integral_sub (integrable_const 1) hπu_comp_int, integral_const]
    simp
  have e1 : ∫ x, G.π (G.u x) * G.u x - G.u x ∂(G.p : Measure ℝ)
      = - μ * (∫ x, (1 - G.π (G.u x)) ∂(G.p : Measure ℝ))
        + (v : ℝ) * (∫ x, deriv G.π (G.u x) ∂(G.p : Measure ℝ)) := by
    rw [integral_sub hfin.2 hfin.1, e2, hGu_mean, hone]
    ring
  -- Pull the common summand out of the minimum.
  have combine : ∀ a b c : ℝ, min (a + c) (b + c) = min a b + c := by
    intro a b c
    rcases le_total a b with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]
    · rw [min_eq_right h, min_eq_right (by linarith)]
  rw [deferenceIncentive_eq_min G hfin, e1, e2]
  exact combine _ _ _

/-- **Theorem 2 / Equation 7.** Pulling the factor `-|μ|` out of the piecewise minimum in
`deferenceIncentive_eq_plus'` rewrites the deference incentive as

  `Δ = σ² 𝔼[π̇ᴴ] - |μ| Pr(C)`,

where `Pr(C) = probCorrection` is `1 - 𝔼[πᴴ]` when `μ ≥ 0` and `𝔼[πᴴ]` otherwise. -/
theorem gaussian_deferenceIncentive (G : offSwitchGame ℝ)
    (hdiff : IsDifferentiablePolicy G.π) (hgauss : HasGaussianBelief G μ v) (hv : v ≠ 0)
    (hint : IsIntegrablePolicyDerivative G.p G.u G.π) :
    deferenceIncentive G = (v : ℝ) * G.p[deriv G.π ∘ G.u] - abs μ * probCorrection G μ := by
  -- `G.π ∘ G.u` is bounded measurable, hence integrable under the probability measure `G.p`.
  have hcomp_meas : Measurable (fun x ↦ G.π (G.u x)) :=
    (hdiff.continuous.measurable).comp G.hu
  have hcomp_int : Integrable (fun x ↦ G.π (G.u x)) (G.p : Measure ℝ) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hcomp_meas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [G.hπ_ge_zero (G.u x)], G.hπ_le_one (G.u x)⟩
  -- `0 ≤ 𝔼[πᴴ] ≤ 1`.
  have hB0 : 0 ≤ ∫ x, G.π (G.u x) ∂(G.p : Measure ℝ) :=
    integral_nonneg fun x ↦ G.hπ_ge_zero (G.u x)
  have hB1 : ∫ x, G.π (G.u x) ∂(G.p : Measure ℝ) ≤ 1 := by
    calc ∫ x, G.π (G.u x) ∂(G.p : Measure ℝ)
        ≤ ∫ _, (1 : ℝ) ∂(G.p : Measure ℝ) :=
          integral_mono hcomp_int (integrable_const 1) fun x ↦ G.hπ_le_one (G.u x)
      _ = 1 := by simp
  -- `𝔼[1 - πᴴ] = 1 - 𝔼[πᴴ]`.
  have hA : ∫ x, (1 - G.π (G.u x)) ∂(G.p : Measure ℝ)
      = 1 - ∫ x, G.π (G.u x) ∂(G.p : Measure ℝ) := by
    rw [integral_sub (integrable_const 1) hcomp_int, integral_const]; simp
  rw [deferenceIncentive_eq_plus' μ v G hdiff hv hgauss hint, hA]
  by_cases hμ : 0 ≤ μ
  · rw [abs_of_nonneg hμ]
    have hmin : min (-μ * (1 - ∫ x, G.π (G.u x) ∂(G.p : Measure ℝ)))
        (μ * ∫ x, G.π (G.u x) ∂(G.p : Measure ℝ))
        = -μ * (1 - ∫ x, G.π (G.u x) ∂(G.p : Measure ℝ)) := by
      apply min_eq_left; nlinarith [hB0, hB1, hμ]
    rw [hmin, probCorrection, if_pos hμ]
    simp only [Function.comp_apply]; ring
  · push_neg at hμ
    rw [abs_of_neg hμ]
    have hmin : min (-μ * (1 - ∫ x, G.π (G.u x) ∂(G.p : Measure ℝ)))
        (μ * ∫ x, G.π (G.u x) ∂(G.p : Measure ℝ))
        = μ * ∫ x, G.π (G.u x) ∂(G.p : Measure ℝ) := by
      apply min_eq_right; nlinarith [hB0, hB1, hμ]
    rw [hmin, probCorrection, if_neg (not_le.mpr hμ)]
    simp only [Function.comp_apply]; ring

theorem gradient_gt_of_deference_pos (G : offSwitchGame ℝ)
    (hdiff : IsDifferentiablePolicy G.π) (hgauss : HasGaussianBelief G μ v) (hv : v ≠ 0)
    (hint : IsIntegrablePolicyDerivative G.p G.u G.π) :
    0 < deferenceIncentive G → ((abs μ / v : ℝ) * probCorrection G μ) < G.p[deriv G.π ∘ G.u] := by
  intro hpos
  have hvpos : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.mpr hv
  rw [gaussian_deferenceIncentive μ v G hdiff hgauss hv hint] at hpos
  rw [div_mul_eq_mul_div, div_lt_iff₀ hvpos]
  nlinarith [hpos]

theorem deference_pos_of_gradient_gt (G : offSwitchGame ℝ)
    (hdiff : IsDifferentiablePolicy G.π) (hgauss : HasGaussianBelief G μ v) (hv : v ≠ 0)
    (hint : IsIntegrablePolicyDerivative G.p G.u G.π) :
    ((abs μ / v : ℝ) * probCorrection G μ) < G.p[deriv G.π ∘ G.u] → 0 < deferenceIncentive G := by
  intro h
  have hvpos : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.mpr hv
  rw [gaussian_deferenceIncentive μ v G hdiff hgauss hv hint]
  rw [div_mul_eq_mul_div, div_lt_iff₀ hvpos] at h
  nlinarith [h]

theorem deference_optimal_iff (G : offSwitchGame ℝ)
    (hdiff : IsDifferentiablePolicy G.π) (hgauss : HasGaussianBelief G μ v) (hv : v ≠ 0)
    (hint : IsIntegrablePolicyDerivative G.p G.u G.π) :
    0 < deferenceIncentive G ↔ ((abs μ / v : ℝ) * probCorrection G μ) < G.p[deriv G.π ∘ G.u] := by
  constructor
  · exact fun a ↦ gradient_gt_of_deference_pos μ v G hdiff hgauss hv hint a
  · exact fun a ↦ deference_pos_of_gradient_gt μ v G hdiff hgauss hv hint a

theorem deference_neg_of_gradient_neg (G : offSwitchGame ℝ)
    (hdiff : IsDifferentiablePolicy G.π) (hgauss : HasGaussianBelief G μ v) (hv : v ≠ 0)
    (hint : IsIntegrablePolicyDerivative G.p G.u G.π) :
    G.p[deriv G.π ∘ G.u] < 0 → deferenceIncentive G < 0 := by
  intro hC
  have hvpos : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.mpr hv
  rw [gaussian_deferenceIncentive μ v G hdiff hgauss hv hint]
  -- `probCorrection` is nonnegative, since `𝔼[πᴴ] ∈ [0, 1]`.
  have hprob_nonneg : 0 ≤ probCorrection G μ := by
    have hcomp_meas : Measurable (fun x ↦ G.π (G.u x)) :=
      (hdiff.continuous.measurable).comp G.hu
    have hcomp_int : Integrable (fun x ↦ G.π (G.u x)) (G.p : Measure ℝ) := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) hcomp_meas.aestronglyMeasurable ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [G.hπ_ge_zero (G.u x)], G.hπ_le_one (G.u x)⟩
    have hB0 : 0 ≤ ∫ x, G.π (G.u x) ∂(G.p : Measure ℝ) :=
      integral_nonneg fun x ↦ G.hπ_ge_zero (G.u x)
    have hB1 : ∫ x, G.π (G.u x) ∂(G.p : Measure ℝ) ≤ 1 := by
      calc ∫ x, G.π (G.u x) ∂(G.p : Measure ℝ)
          ≤ ∫ _, (1 : ℝ) ∂(G.p : Measure ℝ) :=
            integral_mono hcomp_int (integrable_const 1) fun x ↦ G.hπ_le_one (G.u x)
        _ = 1 := by simp
    rw [probCorrection]
    split_ifs with hμ <;> · simp only [Function.comp_apply]; linarith
  nlinarith [hC, hvpos, hprob_nonneg, abs_nonneg μ]

end Gaussian
