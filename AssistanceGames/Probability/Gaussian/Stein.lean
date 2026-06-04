import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Stein's lemma for real Gaussian distributions

This file proves the Gaussian integration-by-parts identity commonly known as Stein's lemma.
-/

open MeasureTheory

namespace ProbabilityTheory

variable {μ : ℝ} {v : NNReal} {f f' : ℝ → ℝ}

/-- The derivative of the density of a nondegenerate real Gaussian distribution. -/
lemma hasDerivAt_gaussianPDFReal (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v)
      (-((x - μ) / (v : ℝ)) * gaussianPDFReal μ v x) x := by
  rw [gaussianPDFReal]
  have hinner :
      HasDerivAt (fun y : ℝ ↦ -((y - μ) ^ 2) / (2 * (v : ℝ)))
        (-(2 * (x - μ)) / (2 * (v : ℝ))) x :=
    by
      simpa using
        (((hasDerivAt_id x).sub_const μ).pow 2).neg.div_const (2 * (v : ℝ))
  have hexp :
      HasDerivAt (fun y : ℝ ↦ Real.exp (-((y - μ) ^ 2) / (2 * (v : ℝ))))
        (Real.exp (-((x - μ) ^ 2) / (2 * (v : ℝ))) *
          (-(2 * (x - μ)) / (2 * (v : ℝ)))) x :=
    Real.hasDerivAt_exp _ |>.comp x hinner
  convert (hasDerivAt_const x (√(2 * Real.pi * (v : ℝ)))⁻¹).mul hexp using 1
  field_simp [NNReal.coe_ne_zero.mpr hv]
  ring

/-- **Stein's lemma**, in centered form, for a nondegenerate real Gaussian distribution.

The integrability assumptions are stated for the density-weighted functions used by integration by
parts. -/
theorem stein_centered_gaussianReal
    (hv : v ≠ 0)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (h_f_pdf : Integrable (fun x ↦ f x * gaussianPDFReal μ v x))
    (h_f'_pdf : Integrable (fun x ↦ f' x * gaussianPDFReal μ v x))
    (h_centered_f_pdf : Integrable (fun x ↦ (x - μ) * f x * gaussianPDFReal μ v x)) :
    ∫ x, (x - μ) * f x ∂gaussianReal μ v =
      (v : ℝ) * ∫ x, f' x ∂gaussianReal μ v := by
  have hpdf : ∀ x, HasDerivAt (gaussianPDFReal μ v)
      (-((x - μ) / (v : ℝ)) * gaussianPDFReal μ v x) x :=
    hasDerivAt_gaussianPDFReal hv
  have h_f_pdf' :
      Integrable (fun x ↦ f x * (-((x - μ) / (v : ℝ)) * gaussianPDFReal μ v x)) := by
    convert h_centered_f_pdf.const_mul (-(v : ℝ)⁻¹) using 1
    funext x
    field_simp [NNReal.coe_ne_zero.mpr hv]
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable hf hpdf h_f_pdf' h_f'_pdf h_f_pdf
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  calc
    ∫ x, gaussianPDFReal μ v x * ((x - μ) * f x)
        = -(v : ℝ) * ∫ x, f x * (-((x - μ) / (v : ℝ)) * gaussianPDFReal μ v x) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          field_simp [NNReal.coe_ne_zero.mpr hv]
    _ = (v : ℝ) * ∫ x, f' x * gaussianPDFReal μ v x := by rw [hibp]; ring
    _ = (v : ℝ) * ∫ x, gaussianPDFReal μ v x * f' x := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      ring

/-- **Stein's lemma** for a nondegenerate real Gaussian distribution. -/
theorem stein_gaussianReal
    (hv : v ≠ 0)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (h_f_pdf : Integrable (fun x ↦ f x * gaussianPDFReal μ v x))
    (h_f'_pdf : Integrable (fun x ↦ f' x * gaussianPDFReal μ v x))
    (h_centered_f_pdf : Integrable (fun x ↦ (x - μ) * f x * gaussianPDFReal μ v x)) :
    ∫ x, x * f x ∂gaussianReal μ v =
      μ * ∫ x, f x ∂gaussianReal μ v + (v : ℝ) * ∫ x, f' x ∂gaussianReal μ v := by
  rw [← stein_centered_gaussianReal hv hf h_f_pdf
    h_f'_pdf h_centered_f_pdf]
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv,
    integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have h_mean_f_pdf : Integrable (fun x ↦ μ * (gaussianPDFReal μ v x * f x)) := by
    convert h_f_pdf.const_mul μ using 1
    funext x
    ring
  have h_centered_f_pdf' :
      Integrable (fun x ↦ gaussianPDFReal μ v x * ((x - μ) * f x)) := by
    convert h_centered_f_pdf using 1
    funext x
    ring
  rw [← integral_const_mul, ← integral_add h_mean_f_pdf h_centered_f_pdf']
  apply integral_congr_ae
  filter_upwards with x
  ring

end ProbabilityTheory
