import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# CuFun: Formal Verification of CDF-based TPP Theoretical Framework

Verified (no sorry):
1. CDF structure + convex combination closure
2. weighted_sum_monotone
3. sigmoid_monotone
4. mnn_with_sigmoid_monotone
5. mnn_output_bounded_monotone
6. log_likelihood_well_defined
7. cdf_intensity_deriv_identity (chain rule)
8. pdf_positive_from_intensity
9. roundingConstant_pos
10. cdf_error_lt_intensity_error
11. mse_decomposition
-/

open Real Filter MeasureTheory Set Topology

-- ============================================================
-- Section 1: CDF Structure
-- ============================================================

structure ConditionalCDF (H : Type*) where
  F : ℝ → H → ℝ
  zero_at_zero : ∀ h : H, F 0 h = 0
  tends_to_one : ∀ h : H, Tendsto (fun τ => F τ h) atTop (𝓝 1)
  mono : ∀ h : H, Monotone (fun τ => F τ h)
  nonneg : ∀ τ h, 0 ≤ F τ h
  le_one : ∀ τ h, F τ h ≤ 1

structure DiffConditionalCDF (H : Type*) extends ConditionalCDF H where
  differentiable : ∀ τ : ℝ, ∀ h : H, DifferentiableAt ℝ (fun t => F t h) τ
  deriv_pos : ∀ τ : ℝ, ∀ h : H, 0 < deriv (fun t => F t h) τ

noncomputable def DiffConditionalCDF.pdf
    {H : Type*} (cdf : DiffConditionalCDF H) (τ : ℝ) (h : H) : ℝ :=
  deriv (fun t => cdf.F t h) τ

-- ============================================================
-- Section 2: Convex Combination of CDFs
-- ============================================================

/-- Convex combination of two valid CDFs is a valid CDF.
    Structural fact enabling the δ-net blending in UAP proof. -/
theorem cdf_convex_combination {H : Type*}
    (c1 c2 : ConditionalCDF H) {mix : ℝ} (hm₀ : 0 ≤ mix) (hm₁ : mix ≤ 1) :
    ∃ c : ConditionalCDF H,
      ∀ τ h, c.F τ h = mix * c1.F τ h + (1 - mix) * c2.F τ h := by
  refine ⟨{
    F := fun τ h => mix * c1.F τ h + (1 - mix) * c2.F τ h,
    zero_at_zero := fun h => by simp [c1.zero_at_zero h, c2.zero_at_zero h],
    tends_to_one := fun h => by
      have h1 := c1.tends_to_one h
      have h2 := c2.tends_to_one h
      have key : Tendsto (fun τ => mix * c1.F τ h + (1 - mix) * c2.F τ h)
               atTop (𝓝 (mix * 1 + (1 - mix) * 1)) :=
        (h1.const_mul mix).add (h2.const_mul (1 - mix))
      simp only [mul_one] at key; convert key using 2; ring,
    mono := fun h a b hab => add_le_add
      (mul_le_mul_of_nonneg_left (c1.mono h hab) hm₀)
      (mul_le_mul_of_nonneg_left (c2.mono h hab) (by linarith)),
    nonneg := fun τ h => add_nonneg
      (mul_nonneg hm₀ (c1.nonneg τ h))
      (mul_nonneg (by linarith) (c2.nonneg τ h)),
    le_one := fun τ h => by
      nlinarith [c1.le_one τ h, c2.le_one τ h, c1.nonneg τ h, c2.nonneg τ h]
  }, fun _ _ => rfl⟩

-- ============================================================
-- Section 3: MNN Monotonicity
-- ============================================================

/-- Weighted sum with non-negative coefficients of monotone functions is monotone. -/
theorem weighted_sum_monotone {n : ℕ}
    (f : Fin n → ℝ → ℝ) (w : Fin n → ℝ)
    (hf : ∀ i, Monotone (f i)) (hw : ∀ i, 0 ≤ w i) :
    Monotone (fun τ => ∑ i : Fin n, w i * f i τ) := fun a b hab =>
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf i hab) (hw i)

/-- Sigmoid σ(x) = 1/(1+exp(-x)) is monotone. -/
theorem sigmoid_monotone : Monotone (fun x : ℝ => (1 + exp (-x))⁻¹) := by
  intro a b hab
  simp only [inv_eq_one_div]
  apply one_div_le_one_div_of_le
  · linarith [exp_pos (-b)]
  · have : exp (-b) ≤ exp (-a) := exp_le_exp.mpr (by linarith)
    linarith

/-- MNN with non-negative weights + sigmoid is monotone in τ. -/
theorem mnn_with_sigmoid_monotone {d : ℕ}
    (w_tau : Fin d → ℝ) (φ : ℝ → ℝ)
    (hw : ∀ i, 0 ≤ w_tau i) (hφ : Monotone φ) :
    Monotone (fun τ => (1 + exp (-(∑ i : Fin d, w_tau i * φ τ)))⁻¹) := by
  have h_sum : Monotone (fun τ => ∑ i : Fin d, w_tau i * φ τ) :=
    weighted_sum_monotone (fun _ τ => φ τ) w_tau (fun _ => hφ) hw
  intro a b hab
  exact sigmoid_monotone (h_sum hab)

-- ============================================================
-- Section 4: Log-Likelihood
-- ============================================================

/-- PDF is strictly positive, so log-likelihood is well-defined. -/
theorem log_likelihood_well_defined {H : Type*}
    (cdf : DiffConditionalCDF H) (τ : ℝ) (h : H) :
    0 < cdf.pdf τ h := cdf.deriv_pos τ h

-- ============================================================
-- Section 5: CDF-Intensity Derivative Identity
-- ============================================================

/-- d/dτ [1 - exp(-∫₀^τ intensity)] = intensity(τ) · (1 - F(τ))
    CDF and intensity representations carry identical information. -/
theorem cdf_intensity_deriv_identity
    (intensity : ℝ → ℝ) (F : ℝ → ℝ)
    (hF_eq : F = fun τ => 1 - exp (-(∫ s in Ioc 0 τ, intensity s)))
    (τ : ℝ)
    (hΛ_deriv : HasDerivAt (fun τ => ∫ s in Ioc 0 τ, intensity s)
                             (intensity τ) τ) :
    HasDerivAt F (intensity τ * (1 - F τ)) τ := by
  subst hF_eq
  have h_exp := hΛ_deriv.neg.exp
  convert (hasDerivAt_const τ 1).sub h_exp using 1
  simp; ring

/-- PDF is positive when intensity is positive. -/
theorem pdf_positive_from_intensity
    (intensity : ℝ → ℝ) (hint_pos : ∀ t, 0 < intensity t)
    (F : ℝ → ℝ)
    (hF : ∀ τ, F τ = 1 - exp (-(∫ s in Ioc 0 τ, intensity s))) :
    ∀ τ, 0 < intensity τ * (1 - F τ) := fun τ => by
  rw [hF]; exact mul_pos (hint_pos τ) (by simp [exp_pos])

-- ============================================================
-- Section 6: Numerical Error Analysis
-- ============================================================

/-- Higham's backward error constant γ_n = n·u / (1 - n·u). -/
noncomputable def roundingConstant (n : ℕ) (u : ℝ) : ℝ :=
  (n * u) / (1 - n * u)

theorem roundingConstant_pos {n : ℕ} {u : ℝ} (hu : 0 < u)
    (hn_pos : 0 < n) (h_stable : (n : ℝ) * u < 1) :
    0 < roundingConstant n u :=
  div_pos (mul_pos (Nat.cast_pos.mpr hn_pos) hu) (by linarith)

/-- γ_{2LW} < γ_N when 2LW < N: CDF ops fewer than N-point quadrature. -/
theorem cdf_error_lt_intensity_error
    {L W N : ℕ} {u : ℝ} (hu : 0 < u)
    (hLW_pos : 0 < 2 * L * W)
    (hLW_stable : (2 * L * W : ℝ) * u < 1)
    (hN_stable : (N : ℝ) * u < 1)
    (h_fewer_ops : 2 * L * W < N) :
    roundingConstant (2 * L * W) u < roundingConstant N u := by
  unfold roundingConstant
  -- a/(1-a) < b/(1-b) ↔ a*(1-b) < b*(1-a) ↔ a < b  (for 0 < a,b < 1)
  have hd1 : (0 : ℝ) < 1 - ↑(2 * L * W) * u := by push_cast; linarith
  have hd2 : (0 : ℝ) < 1 - ↑N * u := by push_cast; linarith
  have h_cast : (↑(2 * L * W) : ℝ) < ↑N := by exact_mod_cast h_fewer_ops
  -- Clear denominators: a/b < c/d ↔ a*d < c*b (b,d > 0)
  have key : ↑(2 * L * W) * u * (1 - ↑N * u) < ↑N * u * (1 - ↑(2 * L * W) * u) := by
    push_cast at *; nlinarith
  rw [div_lt_div_iff₀ hd1 hd2]
  exact key

-- ============================================================
-- Section 7: MSE Decomposition
-- ============================================================

/-- Bias-variance / approximation-estimation decomposition. -/
theorem mse_decomposition {H : Type*}
    (F_hat F_star F_0 : ℝ → H → ℝ) (τ : ℝ) (h : H) :
    (F_hat τ h - F_0 τ h) ^ 2 ≤
    2 * (F_hat τ h - F_star τ h) ^ 2 +
    2 * (F_star τ h - F_0 τ h) ^ 2 := by
  nlinarith [sq_nonneg (F_hat τ h - F_star τ h - (F_star τ h - F_0 τ h)),
             sq_nonneg (F_hat τ h - F_star τ h + (F_star τ h - F_0 τ h))]

-- ============================================================
-- Section 8: MNN Output Validity
-- ============================================================

/-- σ(MNN(τ)) is always in (0,1) and monotone — two of three CDF axioms
    hold purely from architecture. (F(0)=0 needs initialization.) -/
theorem mnn_output_bounded_monotone
    (mnn : ℝ → ℝ) (hmnn_mono : Monotone mnn) :
    Monotone (fun τ => (1 + exp (-(mnn τ)))⁻¹) ∧
    ∀ τ, 0 < (1 + exp (-(mnn τ)))⁻¹ ∧
         (1 + exp (-(mnn τ)))⁻¹ < 1 := by
  refine ⟨fun a b hab => ?_, fun τ => ⟨by positivity, ?_⟩⟩
  · exact sigmoid_monotone (hmnn_mono hab)
  · rw [inv_eq_one_div, div_lt_one (by linarith [exp_pos (-(mnn τ))])]
    linarith [exp_pos (-(mnn τ))]
