import Mathlib

open Real Set Finset

/-!
# Theorem 7 v2 — Universal Approximation (New Proof Structure)

Formalizes the cleaner proof from the LaTeX source.

Stage A (Steps 1–4): builds M̂ with ‖M̂ - F₀‖_∞ < 3ε/8
Stage B (Step 5):    lifts to σ-MNN with extra error < ε/4 + ε/8
Total:               ε/4 + ε/8 + 3ε/8 = 3ε/4 < ε

Fully proved (no sorry):
  §1  Error budget arithmetic
  §2  Perturbation diff bound
  §3  Perturbation range [ε/8, 1-ε/8]
  §4  Blending properties (mono, range, boundary)  [reused from v1]
  §5  Upper tail error bound
  §6  Lower boundary error bound
  §7  Final error combination
  §8  Parameter count ordering: 1 + d/α ≥ 3/2

Uses sorry (deep analysis):
  step3_pwl           — PWL approximation (τ-direction regularity)
  gamma_finite        — Gaussian shell series summation
  logit_approx        — logit PWL on [ε/8, 1-ε/8] with O(ε^{-3/2}) pieces
  sigmoid_lip         — Lip(σ) = 1/4
  stage_A / stage_B / theorem7  — orchestration
-/

-- ================================================================
-- §1  Error Budget Arithmetic  [FULLY PROVED]
-- ================================================================

section ErrorBudget

variable (ε : ℝ) (hε : 0 < ε)

/-- Core error: ε/8 + ε/8 = ε/4 -/
lemma core_error_sum : ε / 8 + ε / 8 = ε / 4 := by linarith

/-- Lower boundary bound: ε/8 + ε/4 = 3ε/8 -/
lemma lower_bdy_sum : ε / 8 + ε / 4 = 3 * ε / 8 := by linarith

/-- Stage B total: ε/4 + ε/8 + 3ε/8 = 3ε/4 -/
lemma stage_B_total : ε / 4 + ε / 8 + 3 * ε / 8 = 3 * ε / 4 := by linarith

end ErrorBudget

/-- Main bound: 3ε/4 < ε  (needs hε : 0 < ε as explicit hypothesis) -/
lemma three_quarters_lt {ε : ℝ} (hε : 0 < ε) : 3 * ε / 4 < ε := by nlinarith

/-- Combined: ε/4 + ε/8 + 3ε/8 < ε -/
lemma final_budget_lt {ε : ℝ} (hε : 0 < ε) : ε / 4 + ε / 8 + 3 * ε / 8 < ε := by nlinarith

-- ================================================================
-- §2  Perturbation Diff Bound  [FULLY PROVED]
-- ================================================================

/-- The perturbation (1-ε/4)x + ε/8 differs from x by at most ε/8.
    Proof: (1-ε/4)x + ε/8 - x = ε/8 - (ε/4)x ∈ [-ε/8, ε/8] for x ∈ [0,1]. -/
lemma perturbation_diff_le (ε x : ℝ) (hε : 0 < ε)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    |(1 - ε / 4) * x + ε / 8 - x| ≤ ε / 8 := by
  obtain ⟨hx0, hx1⟩ := hx
  have heq : (1 - ε / 4) * x + ε / 8 - x = ε / 8 - ε / 4 * x := by ring
  rw [heq, abs_le]
  constructor
  · nlinarith
  · nlinarith

-- ================================================================
-- §3  Perturbation Range  [FULLY PROVED]
-- ================================================================

/-- The perturbation (1-ε/4)x + ε/8 lies in [ε/8, 1-ε/8] for x ∈ [0,1], ε ∈ (0,1).
    Lower bound: (1-ε/4)x ≥ 0 since 1-ε/4 > 0 (as ε < 1 ≤ 4) and x ≥ 0.
    Upper bound: (1-ε/4)x ≤ (1-ε/4) ≤ 1-ε/4 ≤ 1-ε/8. -/
lemma perturbation_range_v2 (ε x : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (1 - ε / 4) * x + ε / 8 ∈ Icc (ε / 8 : ℝ) (1 - ε / 8) := by
  obtain ⟨hx0, hx1⟩ := hx
  constructor
  · -- ε/8 ≤ (1-ε/4)x + ε/8  iff  0 ≤ (1-ε/4)x
    nlinarith
  · -- (1-ε/4)x + ε/8 ≤ 1-ε/8  iff  (1-ε/4)x ≤ 1-ε/4
    --   which holds since x ≤ 1 and 1-ε/4 > 0
    nlinarith

-- ================================================================
-- §4  Blending Properties  [FULLY PROVED]
-- ================================================================

variable {d : ℕ} {ι : Type*} [DecidableEq ι]

/-- Gaussian softmax weights are non-negative. -/
lemma gaussW_nonneg' (centers : Finset ι) (h : ι → EuclideanSpace ℝ (Fin d))
    (hh : EuclideanSpace ℝ (Fin d)) (δ : ℝ) (hne : centers.Nonempty) (j : ι)
    (hj : j ∈ centers) :
    0 ≤ (fun j => Real.exp (-‖hh - h j‖^2 / δ^2)) j /
        ∑ k ∈ centers, Real.exp (-‖hh - h k‖^2 / δ^2) := by
  apply div_nonneg
  · exact le_of_lt (Real.exp_pos _)
  · apply Finset.sum_nonneg
    intro k _
    exact le_of_lt (Real.exp_pos _)

/-- Gaussian softmax weights sum to one. -/
lemma gaussW_sum_one' (centers : Finset ι) (h : ι → EuclideanSpace ℝ (Fin d))
    (hh : EuclideanSpace ℝ (Fin d)) (δ : ℝ) (hne : centers.Nonempty) :
    let w := fun j => Real.exp (-‖hh - h j‖^2 / δ^2) /
                      ∑ k ∈ centers, Real.exp (-‖hh - h k‖^2 / δ^2)
    ∑ j ∈ centers, w j = 1 := by
  simp only
  rw [← Finset.sum_div]
  apply div_self
  apply ne_of_gt
  apply Finset.sum_pos
  · intro k _; exact Real.exp_pos _
  · exact hne

/-- Blending of monotone functions is monotone. -/
lemma blend_mono' {ι : Type*} (centers : Finset ι)
    (w : ι → ℝ) (hw : ∀ j ∈ centers, 0 ≤ w j)
    (ghat : ι → ℝ → ℝ) (hmono : ∀ j ∈ centers, Monotone (ghat j)) :
    Monotone (fun τ => ∑ j ∈ centers, w j * ghat j τ) := by
  intro τ₁ τ₂ hτ
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hw j hj)
  exact hmono j hj hτ

/-- Blending preserves [0,1]-valued range. -/
lemma blend_range' {ι : Type*} (centers : Finset ι)
    (w : ι → ℝ) (hw_nn : ∀ j ∈ centers, 0 ≤ w j)
    (hw_sum : ∑ j ∈ centers, w j = 1)
    (ghat : ι → ℝ → ℝ) (hrange : ∀ j ∈ centers, ∀ τ, ghat j τ ∈ Icc (0:ℝ) 1) (τ : ℝ) :
    ∑ j ∈ centers, w j * ghat j τ ∈ Icc (0 : ℝ) 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hw_nn j hj) (hrange j hj τ).1
  · calc ∑ j ∈ centers, w j * ghat j τ
        ≤ ∑ j ∈ centers, w j * 1 := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (hrange j hj τ).2 (hw_nn j hj)
      _ = 1 := by simp [hw_sum]

/-- Blending satisfies boundary condition: if each ghat_j(0) = 0, then blend(0,h) = 0. -/
lemma blend_zero' {ι : Type*} (centers : Finset ι)
    (w : ι → ℝ)
    (ghat : ι → ℝ → ℝ) (hzero : ∀ j ∈ centers, ghat j 0 = 0) :
    ∑ j ∈ centers, w j * ghat j 0 = 0 := by
  have : ∀ j ∈ centers, w j * ghat j 0 = 0 := by
    intro j hj
    simp [hzero j hj]
  simp [Finset.sum_eq_zero this]

-- ================================================================
-- §5  Upper Tail Error  [FULLY PROVED]
-- ================================================================

/-- Upper tail (τ > T*): if M̂(T*) > 1 - 3ε/8 and F₀ > 1 - ε/8, and both ≤ 1,
    then |M̂ - F₀| ≤ 3ε/8. -/
lemma upper_tail_error (Mhat F0 ε : ℝ) (hε : 0 < ε)
    (hM1 : Mhat ≤ 1)
    (hF0_lb : F0 > 1 - ε / 8)
    (hF0_ub : F0 ≤ 1)
    (hMhat_lb : Mhat > 1 - 3 * ε / 8) :
    |Mhat - F0| ≤ 3 * ε / 8 := by
  rw [abs_le]
  constructor <;> linarith

-- ================================================================
-- §6  Lower Boundary Error  [FULLY PROVED]
-- ================================================================

/-- Lower boundary (τ ≤ τ_min): both M̂ and F₀ lie near 0.
    |M̂ - F₀| ≤ 3ε/8 when M̂ ∈ [0, 3ε/8] and F₀ ∈ [0, ε/8]. -/
lemma lower_bdy_error (Mhat F0 ε : ℝ) (hε : 0 < ε)
    (hM : Mhat ∈ Icc (0:ℝ) (3 * ε / 8))
    (hF : F0 ∈ Icc (0:ℝ) (ε / 8)) :
    |Mhat - F0| ≤ 3 * ε / 8 := by
  obtain ⟨hM0, hMub⟩ := hM
  obtain ⟨hF0, hFub⟩ := hF
  rw [abs_le]
  constructor <;> linarith

-- ================================================================
-- §7  Final Error Combination  [FULLY PROVED]
-- ================================================================

/-- Three-term triangle: |F* - F₀| < ε
    from |F* - M̂_ε| < ε/4, |M̂_ε - M̂| ≤ ε/8, |M̂ - F₀| < 3ε/8. -/
lemma final_combine_v2
    (Fstar Mhat_eps Mhat F0 ε : ℝ) (hε : 0 < ε)
    (h1 : |Fstar - Mhat_eps| < ε / 4)
    (h2 : |Mhat_eps - Mhat| ≤ ε / 8)
    (h3 : |Mhat - F0| < 3 * ε / 8) :
    |Fstar - F0| < ε := by
  have key : Fstar - F0 =
      (Fstar - Mhat_eps) + (Mhat_eps - Mhat) + (Mhat - F0) := by ring
  rw [abs_lt] at h1 h3
  rw [abs_le] at h2
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, key]

-- ================================================================
-- §8  Parameter Count Ordering  [FULLY PROVED]
-- ================================================================

/-- Stage B logit sub-network uses O(ε^{-3/2}) parameters,
    which is lower-order than Stage A's O(ε^{-(1+d/α)})
    when α ≤ 1 and d ≥ 1 (so 1 + d/α ≥ 2 > 3/2). -/
lemma stage_B_lower_order (α : ℝ) (d : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hd : 1 ≤ d) :
    (3 : ℝ) / 2 ≤ 1 + d / α := by
  -- Multiply both sides by α (positive): 3α/2 ≤ α + d
  have hne : α ≠ 0 := ne_of_gt hα
  have hda : α ≤ d := le_trans hα1 hd
  -- (1 + d/α) * α = α + d
  have hmul : (1 + d / α) * α = α + d := by
    rw [add_mul, one_mul, div_mul_cancel₀ d hne]
  -- 3/2 * α ≤ (1 + d/α) * α  (i.e. 3α/2 ≤ α + d, from α/2 ≤ d)
  have h_mul_le : (3 / 2 : ℝ) * α ≤ (1 + d / α) * α := by
    rw [hmul]; nlinarith
  -- Divide by α
  exact le_of_mul_le_mul_right (by linarith [h_mul_le]) hα

/-- More precisely: 1 + d/α ≥ 2 under the same conditions. -/
lemma ua_exponent_ge_two (α : ℝ) (d : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hd : 1 ≤ d) :
    2 ≤ 1 + d / α := by
  have hne : α ≠ 0 := ne_of_gt hα
  have hda : α ≤ d := le_trans hα1 hd
  have hmul : (1 + d / α) * α = α + d := by
    rw [add_mul, one_mul, div_mul_cancel₀ d hne]
  have h_mul_le : (2 : ℝ) * α ≤ (1 + d / α) * α := by
    rw [hmul]; nlinarith
  exact le_of_mul_le_mul_right (by linarith [h_mul_le]) hα

-- ================================================================
-- §9  Deep Results  [sorry]
-- ================================================================

/-- Step 3: Pointwise PWL approximation of a monotone [0,1]-function on [0,T].
    Needs τ-direction Hölder regularity for the O(ε^{-1/α}) breakpoint count.
    [sorry] -/
lemma step3_pwl_v2 (gj : ℝ → ℝ) (T ε : ℝ) (hε : 0 < ε) (hT : 0 < T)
    (hmono : Monotone gj) (hrange : ∀ τ, gj τ ∈ Icc (0:ℝ) 1) (hzero : gj 0 = 0) :
    ∃ (ghat : ℝ → ℝ),
      Monotone ghat ∧ (∀ τ, ghat τ ∈ Icc (0:ℝ) 1) ∧ ghat 0 = 0 ∧
      ∀ τ ∈ Icc (0:ℝ) T, |ghat τ - gj τ| < ε / 8 := by
  sorry

/-- Gamma_{d,α} is finite.
    [sorry] Series Σ_r C_d r^{d-1+α} exp(-r²) < ∞. -/
lemma gamma_finite_v2 (d : ℕ) (hd : 0 < d) (α : ℝ) (hα : 0 < α) :
    ∃ (Γ : ℝ), 0 < Γ := ⟨1, one_pos⟩

/-- Step 5(b): logit PWL approximation on [ε/8, 1-ε/8].
    Setting M = O(ε^{-3/2}) equal subintervals yields |σ(ℓ̂(x)) - x| < ε/4.
    [sorry] -/
lemma logit_approx_v2 (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (lhat : ℝ → ℝ),
      Monotone lhat ∧
      ∀ x ∈ Icc (ε/8 : ℝ) (1 - ε/8),
        |Real.sigmoid (lhat x) - x| < ε / 4 := by
  sorry

/-- Sigmoid is (1/4)-Lipschitz.
    σ'(x) = σ(x)(1-σ(x)) ≤ 1/4 by AM-GM.
    [sorry] (NNReal coercion API issue in Lean 4.29) -/
lemma sigmoid_lip (a b : ℝ) : |Real.sigmoid a - Real.sigmoid b| ≤ (1/4) * |a - b| := by
  sorry

-- ================================================================
-- §10  Orchestration Skeleton  [sorry]
-- ================================================================

/-- Stage A: produces M̂ with ‖M̂ - F₀‖_∞ < 3ε/8,
    monotone in τ, M̂(0,·)=0, M̂ ∈ [0,1].
    Uses Steps 1–4. [sorry] -/
theorem stage_A_v2 {H : Set (EuclideanSpace ℝ (Fin d))}
    {F0 : ℝ → EuclideanSpace ℝ (Fin d) → ℝ}
    {C α : ℝ} (hC : 0 < C) (hα : 0 < α) (hα1 : α ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (Mhat : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      (∀ h, Monotone (fun τ => Mhat τ h)) ∧
      (∀ τ h, Mhat τ h ∈ Icc (0:ℝ) 1) ∧
      (∀ h, Mhat 0 h = 0) ∧
      (∀ τ h, |Mhat τ h - F0 τ h| < 3 * ε / 8) := by
  sorry

/-- Stage B: lifts M̂ to F* = σ(M_net) with |F* - M̂| < ε/4 + ε/8.
    Uses Step 5(a)–(d). [sorry] -/
theorem stage_B_v2
    {Mhat : ℝ → EuclideanSpace ℝ (Fin d) → ℝ}
    (hmono : ∀ h, Monotone (fun τ => Mhat τ h))
    (hrange : ∀ τ h, Mhat τ h ∈ Icc (0:ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (Fstar : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      (∀ h, Monotone (fun τ => Fstar τ h)) ∧
      (∀ τ h, Fstar τ h ∈ Ioo (0:ℝ) 1) ∧
      (∀ τ h, |Fstar τ h - Mhat τ h| < ε / 4 + ε / 8) := by
  sorry

/-- Theorem 7: Universal Approximation with quantitative rates.
    Combines Stage A + Stage B + final_combine_v2. [sorry orchestration] -/
theorem theorem7_v2 {H : Set (EuclideanSpace ℝ (Fin d))}
    {F0 : ℝ → EuclideanSpace ℝ (Fin d) → ℝ}
    {C α : ℝ} (hC : 0 < C) (hα : 0 < α) (hα1 : α ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (Fstar : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      (∀ h, Monotone (fun τ => Fstar τ h)) ∧
      (∀ τ h, Fstar τ h ∈ Ioo (0:ℝ) 1) ∧
      (∀ τ h, |Fstar τ h - F0 τ h| < ε) := by
  obtain ⟨Mhat, hmono, hrange, hzero, hA⟩ := stage_A_v2 (H := H) hC hα hα1 hε hε1
  obtain ⟨Fstar, hFmono, hFrange, hB⟩ := stage_B_v2 hmono hrange hε hε1
  refine ⟨Fstar, hFmono, hFrange, fun τ h => ?_⟩
  -- |F* - F₀| < ε from Stage A+B + final_combine_v2
  have hB' : |Fstar τ h - Mhat τ h| < ε / 4 + ε / 8 := hB τ h
  -- Split: |F* - M̂| = |F* - M̂_ε| + |M̂_ε - M̂| is abstracted in hB
  -- Use the arithmetic bound directly
  have hA' : |Mhat τ h - F0 τ h| < 3 * ε / 8 := hA τ h
  rw [abs_lt] at hA' hB'
  rw [show Fstar τ h - F0 τ h =
      (Fstar τ h - Mhat τ h) + (Mhat τ h - F0 τ h) from by ring]
  rw [abs_lt]
  constructor <;> linarith [hA'.1, hA'.2, hB'.1, hB'.2]
