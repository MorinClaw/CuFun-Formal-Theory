import Mathlib

/-!
# Theorem 7 — Universal Approximation with Quantitative Rates
  Lean 4 / Mathlib 4 formalization.

  Fully proved (no sorry):
    step1_tail_bdy, gaussW properties (nonneg, sum_one),
    step4a_mono, step4b_range, step4c_boundary,
    step6_upper_tail, step6_lower_bdy,
    step7_combine, perturbation_range.

  Uses sorry (deep analysis / external lemmas):
    step2_Gamma_finite  — Gaussian shell summation
    step3_pwl           — PWL approximation theory
    step5_core_error    — mixture triangle inequality
    sigmoid_quarter_lip — NNReal coercion detail
    logit_lip_on_interval — MVT on σ⁻¹
    stage_A, stage_B, theorem7 — orchestration skeleton
-/

set_option maxHeartbeats 800000

open Real Finset Set

variable {d : ℕ}

abbrev H_space (d : ℕ) := EuclideanSpace ℝ (Fin d)

-- ================================================================
-- §0  Assumptions on the true CDF
-- ================================================================

structure CDFAssumptions (d : ℕ) (H : Set (H_space d))
    (F₀ : ℝ → H_space d → ℝ) (C α : ℝ) : Prop where
  hα     : 0 < α
  hC     : 0 < C
  mono   : ∀ h ∈ H, Monotone fun τ => F₀ τ h
  zero   : ∀ h ∈ H, F₀ 0 h = 0
  range  : ∀ τ, ∀ h ∈ H, F₀ τ h ∈ Icc (0 : ℝ) 1
  tail   : ∀ ε > 0, ∃ T > 0, ∀ h ∈ H, F₀ T h > 1 - ε
  bdy    : ∀ ε > 0, ∃ τ_min > 0, ∀ h ∈ H, F₀ τ_min h < ε
  holder : ∀ τ, ∀ h₁ ∈ H, ∀ h₂ ∈ H,
      |F₀ τ h₁ - F₀ τ h₂| ≤ C * ‖h₁ - h₂‖ ^ α

-- ================================================================
-- §1  Step 1 — Tail and Boundary Reduction   [FULLY PROVED]
-- ================================================================

/-- Step 1: obtain T* > τ_min with tail and boundary conditions.
    Construction: T = max T₀ (τ_min + 1) guarantees τ_min < T,
    and monotonicity preserves F₀(T|h) > 1 - ε/8. -/
lemma step1_tail_bdy {H : Set (H_space d)} {F₀ : ℝ → H_space d → ℝ} {C α : ℝ}
    (ha : CDFAssumptions d H F₀ C α) (ε : ℝ) (hε : 0 < ε) :
    ∃ T τ_min : ℝ, 0 < τ_min ∧ τ_min < T ∧
      (∀ h ∈ H, F₀ T h > 1 - ε / 8) ∧
      (∀ h ∈ H, F₀ τ_min h < ε / 8) := by
  obtain ⟨T₀, _, hT₀⟩ := ha.tail (ε / 8) (by linarith)
  obtain ⟨τm, hτm_pos, hτm⟩ := ha.bdy (ε / 8) (by linarith)
  -- T = max T₀ (τm + 1) guarantees τm < T and inherits the tail bound
  refine ⟨max T₀ (τm + 1), τm, hτm_pos, ?_, ?_, hτm⟩
  · -- τm < max T₀ (τm + 1)
    simp only [lt_max_iff]; right; linarith
  · -- F₀(max T₀ (τm+1) | h) > 1 - ε/8 by monotonicity
    intro h hh
    exact lt_of_lt_of_le (hT₀ h hh)
      (ha.mono h hh (le_max_left T₀ (τm + 1)))

-- ================================================================
-- §2  Gaussian Softmax Weights   [FULLY PROVED]
-- ================================================================

/-- Gaussian softmax weight of center c at query h with bandwidth δ. -/
noncomputable def gaussW (centers : Finset (H_space d)) (δ : ℝ)
    (h c : H_space d) : ℝ :=
  Real.exp (-‖h - c‖ ^ 2 / δ ^ 2) /
  (centers.sum fun c' => Real.exp (-‖h - c'‖ ^ 2 / δ ^ 2))

private lemma denom_pos (centers : Finset (H_space d)) (δ : ℝ)
    (h : H_space d) (hne : centers.Nonempty) :
    0 < centers.sum fun c' => Real.exp (-‖h - c'‖ ^ 2 / δ ^ 2) :=
  Finset.sum_pos (fun c _ => Real.exp_pos _) hne

/-- gaussW is non-negative. -/
lemma gaussW_nonneg (centers : Finset (H_space d)) (δ : ℝ)
    (h c : H_space d) (hne : centers.Nonempty) :
    0 ≤ gaussW centers δ h c :=
  div_nonneg (le_of_lt (Real.exp_pos _))
             (le_of_lt (denom_pos centers δ h hne))

/-- gaussW sums to 1 over all centers. -/
lemma gaussW_sum_one (centers : Finset (H_space d)) (δ : ℝ)
    (h : H_space d) (hne : centers.Nonempty) :
    centers.sum (gaussW centers δ h) = 1 := by
  simp only [gaussW, ← Finset.sum_div]
  exact div_self (ne_of_gt (denom_pos centers δ h hne))

/-- Normalized Gaussian softmax α-moment Γ_{d,α}. -/
noncomputable def Γ_moment (centers : Finset (H_space d)) (δ α : ℝ)
    (h : H_space d) : ℝ :=
  centers.sum fun c => gaussW centers δ h c * (‖c - h‖ / δ) ^ α

/-- Step 2: Γ_{d,α} is bounded by a universal constant depending only on d, α.
    [sorry] Full proof: nearest center contributes ≤ 1; center at distance rδ
    receives softmax weight ≤ e^{1-r²}; shell [rδ,(r+1)δ] has O(r^{d-1}) centers;
    hence Γ ≤ 1 + e · ∑_{r≥1} C'·r^{d-1+α}·e^{-r²} < ∞. -/
lemma step2_Gamma_finite (α : ℝ) (hα : 0 < α) :
    ∃ Γ : ℝ, 0 < Γ ∧
    ∀ (δ : ℝ), 0 < δ →
    ∀ (centers : Finset (H_space d)),
      (∀ x : H_space d, ∃ c ∈ centers, ‖x - c‖ ≤ δ) →
    ∀ h : H_space d, Γ_moment centers δ α h ≤ Γ := by
  sorry

-- ================================================================
-- §3  Step 3 — PWL Approximation   [sorry — external lemma]
-- ================================================================

/-- Step 3: α-Hölder monotone CDF g on [0,T] admits a piecewise-linear
    non-decreasing approximation ĝ with O(ε^{-1/α}) breakpoints and
    ‖ĝ - g‖_∞ ≤ ε/8.
    ⚠ PAPER GAP: requires τ-direction Hölder regularity of F₀, which must
    be added to the assumptions (currently only h-direction Hölder is stated).
    [sorry] Standard: uniform mesh with step ~ (ε/8L)^{1/α}. -/
lemma step3_pwl {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hmono : MonotoneOn g (Icc 0 T))
    (hg_range : ∀ τ ∈ Icc 0 T, g τ ∈ Icc (0 : ℝ) 1)
    (hg_zero : g 0 = 0)
    (hg_holder : ∃ L > 0, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        |g s - g t| ≤ L * |s - t| ^ α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (ĝ : ℝ → ℝ) (n : ℕ),
      MonotoneOn ĝ (Icc 0 T) ∧
      (∀ τ ∈ Icc 0 T, ĝ τ ∈ Icc (0 : ℝ) 1) ∧
      ĝ 0 = 0 ∧
      (∀ τ ∈ Icc 0 T, |ĝ τ - g τ| ≤ ε / 8) ∧
      (n : ℝ) ≤ ε ^ (-(1 / α)) + 1 := by
  sorry

-- ================================================================
-- §4  Blending   [FULLY PROVED]
-- ================================================================

/-- Blended approximation Mhat(τ,h) = Σ_j w_j(h) · ĝ_j(τ). -/
noncomputable def M_hat (centers : Finset (H_space d))
    (ĝ : H_space d → ℝ → ℝ) (δ : ℝ) (τ : ℝ) (h : H_space d) : ℝ :=
  centers.sum fun c => gaussW centers δ h c * ĝ c τ

/-- Step 4(a): Mhat is non-decreasing in τ.
    Proof: convex combination of non-decreasing functions with non-negative coefficients. -/
lemma step4a_mono (centers : Finset (H_space d))
    (ĝ : H_space d → ℝ → ℝ)
    (hmono : ∀ c ∈ centers, Monotone (ĝ c))
    (δ : ℝ) (hne : centers.Nonempty) (h : H_space d) :
    Monotone fun τ => M_hat centers ĝ δ τ h := by
  intro τ₁ τ₂ hle
  simp only [M_hat]
  apply Finset.sum_le_sum
  intro c hc
  exact mul_le_mul_of_nonneg_left (hmono c hc hle)
                                   (gaussW_nonneg centers δ h c hne)

/-- Step 4(b): Mhat ∈ [0, 1].
    Proof: convex combination of [0,1]-valued functions. -/
lemma step4b_range (centers : Finset (H_space d))
    (ĝ : H_space d → ℝ → ℝ)
    (hrange : ∀ c ∈ centers, ∀ τ, ĝ c τ ∈ Icc (0 : ℝ) 1)
    (δ : ℝ) (hne : centers.Nonempty) (τ : ℝ) (h : H_space d) :
    M_hat centers ĝ δ τ h ∈ Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · -- lower: nonneg
    apply Finset.sum_nonneg
    intro c hc
    exact mul_nonneg (gaussW_nonneg centers δ h c hne) (hrange c hc τ).1
  · -- upper: Σ w_j · ĝ_j ≤ Σ w_j · 1 = 1
    calc centers.sum (fun c => gaussW centers δ h c * ĝ c τ)
        ≤ centers.sum (fun c => gaussW centers δ h c * 1) := by
          apply Finset.sum_le_sum
          intro c hc
          exact mul_le_mul_of_nonneg_left (hrange c hc τ).2
                                           (gaussW_nonneg centers δ h c hne)
      _ = centers.sum (gaussW centers δ h) := by
          congr 1; ext c; ring
      _ = 1 := gaussW_sum_one centers δ h hne

/-- Step 4(c): Mhat(0, h) = 0, since each ĝ_j(0) = 0. -/
lemma step4c_boundary (centers : Finset (H_space d))
    (ĝ : H_space d → ℝ → ℝ)
    (hzero : ∀ c ∈ centers, ĝ c 0 = 0)
    (δ : ℝ) (h : H_space d) :
    M_hat centers ĝ δ 0 h = 0 := by
  simp only [M_hat]
  apply Finset.sum_eq_zero
  intro c hc
  rw [hzero c hc, mul_zero]

-- ================================================================
-- §5  Step 5 — Core Error Bound   [sorry — mixture triangle ineq]
-- ================================================================

/-- Step 5: |Mhat(τ,h) - F₀(τ,h)| ≤ ε/4 on the core region [τ_min, T*] × H.
    Proof sketch:
      |Mhat - F₀| ≤ Σ_j w_j|ĝ_j - F₀(·|h_j)|          ≤ ε/8  (Step 3)
               + Σ_j w_j · C‖h_j - h‖^α  = C·δ^α·Γ  ≤ ε/8  (choice of δ)
    [sorry] Requires formalizing the weighted triangle inequality. -/
lemma step5_core_error
    (F₀ : ℝ → H_space d → ℝ)
    (centers : Finset (H_space d)) (hne : centers.Nonempty)
    (ĝ : H_space d → ℝ → ℝ)
    (δ ε C α Γ : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (happrox  : ∀ c ∈ centers, ∀ τ, |ĝ c τ - F₀ τ c| ≤ ε / 8)
    (hHolder  : ∀ τ (h₁ h₂ : H_space d),
        |F₀ τ h₁ - F₀ τ h₂| ≤ C * ‖h₁ - h₂‖ ^ α)
    (hΓ       : ∀ h : H_space d, Γ_moment centers δ α h ≤ Γ)
    (hδ_choice : C * δ ^ α * Γ ≤ ε / 8) :
    ∀ τ (h : H_space d),
      |M_hat centers ĝ δ τ h - F₀ τ h| ≤ ε / 4 := by
  sorry

-- ================================================================
-- §6  Step 6 — Boundary and Tail Regions   [FULLY PROVED]
-- ================================================================

/-- Step 6 (upper tail): τ ≥ T* ⟹ |Mhat(τ,h) - F₀(τ,h)| < ε/2. -/
lemma step6_upper_tail (Mhat F₀ : ℝ → H_space d → ℝ)
    (T_star ε : ℝ) (hε : 0 < ε)
    (hcore : ∀ h : H_space d, |Mhat T_star h - F₀ T_star h| ≤ ε / 4)
    (htail  : ∀ h : H_space d, F₀ T_star h > 1 - ε / 8)
    (hmM    : ∀ h, Monotone fun τ => Mhat τ h)
    (hmF    : ∀ h, Monotone fun τ => F₀ τ h)
    (hrM    : ∀ τ h, Mhat τ h ∈ Icc (0 : ℝ) 1)
    (hrF    : ∀ τ h, F₀ τ h ∈ Icc (0 : ℝ) 1) :
    ∀ τ ≥ T_star, ∀ h : H_space d, |Mhat τ h - F₀ τ h| < ε / 2 := by
  intro τ hτ h
  -- Mhat(T*,h) ≥ F₀(T*,h) - ε/4  from core bound
  have hcore_lb : Mhat T_star h ≥ F₀ T_star h - ε / 4 := by
    have habs := hcore h; rw [abs_le] at habs; linarith [habs.1]
  -- Mhat(τ,h) ≥ Mhat(T*,h) ≥ F₀(T*,h) - ε/4 > 1 - ε/8 - ε/4 = 1 - 3ε/8
  have hM_lb : Mhat τ h ≥ 1 - 3 * ε / 8 := by
    have h1 : Mhat τ h ≥ Mhat T_star h := hmM h hτ
    linarith [htail h]
  -- F₀(τ,h) ≥ F₀(T*,h) > 1 - ε/8  by monotonicity
  have hF_lb : F₀ τ h > 1 - ε / 8 :=
    lt_of_lt_of_le (htail h) (hmF h hτ)
  -- Both lie in [1-3ε/8, 1], so |diff| < 3ε/8 < ε/2
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · linarith [(hrF τ h).2]
  · linarith [(hrM τ h).2]

/-- Step 6 (lower boundary): τ ∈ [0, τ_min] ⟹ |Mhat(τ,h) - F₀(τ,h)| < ε/2. -/
lemma step6_lower_bdy (Mhat F₀ : ℝ → H_space d → ℝ)
    (τ_min ε : ℝ) (hε : 0 < ε)
    (hcore : ∀ h : H_space d, |Mhat τ_min h - F₀ τ_min h| ≤ ε / 4)
    (hbdy  : ∀ h : H_space d, F₀ τ_min h < ε / 8)
    (hmM   : ∀ h, Monotone fun τ => Mhat τ h)
    (hmF   : ∀ h, Monotone fun τ => F₀ τ h)
    (hrM   : ∀ τ h, Mhat τ h ∈ Icc (0 : ℝ) 1)
    (hrF   : ∀ τ h, F₀ τ h ∈ Icc (0 : ℝ) 1)
    (hMz   : ∀ h : H_space d, Mhat 0 h = 0) :
    ∀ τ ∈ Icc (0 : ℝ) τ_min, ∀ h : H_space d,
      |Mhat τ h - F₀ τ h| < ε / 2 := by
  intro τ ⟨h0τ, hτm⟩ h
  -- Mhat(τ_min,h) ≤ F₀(τ_min,h) + ε/4 < ε/8 + ε/4 = 3ε/8
  have hMτm_ub : Mhat τ_min h ≤ 3 * ε / 8 := by
    have hle : Mhat τ_min h ≤ F₀ τ_min h + ε / 4 := by
      have habs := hcore h; rw [abs_le] at habs; linarith [habs.2]
    linarith [hbdy h]
  -- Mhat(τ,h) ≤ Mhat(τ_min,h) ≤ 3ε/8  and  Mhat(τ,h) ≥ 0
  have hM_ub : Mhat τ h ≤ 3 * ε / 8 := le_trans (hmM h hτm) hMτm_ub
  have hM_lb : (0 : ℝ) ≤ Mhat τ h := by
    rw [← hMz h]; exact hmM h h0τ
  -- F₀(τ,h) ≤ F₀(τ_min,h) < ε/8  and  F₀(τ,h) ≥ 0
  have hF_ub : F₀ τ h ≤ ε / 8 :=
    le_of_lt (lt_of_le_of_lt (hmF h hτm) (hbdy h))
  -- Both in [0, 3ε/8], so |diff| < 3ε/8 < ε/2
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · linarith [(hrF τ h).1]
  · linarith [(hrF τ h).1]

-- ================================================================
-- §7  Sigmoid and Stage B Tools
-- ================================================================

/-- Sigmoid is (1/4)-Lipschitz.
    Proof: σ'(x) = σ(x)(1-σ(x)) ≤ 1/4 by AM-GM.
    Uses `lipschitzWith_of_nnnorm_deriv_le` (Mathlib.Analysis.Calculus.MeanValue).
    [sorry] The nnnorm coercion ℝ≥0 ↔ ℝ is finicky in this Lean version;
    the mathematical argument (AM-GM + MVT) is complete in the proof sketch below. -/
lemma sigmoid_quarter_lip (a b : ℝ) :
    |Real.sigmoid a - Real.sigmoid b| ≤ (1 / 4) * |a - b| := by
  -- Mathematical proof:
  -- (1) deriv sigmoid x = σ(x)(1-σ(x)) ≤ 1/4  [AM-GM: σ(1-σ) ≤ ((σ+1-σ)/2)² = 1/4]
  -- (2) sigmoid is differentiable everywhere
  -- (3) lipschitzWith_of_nnnorm_deriv_le gives LipschitzWith (1/4) sigmoid
  -- (4) LipschitzWith.dist_le_mul + Real.dist_eq gives the abs-value bound
  -- Full Lean proof blocked only by nnnorm-to-ℝ coercion API
  sorry

/-- Perturbation (1-2η)·v + η maps [0,1] into the closed interval [η, 1-η].
    Note: the interval is CLOSED (endpoints achieved at v=0 and v=1).
    [η, 1-η] ⊂ (0,1) since η > 0 and η < 1/2. -/
lemma perturbation_range (v η : ℝ)
    (hη : 0 < η) (hη' : η < 1 / 2)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    (1 - 2 * η) * v + η ∈ Icc η (1 - η) := by
  obtain ⟨hv₀, hv₁⟩ := hv
  constructor
  · -- η ≤ (1-2η)v + η  iff  0 ≤ (1-2η)v, which holds since 1-2η > 0 and v ≥ 0
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * η) hv₀]
  · -- (1-2η)v + η ≤ 1-η  iff  (1-2η)v ≤ 1-2η  iff  v ≤ 1  (since 1-2η > 0)
    nlinarith [mul_le_mul_of_nonneg_left hv₁ (by linarith : (0 : ℝ) ≤ 1 - 2 * η)]

/-- Logit (σ⁻¹) is Lipschitz on [η, 1-η] with constant 1/(η(1-η)).
    [sorry] MVT: (σ⁻¹)'(y) = 1/(y(1-y)), maximized at boundary η giving 1/(η(1-η)). -/
lemma logit_lip_on_interval (η y₁ y₂ : ℝ)
    (hη : 0 < η) (hη' : η < 1 / 2)
    (hy₁ : y₁ ∈ Icc η (1 - η))
    (hy₂ : y₂ ∈ Icc η (1 - η)) :
    |Real.log (y₁ / (1 - y₁)) - Real.log (y₂ / (1 - y₂))| ≤
    (1 / (η * (1 - η))) * |y₁ - y₂| := by
  sorry

/-- Step 7 — Error combination: triangle inequality gives |F* - F₀| < ε.
    Decomposition: |F* - F₀| ≤ |σ(M_net) - M̃| + |M̃ - Mhat| + |Mhat - F₀|
                              < ε/2           + η   + (ε/2 - η) = ε. -/
lemma step7_combine
    (F_star M_hat_val M_tilde F₀_val η ε : ℝ)
    (hη : 0 < η) (hε : ε > 2 * η)
    (h1 : |F_star - M_tilde|    < ε / 2)       -- σ-Lipschitz applied
    (h2 : |M_tilde - M_hat_val| ≤ η)            -- perturbation size
    (h3 : |M_hat_val - F₀_val|  < ε / 2 - η) : -- Stage A with adj. tol.
    |F_star - F₀_val| < ε := by
  -- Unpack absolute value bounds via abs_lt / abs_le
  rw [abs_lt] at h1 h3
  rw [abs_le] at h2
  -- Ring identity: sum telescopes
  have key : F_star - F₀_val =
      (F_star - M_tilde) + (M_tilde - M_hat_val) + (M_hat_val - F₀_val) := by ring
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, key]

-- ================================================================
-- §8  Stage A and Stage B Orchestration   [sorry — skeleton]
-- ================================================================

/-- Stage A: construct Mhat ∈ [0,1], monotone, with Mhat(0,·)=0 and
    ‖Mhat - F₀‖_∞ < ε/2 over all (τ,h). Combines Steps 1–6. -/
theorem stage_A {H : Set (H_space d)} {F₀ : ℝ → H_space d → ℝ} {C α : ℝ}
    (ha : CDFAssumptions d H F₀ C α)
    (hH_cpt : IsCompact H) (hH_ne : H.Nonempty)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Mhat : ℝ → H_space d → ℝ,
      (∀ h ∈ H, Monotone fun τ => Mhat τ h) ∧
      (∀ τ, ∀ h ∈ H, Mhat τ h ∈ Icc (0 : ℝ) 1) ∧
      (∀ h ∈ H, Mhat 0 h = 0) ∧
      ∀ τ, ∀ h ∈ H, |Mhat τ h - F₀ τ h| < ε / 2 := by
  sorry

/-- Stage B: given Mhat ∈ [0,1] with CDF properties, construct
    F* = σ(M_net) with |F* - Mhat| < ε/2 and F* a valid CDF in (0,1).
    Uses: perturbation, logit lift, re-discretization, σ-composition. -/
theorem stage_B (Mhat : ℝ → H_space d → ℝ)
    (η ε : ℝ) (hη : 0 < η) (hη' : η < 1 / 2) (hε : ε > 2 * η)
    (hmono  : ∀ h, Monotone fun τ => Mhat τ h)
    (hrange : ∀ τ h, Mhat τ h ∈ Icc (0 : ℝ) 1)
    (hzero  : ∀ h, Mhat 0 h = 0) :
    ∃ F_star : ℝ → H_space d → ℝ,
      (∀ τ h, |F_star τ h - Mhat τ h| ≤ η + ε / 2) ∧
      (∀ h, Monotone fun τ => F_star τ h) ∧
      (∀ τ h, F_star τ h ∈ Ioo (0 : ℝ) 1) := by
  sorry

-- ================================================================
-- §9  Main Theorem   [sorry — combines stage_A + stage_B]
-- ================================================================

/-- **Theorem 7** — Universal Approximation with Quantitative Rates.
    For any ε > 0, ∃ MNN F* with N* = O(ε^{-(1+d/α)}) parameters such that:
      (i)  sup_{τ≥0, h∈H} |F*(τ|h) - F₀(τ|h)| < ε
      (ii) F*(τ|h) is a valid CDF for all parameters. -/
theorem theorem7 (d : ℕ) {H : Set (H_space d)}
    {F₀ : ℝ → H_space d → ℝ} {C α : ℝ}
    (ha : CDFAssumptions d H F₀ C α)
    (hH_cpt : IsCompact H) (hH_ne : H.Nonempty)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (F_star : ℝ → H_space d → ℝ) (N : ℕ),
      -- (i) Uniform approximation
      (∀ τ ≥ 0, ∀ h ∈ H, |F_star τ h - F₀ τ h| < ε) ∧
      -- (ii) Valid CDF: monotone
      (∀ h ∈ H, Monotone fun τ => F_star τ h) ∧
      -- (iii) Valid CDF: values in (0,1)
      (∀ τ, ∀ h ∈ H, F_star τ h ∈ Ioo (0 : ℝ) 1) ∧
      -- (iv) Parameter count bound
      (N : ℝ) ≤ 2 * ε ^ (-(1 + (d : ℝ) / α)) := by
  sorry
