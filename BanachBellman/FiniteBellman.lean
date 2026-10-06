import BanachBellman.Banach

/-!
# Finite discounted Bellman equations

For a finite state space and a stochastic transition kernel, prove that the
discounted fixed-policy Bellman operator is a contraction, has a unique fixed
point, and its iterates converge from any initial value function.
-/

-- S is a finite type (the state space; nonemptiness is not required)
-- P : S ⨯ S → ℝ (Transition kernel)
-- r : S → ℝ (Immediate one-step reward)
-- V : S → ℝ (The total expected discounted future value)
-- 0 ≤ γ < 1 (The discount factor)

-- Stochastic kernel condition:
-- P is a stochastic kernel if it satisfies:
-- P(s, s') ≥ 0
-- ∑ P(s, s') = 1
def stochastic_kernel_cond {S : Type*} [Fintype S] (P : S → S → ℝ) : Prop :=
  (∀ s s', 0 ≤ P s s') ∧ (∀ s, ∑ s' : S, P s s' = 1)

-- (TV)(s) = r(s) + γ ∑ P(s, s')V(s')
def bellman_operator {S : Type*} [Fintype S] (P : S → S → ℝ) (r : S → ℝ) (γ : ℝ)
  (V : S → ℝ) : S → ℝ :=
  fun s => r s + γ * ∑ s' : S, P s s' * V s'

-- Given a stochastic kernel P, a discount factor 0 ≤ γ < 1,
-- The Bellman Operator is a contraction, i.e. γ Lipschitz
lemma bellman_is_contraction {S : Type*} [Fintype S] (P : S → S → ℝ) (r : S → ℝ)
  (γ : ℝ) (hP : stochastic_kernel_cond P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
  contraction (bellman_operator P r γ) γ := by
  constructor
  · intro V W
    have hineq : ∀ s : S, dist (bellman_operator P r γ V s) (bellman_operator P r γ W s) ≤ γ * dist V W := by
      intro s
      calc
        dist (bellman_operator P r γ V s) (bellman_operator P r γ W s) =
        dist (r s + γ * ∑ s' : S, P s s' * V s') (r s + γ * ∑ s' : S, P s s' * W s') := by
          simp [bellman_operator]
        _ = γ * dist (∑ s' : S, P s s' * V s') (∑ s' : S, P s s' * W s') := by
          rw [Real.dist_eq, Real.dist_eq]
          have hrewrite : (r s + γ * ∑ s' : S, P s s' * V s') - (r s + γ * ∑ s' : S, P s s' * W s')
            = γ * ((∑ s' : S, P s s' * V s') - (∑ s' : S, P s s' * W s')) := by ring
          rw [hrewrite, abs_mul, abs_of_nonneg hγ0]
        _ ≤ γ * ∑ s' : S, P s s' * dist (V s') (W s') := by
          have hdist_sum : dist (∑ s' : S, P s s' * V s') (∑ s' : S, P s s' * W s')
            ≤ ∑ s' : S, P s s' * dist (V s') (W s') := by
            rw [Real.dist_eq]
            calc
              |(∑ s' : S, P s s' * V s') - (∑ s' : S, P s s' * W s')| = |∑ s' : S, P s s' * (V s' - W s')| := by
                congr 1
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro s' hs'
                ring
              _ ≤ ∑ s' : S, |P s s' * (V s' - W s')| := by
                    exact Finset.abs_sum_le_sum_abs (fun s' => P s s' * (V s' - W s')) Finset.univ
              _ = ∑ s' : S, P s s' * dist (V s') (W s') := by
                    apply Finset.sum_congr rfl
                    intro s' hs'
                    rw [abs_mul, abs_of_nonneg (hP.1 s s'), Real.dist_eq]
          exact mul_le_mul_of_nonneg_left hdist_sum hγ0
        _ ≤ γ * dist V W := by
          have hsum_le_dist : ∑ s' : S, P s s' * dist (V s') (W s') ≤ dist V W := by
            calc
              ∑ s' : S, P s s' * dist (V s') (W s') ≤ ∑ s' : S, P s s' * dist V W := by
                apply Finset.sum_le_sum
                intro s' hs'
                exact mul_le_mul_of_nonneg_left (dist_le_pi_dist V W s') (hP.1 s s')
              _ = dist V W := by
                rw [← Finset.sum_mul, hP.2 s, one_mul]
          exact mul_le_mul_of_nonneg_left hsum_le_dist hγ0
    exact (dist_pi_le_iff (mul_nonneg hγ0 dist_nonneg)).mpr hineq -- this line converts pointwise bound into uniform
  · exact hγ1
  · exact hγ0


-- ∃!V_star : S → ℝ such that T(V_star) = V_star
-- Semantically: the discounted fixed-policy Bellman equation
-- has a unique value-function solution on the finite state space S.
-- If we work with an infinite state space, which is the case for most interesting problems
-- the analysis becomes more involved and we have to do more work.
theorem bellman_eq_uniq_existence_of_solution  {S : Type*} [Fintype S] (P : S → S → ℝ) (r : S → ℝ)
  (γ : ℝ) (hP : stochastic_kernel_cond P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
  ∃! V_star : S → ℝ, bellman_operator P r γ V_star = V_star := by
    exact banach_fixed_point (bellman_operator P r γ) γ (bellman_is_contraction P r γ hP hγ0 hγ1)


-- This next theorem states that for any arbitrary initial point x₀
-- with a sequence recursively defined by applying f
-- The discrete dynamical system defined by the sequence satisfy the bound:
-- d(x_n, x_star) ≤ c^n d(x_0, x_star)
theorem global_conv_of_contraction_dynamics {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (f : X → X) (c : ℝ) (hf : contraction f c) (x₀ : X) :
    ∃! x_star : X, f x_star = x_star
    ∧
    ∀ n : ℕ, dist (fixed_point_seq f x₀ n) x_star ≤ c ^ n * dist x₀ x_star := by
    obtain ⟨x_star, hx_star, huniq⟩ := banach_fixed_point f c hf
    use x_star
    constructor
    · constructor
      · exact hx_star
      · intro n
        induction n with
        | zero => simp [fixed_point_seq]
        | succ n ih =>
          calc
            dist (fixed_point_seq f x₀ (n + 1)) x_star = dist (f (fixed_point_seq f x₀ n)) (f x_star) := by
              rw [fixed_point_seq, hx_star]
            _ ≤ c * dist (fixed_point_seq f x₀ n) (x_star) := by exact hf.lipschitz (fixed_point_seq f x₀ n) x_star
            _ ≤ c * c ^ n * dist x₀ x_star := by
              have h := mul_le_mul_of_nonneg_left ih hf.nonneg
              simpa [mul_assoc] using h
            _ = c ^ (n + 1) * dist x₀ x_star := by ring_nf
    · intro y
      exact fun a ↦ And.elim (fun a ↦ huniq y) (id (And.symm a))


-- V_n
def bellman_it_seq {S : Type*} [Fintype S] (P : S → S → ℝ) (r : S → ℝ) (γ : ℝ)
  (V₀ : S → ℝ) : ℕ → (S → ℝ) :=
  fixed_point_seq (bellman_operator P r γ) V₀

-- Finally, we will use this global convergence theorem together with
-- Bellman equation existence of solution to prove a stronger result
-- Fix a policy π, then by iteratively applying the bellman equation
-- the sequence of functions V_n generated from this process converges
-- to the unique solution V_star

-- ∃ ! V_star such that V_n → V_star
theorem iterate_eval_conv {S : Type*} [Fintype S] (P : S → S → ℝ) (r : S → ℝ)
  (γ : ℝ) (hP : stochastic_kernel_cond P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (V₀ : S → ℝ) :
  ∃! V_star : S → ℝ, Filter.Tendsto (bellman_it_seq P r γ V₀) Filter.atTop (nhds V_star) := by
  obtain ⟨V_star, hV_star, huniq⟩ := by exact bellman_eq_uniq_existence_of_solution P r γ hP hγ0 hγ1

  -- d(Vₙ, V_star) ≤ γ ^ n * d(V₀, V_star),
  have hbound : ∀ n : ℕ, dist (bellman_it_seq P r γ V₀ n) V_star ≤ γ ^ n * dist V₀ V_star := by
    obtain ⟨W, ⟨hWfix, hWbound⟩, -⟩ :=
      global_conv_of_contraction_dynamics (bellman_operator P r γ) γ
      (bellman_is_contraction P r γ hP hγ0 hγ1) V₀
    have hWeq : W = V_star := huniq W hWfix
    simpa [bellman_it_seq, hWeq] using hWbound

  -- Prove the sequence converges via the geometric bound
  have hb : Filter.Tendsto (fun n : ℕ => γ ^ n * dist V₀ V_star) Filter.atTop (nhds 0) := by
    have hpow : Filter.Tendsto (fun n : ℕ => γ ^ n) Filter.atTop (nhds 0) :=
      by exact tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1
    simpa using hpow.mul_const (dist V₀ V_star)

  -- Squeeze thm: 0 ≤ d(Vₙ, V_star) ≤ γ ^ n * d(V₀, V_star) → 0
  have hdist : Filter.Tendsto (fun n : ℕ => dist (bellman_it_seq P r γ V₀ n) V_star) Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact dist_nonneg
    · exact hbound
    · exact hb

  use V_star
  constructor
  · exact tendsto_iff_dist_tendsto_zero.mpr hdist -- d(Vₙ V_star) → 0 ↔ Vₙ → V_star
  · intro y hy
    have hconv : Filter.Tendsto (bellman_it_seq P r γ V₀) Filter.atTop (nhds V_star) :=
      by exact tendsto_iff_dist_tendsto_zero.mpr hdist -- uniqueness of limit
    exact tendsto_nhds_unique hy hconv
