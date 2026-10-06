import Mathlib

/-!
# Banach fixed-point theorem

A direct proof using geometric estimates on the iterates of a contraction,
completeness, continuity, and uniqueness of limits.
-/

structure contraction {X : Type*} [MetricSpace X] (f : X → X) (c : ℝ) : Prop where
  lipschitz : ∀ x y, dist (f x) (f y) ≤ c * dist x y
  lt_one : c < 1
  nonneg : 0 ≤ c

-- ε δ proof of continuity using contraction
lemma contraction_continuous {X : Type*} [MetricSpace X] (f : X → X)
  (c : ℝ) (hf : contraction f c) : Continuous f := by
    rw [Metric.continuous_iff]
    intro b ε hε
    use ε / (c + 1)
    have h_pos : 0 < c + 1 := by
      calc
        0 ≤ c := by exact hf.nonneg
        _ < c + 1 := by exact lt_add_one c
    constructor
    · exact div_pos hε h_pos
    · intro a hdist
      calc
        dist (f a) (f b) ≤ c * (dist a b) := by exact hf.lipschitz (a) (b)
        _ ≤ c * (ε / (c + 1)) := by
          exact mul_le_mul_of_nonneg_left (le_of_lt hdist) hf.nonneg
        _ < ε := by
          rw [← mul_div_assoc]
          apply (div_lt_iff₀ h_pos).2
          nlinarith [hε]

-- Choose any (x_0) ∈ X
-- Let x_(n + 1) = f (x_n)
def fixed_point_seq {X : Type*} (f : X → X) (x₀ : X) : ℕ → X
  | 0 => x₀
  | n + 1 => f (fixed_point_seq f x₀ n)

theorem banach_fixed_point {X : Type*} [MetricSpace X] [CompleteSpace X]
  [Nonempty X] (f : X → X) (c : ℝ) (hf : contraction f c) :
  ∃! x, f x = x
  := by
    let x₀ : X := Classical.choice (inferInstance : Nonempty X)
    let x : ℕ → X := fixed_point_seq f x₀

    -- |x_(j+1) - x_j| ≤ c^j |x_1 - x_0|
    have hb : ∀ (j : ℕ), dist (x (j + 1)) (x j) ≤ c^j * dist (x 1) (x 0) := by
      intro j
      induction j with
      | zero =>
        linarith
      | succ j ih =>
        calc
          dist (x (j + 1 + 1)) (x (j + 1)) = dist (f (x (j + 1))) (f (x j)) := by rfl
          _ ≤ c * dist (x (j + 1)) (x j) := by exact hf.lipschitz (x (j + 1)) (x j)
          _ ≤ c * (c ^ j * dist (x 1) (x 0)) := by
            apply mul_le_mul_of_nonneg_left ih
            exact hf.nonneg
          _ = c ^ (j + 1) * dist (x 1) (x 0) := by ring_nf

    -- |x_m - x_n| ≤ c^n / (1-c) |x_1 - x_0|
    have hx_geo : ∀ n m : ℕ, n ≤ m → dist (x n) (x m) ≤ c ^ n / (1 - c) * dist (x 1) (x 0) := by
      intro n m hnm
      calc
        dist (x n) (x m) ≤ ∑ k ∈ Finset.Ico n m, c ^ k * dist (x 1) (x 0) := by
          apply dist_le_Ico_sum_of_dist_le hnm
          intro k hk1 hk2
          simpa [dist_comm] using hb k
        _ = (∑ k ∈ Finset.Ico n m, c ^ k) * dist (x 1) (x 0) := by exact
        (Finset.sum_mul (Finset.Ico n m) (fun k => c ^ k) (dist (x 1) (x 0))).symm
        _ ≤ (c ^ n / (1 - c)) * dist (x 1) (x 0) := by
          apply mul_le_mul_of_nonneg_right
          · exact geom_sum_Ico_le_of_lt_one hf.nonneg hf.lt_one
          · exact dist_nonneg

    let b := fun n =>
      c ^ n / (1 - c) * dist (x 1) (x 0)

    -- x_n is cauchy
    have hx_cauchy : CauchySeq x := by
      apply cauchySeq_of_le_tendsto_0' b
      intro n m hnm
      exact Metric.mem_closedBall.mp (hx_geo n m hnm)
      simpa [b, div_eq_mul_inv, mul_assoc] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hf.nonneg hf.lt_one).mul_const
        ((1 - c)⁻¹ * dist (x 1) (x 0))

    -- x_star is our fixed point
    -- hx_star says that lim x_n = x_star
    obtain ⟨x_star, hx_star⟩ := cauchySeq_tendsto_of_complete hx_cauchy
    use x_star

    -- lim f(x_n) = f (lim x_n)
    have hscc : Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds (f x_star)) := by
      exact (contraction_continuous f c hf).tendsto x_star |>.comp hx_star

    -- lim x_(n+1) = x_star
    have hshift : Filter.Tendsto (fun n => x (n + 1)) Filter.atTop (nhds x_star) := by
      exact hx_star.comp (Filter.tendsto_add_atTop_nat 1)

    -- lim f(x_n) = x_star
    have hconv : Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds x_star) := by
        simpa [x, fixed_point_seq] using hshift

    have hfx : f x_star = x_star := by
      exact tendsto_nhds_unique hscc hconv

    constructor
    · exact hfx
    · intro y hfy
      by_contra hne
      push Not at hne
      have hpos : 0 < dist (x_star) (y) := by
        exact dist_pos.mpr (id (Ne.symm hne))

      have hdistne : dist (x_star) (y) < dist (x_star) (y) := by
        calc
          dist (x_star) (y) = dist (f x_star) (f y) := by
            rw [hfx, hfy]
          _ ≤ c * dist (x_star) (y) := by
            exact hf.lipschitz x_star y
          _ < dist (x_star) (y) := by
            exact (mul_lt_iff_lt_one_left hpos).mpr hf.lt_one
      exact (lt_self_iff_false (dist x_star y)).mp hdistne
