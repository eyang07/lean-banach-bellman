# Banach Fixed Points and Discounted Bellman Equations in Lean 4

A small, hand-written formalization of the Banach fixed-point theorem and its
application to finite-state discounted policy evaluation. The project connects
an abstract result in metric-space analysis to convergence of an iterative
algorithm in dynamic programming.

## Main results

| Result | Lean declaration | File |
| --- | --- | --- |
| A contraction is continuous | `contraction_continuous` | [Banach.lean](BanachBellman/Banach.lean) |
| A contraction on a nonempty complete metric space has a unique fixed point | `banach_fixed_point` | [Banach.lean](BanachBellman/Banach.lean) |
| The discounted Bellman operator is a contraction | `bellman_is_contraction` | [FiniteBellman.lean](BanachBellman/FiniteBellman.lean) |
| The Bellman equation has a unique solution | `bellman_eq_uniq_existence_of_solution` | [FiniteBellman.lean](BanachBellman/FiniteBellman.lean) |
| Contraction iterates satisfy a geometric error bound | `global_conv_of_contraction_dynamics` | [FiniteBellman.lean](BanachBellman/FiniteBellman.lean) |
| Policy-evaluation iterates converge from any initial value function | `iterate_eval_conv` | [FiniteBellman.lean](BanachBellman/FiniteBellman.lean) |

## Mathematical setting

For a map `f : X → X` on a nonempty complete metric space, assume

```text
d(f(x), f(y)) ≤ c · d(x, y),    0 ≤ c < 1.
```

The proof constructs `xₙ₊₁ = f(xₙ)`, bounds successive distances by a geometric
sequence, proves the iterates are Cauchy, and uses completeness to obtain a
limit. Continuity shows that the limit is a fixed point; the contraction
inequality establishes uniqueness. This proof does not invoke mathlib's
Banach fixed-point theorem.

For a finite state space `S`, a stochastic transition kernel `P`, a reward
function `r : S → ℝ`, and a discount factor `0 ≤ γ < 1`, define

```text
(TV)(s) = r(s) + γ · ∑ s', P(s, s') · V(s').
```

The finite function space `S → ℝ` carries the uniform metric. Nonnegative
transition probabilities and row sums equal to one give

```text
d(TV, TW) ≤ γ · d(V, W).
```

Applying the project's Banach theorem yields a unique solution `V*` to
`TV* = V*`. For any initial `V₀`, the iteration `Vₙ₊₁ = TVₙ` satisfies

```text
d(Vₙ, V*) ≤ γⁿ · d(V₀, V*),
```

and converges to `V*`. The geometric bound is proved in
`global_conv_of_contraction_dynamics` and used in `iterate_eval_conv`.

The application models a fixed policy through its transition kernel and
reward function. It does not include optimization over actions. This is the
discounted Bellman equation for policy evaluation, not the Bellman–Ford
shortest-path algorithm.

## Build and inspect

Install Lean using [elan](https://github.com/leanprover/elan), then run from the
repository root:

```sh
lake exe cache get
lake build
lake env lean scripts/CheckAxioms.lean
```

The `lean-toolchain` file selects **Lean 4.33.0-rc2**. The Lake configuration and
committed manifest pin mathlib to
`985d97018f12d5ac61a60f551da15d7a4b1e7ac1` and its corresponding dependencies.
The first command downloads precompiled mathlib artifacts; the second checks
both proof modules. The final command checks that the main results use only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

To read the proofs interactively, open this folder in VS Code with the Lean 4
extension and start with `BanachBellman/Banach.lean`. The root module
`BanachBellman.lean` imports both files. A [GitHub Actions workflow template](ci/lean.yml) builds the project and runs
the axiom checks. To enable it, move the template to
`.github/workflows/lean.yml` and push using a GitHub login with permission to
write workflows, or create that file through the GitHub website.

## Authorship and background

The proofs were written by hand by [eyang07](https://github.com/eyang07),
originally in a working repository for the 2026 Utrecht summerschool on
formalising mathematics in Lean. This standalone project contains the two
personal proof files, with module paths and explanatory comments adapted for
presentation; it does not include the course lectures or exercises.

The project uses mathlib's foundational definitions, finite sums, metric and
topological results, and tactics. Its contribution is the explicit Banach
proof and the Bellman contraction and convergence proofs built on it.
