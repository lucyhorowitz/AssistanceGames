# AssistanceGames (readme by Claude)

A Lean 4 formalization of the results in **The Off-Switch Game** (Dylan
Hadfield-Menell, Anca Dragan, Pieter Abbeel, Stuart Russell, IJCAI 2017),
built on Mathlib.

The paper studies when a robot `R`, uncertain about a human `H`'s utility
function, has an incentive to leave its off switch alone rather than disable
it. The central quantity is the **deference incentive** — the difference
between `R`'s expected utility when it defers to `H` and its expected utility
when it acts unilaterally. The paper's claim is that this quantity is
nonnegative when `H` is rational, and that it stays positive under uncertainty
even when `H` is only approximately rational.

This repository states and machine-checks those results.

## Why formalize it

The paper's conclusions are load-bearing for an argument that shows up
throughout AI oversight: corrigibility can be obtained from utility
uncertainty rather than from a hard constraint. The informal statements carry
qualifiers — `H` must be "not too irrational", the belief must be
"nondegenerate" — that do real work in the proofs. Formalizing forces each of
those into an explicit hypothesis, which makes it visible exactly what the
result needs.

## Main definitions

| Definition | Meaning |
|---|---|
| `offSwitchGame α` | A belief `p` over utility parameters, a measurable utility `u : α → ℝ`, and a human policy `π : ℝ → ℝ` with `0 ≤ π ≤ 1`. `π r` is the probability `H` allows the action given utility gap `r`. |
| `deferenceIncentive G` | `𝔼[π(u)·u] − max(𝔼[u], 0)`. The paper's `Δ`. |
| `rationalPolicy` | The deterministic policy: allow iff the utility gap is nonnegative. |
| `noisilyRationalPolicy β` | The logistic (Boltzmann-rational) policy with inverse temperature `β`. |
| `HasGaussianBelief G μ v` | The pushforward of the belief along `u` is `gaussianReal μ v`, matching the paper's `Bᴿ(Uₐ) = N(Uₐ; μ, σ²)`. |
| `HasFiniteExpectations` | The integrability side conditions the expectations require. |

Note that rationality is **not** built into `offSwitchGame`. The structure
assumes only that `π` is a probability. Every rationality assumption appears
as an explicit hypothesis on the theorem that needs it.

## Main results

**Equation 1.** `deferenceIncentive_eq_min` — the deference incentive equals
`min 𝔼[π(u)·u − u] 𝔼[π(u)·u]`.

**Theorem 1.** `deferenceIncentive_nonneg` — if `H` follows the rational
policy, the deference incentive is nonnegative. `R` never loses by leaving the
switch alone.

**Strict version.** `deferenceIncentive_pos_of_nonempty_support` — if in
addition the belief puts positive mass on both positive and negative utility,
the incentive is strictly positive. This makes precise what "genuine
uncertainty" has to mean: it is not variance, it is mass on both signs.

**Converse, point-mass beliefs.** `optimal_iff_rationalPolicy_of_dirac` — for a
Dirac belief at `x` with `u x ≠ 0`, deference is optimal *iff* `H` is rational
at `x`. See Limitations: this direction is currently proved only for Dirac
beliefs.

**Theorem 2 / Equation 7.** `gaussian_deferenceIncentive` — under a Gaussian
belief `N(μ, σ²)` and a differentiable policy,

```
Δ = σ²·𝔼[π̇] − |μ|·Pr(C)
```

where `Pr(C)` is the probability that `H` corrects `R` (`1 − 𝔼[π]` when
`μ ≥ 0`, and `𝔼[π]` otherwise). Proved via Stein's lemma.

**When deference is strictly optimal.** `deference_optimal_iff` — `Δ > 0` iff
`(|μ|/σ²)·Pr(C) < 𝔼[π̇]`. The tradeoff in closed form: `R` defers when the
human's policy is sensitive enough to the utility gap, relative to how
confident `R` already is.

**Failure case.** `deference_neg_of_gradient_neg` — if `𝔼[π̇] < 0`, the
deference incentive is negative. A human whose willingness to allow the action
*decreases* as the action gets better destroys the incentive entirely.

## Supporting material

`AssistanceGames.Probability.Gaussian.Stein` proves Stein's lemma for
`gaussianReal`: for suitably integrable differentiable `f`,
`𝔼[(X − μ)f(X)] = σ²·𝔼[f'(X)]`. This is independent of the off-switch setting
and is the most reusable part of the repository.

<!-- TODO: check whether Mathlib already has this before claiming it is new.
     Ask on the leanprover Zulip #maths or #Is-there-code-for-X channel. If
     it is not there, this is worth a Mathlib PR on its own. -->

## Limitations

- **The converse is Dirac-only.** `optimal_iff_rationalPolicy_of_dirac`
  requires the belief to be a point mass. The general statement — deference
  optimal implies `H` rational, for arbitrary beliefs — is not proved here.
  <!-- TODO: say which it is. Did the general proof resist you, or do you
       think it needs a hypothesis the paper does not state? The second is a
       more interesting sentence and worth writing out if you believe it. -->
- **The noisy-rational policy is defined but not specialized.** The Gaussian
  results are stated for any `IsDifferentiablePolicy`. `noisilyRationalPolicy β`
  satisfies that hypothesis, but there is currently no theorem computing
  `𝔼[π̇]` for the logistic policy specifically, which is what the paper's
  quantitative claims about β rest on.
- **Fully observable, single-shot only.** No partially observable variant, and
  no sequential version.

## Building

```
lake exe cache get
lake build
```

## Reference

Dylan Hadfield-Menell, Anca Dragan, Pieter Abbeel, Stuart Russell.
*The Off-Switch Game.* IJCAI 2017, pp. 220–227.
[doi:10.24963/ijcai.2017/32](https://doi.org/10.24963/ijcai.2017/32)
