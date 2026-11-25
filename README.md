# twin-beams-lean

[![Lean Action CI](https://github.com/ldsufrpe/twin-beams-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/ldsufrpe/twin-beams-lean/actions/workflows/lean_action_ci.yml)

Lean 4 verification of Section 6 (Eqs. (6.3)–(6.5), (6.9)–(6.14)) of the manuscript below.

Machine-checked proofs, in Lean 4 with Mathlib, of the finite-path results of Section 6 of
*From Non-Kolmogorov Refractive-Index Spectra to Measured Twin-Beam Dynamics*.
Equation numbers refer to the version of the manuscript of November 2026.

## Where to start

Read **`Formalization/Statements.lean`**. It restates every definition and every verified
statement, in the order of the PDF, with the equation it corresponds to. Each restatement is
checked by Lean against the theorem actually proved, so that file is an exact account of what was
verified. The other files hold the proofs.

| File                                       | PDF                 | Content                                        |
|--------------------------------------------|---------------------|------------------------------------------------|
| `Formalization/Statements.lean`            | Section 6           | all statements, no proofs                      |
| `Formalization/PathFilter.lean`            | (6.3), (6.4), (6.9) | the filter `F(s, S, P)` and its closed form    |
| `Formalization/TwoBranch.lean`             | (6.5)               | double integral (6.2) → two branches           |
| `Formalization/LongitudinalMoments.lean`   | (6.10)–(6.13)       | `T_{m,j}`, `W_m`, and the identity behind them |
| `Formalization/FinitePathSeries.lean`      | (6.14)              | the series, from the premises below            |

## What is verified

| PDF                     | Lean theorem                                   | Remark                                      |
|-------------------------|------------------------------------------------|---------------------------------------------|
| (6.3)/(6.9)             | `pathFilter_eq`                                | for every real `s` (PDF: `0 ≤ s ≤ S`)       |
| (6.4)                   | `pathFilter_full`                              |                                             |
| —                       | `pathFilter_self`, `pathFilter_nonneg`         | `F(S) = 0`; `F ≥ 0` if `P ≥ 0`, `0 ≤ s ≤ S` |
| (6.5)                   | `double_integral_eq_folded`, `folded_eq_two_branches`, `double_integral_eq_two_branches` | for any continuous `g`; evenness only for the 2nd equality |
| (6.12)                  | `longMoment_eq_sum`                            | for every `j` (PDF: `j ∈ {0, 1, 3}`)        |
| (6.10)–(6.13)           | `integral_filter_branches`                     | `∫₀^S F {[(s-a)²+Q²]^m + [(s+a)²+Q²]^m} ds = W_m` |
| after (6.13)            | `branchPoly_polynomial`                        | `W_m` is a polynomial in `S, P, a, b, c`    |
| —                       | `branchPoly_neg`                               | `W_m` is even in `a`                        |
| (6.14)                  | `finite_path_series`                           | from the four premises below                |
| Proposition 2           | `finite_path_series_summable`                  | (6.14) converges absolutely                 |

A dash means the statement is not in the PDF; it is a by-product of the proofs.

Not covered: the cross term of the tensor (6.15) (the Lean coefficient is `b_i²`, so only the
diagonal covariances are formalized), (6.16)–(6.17), the 2012 kernels (6.6)–(6.8), and Sections
2–5 and 7 onwards.

## What is taken as given

Eq. (6.14) is proved from four statements of the PDF, collected in the structure `Premises`
(`FinitePathSeries.lean`), which enter as hypotheses. They involve objects that are not
formalized here: the mean-square calculus behind (6.2), the spherical Bessel functions behind
(5.10), the Meijer G-function in (4.9), and the integral (4.2) that defines `M_n`.

1. Eq. (6.2), the double integral for `B_i`;
2. Eq. (5.10), the series for the kernel `K_i`, at every real `x` (its absolute convergence is not
   assumed; it is proved);
3. Eq. (4.9), `M_n = 𝒢_n / (2Γ(ν))`;
4. the bound `|M_n| ≤ C Γ(n + 3/2)`, which follows from (4.3) with `C = ½ q_t^{-2ν}`.

Everything else is proved. In particular, the proof of (6.14) justifies the exchange of the sum
(5.10) with the integral over `[0, S]` (dominated convergence; the key bound is
`Γ(m + 3/2)/(2m+1)! ≤ 1/m!`, `gamma_div_factorial_le`).

No statement uses `sorry` or an added axiom: `#print axioms` reports only Lean's standard
`propext`, `Classical.choice` and `Quot.sound` for every theorem above.

## Notation

| Lean                         | PDF                                                  |
|------------------------------|------------------------------------------------------|
| `pathFilter s S P`           | `F(s, S, P)`, with `L = S + P` written out           |
| `f₀ S P`, `f₁ S P`, `f₃`     | `f₀`, `f₁`, `f₃` of (6.9)                            |
| `longMoment m j S a Q`       | `T_{m,j}(a, Q)` of (6.10)                             |
| `branchPoly m S P a Q`       | `W_m(a, Q)` of (6.13)                                |
| `kernelTerm kₜ bᵢ b c M n x` | `n`-th term of (5.10), without `D_H`                  |
| `seriesTerm S P a Q kₜ bᵢ 𝒢 n` | `n`-th term of (6.14), without `D_H/(4Γ(ν))`       |
| `Real.Gamma (H + 3 / 2)`     | `Γ(ν)`                                               |
| `∫ x in u..v, f x`           | oriented integral from `u` to `v`                    |
| `∑' n : ℕ, f (n + 1)`        | `Σ_{n≥1} f(n)`                                       |

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (`lean-toolchain`) is the
stable release `leanprover/lean4:v4.34.1`, and Mathlib is pinned to the same tag (`lakefile.toml`;
exact commits in `lake-manifest.json`).

```sh
git clone https://github.com/ldsufrpe/twin-beams-lean.git
cd twin-beams-lean
lake exe cache get   # download compiled Mathlib (a few GB)
lake build           # check all proofs; succeeds with no errors and no warnings
```

## Citation

This formalization accompanies the article (manuscript in preparation):

I. Roa González, M. Sepúlveda, L. D. da Silva and D. G. Pérez, *From Non-Kolmogorov
Refractive-Index Spectra to Measured Twin-Beam Dynamics*.

See `CITATION.cff`.

## License

Apache License 2.0; see `LICENSE`.
