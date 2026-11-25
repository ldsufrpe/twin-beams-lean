import Formalization.FinitePathSeries

/-!
# What is verified: the statements, in the order of the PDF

This file is meant to be read on its own. It restates every definition and every main statement
of the formalization, with the PDF equation it corresponds to. Each restatement is an `example`
whose proof is the name of the theorem proved in the other files, so Lean checks that the text
written here is exactly what was proved. Proofs are in:

* `PathFilter.lean`          — Eqs. (6.3), (6.4), (6.9);
* `TwoBranch.lean`           — Eq. (6.5);
* `LongitudinalMoments.lean` — Eqs. (6.10)–(6.13);
* `FinitePathSeries.lean`    — Eq. (6.14).

Conventions. `∫ x in u..v, f x` is the oriented integral from `u` to `v`. `L = S + P` is written
out as `S + P`. `Γ(ν)` with `ν = H + 3/2` is `Real.Gamma (H + 3 / 2)`. `∑' n : ℕ, f (n + 1)` is
`Σ_{n≥1} f n`. Natural-number subtraction is truncated (`n - 2 = 0` when `n = 1`).

What is taken as given: only the four premises of (6.14) listed in `Premises` (Section 4 below).
Nothing else is assumed: every statement rests only on Lean's standard axioms.
-/

namespace PathCov

open intervalIntegral Set

variable (s S P L a b c b' c' Q bᵢ H kₜ D_H C B : ℝ) (m j : ℕ) (M 𝒢 : ℕ → ℝ) (K g : ℝ → ℝ)

/-! ## 1. The filter `F(s, S, P)` — Eqs. (6.3), (6.4), (6.9) -/

/-- Definition (6.3): `F(s, S, P) = 2 ∫₀^{S-s} (L - ξ)(L - ξ - s) dξ`. -/
example : pathFilter s S P = 2 * ∫ ξ in (0 : ℝ)..(S - s), (S + P - ξ) * (S + P - ξ - s) := rfl

/-- Coefficients of (6.9). -/
example : f₀ S P = 2 * (S ^ 3 / 3 + P * S ^ 2 + S * P ^ 2) := rfl
example : f₁ S P = -(S ^ 2 + 2 * P * S + 2 * P ^ 2) := rfl
example : f₃ = 1 / 3 := rfl

/-- Eqs. (6.3)/(6.9), for every real `s` (the PDF states it for `0 ≤ s ≤ S`). -/
example : pathFilter s S P = f₀ S P + f₁ S P * s + f₃ * s ^ 3 :=
  pathFilter_eq s S P

/-- Eq. (6.4). -/
example : pathFilter s L 0 = (L - s) ^ 2 * (2 * L + s) / 3 :=
  pathFilter_full s L

/-- Not stated in the PDF: `F(S, S, P) = 0`. -/
example : pathFilter S S P = 0 :=
  pathFilter_self S P

/-- Not stated in the PDF: `F ≥ 0` on `0 ≤ s ≤ S` when `P ≥ 0`. -/
example (hP : 0 ≤ P) (hs : 0 ≤ s) (hsS : s ≤ S) : 0 ≤ pathFilter s S P :=
  pathFilter_nonneg hP hs hsS

/-! ## 2. Two branches — Eq. (6.5)

Stated for every `g` continuous on `[-(S+|a|), S+|a|]`; the PDF uses `g = K_i(·, b, c)`. -/

/-- Eq. (6.5), first equality (no evenness needed). -/
example (hS : 0 ≤ S) (hg : ContinuousOn g (Icc (-(S + |a|)) (S + |a|))) :
    (∫ ξ' in (0 : ℝ)..S, ∫ ξ in (0 : ℝ)..S, (S + P - ξ) * (S + P - ξ') * g (ξ - ξ' - a))
      = (1 / 2) * ∫ s in (-S)..S, pathFilter |s| S P * g (s - a) :=
  double_integral_eq_folded S P a g hS hg

/-- Eq. (6.5), second equality (`g` even). -/
example (hS : 0 ≤ S) (hg : ContinuousOn g (Icc (-(S + |a|)) (S + |a|)))
    (heven : ∀ x ∈ Icc (-(S + |a|)) (S + |a|), g (-x) = g x) :
    (1 / 2) * ∫ s in (-S)..S, pathFilter |s| S P * g (s - a)
      = (1 / 2) * ∫ s in (0 : ℝ)..S, pathFilter s S P * (g (s - a) + g (s + a)) :=
  folded_eq_two_branches S P a g hS hg heven

/-- Eq. (6.5), both equalities combined. -/
example (hS : 0 ≤ S) (hg : ContinuousOn g (Icc (-(S + |a|)) (S + |a|)))
    (heven : ∀ x ∈ Icc (-(S + |a|)) (S + |a|), g (-x) = g x) :
    (∫ ξ' in (0 : ℝ)..S, ∫ ξ in (0 : ℝ)..S, (S + P - ξ) * (S + P - ξ') * g (ξ - ξ' - a))
      = (1 / 2) * ∫ s in (0 : ℝ)..S, pathFilter s S P * (g (s - a) + g (s + a)) :=
  double_integral_eq_two_branches S P a g hS hg heven

/-! ## 3. Longitudinal moments — Eqs. (6.10)–(6.13) -/

/-- Definition (6.10): `T_{m,j}(a, Q) = ∫₀^S s^j [(s - a)² + Q²]^m ds`. -/
example : longMoment m j S a Q = ∫ s in (0 : ℝ)..S, s ^ j * ((s - a) ^ 2 + Q ^ 2) ^ m := rfl

/-- Definition (6.13): `W_m(a, Q) = Σ_{j ∈ {0,1,3}} f_j [T_{m,j}(a,Q) + T_{m,j}(-a,Q)]`. -/
example : branchPoly m S P a Q =
    f₀ S P * (longMoment m 0 S a Q + longMoment m 0 S (-a) Q) +
    f₁ S P * (longMoment m 1 S a Q + longMoment m 1 S (-a) Q) +
    f₃ * (longMoment m 3 S a Q + longMoment m 3 S (-a) Q) := rfl

/-- Eq. (6.12), for every `j ∈ ℕ` (the PDF takes `j ∈ {0, 1, 3}`). -/
example : longMoment m j S a Q =
    ∑ k ∈ Finset.range (m + 1), ∑ ℓ ∈ Finset.range (j + 1),
      (m.choose k : ℝ) * (j.choose ℓ : ℝ) * Q ^ (2 * (m - k)) * a ^ (j - ℓ) *
        (((S - a) ^ (2 * k + ℓ + 1) - (-a) ^ (2 * k + ℓ + 1)) / ((2 * k + ℓ + 1 : ℕ) : ℝ)) :=
  longMoment_eq_sum m j S a Q

/-- The identity behind (6.13), used in the proof of (6.14). -/
example : ∫ s in (0 : ℝ)..S,
      pathFilter s S P * (((s - a) ^ 2 + Q ^ 2) ^ m + ((s + a) ^ 2 + Q ^ 2) ^ m)
    = branchPoly m S P a Q :=
  integral_filter_branches m S P a Q

/-- Sentence after (6.13): `W_m` is a polynomial in `S, P, a, b, c` that depends on `(b, c)` only
through `b² + c²`. -/
example : ∃ p : MvPolynomial (Fin 5) ℝ,
    (∀ S P a b c Q : ℝ, Q ^ 2 = b ^ 2 + c ^ 2 →
      branchPoly m S P a Q = MvPolynomial.eval ![S, P, a, b, c] p) ∧
    (∀ S P a b c b' c' : ℝ, b ^ 2 + c ^ 2 = b' ^ 2 + c' ^ 2 →
      MvPolynomial.eval ![S, P, a, b, c] p = MvPolynomial.eval ![S, P, a, b', c'] p) :=
  branchPoly_polynomial m

/-- Not stated in the PDF: `W_m` is even in `a`. -/
example : branchPoly m S P (-a) Q = branchPoly m S P a Q :=
  branchPoly_neg m S P a Q

/-! ## 4. The series (6.14) -/

/-- The `n`-th term of (5.10), without `D_H`. -/
example (n : ℕ) (x : ℝ) : kernelTerm kₜ bᵢ b c M n x =
    (-1) ^ (n + 1) * kₜ ^ (2 * n) * M n / ((2 * n + 1).factorial : ℝ) *
      (2 * n * (x ^ 2 + b ^ 2 + c ^ 2) ^ (n - 1) +
        4 * n * ((n : ℝ) - 1) * bᵢ ^ 2 * (x ^ 2 + b ^ 2 + c ^ 2) ^ (n - 2)) := rfl

/-- The `n`-th term of (6.14), without `D_H/(4Γ(ν))`. -/
example (n : ℕ) : seriesTerm S P a Q kₜ bᵢ 𝒢 n =
    (-1) ^ (n + 1) * kₜ ^ (2 * n) / ((2 * n + 1).factorial : ℝ) * 𝒢 n *
      (2 * n * branchPoly (n - 1) S P a Q +
        4 * n * ((n : ℝ) - 1) * bᵢ ^ 2 * branchPoly (n - 2) S P a Q) := rfl

/-- The premises taken as given: Eqs. (6.2), (5.10), (4.9), and `|M_n| ≤ C Γ(n + 3/2)`
(which follows from (4.3) with `C = ½ q_t^{-2ν}`). -/
example : Premises S P a b c bᵢ H kₜ D_H C B M 𝒢 K ↔
    (B = ∫ ξ' in (0 : ℝ)..S, ∫ ξ in (0 : ℝ)..S, (S + P - ξ) * (S + P - ξ') * K (ξ - ξ' - a)) ∧
    (∀ x : ℝ, K x = D_H * ∑' n : ℕ, kernelTerm kₜ bᵢ b c M (n + 1) x) ∧
    (∀ n : ℕ, |M n| ≤ C * Real.Gamma (n + 3 / 2)) ∧
    (∀ n : ℕ, M n = 𝒢 n / (2 * Real.Gamma (H + 3 / 2))) :=
  ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

/-- Eq. (6.14). -/
example (hS : 0 ≤ S) (hH : 0 < H) (hQ : Q ^ 2 = b ^ 2 + c ^ 2)
    (h : Premises S P a b c bᵢ H kₜ D_H C B M 𝒢 K) :
    B = D_H / (4 * Real.Gamma (H + 3 / 2)) * ∑' n : ℕ, seriesTerm S P a Q kₜ bᵢ 𝒢 (n + 1) :=
  finite_path_series S P a b c Q bᵢ H kₜ D_H C B M 𝒢 K hS hH hQ h

/-- Proposition 2: the series (6.14) converges absolutely. -/
example (hS : 0 ≤ S) (hH : 0 < H) (hQ : Q ^ 2 = b ^ 2 + c ^ 2)
    (h : Premises S P a b c bᵢ H kₜ D_H C B M 𝒢 K) :
    Summable (fun n : ℕ => |seriesTerm S P a Q kₜ bᵢ 𝒢 (n + 1)|) :=
  finite_path_series_summable S P a b c Q bᵢ H kₜ D_H C B M 𝒢 K hS hH hQ h

end PathCov
