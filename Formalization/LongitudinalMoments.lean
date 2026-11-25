import Formalization.PathFilter
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Longitudinal moments `T_{m,j}` and the polynomial `W_m` (PDF Section 6.4, Eqs. (6.10)–(6.13))

## Main statements

* `longMoment_eq_sum`        — Eq. (6.12): closed form of `T_{m,j}(a, Q)`, for every `m, j ∈ ℕ`.
* `integral_filter_branches` — the identity behind (6.13):
  `∫₀^S F(s,S,P) {[(s-a)²+Q²]^m + [(s+a)²+Q²]^m} ds = W_m(a, Q)`.
* `branchPoly_polynomial`    — the sentence after (6.13): `W_m` is a polynomial in
  `S, P, a, b, c`, and depends on `(b, c)` only through `Q² = b² + c²`.
* `branchPoly_neg`           — `W_m(-a, Q) = W_m(a, Q)` (not stated in the PDF).

## Notation (Lean ↔ PDF)

`longMoment m j S a Q` is `T_{m,j}(a, Q)` of (6.10); `branchPoly m S P a Q` is `W_m(a, Q)` of
(6.13). The PDF takes `j ∈ {0, 1, 3}`; `longMoment_eq_sum` holds for every `j`. The convention
`W_{-1} := 0` is not needed here: `m` ranges over `ℕ` (see `FinitePathSeries.lean`).
-/

namespace PathCov

open intervalIntegral

/-! ## Definitions -/

/-- `T_{m,j}(a, Q) = ∫₀^S s^j [(s - a)² + Q²]^m ds`, PDF Eq. (6.10). -/
noncomputable def longMoment (m j : ℕ) (S a Q : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..S, s ^ j * ((s - a) ^ 2 + Q ^ 2) ^ m

/-- `W_m(a, Q) = Σ_{j ∈ {0,1,3}} f_j [T_{m,j}(a,Q) + T_{m,j}(-a,Q)]`, PDF Eq. (6.13),
written out term by term. -/
noncomputable def branchPoly (m : ℕ) (S P a Q : ℝ) : ℝ :=
  f₀ S P * (longMoment m 0 S a Q + longMoment m 0 S (-a) Q) +
  f₁ S P * (longMoment m 1 S a Q + longMoment m 1 S (-a) Q) +
  f₃ * (longMoment m 3 S a Q + longMoment m 3 S (-a) Q)

/-! ## Eq. (6.12) -/

/-- Paper: PDF Eq. (6.12) — for every `m, j ∈ ℕ` and all real `S, a, Q`,
`T_{m,j}(a,Q) = Σ_{k=0}^m Σ_{ℓ=0}^j C(m,k) C(j,ℓ) Q^{2(m-k)} a^{j-ℓ}
  [(S-a)^{2k+ℓ+1} - (-a)^{2k+ℓ+1}] / (2k+ℓ+1)`.

The PDF takes `j ∈ {0, 1, 3}`. Proof as in the PDF: substitution `v = s - a`, the two binomial
expansions (6.11), and the integral of a monomial. -/
theorem longMoment_eq_sum (m j : ℕ) (S a Q : ℝ) :
    longMoment m j S a Q =
      ∑ k ∈ Finset.range (m + 1), ∑ ℓ ∈ Finset.range (j + 1),
        (m.choose k : ℝ) * (j.choose ℓ : ℝ) * Q ^ (2 * (m - k)) * a ^ (j - ℓ) *
          (((S - a) ^ (2 * k + ℓ + 1) - (-a) ^ (2 * k + ℓ + 1)) / ((2 * k + ℓ + 1 : ℕ) : ℝ)) := by
  have hexp : ∀ v : ℝ, (v + a) ^ j * (v ^ 2 + Q ^ 2) ^ m =
      ∑ k ∈ Finset.range (m + 1), ∑ ℓ ∈ Finset.range (j + 1),
        ((m.choose k : ℝ) * (j.choose ℓ : ℝ) * Q ^ (2 * (m - k)) * a ^ (j - ℓ)) *
          v ^ (2 * k + ℓ) := by
    intro v
    rw [add_pow, add_pow, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun ℓ _ => ?_
    ring
  have h1 := intervalIntegral.integral_comp_add_right (a := -a) (b := S - a)
    (fun s : ℝ => s ^ j * ((s - a) ^ 2 + Q ^ 2) ^ m) a
  simp only [neg_add_cancel, sub_add_cancel, add_sub_cancel_right] at h1
  rw [longMoment, ← h1]
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_finsetSum
    (fun ℓ _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  ring

/-! ## The identity behind Eq. (6.13) -/

/-- One `j`-block of the `W_m` identity (auxiliary). -/
theorem integral_pair (m j : ℕ) (S a Q c : ℝ) :
    ∫ s in (0 : ℝ)..S, c * (s ^ j * ((s - a) ^ 2 + Q ^ 2) ^ m + s ^ j * ((s + a) ^ 2 + Q ^ 2) ^ m)
      = c * (longMoment m j S a Q + longMoment m j S (-a) Q) := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [longMoment, sub_neg_eq_add]

/-- Paper: PDF Eqs. (6.10)–(6.13) — for every `m ∈ ℕ` and all real `S, P, a, Q`,
`∫₀^S F(s,S,P) {[(s-a)²+Q²]^m + [(s+a)²+Q²]^m} ds = W_m(a, Q)`.

This is the identity the PDF uses when it applies (6.12)–(6.13) inside the proof of (6.14).
Proof: insert `F = f₀ + f₁ s + f₃ s³` (`pathFilter_eq`) and use linearity. -/
theorem integral_filter_branches (m : ℕ) (S P a Q : ℝ) :
    ∫ s in (0 : ℝ)..S, pathFilter s S P * (((s - a) ^ 2 + Q ^ 2) ^ m + ((s + a) ^ 2 + Q ^ 2) ^ m)
      = branchPoly m S P a Q := by
  have hpt : ∀ s : ℝ,
      pathFilter s S P * (((s - a) ^ 2 + Q ^ 2) ^ m + ((s + a) ^ 2 + Q ^ 2) ^ m) =
        (f₀ S P * (s ^ 0 * ((s - a) ^ 2 + Q ^ 2) ^ m + s ^ 0 * ((s + a) ^ 2 + Q ^ 2) ^ m) +
          f₁ S P * (s ^ 1 * ((s - a) ^ 2 + Q ^ 2) ^ m + s ^ 1 * ((s + a) ^ 2 + Q ^ 2) ^ m)) +
          f₃ * (s ^ 3 * ((s - a) ^ 2 + Q ^ 2) ^ m + s ^ 3 * ((s + a) ^ 2 + Q ^ 2) ^ m) := by
    intro s
    rw [pathFilter_eq]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    integral_pair, integral_pair, integral_pair]
  rfl

/-! ## Polynomial structure of `W_m` (sentence after Eq. (6.13)) -/

open MvPolynomial in
/-- Auxiliary: the closed form of `T_{m,j}` as a polynomial in `(S, P, a, b, c)` (variables
`0, 1, 2, 3, 4`), with `Q²` replaced by `b² + c²` and the shift `a` replaced by a polynomial `σ`. -/
noncomputable def momentPoly (m j : ℕ) (σ : MvPolynomial (Fin 5) ℝ) : MvPolynomial (Fin 5) ℝ :=
  ∑ k ∈ Finset.range (m + 1), ∑ ℓ ∈ Finset.range (j + 1),
    C ((m.choose k : ℝ) * (j.choose ℓ : ℝ) / ((2 * k + ℓ + 1 : ℕ) : ℝ)) *
      (X 3 ^ 2 + X 4 ^ 2) ^ (m - k) * σ ^ (j - ℓ) *
      ((X 0 - σ) ^ (2 * k + ℓ + 1) - (-σ) ^ (2 * k + ℓ + 1))

open MvPolynomial in
theorem eval_momentPoly (m j : ℕ) (σ : MvPolynomial (Fin 5) ℝ) (S P a b c e Q : ℝ)
    (hσ : eval ![S, P, a, b, c] σ = e) (hQ : Q ^ 2 = b ^ 2 + c ^ 2) :
    eval ![S, P, a, b, c] (momentPoly m j σ) = longMoment m j S e Q := by
  rw [longMoment_eq_sum, momentPoly]
  simp only [map_sum, map_mul, map_pow, map_sub, map_neg, map_add, eval_C, eval_X, hσ]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun ℓ _ => ?_
  rw [pow_mul, hQ]
  simp
  ring

open MvPolynomial in
/-- Auxiliary: the polynomial representing `W_m`. -/
noncomputable def branchMvPoly (m : ℕ) : MvPolynomial (Fin 5) ℝ :=
  C (2 : ℝ) * (X 0 ^ 3 * C (1 / 3 : ℝ) + X 1 * X 0 ^ 2 + X 0 * X 1 ^ 2) *
      (momentPoly m 0 (X 2) + momentPoly m 0 (-X 2)) +
    (-(X 0 ^ 2 + C (2 : ℝ) * X 1 * X 0 + C (2 : ℝ) * X 1 ^ 2)) *
      (momentPoly m 1 (X 2) + momentPoly m 1 (-X 2)) +
    C (1 / 3 : ℝ) * (momentPoly m 3 (X 2) + momentPoly m 3 (-X 2))

open MvPolynomial in
theorem branchPoly_eq_eval (m : ℕ) (S P a b c Q : ℝ) (hQ : Q ^ 2 = b ^ 2 + c ^ 2) :
    branchPoly m S P a Q = eval ![S, P, a, b, c] (branchMvPoly m) := by
  have hX : eval ![S, P, a, b, c] (X 2 : MvPolynomial (Fin 5) ℝ) = a := by simp
  have hnX : eval ![S, P, a, b, c] (-X 2 : MvPolynomial (Fin 5) ℝ) = -a := by simp
  simp only [branchMvPoly, map_add, map_mul, eval_momentPoly m _ _ S P a b c _ Q hX hQ,
    eval_momentPoly m _ _ S P a b c _ Q hnX hQ]
  simp only [branchPoly, f₀, f₁, f₃, map_add, map_mul, map_pow, map_neg, eval_C, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Paper: PDF, sentence after Eq. (6.13) ("all path integrals needed for Eq. (5.10) are finite
polynomial expressions in `S, P, a, b, c`") — for every `m ∈ ℕ` there is a real polynomial `p` in
five variables such that `W_m(a, Q) = p(S, P, a, b, c)` whenever `Q² = b² + c²`; and the value of
`p` depends on `(b, c)` only through `b² + c²`. -/
theorem branchPoly_polynomial (m : ℕ) :
    ∃ p : MvPolynomial (Fin 5) ℝ,
      (∀ S P a b c Q : ℝ, Q ^ 2 = b ^ 2 + c ^ 2 →
        branchPoly m S P a Q = MvPolynomial.eval ![S, P, a, b, c] p) ∧
      (∀ S P a b c b' c' : ℝ, b ^ 2 + c ^ 2 = b' ^ 2 + c' ^ 2 →
        MvPolynomial.eval ![S, P, a, b, c] p = MvPolynomial.eval ![S, P, a, b', c'] p) := by
  refine ⟨branchMvPoly m, fun S P a b c Q hQ => branchPoly_eq_eval m S P a b c Q hQ, ?_⟩
  intro S P a b c b' c' h
  have hq : Real.sqrt (b ^ 2 + c ^ 2) ^ 2 = b ^ 2 + c ^ 2 := Real.sq_sqrt (by positivity)
  rw [← branchPoly_eq_eval m S P a b c _ hq,
    branchPoly_eq_eval m S P a b' c' (Real.sqrt (b ^ 2 + c ^ 2)) (hq.trans h)]

/-- Paper: none — not stated in the PDF. `W_m` is even in `a`: `W_m(-a, Q) = W_m(a, Q)`. -/
theorem branchPoly_neg (m : ℕ) (S P a Q : ℝ) : branchPoly m S P (-a) Q = branchPoly m S P a Q := by
  simp only [branchPoly, neg_neg]
  ring

/-! ## Non-vacuity witness -/

/-- The hypothesis `Q² = b² + c²` of `branchPoly_polynomial` can hold with `Q ≠ 0`; and the
closed form (6.12) reproduces `∫₀¹ s² ds = 1/3` at `m = 1, j = 0, a = Q = 0`. -/
theorem longMoment_witness :
    longMoment 1 0 1 0 0 = 1 / 3 ∧ ∃ b c Q : ℝ, Q ^ 2 = b ^ 2 + c ^ 2 ∧ Q ≠ 0 := by
  refine ⟨?_, 3, 4, 5, by norm_num, by norm_num⟩
  rw [longMoment_eq_sum]
  simp [Finset.sum_range_succ]
  norm_num

end PathCov
