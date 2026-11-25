import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The path filter `F(s, S, P)` (PDF Sections 6.1 and 6.4, Eqs. (6.3), (6.4), (6.9))

PDF definition (6.3), with `L = S + P`:
`F(s, S, P) = 2 ∫₀^{S-s} (L - ξ)(L - ξ - s) dξ`.

## Main statements

* `pathFilter_eq`       — Eqs. (6.3)/(6.9): `F = f₀ + f₁ s + f₃ s³`, for every real `s`.
* `pathFilter_full`     — Eq. (6.4): `F(s, L, 0) = (L - s)²(2L + s)/3`.
* `pathFilter_self`     — `F(S, S, P) = 0` (not stated in the PDF).
* `pathFilter_nonneg`   — `F ≥ 0` on `0 ≤ s ≤ S` when `P ≥ 0` (not stated in the PDF).

## Notation (Lean ↔ PDF)

`pathFilter s S P` is `F(s, S, P)`; `f₀ S P`, `f₁ S P`, `f₃` are `f₀`, `f₁`, `f₃` of (6.9).
The Lean integral `∫ ξ in a..b` is the oriented integral, so `F(s, S, P)` is defined for every
real `s`, including `s > S`.
-/

namespace PathCov

open intervalIntegral

/-! ## Definitions -/

/-- The path filter of PDF Eq. (6.3): `F(s, S, P) = 2 ∫₀^{S-s} (L - ξ)(L - ξ - s) dξ`,
`L = S + P`. -/
noncomputable def pathFilter (s S P : ℝ) : ℝ :=
  2 * ∫ ξ in (0 : ℝ)..(S - s), (S + P - ξ) * (S + P - ξ - s)

/-- `f₀ = 2 (S³/3 + P S² + S P²)`, PDF Eq. (6.9). -/
noncomputable def f₀ (S P : ℝ) : ℝ := 2 * (S ^ 3 / 3 + P * S ^ 2 + S * P ^ 2)

/-- `f₁ = -(S² + 2 P S + 2 P²)`, PDF Eq. (6.9). -/
noncomputable def f₁ (S P : ℝ) : ℝ := -(S ^ 2 + 2 * P * S + 2 * P ^ 2)

/-- `f₃ = 1/3`, PDF Eq. (6.9). -/
noncomputable def f₃ : ℝ := 1 / 3

/-! ## Main statements -/

/-- Paper: PDF Eqs. (6.3) and (6.9) — `F(s, S, P) = f₀ + f₁ s + f₃ s³`.

The PDF states it for `0 ≤ s ≤ S`; it holds for every real `s`, `S`, `P`.
Proof: an explicit antiderivative of the integrand. -/
theorem pathFilter_eq (s S P : ℝ) :
    pathFilter s S P = f₀ S P + f₁ S P * s + f₃ * s ^ 3 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (S - s),
      HasDerivAt
        (fun y : ℝ => y ^ 3 / 3 - (2 * (S + P) - s) * y ^ 2 / 2 + (S + P) * (S + P - s) * y)
        ((S + P - x) * (S + P - x - s)) x := by
    intro x _
    have h := (((hasDerivAt_pow 3 x).div_const 3).sub
      (((hasDerivAt_pow 2 x).const_mul (2 * (S + P) - s)).div_const 2)).add
      ((hasDerivAt_id' x).const_mul ((S + P) * (S + P - s)))
    exact h.congr_deriv (by norm_num; ring)
  have hint : IntervalIntegrable (fun x : ℝ => (S + P - x) * (S + P - x - s)) MeasureTheory.volume
      0 (S - s) :=
    (by fun_prop : Continuous fun x : ℝ => (S + P - x) * (S + P - x - s)).intervalIntegrable _ _
  rw [pathFilter, integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [f₀, f₁, f₃]
  ring

/-- Paper: PDF Eq. (6.4) — with `P = 0` and `S = L`, `F(s, L, 0) = (L - s)²(2L + s)/3`,
for every real `L` and `s`. -/
theorem pathFilter_full (s L : ℝ) : pathFilter s L 0 = (L - s) ^ 2 * (2 * L + s) / 3 := by
  rw [pathFilter_eq]
  simp only [f₀, f₁, f₃]
  ring

/-- Paper: none — not stated in the PDF. The filter vanishes at the end of the interval:
`F(S, S, P) = 0` for every real `S`, `P`. -/
theorem pathFilter_self (S P : ℝ) : pathFilter S S P = 0 := by
  rw [pathFilter_eq]
  simp only [f₀, f₁, f₃]
  ring

/-- Paper: none — not stated in the PDF. If `P ≥ 0` and `0 ≤ s ≤ S`, then `F(s, S, P) ≥ 0`
(the integrand of (6.3) is a product of two nonnegative factors). -/
theorem pathFilter_nonneg {s S P : ℝ} (hP : 0 ≤ P) (hs : 0 ≤ s) (hsS : s ≤ S) :
    0 ≤ pathFilter s S P := by
  unfold pathFilter
  apply mul_nonneg zero_le_two
  apply intervalIntegral.integral_nonneg (by linarith)
  intro ξ hξ
  obtain ⟨h1, h2⟩ := hξ
  apply mul_nonneg <;> linarith

/-! ## Auxiliary lemma -/

/-- `F` is continuous in `s` (it is a cubic polynomial). -/
theorem pathFilter_continuous (S P : ℝ) : Continuous (fun s => pathFilter s S P) := by
  have : (fun s => pathFilter s S P) = fun s => f₀ S P + f₁ S P * s + f₃ * s ^ 3 :=
    funext fun s => pathFilter_eq s S P
  rw [this]
  fun_prop

/-! ## Non-vacuity witness -/

/-- The hypotheses of `pathFilter_nonneg` can all hold, at a point where `F > 0`
(`S = 1`, `P = 0`, `s = 0`, where `F = 2/3`). -/
theorem pathFilter_witness :
    ∃ s S P : ℝ, 0 ≤ P ∧ 0 ≤ s ∧ s ≤ S ∧ pathFilter s S P = 2 / 3 := by
  refine ⟨0, 1, 0, le_rfl, le_rfl, zero_le_one, ?_⟩
  rw [pathFilter_eq]
  simp only [f₀, f₁, f₃]
  norm_num

end PathCov
