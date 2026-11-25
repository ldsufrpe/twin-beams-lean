import Formalization.LongitudinalMoments
import Formalization.TwoBranch
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The finite-path series (6.14) (PDF Section 6.4, Proposition "Exact finite-path
spatiotemporal beam-wander covariance")

This file proves that (6.14) follows from four statements of the PDF, collected in the
structure `Premises`: Eqs. (6.2), (5.10), (4.9) and the bound `|M_n| ≤ C Γ(n + 3/2)`. These four
are taken as given. They involve objects that are not formalized here: the mean-square calculus
behind (6.2), the spherical Bessel functions behind (5.10), the Meijer G-function in (4.9), and
the integral (4.2) that defines `M_n`. Everything after them is proved.

## Main statements

* `finite_path_series`           — Eq. (6.14):
  `B_i = D_H/(4Γ(ν)) Σ_{n≥1} (-1)^{n+1} k_t^{2n}/(2n+1)! 𝒢_n [2n W_{n-1} + 4n(n-1) b_i² W_{n-2}]`.
* `finite_path_series_summable`  — the series (6.14) converges absolutely (Proposition 2).

The proof carries out in full the step that the PDF's proof justifies in one sentence:
integrating the series (5.10) term by term over `[0, S]`. It uses dominated convergence with
the summable majorant `summable_majorant`, which rests on `Γ(m + 3/2)/(2m+1)! ≤ 1/m!`
(`gamma_div_factorial_le`).

## Notation (Lean ↔ PDF)

| Lean                              | PDF                                                   |
|-----------------------------------|-------------------------------------------------------|
| `kₜ`, `bᵢ`, `D_H`, `H`            | `k_t`, `b_i` (`b_y = b`, `b_z = c`), `D_H`, `H`       |
| `Real.Gamma (H + 3 / 2)`          | `Γ(ν)`, `ν = H + 3/2`                                 |
| `M n`, `𝒢 n`                      | `M_n(q_t, H)` of (4.2), `𝒢_n(q_t, H)` of (6.14)       |
| `K`, `B`                          | `K_i(·, b, c)` of (5.6), `B_i(d, τ)` of (6.2)         |
| `a`, `b`, `c`, `Q`                | `V_x τ`, `d - V_y τ`, `-V_z τ`, `Q² = b² + c²`        |
| `kernelTerm kₜ bᵢ b c M n x`      | the `n`-th term of (5.10), without `D_H`               |
| `seriesTerm S P a Q kₜ bᵢ 𝒢 n`    | the `n`-th term of (6.14)                             |
| `branchPoly m S P a Q`            | `W_m(a, Q)` of (6.13)                                 |

`a`, `b`, `c` are arbitrary reals: every triple `(a, b, c)` is of the form
`(V_x τ, d - V_y τ, -V_z τ)`. `M`, `𝒢`, `K`, `B` are arbitrary and constrained only by
`Premises`. The PDF's convention `W_{-1} := 0` is replaced by natural-number exponents: at
`n = 1` the `W_{n-2}` term is multiplied by `n - 1 = 0`. The hypotheses `q_t > 0` and
`H ≤ 1/3` are not used.
-/

namespace PathCov

open MeasureTheory intervalIntegral Set

/-! ## Definitions -/

/-- The `n`-th term of the series (5.10), without the factor `D_H`:
`(-1)^{n+1} k_t^{2n} M_n / (2n+1)! · [2n (x²+b²+c²)^{n-1} + 4n(n-1) b_i² (x²+b²+c²)^{n-2}]`.
Exponents are natural numbers; for `n = 1` the second term carries the factor `n - 1 = 0`. -/
noncomputable def kernelTerm (kₜ bᵢ b c : ℝ) (M : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (-1) ^ (n + 1) * kₜ ^ (2 * n) * M n / ((2 * n + 1).factorial : ℝ) *
    (2 * n * (x ^ 2 + b ^ 2 + c ^ 2) ^ (n - 1) +
      4 * n * ((n : ℝ) - 1) * bᵢ ^ 2 * (x ^ 2 + b ^ 2 + c ^ 2) ^ (n - 2))

/-- The `n`-th term of the series (6.14), without the factor `D_H/(4Γ(ν))`:
`(-1)^{n+1} k_t^{2n} / (2n+1)! · 𝒢_n · [2n W_{n-1}(a,Q) + 4n(n-1) b_i² W_{n-2}(a,Q)]`. -/
noncomputable def seriesTerm (S P a Q kₜ bᵢ : ℝ) (𝒢 : ℕ → ℝ) (n : ℕ) : ℝ :=
  (-1) ^ (n + 1) * kₜ ^ (2 * n) / ((2 * n + 1).factorial : ℝ) * 𝒢 n *
    (2 * n * branchPoly (n - 1) S P a Q +
      4 * n * ((n : ℝ) - 1) * bᵢ ^ 2 * branchPoly (n - 2) S P a Q)

/-- The four statements of the PDF from which (6.14) is derived. They are taken as given.

* `B_eq_double_integral` — Eq. (6.2): `B = ∫₀^S∫₀^S (L-ξ)(L-ξ') K(ξ-ξ'-a) dξ dξ'`, `L = S + P`.
* `K_eq_series` — Eq. (5.10): `K(x) = D_H Σ_{n≥1} kernelTerm n x` for every real `x`. Absolute
  convergence of this series is not assumed; it is derived from `M_bound`.
* `M_bound` — `|M_n| ≤ C Γ(n + 3/2)` for every `n`. Not printed in the PDF; it follows from
  (4.3) with `C = ½ q_t^{-2ν}`, because `(y + q_t²)^{-ν} ≤ q_t^{-2ν}` for `y ≥ 0`.
* `M_eq_G` — Eq. (4.9): `M_n = 𝒢_n / (2Γ(ν))`, `ν = H + 3/2`. -/
structure Premises (S P a b c bᵢ H kₜ D_H C B : ℝ) (M 𝒢 : ℕ → ℝ) (K : ℝ → ℝ) : Prop where
  B_eq_double_integral :
    B = ∫ ξ' in (0 : ℝ)..S, ∫ ξ in (0 : ℝ)..S, (S + P - ξ) * (S + P - ξ') * K (ξ - ξ' - a)
  K_eq_series : ∀ x : ℝ, K x = D_H * ∑' n : ℕ, kernelTerm kₜ bᵢ b c M (n + 1) x
  M_bound : ∀ n : ℕ, |M n| ≤ C * Real.Gamma (n + 3 / 2)
  M_eq_G : ∀ n : ℕ, M n = 𝒢 n / (2 * Real.Gamma (H + 3 / 2))

/-! ## Step 1: a summable majorant for the series (5.10) -/

/-- Majorant of `|kernelTerm (n+1) x|` on `{x² + b² + c² ≤ Λ}`, given `|M_n| ≤ C Γ(n + 3/2)`. -/
noncomputable def majorant (C kₜ bᵢ Λ : ℝ) (n : ℕ) : ℝ :=
  (|kₜ| ^ (2 * (n + 1)) * |C|) *
    (Real.Gamma (((n + 1 : ℕ) : ℝ) + 3 / 2) / ((2 * (n + 1) + 1).factorial : ℝ)) *
    (2 * ((n + 1 : ℕ) : ℝ) * Λ ^ (n + 1 - 1) + 4 * ((n + 1 : ℕ) : ℝ) * (n : ℝ) * bᵢ ^ 2 *
      Λ ^ (n + 1 - 2))

/-- `Γ(m + 3/2)/(2m+1)! ≤ 1/m!` for `m = n + 1`. -/
theorem gamma_div_factorial_le (n : ℕ) :
    Real.Gamma (((n + 1 : ℕ) : ℝ) + 3 / 2) / ((2 * (n + 1) + 1).factorial : ℝ)
      ≤ 1 / ((n + 1).factorial : ℝ) := by
  have hΓ : Real.Gamma (((n + 1 : ℕ) : ℝ) + 3 / 2) ≤ ((n + 2).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    apply Real.Gamma_strictMonoOn_Ici.monotoneOn
    · simp only [Set.mem_Ici]; push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    · simp only [Set.mem_Ici]; push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    · push_cast; linarith
  have hfac : (n + 2).factorial * (n + 1).factorial ≤ (2 * (n + 1) + 1).factorial := by
    have h := Nat.factorial_mul_factorial_dvd_factorial_add (n + 2) (n + 1)
    rw [show n + 2 + (n + 1) = 2 * (n + 1) + 1 by ring] at h
    exact Nat.le_of_dvd (Nat.factorial_pos _) h
  have hfacR : ((n + 2).factorial : ℝ) * ((n + 1).factorial : ℝ)
      ≤ ((2 * (n + 1) + 1).factorial : ℝ) := by exact_mod_cast hfac
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc Real.Gamma (((n + 1 : ℕ) : ℝ) + 3 / 2) * ((n + 1).factorial : ℝ)
      ≤ ((n + 2).factorial : ℝ) * ((n + 1).factorial : ℝ) := by gcongr
    _ ≤ _ := hfacR

theorem majorant_nonneg (C kₜ bᵢ Λ : ℝ) (hΛ : 0 ≤ Λ) (n : ℕ) : 0 ≤ majorant C kₜ bᵢ Λ n := by
  have hΓ : 0 < Real.Gamma (((n + 1 : ℕ) : ℝ) + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
  unfold majorant
  positivity

/-- The majorant is summable: it is dominated by `K₀ (2 k_t² (Λ+1))ⁿ / n!`. -/
theorem summable_majorant (C kₜ bᵢ Λ : ℝ) (hΛ : 0 ≤ Λ) : Summable (majorant C kₜ bᵢ Λ) := by
  set y := 2 * (kₜ ^ 2 * (Λ + 1)) with hy
  set K0 := 4 * |C| * (1 + bᵢ ^ 2) * kₜ ^ 2 with hK0
  have hle : ∀ n : ℕ, majorant C kₜ bᵢ Λ n ≤ K0 * (y ^ n / (n.factorial : ℝ)) := by
    intro n
    have hpow1 : Λ ^ (n + 1 - 1) ≤ (Λ + 1) ^ n := by
      rw [Nat.add_sub_cancel]; exact pow_le_pow_left₀ hΛ (by linarith) n
    have hpow2 : Λ ^ (n + 1 - 2) ≤ (Λ + 1) ^ n :=
      (pow_le_pow_left₀ hΛ (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
    have hβ : 2 * ((n + 1 : ℕ) : ℝ) * Λ ^ (n + 1 - 1) + 4 * ((n + 1 : ℕ) : ℝ) * (n : ℝ) * bᵢ ^ 2 *
        Λ ^ (n + 1 - 2) ≤ 4 * ((n : ℝ) + 1) ^ 2 * (1 + bᵢ ^ 2) * (Λ + 1) ^ n := by
      have h1 : 2 * ((n + 1 : ℕ) : ℝ) * Λ ^ (n + 1 - 1) + 4 * ((n + 1 : ℕ) : ℝ) * (n : ℝ) * bᵢ ^ 2 *
          Λ ^ (n + 1 - 2) ≤ 2 * ((n + 1 : ℕ) : ℝ) * (Λ + 1) ^ n +
            4 * ((n + 1 : ℕ) : ℝ) * (n : ℝ) * bᵢ ^ 2 * (Λ + 1) ^ n :=
        add_le_add (mul_le_mul_of_nonneg_left hpow1 (by positivity))
          (mul_le_mul_of_nonneg_left hpow2 (by positivity))
      refine h1.trans ?_
      rw [← sub_nonneg]
      have e : 4 * ((n : ℝ) + 1) ^ 2 * (1 + bᵢ ^ 2) * (Λ + 1) ^ n -
          (2 * ((n + 1 : ℕ) : ℝ) * (Λ + 1) ^ n +
            4 * ((n + 1 : ℕ) : ℝ) * (n : ℝ) * bᵢ ^ 2 * (Λ + 1) ^ n) =
          (Λ + 1) ^ n * (((n : ℝ) + 1) * (4 * n + 2) + 4 * ((n : ℝ) + 1) * bᵢ ^ 2) := by
        push_cast; ring
      rw [e]
      positivity
    have h2n : ((n : ℝ) + 1) ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    have e1 : |kₜ| ^ (2 * (n + 1)) = kₜ ^ 2 * (kₜ ^ 2) ^ n := by
      rw [pow_mul, sq_abs, pow_succ]; ring
    have e2 : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hn0 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hf0 : (n.factorial : ℝ) ≠ 0 := by positivity
    have hK0nn : 0 ≤ K0 := by rw [hK0]; positivity
    have hβ0 : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ) * Λ ^ (n + 1 - 1) +
        4 * ((n + 1 : ℕ) : ℝ) * (n : ℝ) * bᵢ ^ 2 * Λ ^ (n + 1 - 2) := by positivity
    calc majorant C kₜ bᵢ Λ n
        ≤ (|kₜ| ^ (2 * (n + 1)) * |C|) * (1 / ((n + 1).factorial : ℝ)) *
            (4 * ((n : ℝ) + 1) ^ 2 * (1 + bᵢ ^ 2) * (Λ + 1) ^ n) := by
          unfold majorant
          exact mul_le_mul (mul_le_mul_of_nonneg_left (gamma_div_factorial_le n) (by positivity))
            hβ hβ0 (by positivity)
      _ = K0 * ((kₜ ^ 2) ^ n * (Λ + 1) ^ n * (((n : ℝ) + 1) / (n.factorial : ℝ))) := by
          rw [e1, e2, hK0]
          field_simp
      _ ≤ K0 * ((kₜ ^ 2) ^ n * (Λ + 1) ^ n * (2 ^ n / (n.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right h2n (by positivity)) (by positivity)) hK0nn
      _ = K0 * (y ^ n / (n.factorial : ℝ)) := by
          rw [hy, mul_pow, mul_pow]
          ring
  exact Summable.of_nonneg_of_le (majorant_nonneg C kₜ bᵢ Λ hΛ) hle
    ((Real.summable_pow_div_factorial y).mul_left K0)

/-- Termwise bound: `|kernelTerm (n+1) x| ≤ majorant n` whenever `0 ≤ x² + b² + c² ≤ Λ`. -/
theorem kernelTerm_abs_le (kₜ bᵢ b c C Λ x : ℝ) (M : ℕ → ℝ) (n : ℕ)
    (hM : ∀ n : ℕ, |M n| ≤ C * Real.Gamma (n + 3 / 2))
    (hxΛ : x ^ 2 + b ^ 2 + c ^ 2 ≤ Λ) :
    |kernelTerm kₜ bᵢ b c M (n + 1) x| ≤ majorant C kₜ bᵢ Λ n := by
  have hn1 : ((n + 1 : ℕ) : ℝ) - 1 = n := by push_cast; ring
  have hfact : (0 : ℝ) < ((2 * (n + 1) + 1).factorial : ℝ) := by positivity
  have hΓ : 0 < Real.Gamma (((n + 1 : ℕ) : ℝ) + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hMn : |M (n + 1)| ≤ |C| * Real.Gamma (((n + 1 : ℕ) : ℝ) + 3 / 2) :=
    (hM (n + 1)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hΓ.le)
  unfold kernelTerm majorant
  rw [hn1]
  have hβ0 : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ) * (x ^ 2 + b ^ 2 + c ^ 2) ^ (n + 1 - 1) +
      4 * ((n + 1 : ℕ) : ℝ) * (n : ℝ) * bᵢ ^ 2 * (x ^ 2 + b ^ 2 + c ^ 2) ^ (n + 1 - 2) := by
    positivity
  have hβ : 2 * ((n + 1 : ℕ) : ℝ) * (x ^ 2 + b ^ 2 + c ^ 2) ^ (n + 1 - 1) +
      4 * ((n + 1 : ℕ) : ℝ) * (n : ℝ) * bᵢ ^ 2 * (x ^ 2 + b ^ 2 + c ^ 2) ^ (n + 1 - 2) ≤
      2 * ((n + 1 : ℕ) : ℝ) * Λ ^ (n + 1 - 1) +
        4 * ((n + 1 : ℕ) : ℝ) * (n : ℝ) * bᵢ ^ 2 * Λ ^ (n + 1 - 2) := by
    gcongr
  rw [abs_mul, abs_of_nonneg hβ0, abs_div, abs_of_pos hfact, abs_mul, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, abs_pow]
  calc |kₜ| ^ (2 * (n + 1)) * |M (n + 1)| / ((2 * (n + 1) + 1).factorial : ℝ) *
        (2 * ((n + 1 : ℕ) : ℝ) * (x ^ 2 + b ^ 2 + c ^ 2) ^ (n + 1 - 1) +
          4 * ((n + 1 : ℕ) : ℝ) * (n : ℝ) * bᵢ ^ 2 * (x ^ 2 + b ^ 2 + c ^ 2) ^ (n + 1 - 2))
      ≤ |kₜ| ^ (2 * (n + 1)) * (|C| * Real.Gamma (((n + 1 : ℕ) : ℝ) + 3 / 2)) /
          ((2 * (n + 1) + 1).factorial : ℝ) *
        (2 * ((n + 1 : ℕ) : ℝ) * Λ ^ (n + 1 - 1) +
          4 * ((n + 1 : ℕ) : ℝ) * (n : ℝ) * bᵢ ^ 2 * Λ ^ (n + 1 - 2)) := by
        gcongr
    _ = _ := by ring

/-! ## Step 2: consequences of (5.10) for the kernel `K` -/

/-- Under (5.10), `K` is even: `K(-x) = K(x)` (each term depends on `x` through `x²`). -/
theorem kernel_even (kₜ bᵢ b c D_H : ℝ) (M : ℕ → ℝ) (K : ℝ → ℝ)
    (hK : ∀ x : ℝ, K x = D_H * ∑' n : ℕ, kernelTerm kₜ bᵢ b c M (n + 1) x) (x : ℝ) :
    K (-x) = K x := by
  rw [hK, hK]
  simp only [kernelTerm, neg_sq]

/-- Under (5.10) and the bound on `M_n`, `K` is continuous on every interval `[-R, R]`
(uniform convergence, by the majorant of Step 1). -/
theorem kernel_continuousOn (kₜ bᵢ b c D_H C R : ℝ) (M : ℕ → ℝ) (K : ℝ → ℝ)
    (hK : ∀ x : ℝ, K x = D_H * ∑' n : ℕ, kernelTerm kₜ bᵢ b c M (n + 1) x)
    (hM : ∀ n : ℕ, |M n| ≤ C * Real.Gamma (n + 3 / 2)) :
    ContinuousOn K (Icc (-R) R) := by
  have hΛ0 : 0 ≤ R ^ 2 + b ^ 2 + c ^ 2 := by positivity
  have hbound : ∀ (n : ℕ) (x : ℝ), x ∈ Icc (-R) R →
      ‖kernelTerm kₜ bᵢ b c M (n + 1) x‖ ≤ majorant C kₜ bᵢ (R ^ 2 + b ^ 2 + c ^ 2) n := by
    intro n x hx
    have hx' : |x| ≤ R := abs_le.mpr hx
    have : x ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) hx' 2
    rw [Real.norm_eq_abs]
    exact kernelTerm_abs_le kₜ bᵢ b c C _ x M n hM (by linarith)
  have h := continuousOn_tsum (s := Icc (-R) R)
    (f := fun n x => kernelTerm kₜ bᵢ b c M (n + 1) x)
    (fun n => (by unfold kernelTerm; fun_prop : Continuous _).continuousOn)
    (summable_majorant C kₜ bᵢ _ hΛ0) hbound
  exact (continuousOn_const.mul h).congr (fun x _ => hK x)

/-! ## Step 3: termwise integrals against the filter -/

/-- `|F(s, S, P)| ≤ |f₀| + |f₁| S + f₃ S³` for `0 ≤ s ≤ S`. -/
theorem abs_pathFilter_le (S P : ℝ) :
    ∀ s ∈ Icc (0 : ℝ) S, |pathFilter s S P| ≤ |f₀ S P| + |f₁ S P| * S + f₃ * S ^ 3 := by
  have hf3 : (0 : ℝ) ≤ f₃ := by norm_num [f₃]
  rintro s ⟨hs0, hsS⟩
  rw [pathFilter_eq]
  have h3 : s ^ 3 ≤ S ^ 3 := pow_le_pow_left₀ hs0 hsS 3
  calc |f₀ S P + f₁ S P * s + f₃ * s ^ 3| ≤ |f₀ S P| + |f₁ S P * s| + |f₃ * s ^ 3| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ |f₀ S P| + |f₁ S P| * S + f₃ * S ^ 3 := by
        rw [abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 3),
          abs_of_nonneg hf3]
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsS (abs_nonneg _)))
          (mul_le_mul_of_nonneg_left h3 hf3)

/-- The integral of the `(n+1)`-th term of (5.10), on both branches, against the filter:
by `integral_filter_branches` (Eqs. (6.12)–(6.13)) it is the `W`-combination of (6.14). -/
theorem integral_kernelTerm_branches (S P a b c Q kₜ bᵢ : ℝ) (M : ℕ → ℝ)
    (hQ : Q ^ 2 = b ^ 2 + c ^ 2) (n : ℕ) :
    ∫ s in (0 : ℝ)..S, pathFilter s S P *
        (kernelTerm kₜ bᵢ b c M (n + 1) (s - a) + kernelTerm kₜ bᵢ b c M (n + 1) (s + a)) =
      (-1) ^ (n + 1 + 1) * kₜ ^ (2 * (n + 1)) * M (n + 1) / ((2 * (n + 1) + 1).factorial : ℝ) *
        (2 * ((n + 1 : ℕ) : ℝ) * branchPoly (n + 1 - 1) S P a Q +
          4 * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) * bᵢ ^ 2 *
            branchPoly (n + 1 - 2) S P a Q) := by
  have hQx : ∀ y : ℝ, y ^ 2 + b ^ 2 + c ^ 2 = y ^ 2 + Q ^ 2 := fun y => by rw [hQ]; ring
  have hcF := pathFilter_continuous S P
  rw [← integral_filter_branches, ← integral_filter_branches]
  simp only [kernelTerm, hQx]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-! ## Step 4: (6.14) and its absolute convergence -/

/-- Both conclusions at once; `finite_path_series` and `finite_path_series_summable` below state
them separately. -/
theorem finite_path_series_and_summable
    (S P a b c Q bᵢ H kₜ D_H C B : ℝ) (M 𝒢 : ℕ → ℝ) (K : ℝ → ℝ)
    (hS : 0 ≤ S) (hH : 0 < H) (hQ : Q ^ 2 = b ^ 2 + c ^ 2)
    (h : Premises S P a b c bᵢ H kₜ D_H C B M 𝒢 K) :
    B = D_H / (4 * Real.Gamma (H + 3 / 2)) * ∑' n : ℕ, seriesTerm S P a Q kₜ bᵢ 𝒢 (n + 1) ∧
    Summable (fun n : ℕ => |seriesTerm S P a Q kₜ bᵢ 𝒢 (n + 1)|) := by
  obtain ⟨hB, hK, hM, hMG⟩ := h
  have hΓpos : 0 < Real.Gamma (H + 3 / 2) := Real.Gamma_pos_of_pos (by linarith)
  -- the majorant of Step 1 on `|x| ≤ R := S + |a|`
  set R := S + |a| with hRdef
  set Λ := R ^ 2 + b ^ 2 + c ^ 2 with hΛdef
  have hΛ0 : 0 ≤ Λ := by positivity
  have hbound : ∀ (n : ℕ) (x : ℝ), |x| ≤ R →
      |kernelTerm kₜ bᵢ b c M (n + 1) x| ≤ majorant C kₜ bᵢ Λ n := by
    intro n x hx
    have : x ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
    exact kernelTerm_abs_le kₜ bᵢ b c C Λ x M n hM (by linarith)
  have hu := summable_majorant C kₜ bᵢ Λ hΛ0
  have hsumm : ∀ x : ℝ, |x| ≤ R → Summable (fun n => kernelTerm kₜ bᵢ b c M (n + 1) x) :=
    fun x hx => Summable.of_norm_bounded hu
      (fun n => by rw [Real.norm_eq_abs]; exact hbound n x hx)
  have hkc : ∀ n : ℕ, Continuous (kernelTerm kₜ bᵢ b c M (n + 1)) := fun n => by
    unfold kernelTerm; fun_prop
  -- (6.5) applied to `K` (Step 2 gives its hypotheses)
  have hB2 : B = (1 / 2) * ∫ s in (0 : ℝ)..S, pathFilter s S P * (K (s - a) + K (s + a)) := by
    rw [hB, double_integral_eq_two_branches S P a K hS
      (kernel_continuousOn kₜ bᵢ b c D_H C R M K hK hM)
      (fun x _ => kernel_even kₜ bᵢ b c D_H M K hK x)]
  -- bounds used by dominated convergence
  set BF := |f₀ S P| + |f₁ S P| * S + f₃ * S ^ 3 with hBFdef
  have hBF := abs_pathFilter_le S P
  have hBF0 : 0 ≤ BF := (abs_nonneg _).trans (hBF 0 ⟨le_rfl, hS⟩)
  have hshift : ∀ t ∈ Icc (0 : ℝ) S, |t - a| ≤ R ∧ |t + a| ≤ R := by
    rintro t ⟨ht0, htS⟩
    have h1 := le_abs_self a
    have h2 := neg_abs_le a
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hcF := pathFilter_continuous S P
  -- the termwise integrals (Step 3)
  set I : ℕ → ℝ := fun n => ∫ s in (0 : ℝ)..S, pathFilter s S P *
    (kernelTerm kₜ bᵢ b c M (n + 1) (s - a) + kernelTerm kₜ bᵢ b c M (n + 1) (s + a)) with hIdef
  have hI := integral_kernelTerm_branches S P a b c Q kₜ bᵢ M hQ
  -- termwise integration (justified in one sentence in the PDF): dominated convergence
  have hsum : HasSum (fun n => D_H * I n)
      (∫ s in (0 : ℝ)..S, pathFilter s S P * (K (s - a) + K (s + a))) := by
    have hmem : ∀ t ∈ Set.uIoc (0 : ℝ) S, t ∈ Icc (0 : ℝ) S := fun t ht => by
      rw [uIoc_of_le hS] at ht; exact ⟨ht.1.le, ht.2⟩
    have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
      (b := S) (F := fun n t => D_H * (pathFilter t S P *
        (kernelTerm kₜ bᵢ b c M (n + 1) (t - a) + kernelTerm kₜ bᵢ b c M (n + 1) (t + a))))
      (f := fun t => pathFilter t S P * (K (t - a) + K (t + a)))
      (fun n _ => |D_H| * (BF * (2 * majorant C kₜ bᵢ Λ n)))
      (fun n => (Continuous.aestronglyMeasurable (by have := hkc n; fun_prop)))
      (fun n => ae_of_all _ fun t ht => by
        obtain ⟨ha1, ha2⟩ := hshift t (hmem t ht)
        have hk1 := hbound n _ ha1
        have hk2 := hbound n _ ha2
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hBF t (hmem t ht))
          ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _) hBF0) (abs_nonneg D_H))
      (ae_of_all _ fun t _ => ((hu.mul_left 2).mul_left BF).mul_left |D_H|)
      intervalIntegrable_const
      (ae_of_all _ fun t ht => by
        obtain ⟨ha1, ha2⟩ := hshift t (hmem t ht)
        have e := ((((hsumm _ ha1).hasSum).add (hsumm _ ha2).hasSum).mul_left
          (pathFilter t S P)).mul_left D_H
        have hval : D_H * (pathFilter t S P *
            (∑' n : ℕ, kernelTerm kₜ bᵢ b c M (n + 1) (t - a) +
              ∑' n : ℕ, kernelTerm kₜ bᵢ b c M (n + 1) (t + a))) =
            pathFilter t S P * (K (t - a) + K (t + a)) := by
          rw [hK (t - a), hK (t + a)]
          ring
        rw [← hval]
        exact e)
    simpa only [intervalIntegral.integral_const_mul] using h
  -- the factor `[2Γ(ν)]⁻¹` of (4.9)
  have hrel2 : ∀ n : ℕ,
      seriesTerm S P a Q kₜ bᵢ 𝒢 (n + 1) = 2 * Real.Gamma (H + 3 / 2) * I n := by
    intro n
    rw [show I n = _ from hI n, hMG (n + 1)]
    simp only [seriesTerm]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hB2, ← hsum.tsum_eq, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [hrel2 n]
    field_simp
    ring
  · have hIb : ∀ n : ℕ, |I n| ≤ BF * (2 * majorant C kₜ bᵢ Λ n) * S := by
      intro n
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := S)
        (C := BF * (2 * majorant C kₜ bᵢ Λ n))
        (f := fun s => pathFilter s S P *
          (kernelTerm kₜ bᵢ b c M (n + 1) (s - a) + kernelTerm kₜ bᵢ b c M (n + 1) (s + a)))
        (fun t ht => by
          have ht' : t ∈ Icc (0 : ℝ) S := by
            rw [uIoc_of_le hS] at ht; exact ⟨ht.1.le, ht.2⟩
          obtain ⟨ha1, ha2⟩ := hshift t ht'
          have hk1 := hbound n _ ha1
          have hk2 := hbound n _ ha2
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hBF t ht') ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _) hBF0)
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hS] at h
      exact h
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      (hu.mul_left (2 * Real.Gamma (H + 3 / 2) * (BF * 2 * S)))
    rw [hrel2 n, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.Gamma (H + 3 / 2))]
    calc 2 * Real.Gamma (H + 3 / 2) * |I n|
        ≤ 2 * Real.Gamma (H + 3 / 2) * (BF * (2 * majorant C kₜ bᵢ Λ n) * S) :=
          mul_le_mul_of_nonneg_left (hIb n) (by positivity)
      _ = 2 * Real.Gamma (H + 3 / 2) * (BF * 2 * S) * majorant C kₜ bᵢ Λ n := by ring

/-! ## Main statements -/

/-- Paper: PDF Eq. (6.14) — for all real `S ≥ 0`, `P`, `a`, `b`, `c`, `Q` with `Q² = b² + c²`,
every real `b_i`, `H > 0`, `k_t`, `D_H`, `C`, `B`, and all `M`, `𝒢`, `K` satisfying the four
premises (6.2), (5.10), (4.9) and `|M_n| ≤ C Γ(n + 3/2)` (`Premises`),
`B = D_H/(4Γ(ν)) Σ_{n≥1} (-1)^{n+1} k_t^{2n}/(2n+1)! 𝒢_n
  [2n W_{n-1}(a,Q) + 4n(n-1) b_i² W_{n-2}(a,Q)]`, `ν = H + 3/2`.

Proof (`finite_path_series_and_summable`): (6.5) for `K`; termwise integration of (5.10) over
`[0, S]` by dominated convergence; each term by (6.12)–(6.13); the factor `[2Γ(ν)]⁻¹` from
(4.9). -/
theorem finite_path_series
    (S P a b c Q bᵢ H kₜ D_H C B : ℝ) (M 𝒢 : ℕ → ℝ) (K : ℝ → ℝ)
    (hS : 0 ≤ S) (hH : 0 < H) (hQ : Q ^ 2 = b ^ 2 + c ^ 2)
    (h : Premises S P a b c bᵢ H kₜ D_H C B M 𝒢 K) :
    B = D_H / (4 * Real.Gamma (H + 3 / 2)) * ∑' n : ℕ, seriesTerm S P a Q kₜ bᵢ 𝒢 (n + 1) :=
  (finite_path_series_and_summable S P a b c Q bᵢ H kₜ D_H C B M 𝒢 K hS hH hQ h).1

/-- Paper: Proposition 2 ("Both series converge absolutely"). Under the hypotheses of
`finite_path_series`, the series (6.14) converges absolutely: `Σ_{n≥1} |seriesTerm n| < ∞`. -/
theorem finite_path_series_summable
    (S P a b c Q bᵢ H kₜ D_H C B : ℝ) (M 𝒢 : ℕ → ℝ) (K : ℝ → ℝ)
    (hS : 0 ≤ S) (hH : 0 < H) (hQ : Q ^ 2 = b ^ 2 + c ^ 2)
    (h : Premises S P a b c bᵢ H kₜ D_H C B M 𝒢 K) :
    Summable (fun n : ℕ => |seriesTerm S P a Q kₜ bᵢ 𝒢 (n + 1)|) :=
  (finite_path_series_and_summable S P a b c Q bᵢ H kₜ D_H C B M 𝒢 K hS hH hQ h).2

/-! ## Non-vacuity witness -/

/-- The hypotheses of `finite_path_series` can all hold with a nonzero sequence `M`:
`M_n = Γ(n + 3/2)`, `C = 1`, `𝒢_n = 2Γ(ν) M_n`, `K` the series (5.10) itself, `B` the double
integral (6.2), at `S = 1`, `P = 1/2`, `a = 1/4`, `b = 3`, `c = 4`, `Q = 5`, `b_i = 3`,
`H = 1/2`, `k_t = D_H = 1`. -/
theorem finite_path_witness :
    ∃ (S P a b c Q bᵢ H kₜ D_H C B : ℝ) (M 𝒢 : ℕ → ℝ) (K : ℝ → ℝ),
      0 ≤ S ∧ 0 < H ∧ Q ^ 2 = b ^ 2 + c ^ 2 ∧ Premises S P a b c bᵢ H kₜ D_H C B M 𝒢 K ∧
      (∀ n : ℕ, M n ≠ 0) ∧ S ≠ 0 ∧ a ≠ 0 ∧
      B = D_H / (4 * Real.Gamma (H + 3 / 2)) * ∑' n : ℕ, seriesTerm S P a Q kₜ bᵢ 𝒢 (n + 1) := by
  let M : ℕ → ℝ := fun n => Real.Gamma (n + 3 / 2)
  let 𝒢 : ℕ → ℝ := fun n => 2 * Real.Gamma (1 / 2 + 3 / 2) * M n
  let K : ℝ → ℝ := fun x => 1 * ∑' n : ℕ, kernelTerm 1 3 3 4 M (n + 1) x
  let B : ℝ := ∫ ξ' in (0 : ℝ)..1, ∫ ξ in (0 : ℝ)..1,
    (1 + 1 / 2 - ξ) * (1 + 1 / 2 - ξ') * K (ξ - ξ' - 1 / 4)
  have hΓ : 0 < Real.Gamma (1 / 2 + 3 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have hMpos : ∀ n : ℕ, 0 < M n := fun n => Real.Gamma_pos_of_pos (by positivity)
  have hM : ∀ n : ℕ, |M n| ≤ 1 * Real.Gamma (n + 3 / 2) := fun n => by
    rw [one_mul, abs_of_pos (hMpos n)]
  have hMG : ∀ n : ℕ, M n = 𝒢 n / (2 * Real.Gamma (1 / 2 + 3 / 2)) := fun n =>
    (mul_div_cancel_left₀ (M n) (mul_pos two_pos hΓ).ne').symm
  have hQ : (5 : ℝ) ^ 2 = 3 ^ 2 + 4 ^ 2 := by norm_num
  have hP : Premises 1 (1 / 2) (1 / 4) 3 4 3 (1 / 2) 1 1 1 B M 𝒢 K :=
    ⟨rfl, fun x => rfl, hM, hMG⟩
  exact ⟨1, 1 / 2, 1 / 4, 3, 4, 5, 3, 1 / 2, 1, 1, 1, B, M, 𝒢, K, zero_le_one, by norm_num, hQ,
    hP, fun n => (hMpos n).ne', one_ne_zero, by norm_num,
    finite_path_series 1 (1 / 2) (1 / 4) 3 4 5 3 (1 / 2) 1 1 1 B M 𝒢 K zero_le_one (by norm_num)
      hQ hP⟩

end PathCov
