import Formalization.PathFilter
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-!
# Reduction of the double integral (6.2) to two branches (PDF Section 6.2, Eq. (6.5))

The PDF states (6.5) for the kernel `K_i(·, b, c)` of (5.6)/(5.10). Here it is proved for every
function `g` continuous on `[-(S+|a|), S+|a|]`; the first equality does not need `g` to be even,
the second one does. `FinitePathSeries.lean` applies it to the kernel of (5.10).

## Main statements

* `double_integral_eq_folded`       — first equality of (6.5):
  `∫₀^S∫₀^S (L-ξ)(L-ξ') g(ξ-ξ'-a) dξ dξ' = ½ ∫_{-S}^S F(|s|,S,P) g(s-a) ds`.
* `folded_eq_two_branches`          — second equality of (6.5), for even `g`:
  `½ ∫_{-S}^S F(|s|,S,P) g(s-a) ds = ½ ∫₀^S F(s,S,P) [g(s-a) + g(s+a)] ds`.
* `double_integral_eq_two_branches` — the two combined.

## Notation (Lean ↔ PDF)

`L = S + P`, so the weight `(L - ξ)(L - ξ')` is written `(S + P - ξ) * (S + P - ξ')`. The inner
integral is in `ξ`, the outer one in `ξ'`. `pathFilter s S P` is `F(s, S, P)` of (6.3).
-/

namespace PathCov

open MeasureTheory intervalIntegral Set

/-! ## Auxiliary lemmas -/

/-- After the shear `ξ = s + ξ'`, the admissible `ξ'` form an interval. -/
theorem shear_set (S s : ℝ) :
    {ξ' : ℝ | ξ' ∈ Ioc 0 S ∧ s + ξ' ∈ Ioc 0 S} = Ioc (max 0 (-s)) (min S (S - s)) := by
  ext ξ'
  simp only [Set.mem_ofPred_eq, mem_Ioc, max_lt_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, by linarith⟩, h2, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, h3⟩, by linarith, by linarith⟩

/-- The branch weight: for `|s| ≤ S`, `∫_{max(0,-s)}^{min(S,S-s)} w(s+ξ') w(ξ') dξ' = F(|s|)/2`. -/
theorem branch_weight (S P s : ℝ) (hs : s ∈ Icc (-S) S) :
    ∫ ξ' in Ioc (max 0 (-s)) (min S (S - s)), (S + P - (s + ξ')) * (S + P - ξ')
      = pathFilter |s| S P / 2 := by
  obtain ⟨hs1, hs2⟩ := hs
  have hle : max 0 (-s) ≤ min S (S - s) :=
    max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith))
  rw [← intervalIntegral.integral_of_le hle]
  have hderiv : ∀ x ∈ uIcc (max 0 (-s)) (min S (S - s)),
      HasDerivAt (fun y : ℝ =>
          y ^ 3 / 3 - (2 * (S + P) - s) * y ^ 2 / 2 + (S + P) * (S + P - s) * y)
        ((S + P - (s + x)) * (S + P - x)) x := by
    intro x _
    have h := (((hasDerivAt_pow 3 x).div_const 3).sub
      (((hasDerivAt_pow 2 x).const_mul (2 * (S + P) - s)).div_const 2)).add
      ((hasDerivAt_id' x).const_mul ((S + P) * (S + P - s)))
    exact h.congr_deriv (by norm_num; ring)
  rw [integral_eq_sub_of_hasDerivAt hderiv (Continuous.intervalIntegrable (by fun_prop) _ _),
    pathFilter_eq]
  simp only [f₀, f₁, f₃]
  rcases le_total 0 s with h | h
  · rw [max_eq_left (by linarith : -s ≤ 0), min_eq_right (by linarith : S - s ≤ S),
      abs_of_nonneg h]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ -s), min_eq_left (by linarith : S ≤ S - s),
      abs_of_nonpos h]
    ring

/-- First equality of (6.5) for `g` continuous on all of `ℝ`: shear, Fubini, branch weight. -/
theorem double_integral_eq_folded_of_continuous (S P a : ℝ) (g : ℝ → ℝ) (hS : 0 ≤ S)
    (hg : Continuous g) :
    (∫ ξ' in (0 : ℝ)..S, ∫ ξ in (0 : ℝ)..S, (S + P - ξ) * (S + P - ξ') * g (ξ - ξ' - a))
      = (1 / 2) * ∫ s in (-S)..S, pathFilter |s| S P * g (s - a) := by
  set I : Set ℝ := Ioc 0 S with hI
  set k : ℝ × ℝ → ℝ := fun p => (S + P - (p.2 + p.1)) * (S + P - p.1) * g (p.2 - a) with hk
  set A : Set (ℝ × ℝ) := {p | p.1 ∈ I ∧ p.2 + p.1 ∈ I} with hAdef
  have hA : MeasurableSet A :=
    (measurableSet_Ioc.preimage measurable_fst).inter
      (measurableSet_Ioc.preimage (measurable_snd.add measurable_fst))
  have hkc : Continuous k := by rw [hk]; fun_prop
  have hsub : A ⊆ Icc 0 S ×ˢ Icc (-S) S := by
    rintro ⟨x, y⟩ ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1.le, h2⟩, by linarith, by linarith⟩
  have hint : Integrable (A.indicator k) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    ((hkc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      hsub).integrable_indicator hA
  -- inner integral after the shear
  have step2 : ∀ ξ' : ℝ,
      I.indicator (fun ξ' => ∫ ξ in (0 : ℝ)..S, (S + P - ξ) * (S + P - ξ') * g (ξ - ξ' - a)) ξ'
        = ∫ s, A.indicator k (ξ', s) := by
    intro ξ'
    by_cases h : ξ' ∈ I
    · rw [indicator_of_mem h, intervalIntegral.integral_of_le hS, ← hI,
        ← MeasureTheory.integral_indicator measurableSet_Ioc, ← hI,
        ← integral_add_right_eq_self _ ξ']
      congr 1
      ext s
      by_cases h2 : s + ξ' ∈ I
      · rw [indicator_of_mem h2, indicator_of_mem (show (ξ', s) ∈ A from ⟨h, h2⟩), hk]
        simp only
        rw [show s + ξ' - ξ' - a = s - a by ring]
      · rw [indicator_of_notMem h2,
          indicator_of_notMem (show (ξ', s) ∉ A from fun hh => h2 hh.2)]
    · rw [indicator_of_notMem h]
      have h0 : ∀ s : ℝ, A.indicator k (ξ', s) = 0 :=
        fun s => indicator_of_notMem (fun hh => h hh.1) _
      simp [h0]
  -- inner integral after the swap
  have step3 : ∀ s : ℝ, ∫ ξ', A.indicator k (ξ', s)
      = g (s - a) * ∫ ξ' in Ioc (max 0 (-s)) (min S (S - s)),
          (S + P - (s + ξ')) * (S + P - ξ') := by
    intro s
    rw [← shear_set, ← MeasureTheory.integral_indicator ?meas, ← MeasureTheory.integral_const_mul]
    case meas => rw [shear_set]; exact measurableSet_Ioc
    congr 1
    ext ξ'
    by_cases h : (ξ', s) ∈ A
    · rw [indicator_of_mem h, indicator_of_mem (show ξ' ∈ {ξ' : ℝ | ξ' ∈ Ioc 0 S ∧ s + ξ' ∈ Ioc 0 S}
        from ⟨h.1, h.2⟩), hk]
      simp only
      ring
    · rw [indicator_of_notMem h, indicator_of_notMem (show ξ' ∉ {ξ' : ℝ | ξ' ∈ Ioc 0 S ∧
        s + ξ' ∈ Ioc 0 S} from fun hh => h ⟨hh.1, hh.2⟩)]
      ring
  have hzero : ∀ s ∉ Ioc (-S) S, g (s - a) * ∫ ξ' in Ioc (max 0 (-s)) (min S (S - s)),
      (S + P - (s + ξ')) * (S + P - ξ') = 0 := by
    intro s hs
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hs
    have hempty : Ioc (max 0 (-s)) (min S (S - s)) = ∅ := by
      apply Ioc_eq_empty
      rw [not_lt]
      rcases hs with hs | hs
      · exact (min_le_left _ _).trans ((by linarith : S ≤ -s).trans (le_max_right _ _))
      · exact (min_le_right _ _).trans ((by linarith : S - s ≤ 0).trans (le_max_left _ _))
    rw [hempty, setIntegral_empty, mul_zero]
  calc (∫ ξ' in (0 : ℝ)..S, ∫ ξ in (0 : ℝ)..S, (S + P - ξ) * (S + P - ξ') * g (ξ - ξ' - a))
      = ∫ ξ', I.indicator
          (fun ξ' => ∫ ξ in (0 : ℝ)..S, (S + P - ξ) * (S + P - ξ') * g (ξ - ξ' - a)) ξ' := by
        rw [intervalIntegral.integral_of_le hS, ← hI,
          MeasureTheory.integral_indicator measurableSet_Ioc]
    _ = ∫ ξ', ∫ s, A.indicator k (ξ', s) := by simp_rw [step2]
    _ = ∫ s, ∫ ξ', A.indicator k (ξ', s) := integral_integral_swap (by
        simpa only [Function.uncurry_def] using hint)
    _ = ∫ s, g (s - a) * ∫ ξ' in Ioc (max 0 (-s)) (min S (S - s)),
          (S + P - (s + ξ')) * (S + P - ξ') := by simp_rw [step3]
    _ = ∫ s in (-S)..S, g (s - a) * ∫ ξ' in Ioc (max 0 (-s)) (min S (S - s)),
          (S + P - (s + ξ')) * (S + P - ξ') := by
        rw [intervalIntegral.integral_of_le (by linarith),
          setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    _ = (1 / 2) * ∫ s in (-S)..S, pathFilter |s| S P * g (s - a) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by linarith)] at hs
        simp only
        rw [branch_weight S P s hs]
        ring

/-- Membership bookkeeping: `s ∈ [-S,S]` and `|e| ≤ |a|` put `s + e` in `[-(S+|a|), S+|a|]`. -/
theorem mem_big (S a s e : ℝ) (hs : s ∈ Icc (-S) S) (he : |e| ≤ |a|) :
    s + e ∈ Icc (-(S + |a|)) (S + |a|) := by
  obtain ⟨h1, h2⟩ := hs
  obtain ⟨h3, h4⟩ := abs_le.mp he
  exact ⟨by linarith, by linarith⟩

/-! ## Main statements -/

/-- Paper: PDF Eq. (6.5), first equality — for all real `S ≥ 0`, `P`, `a` and every `g`
continuous on `[-(S+|a|), S+|a|]`,
`∫₀^S∫₀^S (L-ξ)(L-ξ') g(ξ-ξ'-a) dξ dξ' = ½ ∫_{-S}^S F(|s|,S,P) g(s-a) ds`.

`g` need not be even. Proof: shear `ξ = s + ξ'`, Fubini, and the inner integral equals
`F(|s|, S, P)/2` (`branch_weight`). -/
theorem double_integral_eq_folded (S P a : ℝ) (g : ℝ → ℝ) (hS : 0 ≤ S)
    (hg : ContinuousOn g (Icc (-(S + |a|)) (S + |a|))) :
    (∫ ξ' in (0 : ℝ)..S, ∫ ξ in (0 : ℝ)..S, (S + P - ξ) * (S + P - ξ') * g (ξ - ξ' - a))
      = (1 / 2) * ∫ s in (-S)..S, pathFilter |s| S P * g (s - a) := by
  -- extend `g` continuously to `ℝ` by clamping to the interval
  have hR : -(S + |a|) ≤ S + |a| := by have := abs_nonneg a; linarith
  set ĝ : ℝ → ℝ := fun x => g (projIcc (-(S + |a|)) (S + |a|) hR x) with hĝ
  have hĝc : Continuous ĝ :=
    hg.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun x => Subtype.mem _
  have hĝeq : ∀ x ∈ Icc (-(S + |a|)) (S + |a|), ĝ x = g x := by
    intro x hx
    rw [hĝ]
    simp only [projIcc_of_mem hR hx]
  have hmem : ∀ s ∈ Icc (-S) S, s - a ∈ Icc (-(S + |a|)) (S + |a|) := fun s hs => by
    simpa [sub_eq_add_neg] using mem_big S a s (-a) hs (by rw [abs_neg])
  have hL : (∫ ξ' in (0 : ℝ)..S, ∫ ξ in (0 : ℝ)..S, (S + P - ξ) * (S + P - ξ') * g (ξ - ξ' - a))
      = ∫ ξ' in (0 : ℝ)..S, ∫ ξ in (0 : ℝ)..S, (S + P - ξ) * (S + P - ξ') * ĝ (ξ - ξ' - a) := by
    apply intervalIntegral.integral_congr
    intro ξ' hξ'
    rw [uIcc_of_le hS] at hξ'
    apply intervalIntegral.integral_congr
    intro ξ hξ
    rw [uIcc_of_le hS] at hξ
    simp only
    rw [hĝeq _ (hmem _ ⟨by linarith [hξ.1, hξ'.2], by linarith [hξ.2, hξ'.1]⟩)]
  have hM : (∫ s in (-S)..S, pathFilter |s| S P * g (s - a))
      = ∫ s in (-S)..S, pathFilter |s| S P * ĝ (s - a) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by linarith)] at hs
    simp only
    rw [hĝeq _ (hmem s hs)]
  rw [hL, hM]
  exact double_integral_eq_folded_of_continuous S P a ĝ hS hĝc

/-- Paper: PDF Eq. (6.5), second equality — for all real `S ≥ 0`, `P`, `a` and every `g`
continuous and even on `[-(S+|a|), S+|a|]`,
`½ ∫_{-S}^S F(|s|,S,P) g(s-a) ds = ½ ∫₀^S F(s,S,P) [g(s-a) + g(s+a)] ds`.

Proof: split `[-S, S]` at `0`, reflect the left half, use evenness. -/
theorem folded_eq_two_branches (S P a : ℝ) (g : ℝ → ℝ) (hS : 0 ≤ S)
    (hg : ContinuousOn g (Icc (-(S + |a|)) (S + |a|)))
    (heven : ∀ x ∈ Icc (-(S + |a|)) (S + |a|), g (-x) = g x) :
    (1 / 2) * ∫ s in (-S)..S, pathFilter |s| S P * g (s - a)
      = (1 / 2) * ∫ s in (0 : ℝ)..S, pathFilter s S P * (g (s - a) + g (s + a)) := by
  have hcF := pathFilter_continuous S P
  have hsubL : Icc (-S) 0 ⊆ Icc (-S) S := Icc_subset_Icc le_rfl hS
  have hsubR : Icc 0 S ⊆ Icc (-S) S := Icc_subset_Icc (by linarith) le_rfl
  have hgm : ContinuousOn (fun s => g (s - a)) (Icc (-S) S) := by
    refine hg.comp (by fun_prop) fun s hs => ?_
    simpa [sub_eq_add_neg] using mem_big S a s (-a) hs (by rw [abs_neg])
  have hgp : ContinuousOn (fun s => g (s + a)) (Icc (-S) S) :=
    hg.comp (by fun_prop) fun s hs => mem_big S a s a hs le_rfl
  have hh : ContinuousOn (fun s => pathFilter |s| S P * g (s - a)) (Icc (-S) S) :=
    (hcF.comp continuous_abs).continuousOn.mul hgm
  have iL : IntervalIntegrable (fun s => pathFilter |s| S P * g (s - a)) volume (-S) 0 :=
    (hh.mono (by rw [uIcc_of_le (by linarith)]; exact hsubL)).intervalIntegrable
  have iR : IntervalIntegrable (fun s => pathFilter |s| S P * g (s - a)) volume 0 S :=
    (hh.mono (by rw [uIcc_of_le hS]; exact hsubR)).intervalIntegrable
  have iP : IntervalIntegrable (fun s => pathFilter s S P * g (s + a)) volume 0 S :=
    ((hcF.continuousOn.mul hgp).mono (by rw [uIcc_of_le hS]; exact hsubR)).intervalIntegrable
  congr 1
  rw [← intervalIntegral.integral_add_adjacent_intervals iL iR]
  have hneg : ∫ s in (-S)..0, pathFilter |s| S P * g (s - a)
      = ∫ s in (0 : ℝ)..S, pathFilter s S P * g (s + a) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := S)
      (fun s => pathFilter |s| S P * g (s - a))
    rw [neg_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hS] at hs
    simp only
    rw [abs_neg, abs_of_nonneg hs.1, show -s - a = -(s + a) by ring,
      heven _ (mem_big S a s a (hsubR hs) le_rfl)]
  rw [hneg, ← intervalIntegral.integral_add iP iR]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hS] at hs
  simp only
  rw [abs_of_nonneg hs.1]
  ring

/-- Paper: PDF Eq. (6.5) — the two equalities combined: for all real `S ≥ 0`, `P`, `a` and every
`g` continuous and even on `[-(S+|a|), S+|a|]`,
`∫₀^S∫₀^S (L-ξ)(L-ξ') g(ξ-ξ'-a) dξ dξ' = ½ ∫₀^S F(s,S,P) [g(s-a) + g(s+a)] ds`. -/
theorem double_integral_eq_two_branches (S P a : ℝ) (g : ℝ → ℝ) (hS : 0 ≤ S)
    (hg : ContinuousOn g (Icc (-(S + |a|)) (S + |a|)))
    (heven : ∀ x ∈ Icc (-(S + |a|)) (S + |a|), g (-x) = g x) :
    (∫ ξ' in (0 : ℝ)..S, ∫ ξ in (0 : ℝ)..S, (S + P - ξ) * (S + P - ξ') * g (ξ - ξ' - a))
      = (1 / 2) * ∫ s in (0 : ℝ)..S, pathFilter s S P * (g (s - a) + g (s + a)) :=
  (double_integral_eq_folded S P a g hS hg).trans (folded_eq_two_branches S P a g hS hg heven)

/-! ## Non-vacuity witness -/

/-- The hypotheses of the three statements can all hold with an even, continuous, non-constant
`g` and a nonzero shift (`g(x) = x²`, `S = 1`, `P = 0`, `a = 1`). -/
theorem two_branch_witness :
    ∃ (S P a : ℝ) (g : ℝ → ℝ), 0 ≤ S ∧ S ≠ 0 ∧ a ≠ 0 ∧
      ContinuousOn g (Icc (-(S + |a|)) (S + |a|)) ∧
      (∀ x ∈ Icc (-(S + |a|)) (S + |a|), g (-x) = g x) ∧ g 1 ≠ g 0 ∧
      (∫ ξ' in (0 : ℝ)..S, ∫ ξ in (0 : ℝ)..S, (S + P - ξ) * (S + P - ξ') * g (ξ - ξ' - a))
        = (1 / 2) * ∫ s in (0 : ℝ)..S, pathFilter s S P * (g (s - a) + g (s + a)) := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 2) (Icc (-(1 + |(1 : ℝ)|)) (1 + |(1 : ℝ)|)) :=
    (continuous_pow 2).continuousOn
  have he : ∀ x ∈ Icc (-(1 + |(1 : ℝ)|)) (1 + |(1 : ℝ)|), (-x) ^ 2 = x ^ 2 := fun x _ => neg_sq x
  exact ⟨1, 0, 1, fun x => x ^ 2, zero_le_one, one_ne_zero, one_ne_zero, hc, he,
    by norm_num, double_integral_eq_two_branches 1 0 1 (fun x => x ^ 2) zero_le_one hc he⟩

end PathCov
