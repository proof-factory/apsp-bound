/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Parameter and numerical refinements (c) 2026 Joshua Wharton, QFEX.
Author of modifications: Joshua Wharton <joshua@qfex.com>
-/
module

public import Submission.ThreeSumApsp.Pruned.Costs
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Refined numbers for `c = 20`, `θ = 155816/1377219`

The logarithms are proved from forty terms of the positive atanh series, with
Mathlib's geometric remainder bound. Python selected the rational endpoints;
it supplies no assumptions to Lean. The public bounds are
`Γ > 0.0660254968003`, `q < 0.4339745031995`, and `19 ln 3 / ln 4 < 15.057143756851`.
The coarser, unchanged `κ < 2.9` certificate retains ample slack.

This module refines the certificate by Hrishik Sai Bojnal (fringewidth), built
on Li Xuanji's deterministic batched APSP proof and the Anthropic development.
-/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

namespace ThreeSumApsp
open scoped BigOperators

private theorem refinedAtanhLogBounds (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * (i : ℝ) + 1))
        ≤ Real.log ((1 + z) / (1 - z)) ∧
    Real.log ((1 + z) / (1 - z)) ≤
      2 * ((∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
        z ^ (2 * n + 1) / (1 - z ^ 2)) := by
  have hlo := Real.sum_range_le_log_div hz0 hz1 n
  have hhi := Real.log_div_le_sum_range_add hz0 hz1 n
  constructor <;> linarith

private theorem fineLogTwo :
    (693147180559945309417232 / 10^24 : ℝ) < Real.log (2 : ℝ) ∧
    Real.log (2 : ℝ) < (693147180559945309417233 / 10^24 : ℝ) := by
  have h := refinedAtanhLogBounds (1 / 3 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem fineLogThreeHalf :
    (405465108108164381978013 / 10^24 : ℝ) < Real.log (3 / 2 : ℝ) ∧
    Real.log (3 / 2 : ℝ) < (405465108108164381978014 / 10^24 : ℝ) := by
  have h := refinedAtanhLogBounds (1 / 5 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem fineLogCompTwice :
    (573081130066520453705494 / 10^24 : ℝ) < Real.log (2442806 / 1377219 : ℝ) ∧
    Real.log (2442806 / 1377219 : ℝ) < (573081130066520453705495 / 10^24 : ℝ) := by
  have h := refinedAtanhLogBounds (1065587 / 3820025 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem fineLogNearOne :
    (5936980302083498201512 / 10^24 : ℝ) < Real.log (26322977 / 26167161 : ℝ) ∧
    Real.log (26322977 / 26167161 : ℝ) < (5936980302083498201513 / 10^24 : ℝ) := by
  have h := refinedAtanhLogBounds (77908 / 26245069 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem fineLogTheta16 :
    (593443018690131333854015 / 10^24 : ℝ) < Real.log (2493056 / 1377219 : ℝ) ∧
    Real.log (2493056 / 1377219 : ℝ) < (593443018690131333854016 / 10^24 : ℝ) := by
  have h := refinedAtanhLogBounds (1115837 / 3870275 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem fineLogHighOver16 :
    (177787237228742720541611 / 10^24 : ℝ) < Real.log (26322977 / 22035504 : ℝ) ∧
    Real.log (26322977 / 22035504 : ℝ) < (177787237228742720541612 / 10^24 : ℝ) := by
  have h := refinedAtanhLogBounds (4287473 / 48358481 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem refinedLogSixteen : Real.log 16 = 4 * Real.log 2 := by
  convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num

private lemma logB_a : Real.log (1221403 / 1377219 : ℝ) ∈
    Set.Icc (-12006605049342485572 / 10^20 : ℝ) (-12006605049342485571 / 10^20 : ℝ) := by
  have hr := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by norm_num : (1221403 / 1377219 : ℝ) ≠ 0)
  norm_num at hr
  have h1 := fineLogCompTwice
  have h2 := fineLogTwo
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private lemma logB_b : Real.log (26322977 / 26167161 : ℝ) ∈
    Set.Icc (593698030208349820 / 10^20 : ℝ) (593698030208349821 / 10^20 : ℝ) := by
  have h1 := fineLogNearOne
  have h2 := fineLogTwo
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private lemma logB_c : Real.log (26322977 / 1377219 : ℝ) ∈
    Set.Icc (295037595946852395821 / 10^20 : ℝ) (295037595946852395822 / 10^20 : ℝ) := by
  have hr := Real.log_mul (by norm_num : (16 : ℝ) ≠ 0)
    (by norm_num : (26322977 / 22035504 : ℝ) ≠ 0)
  rw [refinedLogSixteen] at hr
  norm_num at hr
  have h1 := fineLogHighOver16
  have h2 := fineLogTwo
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private lemma logB_3 : Real.log (3 : ℝ) ∈
    Set.Icc (109861228866810969139 / 10^20 : ℝ) (109861228866810969140 / 10^20 : ℝ) := by
  have hr := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by norm_num : (3 / 2 : ℝ) ≠ 0)
  norm_num at hr
  have h1 := fineLogThreeHalf
  have h2 := fineLogTwo
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private lemma logB_theta : Real.log (155816 / 1377219 : ℝ) ∈
    Set.Icc (-217914570354964990382 / 10^20 : ℝ) (-217914570354964990381 / 10^20 : ℝ) := by
  have hr := Real.log_mul (by norm_num : (16 : ℝ) ≠ 0)
    (by norm_num : (155816 / 1377219 : ℝ) ≠ 0)
  rw [refinedLogSixteen] at hr
  norm_num at hr
  have h1 := fineLogTheta16
  have h2 := fineLogTwo
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private lemma logB_9 : Real.log (9 : ℝ) ∈
    Set.Icc (219722457733621938278 / 10^20 : ℝ) (219722457733621938281 / 10^20 : ℝ) := by
  rw [Real.log_nine]
  have h := logB_3
  constructor <;> linarith [h.1, h.2]

private lemma logB_4 : Real.log (4 : ℝ) ∈
    Set.Icc (138629436111989061882 / 10^20 : ℝ) (138629436111989061885 / 10^20 : ℝ) := by
  rw [Real.log_four]
  have h := fineLogTwo
  constructor <;> linarith [h.1, h.2]

private lemma logB_19 : Real.log 19 ∈ Set.Icc 2.94443897 2.94443899 :=
  ⟨le_trans (by numerics) (log_mem 4 8).1, (log_mem 4 8).2.trans (by numerics)⟩

private lemma logB_20 : Real.log 20 ∈ Set.Icc 2.99573226 2.99573228 :=
  ⟨le_trans (by numerics) (log_mem 4 8).1, (log_mem 4 8).2.trans (by numerics)⟩

/-- Cancellation of the large entropy terms, exactly at the new rational point. -/
private lemma GammaOf_B_eq :
    GammaOf 20 (155816 / 1377219) * Real.log 4
      = 1221403 / 1377219 * Real.log (1221403 / 1377219)
        + 19 * Real.log (26322977 / 26167161)
        + 155816 / 1377219 * Real.log (26322977 / 1377219)
        - 155816 / 1377219 * Real.log 9 := by
  rw [GammaOf_mul_log_four (by norm_num) (by norm_num) (by norm_num)]
  have h1 : (1 : ℝ) - 155816 / 1377219 = 1221403 / 1377219 := by norm_num
  have h2 : (20 : ℝ) - 1 + 155816 / 1377219 = 26322977 / 1377219 := by norm_num
  have h3 : (20 : ℝ) - 1 = 19 := by norm_num
  rw [h1, h2, h3, show (26322977 / 26167161 : ℝ) = (26322977 / 1377219) / 19 by
    norm_num, Real.log_div (x := 26322977 / 1377219) (y := 19) (by norm_num) (by norm_num)]
  ring

/-- The certified lower bound used for preprocessing boxes. -/
theorem GammaOf_B : (0.0660254968003 : ℝ) < GammaOf 20 (155816 / 1377219) := by
  refine lt_of_mul_lt_mul_right ?_ log_four_pos.le
  rw [GammaOf_B_eq]
  have h1 := logB_a; have h2 := logB_b; have h3 := logB_c; have h4 := logB_9
  have h5 := logB_4
  simp only [Set.mem_Icc] at *
  linarith

/-- A coarse upper bound required by the unchanged tensor geometry. -/
theorem GammaOf_B_lt : GammaOf 20 (155816 / 1377219) < (0.0661 : ℝ) := by
  refine lt_of_mul_lt_mul_right ?_ log_four_pos.le
  rw [GammaOf_B_eq]
  have h1 := logB_a; have h2 := logB_b; have h3 := logB_c; have h4 := logB_9
  have h5 := logB_4
  simp only [Set.mem_Icc] at *
  linarith

theorem GammaOf_B_pos : 0 < GammaOf 20 (155816 / 1377219) :=
  lt_trans (by norm_num) GammaOf_B

/-- The certified upper bound used for queries. -/
theorem qOf_B : qOf (155816 / 1377219) < (0.4339745031995 : ℝ) := by
  unfold qOf entropy
  rw [div_lt_iff₀ log_four_pos]
  have h1 := logB_theta; have h2 := logB_a; have h3 := logB_9; have h4 := logB_4
  norm_num only [show (1 : ℝ) - 155816 / 1377219 = 1221403 / 1377219 by norm_num]
  simp only [Set.mem_Icc] at *
  linarith

/-- The certified upper bound used for pruned encodings. -/
theorem bExp_B : 19 * Real.log 3 / Real.log 4 < (15.057143756851 : ℝ) := by
  rw [div_lt_iff₀ log_four_pos]
  have h3 := logB_3; have h5 := logB_4
  simp only [Set.mem_Icc] at *
  linarith

/-- The unchanged, coarse binomial coefficient bound. -/
theorem kappa_B : 20 * entropy (1 / 20) / Real.log 4 < (2.9 : ℝ) := by
  rw [div_lt_iff₀ log_four_pos, PrunedAux.mul_entropy_inv (by norm_num)]
  have h1 := logB_19; have h2 := logB_20; have h5 := logB_4
  simp only [Set.mem_Icc] at *
  norm_num
  linarith

end ThreeSumApsp
