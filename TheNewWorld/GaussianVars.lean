import Mathlib

open MeasureTheory Real

noncomputable def fμσ (μ : ℝ) (σ : ℝ) := fun x => ENNReal.ofReal (Real.sqrt (π/(1 / (2*σ^2)))⁻¹ * Real.exp (-(x - μ)^2 / (2*σ^2)))

noncomputable def gaussianMeasure (μ : ℝ) (σ : ℝ) : MeasureTheory.Measure ℝ := by
  apply MeasureTheory.Measure.withDensity volume (fμσ μ σ)


lemma gaussianMeasure_isProbabilityMeasure (μ : ℝ) (σ : ℝ)(hσ: 0 < σ) : 
    IsProbabilityMeasure (gaussianMeasure μ σ) := by
  have h1 : ∀ (a : ℝ), -a ^ 2 / (2*σ^2) = -(1/(2*σ^2)) * (a ^ 2) := by intro; ring;
  have σ2_pos : 0 < (2*σ^2)⁻¹ := by 
    simp only [rpow_two]; apply inv_pos.2 (mul_pos two_pos (pow_pos hσ _))
    done
  let fσ := (fun x => ENNReal.ofReal (Real.exp (-(x^2 / (2*σ^2)))))

  unfold gaussianMeasure
  refine' {measure_univ := _}
  simp only [MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
  unfold fμσ
  -- simp only [Real.rpow_two]
  rw [← ofReal_integral_eq_lintegral_ofReal] -- Generates three side goals
  -- SUBGOAL 1: Integral of function = 1
  · rw [← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff _ zero_le_one]
    simp_rw [sub_eq_neg_add, add_comm]
    rw [integral_add_right_eq_self (fun x => (Real.sqrt (π/( 1 / (2*σ^2)))⁻¹ * Real.exp (-(x)^2 / (2*σ^2)))) (-μ)]
    simp_rw [←smul_eq_mul, integral_smul, smul_eq_mul, h1, rpow_two] -- div_eq_mul_inv, mul_comm, mul_neg, ← neg_mul
    rw [ integral_gaussian, ← sqrt_mul, sqrt_eq_one, inv_mul_cancel]
    apply div_ne_zero (pi_ne_zero) (div_ne_zero one_ne_zero ((ne_of_gt (mul_pos two_pos (pow_pos hσ _)))))
    rw [inv_nonneg]
    apply div_nonneg (le_of_lt pi_pos) (le_of_lt _)
    apply div_pos one_pos (mul_pos two_pos (pow_pos hσ _))
    apply integral_nonneg
    · intro x
      simpa [Pi.zero_apply] using (mul_nonneg (sqrt_nonneg _) (le_of_lt (exp_pos _)))

  -- SUBGOAL 2:  Lebesgue Integral is finite
  · apply Integrable.const_mul
    simp_rw [mul_div_right_comm, neg_div]
    unfold Integrable
    constructor
    -- Continuity of the gaussian function
    simp only [rpow_two]
    apply Measurable.aestronglyMeasurable (Continuous.measurable _)
    apply Continuous.comp Real.continuous_exp (Continuous.neg (Continuous.div_const _ _))
    apply Continuous.pow (Continuous.sub continuous_id continuous_const)
    -- Finiteness of the Gaussian Integral
    unfold HasFiniteIntegral
    simp_rw [← rpow_two]
    rw [lintegral_nnnorm_eq_of_nonneg, lintegral_sub_right_eq_self fσ μ, 
      ← lintegral_nnnorm_eq_of_nonneg]
    apply Integrable.hasFiniteIntegral
    simp_rw [div_eq_inv_mul, ← neg_mul]
    convert integrable_exp_neg_mul_sq σ2_pos
    simp only [rpow_two]
    all_goals ( intro x; simp only [Pi.zero_apply, rpow_two]; apply (le_of_lt (exp_pos _)))

  -- SUBGOAL 3:  Something about measurability!!!
  · unfold Filter.EventuallyLE Filter.Eventually
    dsimp only [Pi.zero_apply]
    apply Filter.univ_mem'
    intro x
    simp only [Set.mem_setOf_eq]
    apply mul_nonneg (sqrt_nonneg _) (le_of_lt (exp_pos _))
