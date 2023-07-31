import Mathlib

open MeasureTheory Real

noncomputable def fμσ (μ : ℝ) (σ : ℝ) := fun x => ENNReal.ofReal (Real.sqrt (π/(2 / (2*σ^2)))⁻¹ * Real.exp (-2*(x)^2 / (2*σ^2)))

noncomputable def gaussianMeasure (μ : ℝ) (σ : ℝ) : MeasureTheory.Measure ℝ := by
  apply MeasureTheory.Measure.withDensity volume (fμσ μ σ)

lemma gaussianMeasure_isProbabilityMeasure (μ : ℝ) (σ : ℝ)(hσ: 0 < σ) : 
    IsProbabilityMeasure (gaussianMeasure μ σ) := by
  unfold gaussianMeasure
  refine' {measure_univ := _}
  simp only [MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
  unfold fμσ
  simp only [Real.rpow_two]

  rw [← ofReal_integral_eq_lintegral_ofReal] -- Generates three side goals
   -- Integral of function = 1
  · rw [← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff _ zero_le_one]
    simp_rw [←smul_eq_mul, integral_smul, smul_eq_mul, mul_div_right_comm, neg_div]
    rw [ integral_gaussian, ← sqrt_mul, sqrt_eq_one, inv_mul_cancel]
    apply div_ne_zero (pi_ne_zero) (div_ne_zero two_ne_zero (ne_of_gt (mul_pos two_pos (pow_pos hσ _))))
    rw [inv_nonneg]
    apply div_nonneg (le_of_lt pi_pos) (le_of_lt _)
    apply div_pos two_pos (mul_pos two_pos (pow_pos hσ _))
    apply integral_nonneg
    · intro x
      simpa [Pi.zero_apply] using (mul_nonneg (sqrt_nonneg _) (le_of_lt (exp_pos _)))
  -- Lebesgue Integral is finite
  · apply Integrable.const_mul
    simp_rw [mul_div_right_comm, neg_div]
    apply integrable_exp_neg_mul_sq (div_pos two_pos (mul_pos two_pos (pow_pos hσ _)))
  -- Something about measurability!!!
  · unfold Filter.EventuallyLE Filter.Eventually
    dsimp only [Pi.zero_apply]
    apply Filter.univ_mem'
    intro x
    simp only [Set.mem_setOf_eq]
    apply mul_nonneg (sqrt_nonneg _) (le_of_lt (exp_pos _))

