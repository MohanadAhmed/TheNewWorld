import Mathlib
-- import Mathlib.Data.Real.Pi.Bounds

open MeasureTheory Real

-- noncomputable def fμσ (μ : ℝ) (σ : ℝ) := fun x => ENNReal.ofReal (Real.exp (-2*(x)^2 / (2*σ^2)))
noncomputable def fμσ (μ : ℝ) (σ : ℝ) := fun x => ENNReal.ofReal (Real.sqrt (π/2)⁻¹ * Real.exp (-2*(x)^2))

noncomputable def gaussianMeasure (μ : ℝ) (σ : ℝ) : MeasureTheory.Measure ℝ := by
  apply MeasureTheory.Measure.withDensity volume (fμσ μ σ)

lemma gaussianMeasure_isProbability (μ : ℝ) (σ : ℝ)(hσ: 0 < σ) : 
    IsProbabilityMeasure (gaussianMeasure μ σ) := by
  unfold gaussianMeasure
  refine' {measure_univ := _}
  simp only [MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
  unfold fμσ
  simp only [Real.rpow_two]

  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff _ zero_le_one]
    simp_rw [← @smul_eq_mul ℝ _ (Real.sqrt (π/2)⁻¹)]
    rw [integral_smul, integral_gaussian, smul_eq_mul, ← sqrt_mul, inv_mul_cancel, sqrt_one]
    apply div_ne_zero pi_ne_zero two_ne_zero
    simp only [inv_div, le_div_iff pi_pos, zero_mul, zero_le_two]
    apply integral_nonneg
    · intro x
      simpa [Pi.zero_apply] using (mul_nonneg (sqrt_nonneg _) (le_of_lt (exp_pos _)))

  · apply Integrable.const_mul (integrable_exp_neg_mul_sq two_pos) _

  · unfold Filter.EventuallyLE Filter.Eventually
    dsimp only [Pi.zero_apply]
    apply Filter.univ_mem'
    intro x
    simp only [Set.mem_setOf_eq]
    apply mul_nonneg (sqrt_nonneg _) (le_of_lt (exp_pos _))
  
