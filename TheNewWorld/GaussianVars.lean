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
  
  -- Attempt 1: requires injectivity of toReal
  -- apply_fun ENNReal.toReal
  -- rw [← MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  -- simp only [ENNReal.one_toReal]
  -- rw [integral_gaussian]
  
  
  
  -- Attempt 2: 
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff _ zero_le_one]
    set c := Real.sqrt (π/2)⁻¹
    -- change Real.sqrt (2*π)⁻¹ with c
    simp_rw [← @smul_eq_mul ℝ _ c]
    rw [integral_smul]
    rw [integral_gaussian]
    rw [smul_eq_mul, ← sqrt_mul, inv_mul_cancel, sqrt_one]
    norm_num
    apply Real.pi_ne_zero
    simp only [inv_div]
    rw [le_div_iff pi_pos, zero_mul]
    exact zero_le_two
    apply integral_nonneg
    · intro x
      simp only [Pi.zero_apply, inv_div, neg_mul, gt_iff_lt, sqrt_pos]
      apply mul_nonneg
      apply sqrt_nonneg
      apply le_of_lt (exp_pos _)

  -- Attempt 2a
  -- apply MeasureTheory.Integrable.ofReal
  -- unfold Integrable
  -- constructor
  -- sorry
  -- unfold HasFiniteIntegral
  -- dsimp
  
  · apply Integrable.const_mul
    exact integrable_exp_neg_mul_sq two_pos
  -- Attempt 3a
  · unfold Filter.EventuallyLE Filter.Eventually
    dsimp only [Pi.zero_apply]
    apply Filter.univ_mem'
    intro x
    simp only [Set.mem_setOf_eq]
    apply mul_nonneg
    apply sqrt_nonneg
    apply le_of_lt (exp_pos _)
    -- unfold volume measureSpace Measure.ae
    -- simp only [Filter.mem_mk, Set.mem_setOf_eq]
    -- rw [MeasureTheory.measure_compl]
    
    -- have : {x | 0 ≤ sqrt (π/2)⁻¹ * Real.exp (-2 * x ^ 2)} = {x | True} := by
    --   rw [Set.setOf_true]
    --   apply Set.eq_univ_iff_forall.2
    --   intro x
    --   simp only [Set.mem_setOf_eq]
    --   apply mul_nonneg
    --   apply sqrt_nonneg
    --   apply le_of_lt (exp_pos _)
    
    
    
    
    
    
    
  
  
  
  
  
  -- apply integral_nonneg
  -- · intro x
  --   simp only [Pi.zero_apply]
  --   apply le_of_lt
  --   apply Real.exp_pos
  -- · unfold Integrable
  --   constructor
  --   · apply StronglyMeasurable.aestronglyMeasurable
  --     apply Measurable.stronglyMeasurable
  --     apply Continuous.measurable
  --     apply Continuous.comp Real.continuous_exp
  --     apply Continuous.div
  --     apply Continuous.neg
  --     apply Continuous.pow
  --     apply Continuous.sub
  --     apply continuous_id
  --     apply continuous_const
  --     apply continuous_const
  --     simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, zero_lt_two, pow_eq_zero_iff, false_or, forall_const]
  --     rw [eq_comm]
  --     apply ne_of_lt hσ
  --   · unfold HasFiniteIntegral
  --     dsimp only
  --     rw [MeasureTheory.lintegral_nnnorm_eq_of_nonneg]
  --     rw [@lt_top_iff_ne_top]
      
  --     sorry
  -- · sorry

  