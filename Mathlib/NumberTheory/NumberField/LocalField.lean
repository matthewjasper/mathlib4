import Mathlib.NumberTheory.NumberField.FinitePlaces
import Mathlib.Analysis.Normed.ValuativeRel
import Mathlib.Topology.Algebra.Valued.LocallyCompact

open NumberField
open NormedField

variable {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation "Khat" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v

#synth Field Khat
#synth ValuativeRel Khat
#synth UniformSpace Khat
#synth IsTopologicalDivisionRing Khat
#synth CompleteSpace Khat
#synth ValuativeTopology Khat
#synth ValuativeRel.IsRankLeOne Khat

noncomputable local instance : NontriviallyNormedField Khat where
  non_trivial := by
    obtain ⟨ϖ, hϖ⟩ := v.valuation_exists_uniformizer K
    use ϖ⁻¹
    rw [Valued.toNormedField.one_lt_norm_iff]
    simp [hϖ]
    decide

set_option linter.style.longLine false in
instance : ProperSpace Khat := by
  rw [Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField]
  -- Should be in FLT
  refine ⟨inferInstance, ?_, ?_⟩
  · sorry
  · sorry

local instance : LocallyCompactSpace Khat := locallyCompact_of_proper

local instance : Valued.v.Compatible (R := Khat) where
  rel_iff_le x y := by
    have hc := Valuation.Compatible.ofValuation (NormedField.valuation' (R := Khat))
    rw [hc.rel_iff_le, valuation'_apply, valuation'_apply, ← NNReal.coe_le_coe,
      coe_nnnorm, coe_nnnorm, Valued.toNormedField.norm_le_iff]

local instance : ValuativeRel.IsNontrivial Khat where
  condition := by
    obtain ⟨ϖ, hϖ⟩ := v.valuation_exists_uniformizer K
    use ValuativeRel.valuation Khat ϖ
    refine ⟨?_, ?_⟩
    · intro h
      simp [← UniformSpace.Completion.coe_zero] at h
      obtain rfl := UniformSpace.Completion.coe_injective (WithVal (v.valuation K)) h
      simp at hϖ
    · intro h
      have heq : (ValuativeRel.valuation Khat).IsEquiv (Valued.v (R := Khat)) := by
        apply ValuativeRel.isEquiv
      rw [heq.eq_one_iff_eq_one, v.valuedAdicCompletion_eq_valuation' ϖ] at h
      rw [h] at hϖ
      contradiction

local instance : ValuativeRel.IsDiscrete Khat where
  has_maximal_element := by
    obtain ⟨ϖ, hϖ⟩ := v.valuation_exists_uniformizer K
    use ValuativeRel.valuation Khat ϖ
    have heq : (ValuativeRel.valuation Khat).IsEquiv (Valued.v (R := Khat)) := by
      apply ValuativeRel.isEquiv
    refine ⟨?_, ?_⟩
    · rw [heq.lt_one_iff_lt_one, v.valuedAdicCompletion_eq_valuation' ϖ, hϖ]
      decide
    · intro δ hδ
      obtain ⟨x, y, rfl⟩ := ValuativeRel.valuation_surjective δ
      rw [← Valuation.map_div] at hδ ⊢
      rw [heq.lt_one_iff_lt_one] at hδ
      rw [heq, v.valuedAdicCompletion_eq_valuation' ϖ, hϖ]
      -- How much of this already exists in Mathlib?
      by_cases h : Valued.v (x / ↑y) = 0
      · rw [h]
        decide
      · change _ ≠ _ at h
        rw [WithZero.ne_zero_iff_exists] at h
        obtain ⟨a, ha⟩ := h
        rw [← ha] at hδ ⊢
        rw [WithZero.coe_lt_one, ← Multiplicative.toAdd_lt, toAdd_one] at hδ
        have := Int.le_sub_one_of_lt hδ
        rwa [WithZero.coe_le_coe, ← Multiplicative.toAdd_le, toAdd_ofAdd]
