/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.GroupWithZero.Int
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Discrete Valuations

A valuation `v : A → ℤₘ₀` on a ring `A` is said to be a (normalized) discrete valuation if
`ofAdd (-1 : ℤ)` belongs to the image of `v`. Note that valuations in Mathlib are multiplicative;
if `a : A → ℤ ∪ {infty}` is the additive valuation associated to `v`, this is equivalent to asking
that `1 : ℤ` belongs to the image of `a`.

## Main Definitions
* `IsDiscrete`: We define a valuation to be discrete if it is `ℤₘ₀`-valued and `ofAdd (-1 : ℤ)`
belongs to the image.

## TODO
* Define (pre)uniformizers for nontrivial `ℤₘ₀`-valued valuations.
* Relate discrete valuations and discrete valuation rings.

-/

namespace Valuation

open Function Multiplicative Set

variable {A : Type*} [Ring A]

/-- A valuation `v` on a ring `A` is (normalized) discrete if it is `ℤₘ₀`-valued and
  `ofAdd (-1 : ℤ)` belongs to the image. Note that the latter is equivalent to
  asking that `1 : ℤ` belongs to the image of the corresponding additive valuation. -/
class IsDiscrete (v : Valuation A ℤₘ₀) : Prop where
  one_mem_range : (↑(ofAdd (-1 : ℤ)) : ℤₘ₀) ∈ range v

variable {K : Type*} [Field K]

/-- A discrete valuation on a field `K` is surjective. -/
lemma IsDiscrete.surj (v : Valuation K ℤₘ₀) [hv : IsDiscrete v] :
    Surjective v := by
  intro c
  obtain ⟨π, hπ⟩ := hv
  refine WithZero.cases_on c ⟨0, map_zero _⟩ fun a ↦ ⟨π ^ (-a.toAdd), ?_⟩
  simp [hπ, ← WithZero.ofAdd_zpow]

/-- A `ℤₘ₀`-valued valuation on a field `K` is discrete if and only if it is surjective. -/
lemma isDiscrete_iff_surjective (v : Valuation K ℤₘ₀) :
    IsDiscrete v ↔ Surjective v :=
  ⟨fun _ ↦ IsDiscrete.surj v, fun hv ↦ ⟨hv _⟩⟩

theorem lt_iff_le_pred {x : ℤₘ₀} {m : Multiplicative ℤ} : x < m ↔ x ≤ m * ofAdd (-1 : ℤ) := by
  obtain rfl | hx := eq_or_ne x 0
  · simp [← WithZero.coe_mul, WithZero.zero_lt_coe, WithZero.zero_le]
  · obtain ⟨x, rfl⟩ := WithZero.ne_zero_iff_exists.mp hx
    rw [ofAdd_neg, WithZero.coe_lt_coe, ← WithZero.coe_mul, WithZero.coe_le_coe,
      le_mul_inv_iff_mul_le]
    rfl

theorem lt_iff_succ_le {x : ℤₘ₀} {m : Multiplicative ℤ} : x < m ↔ x * ofAdd (1 : ℤ) ≤ m := by
  obtain rfl | hx := eq_or_ne x 0
  · simp [← WithZero.coe_mul, WithZero.zero_lt_coe, WithZero.zero_le]
  · obtain ⟨x, rfl⟩ := WithZero.ne_zero_iff_exists.mp hx
    rw [← WithZero.coe_mul, WithZero.coe_lt_coe, WithZero.coe_le_coe]
    rfl

lemma irreducible_of_valuation_eq_ofAdd_neg_one (v : Valuation K ℤₘ₀) (ϖ : v.integer)
    (h : v ϖ = (ofAdd (-1 : ℤ))) : Irreducible ϖ := by
  have hv := Valuation.integer.integers v
  refine ⟨?_, ?_⟩
  · intro hu
    rw [Integers.isUnit_iff_valuation_eq_one hv, Algebra.algebraMap_ofSubring_apply, h] at hu
    contradiction
  · intro a b hab
    apply_fun v at hab
    simp only [Subring.coe_mul, map_mul, h] at hab
    simp only [Integers.isUnit_iff_valuation_eq_one hv]
    rw [or_iff_not_and_not]
    intro ⟨ha, hb⟩
    have ha := lt_of_le_of_ne a.prop ha
    have hb := lt_of_le_of_ne b.prop hb
    rw [← WithZero.coe_one, lt_iff_le_pred, WithZero.coe_one, one_mul] at ha hb
    have := le_of_eq_of_le hab <| mul_le_mul' ha hb
    contradiction

section IsDiscreteValuationRing

open IsDiscreteValuationRing

theorem hasUnitMulPowIrreducibleFactorization (v : Valuation K ℤₘ₀) [hv : IsDiscrete v] :
    HasUnitMulPowIrreducibleFactorization v.integer := by
  have hvi := Valuation.integer.integers v
  obtain ⟨ϖ, hϖ⟩ := hv.one_mem_range
  have hϖ' : v ϖ ≤ 1 := by rw [hϖ]; decide
  refine ⟨⟨ϖ, hϖ'⟩, irreducible_of_valuation_eq_ofAdd_neg_one v _ hϖ, ?_⟩
  intro ⟨x, (hvx : v x ≤ 1)⟩ hx
  have hx' : v x ≠ 0 := by
    rw [ne_zero_iff v]
    rintro rfl
    contradiction
  rw [WithZero.ne_zero_iff_exists] at hx'
  obtain ⟨n', hn'⟩ := hx'
  rw [← hn', WithZero.coe_le_one] at hvx
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hvx
  use n
  simp only [hvi.associated_iff_eq, Algebra.algebraMap_ofSubring_apply, ← hn', hn, map_pow, hϖ,
    Int.reduceNeg, ← WithZero.coe_pow, ← ofAdd_nsmul, smul_neg, nsmul_eq_mul, mul_one,
    WithZero.coe_inj]
  rfl

instance instIsDiscreteValuationRing (v : Valuation K ℤₘ₀) [hv : IsDiscrete v] :
    IsDiscreteValuationRing v.integer :=
  ofHasUnitMulPowIrreducibleFactorization (hasUnitMulPowIrreducibleFactorization v)

open WithZero Multiplicative in
lemma ofAdd_one_le_apply_ofAdd_one (f : ℤₘ₀ ≃*o ℤₘ₀) : (ofAdd (1 : ℤ)) ≤ f ↑(ofAdd (1 : ℤ)) := by
  have hf : f ↑(ofAdd (1 : ℤ)) ≠ 0 := by
    simp
  rw [WithZero.ne_zero_iff_exists] at hf
  obtain ⟨g, hg⟩ := hf
  have : 1 < f ↑(ofAdd (1 : ℤ)) := by
    rw [← map_one f, map_lt_map_iff f]
    decide
  rwa [← hg, lt_iff_succ_le, one_mul, hg] at this

open WithZero Multiplicative in
lemma OrderedMonoidIso.apply_of_zm0 (f : ℤₘ₀ ≃*o ℤₘ₀) { x : ℤₘ₀ } : f x = x := by
  by_cases h : x = 0
  · simp [h]
  lift x to Multiplicative ℤ using h
  have hxval : x = (Multiplicative.ofAdd 1) ^ x.toAdd := by
    rw [← Int.ofAdd_mul, Int.one_mul, ofAdd_toAdd]
  rw [hxval]
  simp only [WithZero.coe_zpow, map_zpow₀, OrderMonoidIso.coe_refl, id_eq]
  congr
  apply le_antisymm _ (ofAdd_one_le_apply_ofAdd_one f)
  nth_rw 2 [← OrderMonoidIso.apply_symm_apply f ↑(ofAdd (1 : ℤ))]
  rw [map_le_map_iff f]
  exact ofAdd_one_le_apply_ofAdd_one f.symm

open WithZero Multiplicative in
instance unique_zm0_iso : Unique (ℤₘ₀ ≃*o ℤₘ₀) := {
  default := OrderMonoidIso.refl _
  uniq f := OrderMonoidIso.ext fun _ ↦ OrderedMonoidIso.apply_of_zm0 f
}

theorem eq_ofEquiv (v v' : Valuation K ℤₘ₀) [IsDiscrete v] [IsDiscrete v']
    (h : v.IsEquiv v') : v = v' := by
  ext x
  have hsurj := IsDiscrete.surj v
  have hsurj' := IsDiscrete.surj v'
  rw [← orderEquiv_of_isEquiv_surjective_apply (r:=⟨v x, x, rfl⟩) h rfl hsurj hsurj',
    OrderedMonoidIso.apply_of_zm0]

end IsDiscreteValuationRing

end Valuation
