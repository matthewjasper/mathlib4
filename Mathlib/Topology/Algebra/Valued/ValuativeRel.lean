/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.RingTheory.Valuation.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.UniformSpace.Ultra.Basic

/-!

# Valuative Relations as Valued

In this temporary file, we provide a helper instance
for `Valued R Γ` derived from a `ValuativeRel R`,
so that downstream files can refer to `ValuativeRel R`,
to facilitate a refactor.

-/

namespace ValuativeTopology

variable {R : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R]

open ValuativeRel TopologicalSpace Filter Topology Set Uniformity

local notation "v" => valuation R

lemma of_hasBasis (h : (𝓝 (0 : R)).HasBasis (fun _ ↦ True)
    fun γ : (ValueGroupWithZero R)ˣ ↦ { x | v x < γ }) :
    ValuativeTopology R :=
  ⟨by simp [h.mem_iff]⟩

variable [ValuativeTopology R]

variable (R) in
theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ ↦ True)
      fun γ : (ValueGroupWithZero R)ˣ ↦ { x | v x < γ } := by
  simp [Filter.hasBasis_iff, mem_nhds_iff]

variable [IsTopologicalAddGroup R]

theorem mem_nhds {s : Set R} {x : R} :
    s ∈ 𝓝 x ↔ ∃ γ : (ValueGroupWithZero R)ˣ, { y | v (y - x) < γ } ⊆ s := by
  simp only [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_setOf_eq, true_and,
    ((hasBasis_nhds_zero R).comap fun y => y - x).mem_iff]

instance : UniformSpace R := IsTopologicalAddGroup.toUniformSpace R

open Uniformity in
theorem hasBasis_uniformity : (𝓤 R).HasBasis (fun _ => True)
    fun γ : (ValueGroupWithZero R)ˣ => { p : R × R | v (p.2 - p.1) < γ } := by
  rw [uniformity_eq_comap_nhds_zero']
  exact (hasBasis_nhds_zero R).comap _

instance : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
instance : IsTopologicalRing R := by
  convert (valuation R).subgroups_basis.toRingFilterBasis.isTopologicalRing
  rw [TopologicalSpace.ext_iff_nhds]
  intro x
  ext s
  simp [(RingSubgroupsBasis.hasBasis_nhds _ _).mem_iff, mem_nhds, Valuation.ltAddSubgroup]

instance : IsUltraUniformity R := by
  refine .mk_of_hasBasis hasBasis_uniformity ?_ ?_
  · intros
    ext ⟨x, y⟩
    simp only [preimage_setOf_eq, Prod.snd_swap, Prod.fst_swap, mem_setOf_eq]
    rw [← Valuation.map_neg, neg_sub]
  · intro _ _ _ _ _ h h'
    simp only [mem_setOf_eq] at h h' ⊢
    have := Valuation.map_add_lt _ h h'
    ring_nf at this
    rwa [neg_add_eq_sub] at this

theorem isOpen_ball (r : ValueGroupWithZero R) :
    IsOpen {x | v x < r} := by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · intro x hx
    rw [mem_nhds]
    simp only [setOf_subset_setOf]
    exact ⟨Units.mk0 _ hr,
      fun y hy => (sub_add_cancel y x).symm ▸ ((v).map_add _ x).trans_lt (max_lt hy hx)⟩

theorem isClosed_ball (r : ValueGroupWithZero R) :
    IsClosed {x | v x < r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v (Units.mk0 r hr))
      (isOpen_ball _)

theorem isClopen_ball (r : ValueGroupWithZero R) :
    IsClopen {x | v x < r} :=
  ⟨isClosed_ball _, isOpen_ball _⟩

lemma isOpen_closedBall {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsOpen {x | v x ≤ r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [setOf_subset_setOf]
  exact ⟨Units.mk0 _ hr, fun y hy => (sub_add_cancel y x).symm ▸
    le_trans ((v).map_add _ _) (max_le (le_of_lt hy) hx)⟩

theorem isClosed_closedBall (r : ValueGroupWithZero R) :
    IsClosed {x | v x ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_setOf_eq, not_le] at hx
  rw [mem_nhds]
  have hx' : v x ≠ 0 := ne_of_gt <| lt_of_le_of_lt zero_le' <| hx
  exact ⟨Units.mk0 _ hx', fun y hy hy' => ne_of_lt hy <| Valuation.map_sub_swap v x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

theorem isClopen_closedBall {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsClopen {x | v x ≤ r} :=
  ⟨isClosed_closedBall _, isOpen_closedBall hr⟩

theorem isClopen_sphere {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsClopen {x | v x = r} := by
  have h : {x : R | v x = r} = {x | v x ≤ r} \ {x | v x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall hr) (isClopen_ball _)

lemma isOpen_sphere {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsOpen {x | v x = r} :=
  isClopen_sphere hr |>.isOpen

end ValuativeTopology

namespace ValuativeRel

variable {R : Type*} [CommRing R]

instance [UniformSpace R] [IsUniformAddGroup R] [ValuativeRel R] [ValuativeTopology R] :
    Valued R (ValueGroupWithZero R) :=
  .mk (valuation R) ValuativeTopology.mem_nhds_iff

@[inherit_doc]
scoped notation "𝒪[" R "]" => Valuation.integer (valuation R)

@[inherit_doc]
scoped notation "𝓂[" K "]" => IsLocalRing.maximalIdeal 𝒪[K]

@[inherit_doc]
scoped notation "𝓀[" K "]" => IsLocalRing.ResidueField 𝒪[K]

end ValuativeRel
