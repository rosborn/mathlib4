/-
Copyright (c) 2026 Richard Osborn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Osborn
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Index

/-!
# Hall subgroups

A **Hall subgroup** of a group `G` is a subgroup `H` whose order is coprime to its index.

This file defines `Subgroup.IsHall` and proves the transfer lemmas that need no factorization
theory: preservation under surjective images and automorphisms, restriction to an overgroup,
transitivity, and intersection with arbitrary subgroups (for normal Hall subgroups).

## Main definitions

- `Subgroup.IsHall H` : `Nat.card H` is coprime to `H.index`.
-/

@[expose] public section

namespace Subgroup

variable {G G' : Type*} [Group G] [Group G']

/-- A subgroup `H` is a **Hall subgroup** of `G` if its order is coprime to its index.

For finite `G`, this says that `Nat.card H` is a unitary divisor of `Nat.card G`. -/
structure IsHall (H : Subgroup G) : Prop where
  /-- The order of `H` is coprime to its index. -/
  coprime : Nat.Coprime (Nat.card H) H.index

variable {H : Subgroup G}

@[simp]
theorem isHall_top : (⊤ : Subgroup G).IsHall := ⟨by simp⟩

@[simp]
theorem isHall_bot : (⊥ : Subgroup G).IsHall := ⟨by simp⟩

/-- In an infinite group, the only Hall subgroups are `⊤` and `⊥`. -/
theorem IsHall.eq_top_or_eq_bot_or_finite (hH : H.IsHall) : H = ⊤ ∨ H = ⊥ ∨ Finite G :=
  eq_top_or_eq_bot_or_finite_of_coprime hH.coprime

/-! ### Preservation under images, restriction, and intersection -/

theorem IsHall.map (hH : H.IsHall) {f : G →* G'} (hf : Function.Surjective f) :
    (H.map f).IsHall := by
  refine ⟨?_⟩
  grw [H.card_map_dvd f, H.index_map_dvd hf]
  exact hH.coprime

open scoped Pointwise in
/-- The Hall property is preserved by a group acting by automorphisms. -/
theorem IsHall.smul {α : Type*} [Group α] [MulDistribMulAction α G] (hH : H.IsHall) (a : α) :
    (a • H).IsHall := by
  rw [Subgroup.pointwise_smul_def]
  exact hH.map (MulDistribMulAction.toMulEquiv G a).surjective

theorem IsHall.subgroupOf {K : Subgroup G} (hH : H.IsHall) (hHK : H ≤ K) :
    (H.subgroupOf K).IsHall := by
  refine ⟨?_⟩
  rw [card_subgroupOf_of_le hHK]
  exact hH.coprime.coprime_dvd_right (H.relIndex_dvd_index_of_le hHK)

/-- A Hall subgroup of a Hall subgroup is a Hall subgroup. -/
theorem IsHall.of_subgroupOf {K : Subgroup G} (hH : (H.subgroupOf K).IsHall) (hK : K.IsHall)
    (hHK : H ≤ K) : H.IsHall := by
  refine ⟨?_⟩
  rw [← relIndex_mul_index hHK]
  refine Nat.Coprime.mul_right ?_ (hK.coprime.coprime_dvd_left (card_dvd_of_le hHK))
  rw [← card_subgroupOf_of_le hHK]
  exact hH.coprime

/-- A normal Hall subgroup meets every subgroup `U` in a Hall subgroup of `U`. -/
theorem IsHall.subgroupOf_of_normal [H.Normal] (hH : H.IsHall) (U : Subgroup G) :
    (H.subgroupOf U).IsHall := by
  refine ⟨(hH.coprime.coprime_dvd_left ?_).coprime_dvd_right (relIndex_dvd_index_of_normal H U)⟩
  rw [card_subgroupOf]
  exact card_dvd_of_le inf_le_left

end Subgroup
