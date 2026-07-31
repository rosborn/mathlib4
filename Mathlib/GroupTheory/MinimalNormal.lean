/-
Copyright (c) 2026 Richard Osborn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Osborn
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Torsion

/-!
# Minimal normal subgroups

A minimal normal subgroup of a group `G` is a nontrivial normal subgroup containing no smaller
nontrivial normal subgroup. This file proves that minimal normal subgroups exist whenever the
subgroup lattice is well-founded, and that a minimal normal subgroup of a finite solvable group
is a `p`-group.

## References

* [I. M. Isaacs, *Finite Group Theory*][isaacs2008], Lemma 3.11
-/

@[expose] public section

namespace Subgroup

variable (G : Type*) [Group G]

/-- A nontrivial group whose subgroup lattice is well-founded has a minimal nontrivial
normal subgroup. In particular, this holds for nontrivial finite groups. -/
theorem exists_minimal_normal_ne_bot [WellFoundedLT (Subgroup G)] [Nontrivial G] :
    ∃ N : Subgroup G, Minimal (fun K : Subgroup G ↦ K.Normal ∧ K ≠ ⊥) N :=
  exists_minimal_of_wellFoundedLT _ ⟨⊤, inferInstance, top_ne_bot⟩

variable {G}

open scoped IsMulCommutative

/-- A minimal normal subgroup of a solvable group is abelian. -/
theorem isMulCommutative_of_minimal_normal [Group.IsSolvable G] {M : Subgroup G}
    (h : Minimal (fun K : Subgroup G ↦ K.Normal ∧ K ≠ ⊥) M) : IsMulCommutative M := by
  obtain ⟨hMn, hMne⟩ := h.prop
  rw [← Subgroup.le_centralizer_iff_isMulCommutative,
    ← Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hlt : ⁅M, M⁆ < M := Group.IsSolvable.commutator_lt_of_ne_bot hMne
  exact not_not.mp (not_and.mp (h.not_prop_of_lt hlt) inferInstance)

/-- A minimal normal subgroup of a finite solvable group is a `p`-group for some prime `p`
(Isaacs, *Finite Group Theory*, Lemma 3.11). -/
theorem exists_isPGroup_of_minimal_normal [Finite G] [Group.IsSolvable G] {M : Subgroup G}
    (h : Minimal (fun K : Subgroup G ↦ K.Normal ∧ K ≠ ⊥) M) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p M := by
  obtain ⟨hMn, hMne⟩ := h.prop
  have : IsMulCommutative M := isMulCommutative_of_minimal_normal h
  have : Nontrivial M := M.nontrivial_iff_ne_bot.mpr hMne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := M)).ne'
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, ?_⟩
  suffices hSM : (CommGroup.primaryComponent M p).map M.subtype = M from
    hSM ▸ CommGroup.primaryComponent.isPGroup.map M.subtype
  obtain ⟨g, rfl⟩ := exists_prime_orderOf_dvd_card' (G := M) p hpdvd
  refine h.eq_of_le ⟨inferInstance, fun hbot => hp.ne_one ?_⟩ (map_subtype_le _)
  rw [orderOf_eq_one_iff]
  rw [map_eq_bot_iff_of_injective (hf := M.subtype_injective)] at hbot
  exact mem_bot.mp <| hbot.le <| CommGroup.mem_primaryComponent_iff_orderOf.mpr ⟨1, by simp⟩

end Subgroup
