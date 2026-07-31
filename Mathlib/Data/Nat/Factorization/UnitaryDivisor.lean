/-
Copyright (c) 2026 Richard Osborn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Osborn
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.PrimeFin

/-!
# Unitary divisors

This file defines `Nat.IsUnitaryDivisor d n`, asserting that `d` is a *unitary divisor* of
`n`: a divisor that is coprime to its complement `n / d`. Equivalently, for every prime `p`
the multiplicity `d.factorization p` is either `0` or the full multiplicity `n.factorization p`
(see `Nat.isUnitaryDivisor_iff_factorization`); for example, `ordProj[p] n` is the unitary
divisor of `n` with prime support `{p}`.

The main results are that the complement `n / d` is again a unitary divisor
(`Nat.IsUnitaryDivisor.div`), that the gcd with any divisor `m` of `n` is a unitary divisor
of `m` (`Nat.IsUnitaryDivisor.gcd`), and that a unitary divisor is determined by its prime
support (`Nat.IsUnitaryDivisor.eq_of_primeFactors_eq`).
-/

@[expose] public section

namespace Nat

/-- A *unitary divisor* of `n` is a divisor `d` whose complement `n / d` is coprime to `d`.
Equivalently (for nonzero `d`, see `Nat.isUnitaryDivisor_iff_factorization`), for every prime `p`
the exponent `d.factorization p` is either `0` or the full `n.factorization p`. -/
structure IsUnitaryDivisor (d n : ℕ) : Prop where
  /-- `d` divides `n`. -/
  dvd : d ∣ n
  /-- `d` is coprime to its complement `n / d`. -/
  coprime : Nat.Coprime d (n / d)

namespace IsUnitaryDivisor

variable {d n m : ℕ}

theorem ne_zero (h : IsUnitaryDivisor d n) : d ≠ 0 := by
  rintro rfl
  obtain rfl : n = 0 := Nat.eq_zero_of_zero_dvd h.dvd
  simpa using h.coprime

theorem mul_div_cancel (h : IsUnitaryDivisor d n) : d * (n / d) = n :=
  Nat.mul_div_cancel' h.dvd

theorem eq_one (h : IsUnitaryDivisor d 0) : d = 1 := by
  simpa using h.coprime

@[simp] theorem one_left {n : ℕ} : IsUnitaryDivisor 1 n where
  dvd := one_dvd n
  coprime := Nat.coprime_one_left _

theorem refl (hn : n ≠ 0) : IsUnitaryDivisor n n where
  dvd := dvd_refl n
  coprime := by rw [Nat.div_self (Nat.pos_of_ne_zero hn)]; exact Nat.coprime_one_right _

/-- The complement `n / d` of a unitary divisor of `n` is again a unitary divisor of `n`. -/
theorem div (h : IsUnitaryDivisor d n) (hn : n ≠ 0) : IsUnitaryDivisor (n / d) n where
  dvd := ⟨d, (Nat.div_mul_cancel h.dvd).symm⟩
  coprime := by rw [Nat.div_div_self h.dvd hn]; exact h.coprime.symm

/-- The prime support of the complementary unitary divisor is the complementary support. -/
theorem primeFactors_div (h : IsUnitaryDivisor d n) :
    (n / d).primeFactors = n.primeFactors \ d.primeFactors := by
  conv_rhs => rw [← h.mul_div_cancel]
  exact h.coprime.primeFactors_sdiff

@[gcongr]
theorem primeFactors_subset (h : IsUnitaryDivisor d n) : d.primeFactors ⊆ n.primeFactors := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [h.eq_one]
    simp
  · exact Nat.primeFactors_mono h.dvd hn

theorem of_eq_mul_of_coprime (hd : d ≠ 0) (hn : n = d * m) (hcop : Nat.Coprime d m) :
    IsUnitaryDivisor d n where
  dvd := ⟨m, hn⟩
  coprime := by rwa [hn, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd)]

theorem coprime_of_eq_mul (h : IsUnitaryDivisor d n) (hn : n = d * m) : Nat.Coprime d m := by
  obtain rfl : m = n / d := by
    rw [hn, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h.ne_zero)]
  exact h.coprime

theorem factorization_eq_or_full (h : IsUnitaryDivisor d n) (p : ℕ) :
    d.factorization p = 0 ∨ d.factorization p = n.factorization p := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [h.eq_one]; simp
  by_cases hpd : p ∣ d
  · by_cases hp : p.Prime
    · right
      have hquot_zero : (n / d).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
        fun hpq => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h.coprime hpd hpq)
      have hd_le : d.factorization p ≤ n.factorization p :=
        (Nat.factorization_le_iff_dvd h.ne_zero hn).mpr h.dvd p
      have hquot_eq : (n / d).factorization p = n.factorization p - d.factorization p :=
        Nat.factorization_div_apply h.dvd p
      lia
    · exact Or.inl (Nat.factorization_eq_zero_of_not_prime _ hp)
  · exact Or.inl (Nat.factorization_eq_zero_of_not_dvd hpd)

/-- On its prime support, a unitary divisor of `n` has the full multiplicity of `n`. -/
theorem factorization_eq_of_mem_primeFactors (h : IsUnitaryDivisor d n) {p : ℕ}
    (hp : p ∈ d.primeFactors) : d.factorization p = n.factorization p :=
  (h.factorization_eq_or_full p).resolve_left
    (Nat.factorization_ne_zero_iff_mem_primeFactors.mpr hp)

/-- A nonzero `d` is a unitary divisor of `n` iff at every prime its multiplicity is `0` or the
full multiplicity in `n`. -/
theorem _root_.Nat.isUnitaryDivisor_iff_factorization (hd : d ≠ 0) :
    IsUnitaryDivisor d n ↔
      ∀ p, d.factorization p = 0 ∨ d.factorization p = n.factorization p := by
  refine ⟨fun h => h.factorization_eq_or_full, fun h => ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · obtain rfl : d = 1 := Nat.eq_of_factorization_eq hd one_ne_zero fun p => by simpa using h p
    exact one_left
  have hdvd : d ∣ n := (Nat.factorization_le_iff_dvd hd hn).mp
    (Finsupp.le_def.mpr fun p => by rcases h p with h0 | hfull <;> lia)
  have hq0 : n / d ≠ 0 :=
    Nat.div_ne_zero_iff.mpr ⟨hd, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd⟩
  refine ⟨hdvd,
    (Nat.disjoint_primeFactors hd hq0).mp (Finset.disjoint_left.mpr fun p hpd hpq => ?_)⟩
  rw [← Nat.factorization_ne_zero_iff_mem_primeFactors] at hpd hpq
  have hquot := Nat.factorization_div_apply hdvd p
  rcases h p with h0 | hfull <;> lia

theorem trans (h₁ : IsUnitaryDivisor d m) (h₂ : IsUnitaryDivisor m n) : IsUnitaryDivisor d n := by
  refine (isUnitaryDivisor_iff_factorization h₁.ne_zero).mpr fun p => ?_
  rcases h₁.factorization_eq_or_full p with h | h
  · exact Or.inl h
  · rw [h]
    exact h₂.factorization_eq_or_full p

instance : Trans IsUnitaryDivisor IsUnitaryDivisor IsUnitaryDivisor := ⟨trans⟩

instance : IsTrans ℕ IsUnitaryDivisor := ⟨fun _ _ _ => trans⟩

/-- The gcd of a unitary divisor of `n` with any divisor `m` of `n` is a unitary divisor
of `m`. -/
theorem gcd (h : IsUnitaryDivisor d n) (hmn : m ∣ n) :
    IsUnitaryDivisor (Nat.gcd d m) m := by
  rcases eq_or_ne n 0 with rfl | hn
  · obtain rfl : d = 1 := h.eq_one
    simp [Nat.gcd_one_left]
  have hm : m ≠ 0 := fun h0 => hn (Nat.eq_zero_of_zero_dvd (h0 ▸ hmn))
  refine (isUnitaryDivisor_iff_factorization (Nat.gcd_ne_zero_left h.ne_zero)).mpr fun p => ?_
  rw [Nat.factorization_gcd_apply h.ne_zero hm]
  have hmle : m.factorization p ≤ n.factorization p :=
    (Nat.factorization_le_iff_dvd hm hn).mpr hmn p
  rcases h.factorization_eq_or_full p with h0 | hfull <;> lia

/-- A unitary divisor of `n` splits multiplicatively across any factorization `n = q * m`. -/
theorem gcd_mul_gcd_of_eq_mul {q : ℕ} (h : IsUnitaryDivisor d n) (hq : n = q * m) :
    Nat.gcd d q * Nat.gcd d m = d := by
  rcases eq_or_ne n 0 with rfl | hn
  · obtain rfl : d = 1 := by simpa using h.coprime
    simp
  have hd0 : d ≠ 0 := h.ne_zero
  have hq0 : q ≠ 0 := left_ne_zero_of_mul (hq ▸ hn)
  have hm0 : m ≠ 0 := right_ne_zero_of_mul (hq ▸ hn)
  refine Nat.eq_of_factorization_eq
    (Nat.mul_ne_zero (Nat.gcd_ne_zero_left hd0) (Nat.gcd_ne_zero_left hd0)) hd0 fun p => ?_
  rw [Nat.factorization_mul_apply (Nat.gcd_ne_zero_left hd0) (Nat.gcd_ne_zero_left hd0),
    Nat.factorization_gcd_apply hd0 hq0, Nat.factorization_gcd_apply hd0 hm0]
  have hnf : n.factorization p = q.factorization p + m.factorization p := by
    rw [hq, Nat.factorization_mul_apply hq0 hm0]
  have hor := h.factorization_eq_or_full p
  lia

/-- Cancellation form of `gcd_mul_gcd_of_eq_mul`. -/
theorem eq_gcd_of_eq_mul {q e : ℕ} (h : IsUnitaryDivisor d n) (hq : n = q * m)
    (he : m * e = d) : e = Nat.gcd d q := by
  have hm : m ≠ 0 := left_ne_zero_of_mul (he.trans_ne h.ne_zero)
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) (he.trans ?_)
  rw [Nat.mul_comm, ← Nat.gcd_eq_right ⟨e, he.symm⟩]
  exact (h.gcd_mul_gcd_of_eq_mul hq).symm

theorem dvd_iff_primeFactors_subset {m : ℕ} (h : IsUnitaryDivisor d n) (hn : n ≠ 0)
    (hmn : m ∣ n) : m ∣ d ↔ m.primeFactors ⊆ d.primeFactors := by
  refine ⟨fun hmd => Nat.primeFactors_mono hmd h.ne_zero, fun hsub => ?_⟩
  have hm : m ≠ 0 := fun h0 => hn (zero_dvd_iff.mp (h0 ▸ hmn))
  rw [← Nat.factorization_le_iff_dvd hm h.ne_zero]
  intro p
  rcases eq_or_ne (m.factorization p) 0 with h0 | h0
  · lia
  have hfull := h.factorization_eq_of_mem_primeFactors
    (hsub (Nat.factorization_ne_zero_iff_mem_primeFactors.mp h0))
  have hle := (Nat.factorization_le_iff_dvd hm hn).mpr hmn p
  lia

/-- A unitary divisor of `n` is determined by its set of prime factors. -/
theorem eq_of_primeFactors_eq {a b : ℕ}
    (ha : a.IsUnitaryDivisor n) (hb : b.IsUnitaryDivisor n)
    (hp : a.primeFactors = b.primeFactors) : a = b := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [ha.eq_one, hb.eq_one]
  refine Nat.eq_of_factorization_eq ha.ne_zero hb.ne_zero fun p => ?_
  have mem_iff : a.factorization p ≠ 0 ↔ b.factorization p ≠ 0 := by
    rw [Nat.factorization_ne_zero_iff_mem_primeFactors,
      Nat.factorization_ne_zero_iff_mem_primeFactors, hp]
  rcases ha.factorization_eq_or_full p with ha0 | ha1 <;>
    rcases hb.factorization_eq_or_full p with hb0 | hb1 <;> lia

end IsUnitaryDivisor

end Nat
