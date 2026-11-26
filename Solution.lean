/-
Copyright 2026 EliaSupernova.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

The proof was produced with AI assistance; see `formalization.yaml`.
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Tactic.LinearCombination

/-!
# The two conjectures in OEIS A395839

OEIS A395839 has generating function $10\,C(x)^2 - C(x)$, where
$C(x) = \sum_{n \ge 0} C_n x^n$ is the generating function of the Catalan numbers
(A000108), so that $C(x) = 1 + x\,C(x)^2$.

The main results are

* `OeisA395839.conjecture_1`: $a(n)$ is odd if and only if $n = 2^k - 1$ for some $k \ge 0$;
* `OeisA395839.conjecture_2`: $a(3n+1) \equiv C_n$, $a(3n) \equiv 0$ and $a(3n+2) \equiv 0$
  modulo $3$, for all $n \ge 0$.

## Proof outline

1. `coeff_catSeries_sq`: $[x^n]\,C(x)^2 = C_{n+1}$ (this is `catalan_succ'`), so
   $C(x) = 1 + x\,C(x)^2$ (`catSeries_eq`) and $a(n) = 10\,C_{n+1} - C_n$ (`a_eq`).
2. In characteristic $p$, $F(x)^p = F(x^p)$ for every power series $F$ over $\mathbb{Z}/p$
   (Mathlib's `FiniteField.PowerSeries.expand_card`).
3. Modulo $2$: $a(n) \equiv C_n$, and $C(x) = 1 + x\,C(x^2)$ gives $C_{2m+1} \equiv C_m$ and
   $C_{2m+2} \equiv 0$. Strong induction gives `catalan_odd_iff`, hence `conjecture_1`.
4. Modulo $3$: $10 \equiv 1$, so $A(x) \equiv C^2 - C = C\,(C - 1) = x\,C^3 = x\,C(x^3)$.
   Reading off the coefficients of $x^{3n}$, $x^{3n+1}$ and $x^{3n+2}$ gives `conjecture_2`.

*References:*
- [A395839](https://oeis.org/A395839)
- [A000108](https://oeis.org/A000108)
-/

@[expose] public section

namespace OeisA395839

/-- The generating function $C(x) = \sum_{n \ge 0} C_n x^n$ of the Catalan numbers
(OEIS A000108), as a formal power series with integer coefficients. It satisfies
$C(x) = 1 + x\,C(x)^2$ (see `catSeries_eq` in `Solution.lean`). -/
noncomputable def C : PowerSeries ℤ :=
  PowerSeries.mk fun n => (catalan n : ℤ)

/-- OEIS A395839: $a(n)$ is the coefficient of $x^n$ in $10\,C(x)^2 - C(x)$, where $C(x)$ is the
generating function of the Catalan numbers. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (10 * C ^ 2 - C)

open PowerSeries hiding C

/-! ## The Catalan series over an arbitrary commutative ring -/

/-- The Catalan generating function with coefficients cast into a commutative ring `R`. -/
noncomputable def catSeries (R : Type*) [CommRing R] : R⟦X⟧ :=
  mk fun n => (catalan n : R)

theorem coeff_catSeries (R : Type*) [CommRing R] (n : ℕ) :
    coeff n (catSeries R) = (catalan n : R) :=
  coeff_mk _ _

/-- $[x^n]\,C(x)^2 = C_{n+1}$. -/
theorem coeff_catSeries_sq (R : Type*) [CommRing R] (n : ℕ) :
    coeff n (catSeries R ^ 2) = (catalan (n + 1) : R) := by
  rw [sq, coeff_mul, catalan_succ']
  push_cast
  simp [coeff_catSeries]

/-- $C(x) = 1 + x\,C(x)^2$. -/
theorem catSeries_eq (R : Type*) [CommRing R] :
    catSeries R = 1 + X * catSeries R ^ 2 := by
  ext n
  cases n with
  | zero => simp [coeff_catSeries]
  | succ n => simp [coeff_catSeries, coeff_one, coeff_catSeries_sq]

theorem C_eq_catSeries : C = catSeries ℤ := rfl

/-- The series `C` of the statement satisfies $C(x) = 1 + x\,C(x)^2$. -/
theorem C_eq : C = 1 + X * C ^ 2 := catSeries_eq ℤ

/-- The closed form $a(n) = 10\,C_{n+1} - C_n$. -/
theorem a_eq (n : ℕ) : a n = 10 * (catalan (n + 1) : ℤ) - catalan n := by
  have h10 : (10 : ℤ⟦X⟧) = PowerSeries.C (10 : ℤ) := (map_ofNat _ 10).symm
  rw [a, map_sub, h10, coeff_C_mul, C_eq_catSeries, coeff_catSeries_sq, coeff_catSeries]

/-- The first terms agree with the data of OEIS A395839. -/
theorem a_initial :
    [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8] =
      [9, 19, 48, 135, 406, 1278, 4158, 13871, 47190] := by
  simp only [a_eq, catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]
  decide

/-! ## Frobenius in characteristic `p` -/

theorem coeff_pow_two (f : (ZMod 2)⟦X⟧) (n : ℕ) :
    coeff n (f ^ 2) = if 2 ∣ n then coeff (n / 2) f else 0 := by
  have h := congrArg (coeff n) (FiniteField.PowerSeries.expand_card f)
  rw [coeff_expand] at h
  simpa [ZMod.card] using h.symm

theorem coeff_pow_three (f : (ZMod 3)⟦X⟧) (n : ℕ) :
    coeff n (f ^ 3) = if 3 ∣ n then coeff (n / 3) f else 0 := by
  have h := congrArg (coeff n) (FiniteField.PowerSeries.expand_card f)
  rw [coeff_expand] at h
  simpa [ZMod.card] using h.symm

/-! ## Conjecture 1: parity -/

/-- Modulo 2, $C(x) = 1 + x\,C(x^2)$. -/
theorem catalan_succ_zmod_two (m : ℕ) :
    (catalan (m + 1) : ZMod 2) = if 2 ∣ m then (catalan (m / 2) : ZMod 2) else 0 := by
  rw [← coeff_catSeries_sq, coeff_pow_two, coeff_catSeries]

theorem odd_catalan_iff_zmod_two (n : ℕ) : Odd (catalan n) ↔ (catalan n : ZMod 2) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff_even, Nat.not_even_iff_odd]

/-- The Catalan number $C_n$ is odd if and only if $n = 2^k - 1$ for some $k \ge 0$. -/
theorem catalan_odd_iff (n : ℕ) : Odd (catalan n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · exact ⟨fun _ => ⟨0, rfl⟩, fun _ => by simp⟩
    rw [odd_catalan_iff_zmod_two, catalan_succ_zmod_two]
    rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
    · rw [ite_eq_left (Dvd.intro j rfl), Nat.mul_div_cancel_left j two_pos,
        ← odd_catalan_iff_zmod_two, ih j (by omega)]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        have := Nat.one_le_two_pow (n := k)
        rw [pow_succ]
        omega
      · rintro ⟨k, hk⟩
        rcases k with _ | k
        · simp at hk
        · refine ⟨k, ?_⟩
          rw [pow_succ] at hk
          omega
    · rw [ite_eq_right (by omega)]
      simp only [ne_eq, not_true_eq_false, false_iff, not_exists]
      intro k hk
      rcases k with _ | k
      · simp at hk
      · rw [pow_succ] at hk
        have := Nat.one_le_two_pow (n := k)
        omega

theorem conjecture_1 (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  rw [← catalan_odd_iff, a_eq, Int.odd_iff, Nat.odd_iff]
  omega

/-! ## Conjecture 2: residues modulo 3 -/

/-- Modulo 3, $C^2 - C = x\,C^3$, which with $C(x)^3 = C(x^3)$ reads off the residues. -/
theorem catalan_sub_zmod_three (m : ℕ) :
    (catalan (m + 1) : ZMod 3) - catalan m =
      coeff m (X * catSeries (ZMod 3) ^ 3) := by
  have h : catSeries (ZMod 3) ^ 2 - catSeries (ZMod 3) = X * catSeries (ZMod 3) ^ 3 := by
    linear_combination catSeries (ZMod 3) * catSeries_eq (ZMod 3)
  rw [← h, map_sub, coeff_catSeries_sq, coeff_catSeries]

theorem a_zmod_three (m : ℕ) :
    ((a m : ℤ) : ZMod 3) = coeff m (X * catSeries (ZMod 3) ^ 3) := by
  rw [← catalan_sub_zmod_three, a_eq]
  push_cast
  have : (10 : ZMod 3) = 1 := by decide
  rw [this, one_mul]

theorem conjecture_2 (n : ℕ) :
    a (3 * n + 1) ≡ (catalan n : ℤ) [ZMOD 3] ∧ a (3 * n) ≡ 0 [ZMOD 3] ∧
      a (3 * n + 2) ≡ 0 [ZMOD 3] := by
  refine ⟨?_, ?_, ?_⟩ <;> apply (ZMod.intCast_eq_intCast_iff _ _ 3).1 <;> rw [a_zmod_three]
  · rw [coeff_succ_X_mul, coeff_pow_three, ite_eq_left (Dvd.intro n rfl),
      Nat.mul_div_cancel_left n (by norm_num), coeff_catSeries]
    simp
  · rcases n with _ | n
    · simp
    · rw [show 3 * (n + 1) = (3 * n + 2) + 1 by ring, coeff_succ_X_mul, coeff_pow_three,
        ite_eq_right (by omega)]
      simp
  · rw [coeff_succ_X_mul, coeff_pow_three, ite_eq_right (by omega)]
    simp

end OeisA395839
