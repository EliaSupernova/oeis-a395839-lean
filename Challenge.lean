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
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The two conjectures in OEIS A395839

**Sequence.** OEIS A395839 is named "G.f. 10*C(x)^2 - C(x), where C(x) = 1 + x*C(x)^2 is the
g.f. of the Catalan numbers (A000108)." Its data begin
$9, 19, 48, 135, 406, 1278, 4158, 13871, 47190, \dots$, with offset $0$.

**Definition used here.** `C` is the formal power series $\sum_{n \ge 0} C_n x^n$ over
$\mathbb{Z}$, where $C_n$ is Mathlib's `catalan n` (OEIS A000108). `a n` is the coefficient of
$x^n$ in `10 * C ^ 2 - C`, which is the name of the OEIS entry read literally. The equation
$C(x) = 1 + x\,C(x)^2$ and the closed form $a(n) = 10\,C_{n+1} - C_n$ are proved in
`Solution.lean` (`C_eq` and `a_eq`), together with the first nine terms (`a_initial`).

**Claims.** The OEIS entry, by Paul D. Hanna (May 17 2026), records two conjectures:

1. `conjecture_1`: $a(n)$ is odd if and only if $n = 2^k - 1$ for some $k \ge 0$.
2. `conjecture_2`: $a(3n+1) \equiv C_n \pmod 3$, and $a(3n) \equiv a(3n+2) \equiv 0 \pmod 3$,
   for all $n \ge 0$.

**Reading the statements.** `n : ℕ` ranges over all $n \ge 0$, matching the offset. In
`2 ^ k - 1` the subtraction is on natural numbers, which is exact because $2^k \ge 1$.
`x ≡ y [ZMOD 3]` is congruence of integers modulo $3$.

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

/--
"Conjecture: a(n) is odd iff n is of the form 2^k - 1 (k >= 0)."
- _Paul D. Hanna_, OEIS A395839
-/
theorem conjecture_1 (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  sorry

/--
"Conjecture: a(3*n+1) == A000108(n) (mod 3) for n >= 0 (see A111019 and A111020), with
a(3*n) == a(3*n+2) == 0 (mod 3) for n >= 0."
- _Paul D. Hanna_, OEIS A395839
-/
theorem conjecture_2 (n : ℕ) :
    a (3 * n + 1) ≡ (catalan n : ℤ) [ZMOD 3] ∧ a (3 * n) ≡ 0 [ZMOD 3] ∧
      a (3 * n + 2) ≡ 0 [ZMOD 3] := by
  sorry

end OeisA395839
