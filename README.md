# The parity and mod-3 conjectures of OEIS A395839

A Lean 4 and Mathlib proof of both conjectures that Paul D. Hanna recorded in
[OEIS A395839](https://oeis.org/A395839), laid out for the
[Palomar registry](https://palomar-registry.org/).

## The sequence

Let $C(x) = \sum_{n \ge 0} C_n x^n$ be the generating function of the Catalan numbers
([A000108](https://oeis.org/A000108)), so that $C(x) = 1 + x\,C(x)^2$. OEIS A395839 is the
sequence with generating function

$$A(x) = \sum_{n \ge 0} a(n)\,x^n = 10\,C(x)^2 - C(x) = 9 + 19x + 48x^2 + 135x^3 + 406x^4 + \cdots$$

## The results

**Conjecture 1.** $a(n)$ is odd if and only if $n = 2^k - 1$ for some $k \ge 0$.

**Conjecture 2.** For all $n \ge 0$, $a(3n+1) \equiv C_n \pmod 3$ and
$a(3n) \equiv a(3n+2) \equiv 0 \pmod 3$.

The formal statements, in [`Challenge.lean`](Challenge.lean):

```lean
noncomputable def C : PowerSeries ℤ :=
  PowerSeries.mk fun n => (catalan n : ℤ)

noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (10 * C ^ 2 - C)

theorem OeisA395839.conjecture_1 (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1

theorem OeisA395839.conjecture_2 (n : ℕ) :
    a (3 * n + 1) ≡ (catalan n : ℤ) [ZMOD 3] ∧ a (3 * n) ≡ 0 [ZMOD 3] ∧
      a (3 * n + 2) ≡ 0 [ZMOD 3]
```

`a n` is literally the coefficient of $x^n$ in $10\,C(x)^2 - C(x)$, the name of the OEIS entry.
`Solution.lean` also proves, as checks on the definition, that $C(x) = 1 + x\,C(x)^2$
(`C_eq`), that $a(n) = 10\,C_{n+1} - C_n$ (`a_eq`), and that the first nine terms are
$9, 19, 48, 135, 406, 1278, 4158, 13871, 47190$ as in the OEIS data (`a_initial`).

## Scope and limitations

- Both conjectures are proved for every $n \ge 0$. The other formulas in the entry and its
  10-adic comments are not formalized.
- **No novelty is claimed.** Both statements follow quickly from classical facts about Catalan
  numbers modulo 2 and 3 (for background see E. Deutsch and B. E. Sagan,
  [*J. Number Theory* 117 (2006)](https://doi.org/10.1016/j.jnt.2005.06.005), which was not
  read for this repository). No systematic literature search was made.
- No independent human mathematical review is claimed. The checks are mechanical.

## Proof summary

1. `coeff_catSeries_sq`: $[x^n]\,C(x)^2 = C_{n+1}$, which is Mathlib's `catalan_succ'`. Hence
   $C(x) = 1 + x\,C(x)^2$ and $a(n) = 10\,C_{n+1} - C_n$.
2. In characteristic $p$, $F(x)^p = F(x^p)$ for every power series $F$ over $\mathbb{Z}/p$
   (Mathlib's `FiniteField.PowerSeries.expand_card`; here `coeff_pow_two`, `coeff_pow_three`).
3. **Mod 2.** $a(n) \equiv C_n$, and $C(x) = 1 + x\,C(x)^2 = 1 + x\,C(x^2)$ gives
   $C_{2m+1} \equiv C_m$ and $C_{2m+2} \equiv 0$. Strong induction on $n$ gives
   `catalan_odd_iff`: $C_n$ is odd if and only if $n = 2^k - 1$. This is `conjecture_1`.
4. **Mod 3.** $10 \equiv 1$, so $A(x) \equiv C^2 - C = C\,(C - 1) = x\,C^3 = x\,C(x^3)$. The
   coefficient of $x^{3n+1}$ is $C_n$, and those of $x^{3n}$ and $x^{3n+2}$ are $0$.
   This is `conjecture_2`.

The whole proof is in [`Solution.lean`](Solution.lean) and depends only on Mathlib.

## Provenance and credit

- **Sequence and conjectures:** Paul D. Hanna, OEIS A395839 (May 17 2026; entry revision #37,
  May 18 2026).
- **Formal statement and proof:** written for this repository. No file for A395839 exists in
  google-deepmind/formal-conjectures at commit `9097e2f`.
- **AI assistance:** `EliaSupernova` supplied a task brief with the OEIS statement and a proof
  sketch (reduce to Catalan numbers modulo 2 and 3; use $F(x)^p = F(x^p)$ in characteristic
  $p$). An AI agent (Claude Opus 5.5 in Claude Code) wrote the Lean statements and proof,
  assembled this repository from the
  [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate) layout, drafted the
  metadata and this README. A second AI agent (Claude Sonnet 5.5 in Claude Code) ran the final
  local checks and made the commit.
- **Maintainer:** `EliaSupernova`.

The structured record is in [`formalization.yaml`](formalization.yaml).

## Repository map

| Path | Contents |
| --- | --- |
| `Challenge.lean` | The statements to audit, each with one deliberate `sorry` |
| `Solution.lean` | The proofs, with no `sorry` |
| `comparator.json` | The compared declarations and the permitted axioms |
| `formalization.yaml` | Sources, provenance, automation, scope and review status |
| `docbuild/` | Nested doc-gen4 project |
| `scripts/` | Checks taken unchanged from PalomarTemplate |

## Verification

Requirements: Linux, [`elan`](https://github.com/leanprover/elan), Git, Ruby, Python 3,
[bubblewrap](https://github.com/containers/bubblewrap) and a network connection, with several GiB
of free disk space. The toolchain is Lean `v4.35.0-rc2`, and `lake-manifest.json` pins Mathlib to
commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

From the repository root:

```sh
python3 scripts/check-lean-sources.py
lake exe cache get
lake --wfail build
(cd docbuild && DISABLE_EQUATIONS=1 lake build Challenge:docs Solution:docs)
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

The documentation step needs several GiB of memory and a configured Git remote, which doc-gen4
uses for source links.

`--wfail` turns every warning into a failure. The two expected `sorry` warnings, in
`Challenge.lean`, are switched off for that library only in `lakefile.toml`, so a `sorry` in the
proof still fails the build.

To print the axioms of the theorems:

```sh
printf 'import Solution\n#print axioms OeisA395839.conjecture_1\n#print axioms OeisA395839.conjecture_2\n' | lake env lean --stdin
```

Expected output:

```text
'OeisA395839.conjecture_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA395839.conjecture_2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A successful check shows that the proof proves the statements in `Challenge.lean` from these
axioms. Whether those statements match the intended mathematics is for the reader to check.

Registry submissions go through <https://submit.palomar-registry.org/>.

## License

[Apache License 2.0](LICENSE).
