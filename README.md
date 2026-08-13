# A Lean-checked proof that F_k(N) = o(N) for fixed k

**Try it in Lean4Web:** [open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fgreen-37-sublinear-upper-bound%2Frefs%2Fheads%2Fmain%2Flean4web%2FGreen37UpperBoundsLean4Web.lean)

This repository formalizes a qualitative upper bound for the quantity in
[Ben Green's Open Problem 37](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.37).

For every fixed arithmetic-progression length `k`, the Lean proof establishes

```text
F_k(N) = o(N)  as N → ∞.
```

Here `F_k(N)` is the smallest cardinality of a set of natural numbers containing,
for every `d = 1, …, N`, a `k`-term arithmetic progression with common
difference exactly `d`. It is called `Green37.m N k` in Formal Conjectures.

> **Status.** This is not a solution of Green's Open Problem 37 or of the
> arithmetic Kakeya conjecture. The difficult part of that problem concerns
> lower bounds for `F_k(N)` whose exponent tends to `1` as `k → ∞`.
> The theorem proved here is a weaker, qualitative upper bound and is not
> claimed as a new mathematical result.

The proof also gives the explicit comparison function `N ↦ N` for the
`green_37_littleO` and `green_37_bigO` answer slots currently present in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/GreensOpenProblems/37.lean).
Passing those two formal targets should not be read as solving the original
open problem.

## The proved theorem

The mathematical content is

```lean
theorem m_isLittleO_id (k : ℕ) :
    (fun N ↦ (Green37.m N k : ℝ)) =o[atTop] (fun N ↦ (N : ℝ))
```

The big-O statement is then an immediate consequence:

```lean
theorem m_isBigO_id (k : ℕ) :
    (fun N ↦ (Green37.m N k : ℝ)) =O[atTop] (fun N ↦ (N : ℝ))
```

In the Formal Conjectures-facing file these are exposed as
`Green37.green_37_littleO_solved` and
`Green37.green_37_bigO_solved`. The suffix means only that the corresponding
Lean propositions have been proved with the selected answer `N ↦ N`.

## Faithfulness to the informal problem

The proof uses the intended combinatorial object directly:

- one finite set `A` is constructed for each `N`;
- for every `d` with `1 ≤ d ≤ N`, `A` contains the actual progression
  `a, a+d, …, a+(k-1)d`;
- the common difference is exactly `d`;
- the progression has exactly `k` distinct terms;
- the cardinality of `A` is bounded explicitly.

The natural-language problem does not require `A ⊆ {1, …, N}`; it restricts
the common differences, not the locations of the progression terms. Thus the
large starting points produced by the Chinese remainder theorem are legitimate
for both the original problem and the Lean statement.

The Lean development does not choose the unknown function itself as the answer,
does not use an empty hypothesis, and does not depend on any upstream
`answer(sorry)` theorem.

## Mathematical Explanation (AI generated)

Fix `k`. Choose an index `t` and let

```text
q_j = FermatNumber(t+j),    0 ≤ j < k.
```

These moduli are pairwise coprime. For every desired common difference
`1 ≤ d ≤ N`, the Chinese remainder theorem supplies `a < Q = ∏ q_j`
such that

```text
a + j d ≡ 0 (mod q_j)    for all j < k.
```

Define the finite set

```text
A = ⋃_{j<k} {x < Q + kN : q_j divides x}.
```

Then `a, a+d, …, a+(k-1)d` all belong to `A`. Counting multiples gives

```text
|A| ≤ k ((Q + kN) / FermatNumber(t) + 1)
    ≤ C(t,k) + (k² / FermatNumber(t)) N.
```

Given `ε > 0`, first choose `t` so that
`k² / FermatNumber(t) < ε/2`. Then choose `N` large enough to absorb
the fixed constant `C(t,k)`. Eventually,

```text
F_k(N) ≤ εN,
```

which proves `F_k(N)=o(N)`.

## What remains open

Green's problem asks for the size and asymptotic growth of `F_k(N)`. Its
arithmetic-Kakeya content is the conjectured lower-bound behavior

```text
F_k(N) ≳_k N^(1-c_k),    with c_k → 0 as k → ∞.
```

This repository proves no lower bound and does not determine an exact value,
eventual formula, or Theta class. In particular, it does not settle:

- `Green37.green_37`;
- `Green37.green_37_asymptotic`;
- `Green37.green_37_theta`;
- the arithmetic Kakeya conjecture.

The `bigO` and `littleO` declarations in Formal Conjectures are auxiliary
open-answer targets. Because such targets do not encode optimality or
mathematical significance, Lean verification alone cannot certify that filling
one constitutes a solution of the source problem.

## Proof integrity

The two proof files add no `sorry`, `admit`, custom axiom,
`native_decide`, or `unsafe` theorem. Their final axiom audits report only

```text
[propext, Classical.choice, Quot.sound]
```

and no `sorryAx`.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.27.0` | Imports the pinned Formal Conjectures definitions |
| `lean4web/` | `v4.34.0-rc1` | Standalone proof using mathlib |

Each directory contains one proof file, `lakefile.toml`, `lean-toolchain`,
and a generated `lake-manifest.json`.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone mathlib version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

Both builds complete successfully.

## Sources

- [Ben Green, *100 Open Problems*, Problem 37](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.37)
- [Green and Ruzsa, *On the arithmetic Kakeya conjecture of Katz and Tao*](https://arxiv.org/abs/1712.02108)
- [Formal Conjectures: `GreensOpenProblems/37.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/GreensOpenProblems/37.lean)
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-357-sqrt-lower-bound)

## AI usage disclosure

This formalization was developed with assistance from OpenAI Codex, using GPT-5.6 sol.
