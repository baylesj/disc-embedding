# DiscEmbedding

A Lean 4 / Mathlib project to formalize **Freedman's disc embedding theorem** and its
headline consequence, the **topological 4-dimensional Poincaré conjecture**.

It follows *The Disc Embedding Theorem* (Behrens, Kalmár, Kim, Powell, Ray, eds.;
OUP 2021), cited as [DET], starting with the most Lean-friendly part of the book:
Part I, decomposition space theory.

## Status

| Item | [DET] | Lean declaration | Statement | Proof |
|---|---|---|---|---|
| Model disc, sphere, topological ball | — | `Disc`, `Sphere`, `IsTopBall` | ✅ | — |
| Cellular sets | Ch. 3 | `IsCellular` | ✅ | — |
| Radial squeeze of ℝⁿ; transplanting through open embeddings | Ch. 3 | `squeezeHomeomorph`, `transplant` | ✅ | ✅ |
| Cellular sets shrink (general metric spaces) | Ch. 3 | `IsCellular.satisfiesBSC_of_collapse` | ✅ | ✅ |
| Cellular sets shrink (in Sⁿ) | Ch. 3 | `cellular_quotient_approximable` | ✅ | ✅ |
| Generalized Schoenflies (Brown) | Ch. 3 | `generalized_schoenflies` | ✅ | ⬜ |
| Approximable by homeomorphisms | Ch. 4 | `ApproximableByHomeomorphisms` | ✅ | — |
| Bing shrinking criterion (BSC) condition | Ch. 4 | `SatisfiesBSC` | ✅ | — |
| BSC, easy direction | Ch. 4 | `ApproximableByHomeomorphisms.satisfiesBSC` | ✅ | ✅ |
| BSC, hard direction (Baire category) | Ch. 4 | `SatisfiesBSC.approximableByHomeomorphisms` | ✅ | ✅ |
| **Bing shrinking criterion** | Ch. 4 | `bing_shrinking_criterion` | ✅ | ✅ |
| Bing, Whitehead, starlike decompositions | Ch. 5–9 | — | ⬜ | ⬜ |
| Ball to ball theorem | Ch. 10 | — | ⬜ | ⬜ |
| Skyscrapers, gropes, towers | Ch. 11–27 | — | ⬜ | ⬜ |
| **4D topological Poincaré** | Ch. 1, 21 | `poincare_four` | ✅ | ⬜ |

Every `sorry` corresponds to an entry in the blueprint (`blueprint/src/content.tex`).

## Design choices to review

1. **Cube model.** `Disc n` is the closed unit ball of `Fin n → ℝ` with the sup metric,
   which is the cube `[-1,1]ⁿ`, and `Sphere n` is its boundary. This keeps the imports
   small (no inner-product spaces). Everything in Part I is
   invariant under homeomorphism. Note that `Sphere (n+1)` is the *n*-sphere.
2. **Map formulation of shrinking.** The book works with decompositions `𝒟` of `X` and
   the quotient `X/𝒟`. We use Edwards' map formulation (`f : X → Y` between compact
   metric spaces). For upper semicontinuous decompositions of compact metric spaces
   the two are equivalent; a bridging lemma will be needed when we construct explicit
   decompositions (Ch. 5 on).
3. **Collared cellular sets.** `IsCellular` asks for nested balls `eᵢ(Dⁿ)` where each
   `eᵢ : ℝⁿ → M` is an open embedding, and `Bᵢ₊₁ ⊆ eᵢ(open unit ball)`. In a manifold this
   is equivalent to the book's definition (arbitrary balls with `Bᵢ₊₁ ⊆ int Bᵢ`), but the
   equivalence needs invariance of domain, which Mathlib lacks. Brown's proof produces
   collared balls anyway.
4. **Topological manifolds** are `[T2Space M] [SecondCountableTopology M]
   [ChartedSpace (Fin n → ℝ) M]`. `poincare_four` also assumes `CompactSpace M`,
   which is slightly weaker than Mathlib's `proof_wanted` (Hausdorff only).

## Building

Requires Lean `v4.36.0` and Mathlib `v4.36.0` (pinned in `lakefile.toml`).

```sh
lake exe cache get   # download prebuilt Mathlib (without it, ~1 hour on 2 cores)
lake build
```

`lake build` succeeds; the only warnings are the expected `declaration uses 'sorry'`
for the unproved statements. To check that no hidden axioms crept in, run
`#print axioms DiscEmbedding.bing_shrinking_criterion`, which should
list only `propext`, `Classical.choice` and `Quot.sound`.

Blueprint: `pip install leanblueprint`, then `leanblueprint web` or `leanblueprint pdf`
from the repo root. (`blueprint/src/print.tex` also compiles with plain `pdflatex`.)

## Next steps

1. Post on the Lean Zulip (draft in `ZULIP_DRAFT.md`), ask a 4-manifold topologist to
   check the statements, especially `generalized_schoenflies`, `poincare_four` and the
   map formulation of the BSC.
2. Upstream the Bing shrinking criterion (now fully proved) to Mathlib.
3. Prove `generalized_schoenflies` (Brown's argument, using the cellular-set result).
4. Transcribe the ball to ball theorem (Ch. 10) exactly from [DET] and state it.
5. Only then start the Part II infrastructure (immersed discs, intersection numbers).
