**Stream:** #mathlib4 (or #maths)  
**Topic:** Formalizing the disc embedding theorem / 4D topological Poincaré

Hi all. I'm starting a blueprint-driven project to formalize Freedman's disc embedding
theorem, following *The Disc Embedding Theorem* (Behrens–Kalmár–Kim–Powell–Ray, OUP
2021), with the topological 4D Poincaré conjecture as the headline target.

Before going further, I want to check that I'm not duplicating anyone. I know about
Kuga's Coq work on the Bing shrinking criterion (~2014) and the `proof_wanted` in
`Mathlib/Geometry/Manifold/PoincareConjecture.lean`. Is anyone working on decomposition
space theory, Bing shrinking, or Casson handles in Lean?

The plan is to begin with Part I of the book (decomposition space theory), since it's
pure metric topology and useful outside 4-manifolds. So far there is:

- `ApproximableByHomeomorphisms` and `SatisfiesBSC` (Edwards' map formulation, compact
  metric spaces), and a complete, sorry-free proof of the Bing shrinking criterion
  (Baire category in `C(X, Y)`). I'd like to upstream it to Mathlib.
- a proof that cellular sets shrink (collapsing a cellular set in a compact metric space
  doesn't change it up to homeomorphism)
- statements of Brown's generalized Schoenflies and
  `poincare_four` (closed topological 4-manifold ≃ₕ S⁴ ⇒ ≃ₜ S⁴)

Design questions I'd like opinions on:

1. Is the cube `closedBall (0 : Fin n → ℝ) 1` an acceptable model disc for now, or
   should this be `EuclideanSpace ℝ (Fin n)` from the start?
2. Map formulation vs. decomposition formulation of shrinking. Does Mathlib want an
   upper-semicontinuous-decomposition API, or is the map version enough?
3. `IsCellular` uses collared balls (images of `Dⁿ` under open embeddings `ℝⁿ → M`)
   to avoid needing invariance of domain. Is that acceptable, or is anyone working on
   invariance of domain?
4. Topological manifolds as `ChartedSpace (Fin n → ℝ) M` plus `T2Space` and
   `SecondCountableTopology`. Is that the current recommended idiom for C⁰ manifolds?

I'd especially welcome a 4-manifold topologist willing to check statements as they're
written. Repo and blueprint: https://github.com/baylesj/disc-embedding
