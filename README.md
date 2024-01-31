# DepTyChk

A WIP (see "Current Progress"), simple, sound dependent type checker.
- **Simple:** No type inference, naive typechecking algorithm (all types evaluated to normal form and compared syntactically).
- **Sound:** The main point of interest of this development. I aim for the typechecker aims to produce programs in an intrinsically-typed syntax (so accepted programs are verified to be typeable).
- **Dependent:** The type theory contains pi-types and an eliminator from terms to types.

## Current Progress
### Done: 
- Definition of typed syntax
- Various proofs of useful properties: Injectivity of type constructors, congruence of type substitutions, equivalence index projections (i.e. equivalence of terms implies the types of those terms are equivalent), equations covering how substitutions commute
- Definition of normal forms (as predicates on the typed syntax)
### WIP:
- Normalisation (by hereditary substitution)
- We need a few extra properties of substitutions and a way to `coe`rce variables to fill the remaining holes
- I think showing termination will be a bit tricky. A good first step would be to split substitutions into single-term substitutions (`< M >`) and weakenings (`wk`).
### Future:
- Decidable equivalence on typed terms
- Definition of untyped pre-terms
- A monadic typechecker (pre-term -> maybe typed term) which takes advantage of all this machinery

## Design Decisions
The current developments in this repo use a term syntax with explicit substitutions and an inductive equivalence relation on terms (so terms and this relation together form a setoid). 

This is inconvenient, but some sort of explicit substitutions/setoid relation unfortunately appears to be necessary to avoid getting stuck in dependency hell (recursive term substitutions must take advantage of properties about how substitutions commute on types, but types contain terms, so proving those equations requires implementing term substitutions!) 

Another approach would be to quotient the term syntax, but afaik there currently exists no theorem prover which implements quotient inductive types AND indexed families while retaining canonicity (hopefully this will change in the nearish future given [Higher Inductive Types in Cubical Computational Type Theory](https://dl.acm.org/doi/pdf/10.1145/3290314) and [Observational Equality Meets CIC](https://pujet.fr/pdf/obs_inductives.pdf]), but for now I must work with what I have).

Even following the setoid-based approach though, there is quite a bit of flexibility on the design-side. Compared to András Kovács' "John Major" presentation of TT in TT from this (gist)[https://gist.github.com/AndrasKovacs/1417f92a411b53798c880fd0a6b44169] (which I was largely inspired by) the presentation in this repo defines coercions and substitutions on types recursively, and I include quite a bit of machinery for generically working with symmetric and reflexive-transitive closures over the relations.

If I were to restart now (or commit to a large refactor on this existing repo), I would like to try out combining recursive term substitutions and explicit type substitutions. My hope is that this approach would allow defining terms directly as normal forms, which would simplify the state of things massively (of course, such an approach would be inconvenient if the aim was to make an actually efficient typechecker - i.e. based on reducing to WHNFs - but in any case getting rid of explicit term substitutions while keeping the syntax intrinsically-typed is a very attractive prospect to me).