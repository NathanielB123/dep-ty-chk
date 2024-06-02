# DepTyChk

**The Goal:** A simple, sound dependent type checker.
- **Simple:** No type inference, naive typechecking algorithm (all types evaluated to normal form and compared syntactically).
- **Sound:** The main point of interest of this development. I aim for the typechecker aims to produce programs in an intrinsically-typed syntax (so accepted programs are verified to be typeable).
- **Dependent:** The object type theory contains pi-types and large elimination.

## Current Progress

### Challenges

As it turns out, meta-theory of type theory inside type theory is *quite hard*. Some high-level intuition on why:
- Godel's second incompleteness theorem tells us a sound formal system cannot prove it's own correctness, so formalising a system as powerful as Agda's is literally impossible.
- Intrinsically typed syntax (fusing syntax and typing rules into one inductive datatype) is a really powerful way of modelling type systems in TT (and IMO is the only acceptable approach in Agda, with its limited automation/tactics capabilities). However, a direct consequence of this approach is that operations on syntax must (by definition) preserve types. In TTs with any form of large-elimination, terms can appear inside types, which often leads to circularity (to prove type preservation of a syntax transformation, we must implement that syntax transformation, but to implement the transformation, we must prove type preservation).
- TTs of the intensional variety require a notion of definitional equality. In practice, this means a ton of non-trivial computation must occur at the type-level to check if types are equal. We can attempt to deal with this by trying to always keep types in normal form, but in practice, proving termination with this approach seems extremely challenging; note that substitutions on normal forms are obviously not structurally recursive. Therefore, we usually end up forced to define our own equivalence relation on terms (i.e. beta/eta-rules) and then are obligated to prove all our syntax operations respect this relation, which gets tiresome, fast.


### Organisation

This repo is currently split into two distinct developments, which investigate two distinct approaches to formalising TT with intensionally typed terms. The former is further along but progress has slowed due to some extreme and mostly unavoidable clunkyness, while the latter is more experimental but is IMO very promising:

- [Setoid/](./src/Setoid) 
  - Heavily inspired by [A Formalisation of a Dependently Typed Language as an Inductive-Recursive Family](https://www.cse.chalmers.se/~nad/publications/danielsson-types2006.pdf), [Type Theory in Type Theory using Quotient Inductive Types](https://akaposi.github.io/tt-in-tt.pdf) and Andras Kovacs' [gist](https://gist.github.com/AndrasKovacs/1417f92a411b53798c880fd0a6b44169)
  - The main achievements here are the provably terminating, type-preserving substitutions ([Subst.agda](./src/Setoid/Subst.agda)) and all the lemmas about how substitutions commute ([Equations.agda](./src/Setoid/Equations/Equations.agda)).
  - I have also implemented a very simple normalisation function but asserted termination ([Norm.agda](./src/Setoid/Norm.agda)). I think NbE should definitely be applicable here, but working with the explicit equivalence relations is very painful.
  - There are several large improvements that could made to clean up this development. A big one is placing the equivalence relations in `Prop` so there is no need to worry about making distinct derivations of equality coincide. I also believe the explicit coercions in the syntax could be dealt with in a much more unified way, and there are a few very obvious applications for instance arguments in cleaning up the equivalence relation machinery. See [New.agda](https://github.com/NathanielB123/dep-ty-chk/blob/f435004f5b7c733df6639616c142b2aacc9a8a22/src/New/New.agda) in the `wip-setoid` branch for some WIP code that experiments with some of these ideas. 
  - A huge reduction in the clunkyness of this approach could be obtained by *quotient*-ing the term syntax (ideally as a *QIT* to get congruence of constructors for free), but afaik there currently exists no theorem prover which implements QITs AND indexed families while retaining canonicity (hopefully this will change in the nearish future given [Higher Inductive Types in Cubical Computational Type Theory](https://dl.acm.org/doi/pdf/10.1145/3290314) and [Observational Equality Meets CIC](https://pujet.fr/pdf/obs_inductives.pdf]), but for now I must work with what I have).

- [Coincidences/](./src/Coincidences/)
  - Heavily inspired by [Outrageous but Meaningful Coincidences](https://dl.acm.org/doi/abs/10.1145/1863495.1863497)
  - Similar limitations as described in that paper (equality is constrained in power to that of the meta-theory - i.e. no formalising OTT), but I'm still very excited about this approach; the core syntax is just 100 lines!
  - I am making liberal use of rewrite rules. These are not essential to the technique, but if we can piggy-back of Agda's propositional equality, we might as well take full advantage!

### To Do:
- Terminating Normalisation (NbE)
- Decidable equality of types/terms
- Definition of untyped pre-terms
- A monadic typechecker (pre-term -> maybe typed term) which takes advantage of all this machinery
