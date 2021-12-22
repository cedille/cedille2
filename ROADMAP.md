
# Phase 1 (Basics)
- Implement the following to parity with Cedille
- [ ] REPL
- [ ] Modules
- [ ] Core types (no datatypes, no elaborated rhos, no bohm-out)
    - [ ] Syntax
    - [ ] Reduction and Conversion
    - [ ] Elaboration (intersections to refinements)
    - [ ] Type inference
    - [ ] Kind inference
- [ ] Multiple binding lambdas (λ x -g ⋅T. ...)
- [ ] Basic VSCode support
    - [ ] syntax highlighting
    - [ ] underlined errors and warnings
    - [ ] unicode input
- [ ] Testing framework

# Phase 2 (Finish equality)
- [ ] Elaborate rhos
- [ ] Implement bohm-out

# Phase 3 (New constructs)
- [ ] Add refinement types to the surface syntax
- [ ] Add term existentials to the surface syntax
- [ ] Add "omitted" term for improved type inference
- [ ] Investigate and implement better type inference for refinements / existentials

# Phase 4 (Datatypes)
- Implement datatypes, potentially breaking parity with Cedille
- [ ] Datatype elaboration
    - [ ] Use constructor subtyping signatures
    - [ ] (possibly) GMP Naturals in kernel theory for labels?
- [ ] Type Classes (at least basic) to allow users to prove positivity
- [ ] Simple automatic strict positivity checker (only needs to work for existing Cedille datatypes in use)

# Tooling
- [ ] Implement equality prover (like beta reduction explorer in Cedille)
- [ ] Improve VSCode support
    - [ ] Show type on hover
    - [ ] ...
- [ ] (possibly) Emacs support?

# Datatype Ornaments (Paper Idea)
- [ ] Add ornamentation combinators to datatypes (delete constructors, merge datatypes, add constructors, etc)

# Elaborate Large Eliminations
- [ ] (possibly) Add type-equality primitive?
- [ ] (possibly) Use typeclasses to ensure desired properties? (Syntactic checks seemed difficult or unnatural)

# Cast Inference (Paper Idea)
- [ ] (possibly) Use a Cast typeclass to record available casts?
- [ ] Infer casts so that you don't have to manually cast (especially when it is obvious)
