
# Phase 1 (Basics)
- Implement the following to parity with Cedille
- [ ] REPL
- [ ] Modules
- [ ] Core types (no datatypes, no elaborated rhos, no bohm-out)
    - [x] Syntax
    - [ ] Reduction and Conversion
    - [ ] Basic Elaboration 
    - [x] Basic Type inference
    - [x] Basic Kind inference
- [ ] Multiple binding lambdas (λ x -g ⋅T. ...)
- [x] Basic VSCode support
    - [x] syntax highlighting
    - [x] unicode input
- [ ] Testing framework

# Phase 2 (Finish equality)
- [ ] Finish elaborating equality constructs
- [ ] Implement bohm-out (? not sure why this is needed)
- [ ] Replace intersection types in core language with refinements types
- [ ] Greatly improve error messages in the REPL

# Phase 3 (New constructs)
- [ ] Add refinement types to the surface syntax
- [ ] Add term existentials to the surface syntax
- [ ] Add "omitted" term for improved type inference (i.e. Improve type inference)
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
    - [ ] Underline text with error spans and messages
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
