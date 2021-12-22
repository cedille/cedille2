
# Acronyms
- NbE = Normalization by Evaluation
- HOAS = Higher-Order Abstract Syntax
- SLD = Selective, Linear, Definite

# Andras Kovacs smalltt

## Video (Type theory elaboration 1: bidirectional type checking)
- What importance does laziness / strictness have in NbE?
    - Laziness is important on applications, to switch between call-by-value and call-by-name
    - Also, it allows for constant space conversion checking (think large numerals defined by the same functions)
    - Thunking in Rust: `Thunk<T> = Box<FnOnce() -> T>` (can potentially avoid the heap allocation though)
    - Also, the crate `once_cell` probably has a better thought out Lazy
- The Raw syntax supports only one computational operation: Elaboration
    - When implementing tooling for equality proofs of the surface syntax, this idea will likely be broken
    - However, it can all be isolated in an external tool, which may construct its own syntax anyway
- Conversion checking is on _values_ (of the core syntax)
- Eta conversion:
    ```rust
        // original (this is inside conversion checking, and again only over values)
        // Note that `l` is a de bruijn level
        (VLam t, u) -> conv (l + 1) (t $$ VVar l) (VApp u (VVar l))
    ```
    - This idea only works if you're not comparing two neutrals (to fix that case you need types)
- Source positions are their own constructor, what does Rust do?
    - Rust annotates every variant with a Span
- The operator `~` is a lazy modality in the Haskell code
- "People do too much computation with names, you only need it for printing and lookup" (paraphrasing)
- Laziness is an optimization, but an almost mandatory one (performance is too difficult without it)
- "Without garbage collection this function (eval) just doesn't work"
- "It's possible to do conversion checking in a unification algorithm, but you want to have the simplest conversion
    checking algorithm in evaluation." (paraphrasing)
- What solutions does Rust have for garbage collection?
    - Smart pointers: Rc, and Arc
    - https://lib.rs/crates/gc
    - https://lib.rs/crates/gcmodule

## Video (Type theory elaboration 2: basic pattern unification)
- Describes untyped pattern unification (simplest inference for dep. language)
    - Untyped pattern unification is decidable with unique solutions (when they exist)
    - Idea is to try and produce an inverted substitution (which must be a renaming to satisfy the conditions)
    - then, apply that substitution to construct the solution
- Hole (meaning "_", better called "omits" in Cedille) can appear anywhere in source syntax expression
- Omits are filled in with metavariables during elaboration, and solved in unification
- Represent the meta as a toplevel definition, which captures its local scope (becomes a function)
- "Flex" values
    - records computation blocked on an unsolved meta
    - computation can be restarted if the meta is solved
- "Rigid" values
    - records computation blocked on a bound variable
    - computations can never be resumed

## Video (Type theory elaboration 3: implicit arguments)
- Not a high priority for Cedille
- Icit: implicit or explicit
- Icity has to make its way into core values, because elaboration makes a decision on icity
- Andras recommends not doing the solution in his paper "It is overkill" (paraphrasing), instead use GHC's solution of delaying

## Video (Type theory elaboration 4: glued evaluation and approximate conversion checking)
- Motivation
    - conversion better be complete! (all beta reductions and unfoldings)
    - but with quoting, we don't want to do all unfoldings! (to avoid a size explosion)
- All expensive operations work with Values, but we need quoting to produce core syntax,
- But quoting can cause size explosion by getting meta solutions from quoting
- What metavariable elaboration should be used in Cedille?
    - Front-matter toplevel metavariables (solutions can appear at the toplevel but only before all definitions)
    - Mixed toplevel metavariables (solutions can appear at the toplevel anywhere in the file)
    - Arbitrary metavariables (solutions can appear anywhere in a term)
- To glue: add a field to the variant that contains a Lazy value
    ```rust
        ...
        | VTop Name Spine ~Val
        ...
    ```
    - When you decide an unfolding is necessary then you can choose to compute the lazy value
- Creates a non-determistic evaluation, because you must explore both paths (although one is lazy)
- This non-determinism lets us do conversion with and without unfolding
- This can improve performance by doing some approximation conversion checking
- Andras' advocates not doing approximate checking at every top-level headed spine
    - Try it once, if it fails, then don't be an eternal optimist
    - "I believe this [backtracking at every spine] contributes to some serious slowdowns in Coq and Agda conversion checking" (paraphrasing)

## Video (Type theory elaboration 5 - sigma types)
- Of course we don't have sigma types, but what is applicable to refinement types?
- Putting projections directly as values of a variant is discouraged
    - When using a value in unification we want to know immediately why a computation is blocked (if it is)
    - But projections also block computation
    - To fix: add them instead to the Spine of Rigid and Flex values
    - Note: In Cedille, the problem is dodged, because projections are erased!
- The "Spine" of a value should represent all blocked computation, whatever that might be in a given type theory
- To handle unification, you eliminate sigmas (via eta-expansion):
    ```rust
        ?0 : A -> B = ...
        ?1 : A -> C = ...
        f : A -> B x C = λ a. (?0 a, ?1 a)
    ```
    - However, eta-expansion is not the full solution
- Unification will now lead to partial solutions!
    - Need to rewrite via dependent currying and skolemization equivalences
- Seems like a lot of work to get this to happen: should likely be avoided
- "first order closures tend to be more efficient" (paraphrasing)
- However, HOAS is apparently very convenient when doing the rewriting for dependent currying (but not skolemization)
- Without primitive records, generativity is lost (because record types are not injective)
    - Does this problem show up with Cedille datatypes? E.g. List A =? List B <=> A =? B

## Video (Type theory elaboration 6: research on enhanced unification with sigmas)
- Refining the discussion from last time
- Several examples about applying the definitional isos to examples to eliminate sigmas
- Description of an idea to handle unification with all the definitional isos (some limitations, not clear how to do pruning)
- The idea is "Kind of like recursive pattern unification" (paraphrasing)
    - takes care of all the definitional iso issues (without needing to apply the rewrites)

## Video (Type theory elaboration 7: follow-up on new unification algorithm)
- More on unification with sigmas
- De Brujin indices/levels cause performance problems with insertion in contexts (have to fix all the indices)
- The idea seems to work well, though it is not as simple as hoped
- It would be nice it pruning was extended to also handle sigmas in a more general/direct way, but this seems to require
    adding partial terms to the core syntax

## Video (Type theory elaboration 8: comparison of De Bruijn, non-shadowing and fresh variable conventions)
- (De Bruijn) indices in syntax, levels in values (Andreas Abel liftable terms NbE)
    - values really need levels, so that weakening of values is free (because values have no bound variables)
    - this is not possible in syntax with indices or levels (because syntax has both free and bound variables)
    - Values are "normal forms" with explicit substitutions
    - Gives O(1) comparison of variables
- Insertion and permutation in a context is not efficient with De Bruijn indices/levels
    - This showed up in the previous extension of the unification algorithm, were inserting in the context is required
    - Could the context instead be a tree?
- Non-shadowing: environment is a mapping from names to entries, but names are unique (to a particular environment)
    - with this setup insertion and permutation is cheap
    - But, now the scope comparison is linear time
- Fresh variable convention: every new binder is different from any other binder
    - "For a long time I thought that fresh variables were never better than non-shadowing" (paraphrasing)
    - The main benefit is forcing (forcing computes to head form w.r.t. metasubstitution)
    - Other approaches don't give disjointness of domains and codomains
- Forcing was not needed in weaker unification algorithms (partial renamings) because neutrals/normals are stable under renaming
- With the more complicated unification algorithm, the unification does partial _substitutions_ instead

## Video (Type theory elaboration 9: type classes and dependent types)
- Type classes are a kind of code generation
- complete inference algorithm -> type classes (restricted logic programming) -> typed metaprogramming -> untyped code generation
- in Haskell:
    - instances are Horn clauses
    - standard resolution algorithm works
    - no backtracking allowed
    - no functions, no computation, only static terms
    - domain of usual Prolog-style logic programming
- in Lean/Coq:
    - basis is SLD resolution for instances (depth-first + backtracking)
- Coherence + dependent types is not implemented in any language
    - coherence means that the same instances are the same type
- Andras' is advocating explicitly labeling classes as coherent or incoherent
    - Does not sound like a good solution, just forgo coherence, orphan instances are annoying anyway
- need memoization or sharing preservation of instances for performance
- "Global hash-consing makes not sense in Dep TT"
    - high overhead, and cannot handle beta-reduction
- Don't index by normal terms (don't store normals at all!) because of size explosion
- efficient structure where keys are terms: discrimination trees

## Github Repository (elaboration-zoo)
- Andras' commented that evaluation requires garbage collection
    - This doesn't sound correct, at worst you have to copy the environment, but immutable data structures can ameliorate this
    - https://crates.io/crates/im
- "Names are much less efficient [than levels and indices]"

