# SDitH formalization plan and checklist

Last updated: 2026-10-12, continuation 332.

**Overall status: incomplete; the persistent completion goal remains active.**
The latest full validation passed **3,750 build jobs and audited 19,132 project
declarations**. This checks the current development, not whole-scheme correctness
or security. See [validation output](audit/validation.log).

`[x]` means the stated, limited item is done; `[ ]` means work remains. The
items differ greatly in difficulty, so their count is not a completion percentage.
Several literal source claims have checked counterexamples. Proving those claims
as written is impossible; recording a refutation does not prove a corrected scheme.
**The main signature-security reduction is composed end to end
(`NamedSimulatorTerms.forgery_le_final_named`) but carries named, unproved
hypotheses:** the data-level closeness of the two signings (ideal-model
zero knowledge at uniform hidden blocks), the leaf hiding (the hidden
leaf's key unpredictable from the data at uniform blocks), the retry
bound and the six expansion-dependent simulator terms
(`SimulatorTermBounds`, continuation 331), with the layout and
structural conditions (the seed-collision bound is discharged since
continuation 320, the slope term since 329, the hardness term is
syndrome decoding since 330). Until those
are proved the reduction is not finished. Build/declaration counts must not be
used to estimate its completion.

The composed statement turns a forger into the solver's success plus explicit
terms. The forgery-to-fork step runs against the witness-free simulator, the
extraction from two accepted digests is proved, and the signing simulation is
reduced to the named hypotheses above (see
audit/HUMAN_REVIEW.md, "The final composed bound and its named
hypotheses").

## Completed components

- [x] Pin the submission and reference documents; inventory all 21 numbered
  algorithms and their source locations in [source/index.json](source/index.json).
- [x] Separate [specification](SDitH/Specification.lean),
  [assumptions and candidate models](SDitH/Assumptions.lean),
  [proof modules](SDitH/Proofs/), and the small [final interface](SDitH/Final.lean).
  The assumptions file asserts no cryptographic axioms. The final interface
  currently has three discrepancy statements, not a security theorem.
- [x] Define a bounded adaptive chosen-message game and explicit abstract
  signing/verification sequence. Prove table-entry provenance and the first
  signature-game step: a winning forgery has an earlier adversarial query to
  its final hash input, except for a `2^(-2*lambda)` ROM guessing term. Typed
  hash/signature record equivalences and the parsed verifier's final-test
  correspondence are checked. This is not extraction, a full concrete scheme
  instantiation, or an end-to-end EUF-CMA proof.
- [x] Define cuts before indexed adversarial hash answers and prove exact
  distributional resumption. Derive the distinct-answer two-continuation bound
  at fresh cuts and over random prefixes. Prove persistence of saved answers
  through signing, hash and public queries, and obtain two accepted fresh-message
  attempts at the same input with distinct tested digests. These experiments
  still use the honest secret; the bound is in selected-input success probability.
- [x] Connect useful-query selection to overall forgery probability. The
  instrumented execution has exactly the original law; a present-input winner
  has a request that was fresh when made, at an index below the action budget.
  Uniform index selection and replay give a quantitative forgery-to-fork bound
  with a squared action-budget loss. This still uses the honest signing secret
  and gives distinct accepted digests, not an RSD witness or a runtime bound.
- [x] Reduce inconsistent revealed BAVC seeds to actual hash-query collisions
  or same-index seed-commitment collisions. The computable finder uses the exact
  two hash layers and successful staged reconstruction; its queried strings and
  fixed-width serialization are checked. The latter seed collision implies two
  equal cipher outputs under different seed keys at distinct tweaked inputs.
  The verifier's actual Hashlines/Hashaux chain yields a common BAVC root or a
  collision on those exact queries. Full adaptive ROM/ICM composition and
  full BLC binding are still open; no source binding or scalar equation is repaired.
- [x] Prove an adaptive shared-random-oracle birthday bound and its table/log
  invariants. Connect the actual BAVC two-layer finder to a fully queried binding
  experiment: different salt/commitment data with equal roots has probability
  at most `choose(q,2) / 2^(2*lambda)` after `q` total oracle queries. Query
  coverage is checked by this experiment; faithful full-game coverage, honest
  query counts and cipher/seed binding remain unproved. This does not complete
  the signature reduction or assume that concrete SHAKE is a random oracle.
- [x] Execute both BAVC row/outer hash computations after adaptive commitment
  selection against the adversary's shared oracle. Prove every verification
  program finishes, every required lookup exists, and its roots equal the source
  hash equations. The resulting hash-binding bound includes verification calls:
  `choose(q + 2*(tau+1), 2) / 2^(2*lambda)`. Acceptance has no already-queried
  guard. Full signature/replay query accounting and seed/cipher binding remain.
- [x] Define an adaptive encryption/decryption experiment and prove exact
  equivalence between one initially sampled keyed-permutation family and
  sampling compatible families after observations. Link it to the standalone
  ICM model. Prove repeated-query consistency, fresh uniform unused-range laws,
  transcript bounds and conditional target probabilities. For Category III,
  retain full 256-bit cipher observations and prove the 192-bit target bound
  `2^64 / (2^256-q)` for a fresh call after at most `q` observations. The two-call
  adaptive seed-collision probability is addressed by the next item; executing
  complete commitment verification and counting its calls remain open.
- [x] Prove the source's two cipher inputs are related by a fixed bit-flip
  involution, including after Category-III padding. Derive the joint posterior
  law retaining the hidden family, a conditional companion bound, and the
  first-matching-pair decomposition. The adaptive paired-cipher event is bounded
  by `choose(q,2) * C/(M-q) * C/(M-q-2)`, where each projection fiber has size
  at most C. Both query directions, repeats and changing keys are included.
  Full-output and Category-III instantiations are supplied. Mapping a source
  seed collision into this event currently requires explicit left-half query
  coverage; the next item discharges that requirement for two chosen commitments.
- [x] Execute both adaptively selected seed commitments on the adversary's
  shared cipher, including after early stopping. Derive completion, the exact
  four-call graph, source commitment outputs and the exact source collision
  predicate. Prove equality with the direct source collision experiment, with
  no coverage/freshness/completion guard. The binding bound includes verification:
  `choose(q+4,2) * C/(M-(q+4)) * C/(M-(q+6))`. Full-output and Category-III
  source instantiations discharge the structural and capacity premises. This
  closes two-commitment query coverage, not full reconstruction or signature
  composition; q counts earlier cipher calls, not signature interactions.
- [x] Define one shared adaptive hash/cipher execution and prove its exact
  joint posterior/fixed-family law, transcript consistency, collision-flag
  coverage and total query count. Both collision bounds hold under arbitrary
  interleaving, giving `choose(q,2) * (1/|Digest| + C/(M-q)*C/(M-q-2))` for the
  joint event. Full-output and Category-III sizes/capacities are discharged.
  The joint sampling choice is explicit in `Assumptions.sharedOracleModel`;
  it is not inferred from uniform marginal models or concrete primitive code.
  Existing seed and BAVC hash verification programs have exact operational
  lifts, complete query coverage and winning-to-collision proofs in this model.
  Mixed-program bounds compose and imply completion. The next items extend
  these component results to mixed-adversary sequencing and reconstruction.
- [x] Compose adaptive phases against the same joint hash/cipher model,
  preserving both histories and the OR of both collision flags, even after
  early stopping. Prove exact posterior/fixed-family law, correspondence with
  the standalone joint model, and both collision bounds with q+k total actions.
  Execute the source seed and root-hash checks after a mixed adversary, deriving
  completion and coverage. The seed law equals the literal collision predicate
  for full and Category-III outputs, with q+4 calls; the hash bound includes
  q+2*(tau+1). This does not yet compose the full signature or its replay.
- [x] Execute the cipher operations of Algorithm 9's actual tree expansion,
  revealed-leaf commitments and row loops. Prove exact agreement with the
  staged reconstructionRows value, including all source errors, and derive
  the budget 2*(tau*N-1)+2*N*tau. Full and Category-III layouts have the exact
  Enc* equations. Execution in the shared interpreter preserves the hash
  table/log and records the actual cipher trace. The next item completes the
  ordered reconstruction and its common-revealed-seed disagreement bound.
- [x] Execute complete Algorithm-9 reconstructions with each row hash directly
  after that row's leaf loop, then the outer hash. Prove the exact staged source
  result, including errors, and derive every required hash lookup and cipher
  graph entry. Execute both selected reconstructions after a mixed adversary;
  the second runs even if the first returns an error. Equal roots with a
  disagreeing common revealed seed imply a stored hash collision or a covered
  seed collision. Derive full-output and Category-III probability bounds with
  Q=q+2*B, B=2*(tau*N-1)+(2*N+1)*tau+1. Coverage is proved from actual execution,
  not an added success guard. This is a reconstruction disagreement result,
  not whole BAVC/BLC binding, signature acceptance, or an RSD extractor.
- [x] Execute the verifier's Hashaux/Hashlines chain as an explicit oracle
  program after the complete ordered reconstruction, with the base-matrix
  computation as a supplied bounded program at the line-21 boundary. Prove
  that equal line digests give equal roots or a stored collision on the exact
  query pairs, and derive the full/III bound for equal-line-digest executions
  with a disagreeing common revealed seed, with Q=q+2*(B+p+m+2). Algorithm
  12's separate seed/share bindings are not identified with reconstruction
  output; no signature/replay cost, extraction or simulation is claimed.
- [x] Prove seed-vector extraction on that chain game: two successful chains
  with equal line digests and different hidden indices at an execution
  determine a unique complete leaf-seed vector by pointwise merge, except on
  the bounded disagreement event. Hidden indices are still game inputs, not
  outputs of concrete challenge expansion; no witness lines are recovered.
- [x] Fold an extracted seed vector through Algorithm 12 lines 9–16 under
  explicit extractor bindings for seed/rshare/phi_mu. Prove the share at any
  hidden index is affine in its Gray row, lift this to the reached Q matrix,
  derive the two-index difference identity, and show honest Algorithm-10
  corrections give the committed accumulator as slope. Named bindings only;
  the literal absent-binding behavior and line 21 are unchanged.
- [x] Carry the affine share matrix into the Algorithm-12 suffix: witness
  and randomness values split into per-execution slope terms plus the
  intercept psi, with the constant-slope case affine in delta. Under an
  explicit candidate binary reading of line 21, two challenges differing at
  a Gray bit force the masked slope to equal the plain check. The candidate
  reading is a hypothesis shape, not a source resolution.
- [x] Prove the uniform-mask kernel law: over a uniform binary M, a fixed
  nonzero vector is annihilated by [I|M] with probability at most
  2^-(lambda+B), exactly that when its payload part is nonzero; two distinct
  fixed slopes have equal masked images with at most that probability. The
  XOF correspondence and oracle ordering of the mask remain open.
- [x] Prove the adaptive oracle trap: for the lazy oracle, a predicate that
  is a fixed function of the query input and fresh answer, with per-answer
  probability at most epsilon, holds for some recorded pair with probability
  at most budget*epsilon; repeats cannot create hits. The mask instantiation
  gives budget*2^-(lambda+B). Composition with the auxiliary query and the
  hcom-to-seeds binding remains open.
- [x] Extend the trap to predicates depending on the oracle table before
  each fresh query, on an instrumented trace with the fresh-entry/table
  correspondence and monotone growth proved. The chain-completed-later case
  and the mask oracle's XOF correspondence remain open.
- [x] Bound the chain-completed-later guessing event: a fresh answer equals
  a value mentioned by an earlier fresh query input with probability at most
  choose(budget,2)*m/|Output| for mention sets of size at most m, via a
  prefix-dependent trap bound summed over positions.
- [x] Model hash and mask oracles as the digest and matrix components of
  one product-valued lazy oracle; transfer the table-dependent mask trap
  bound and the digest mention bound to the components. This is an explicit
  modeling device, not the source's XOF structure.
- [x] Prove the ordered-log invariants and the dependency-chain dichotomy:
  a stored sink-first chain whose inputs mention their predecessors'
  digests is present before the sink was answered, or a fresh digest hit a
  mentioned value. The concrete BAVC/BLC chain instantiation remains open.
- [x] Instantiate it with the concrete row/outer/auxiliary strings and the
  mask input: fixed-offset digest-window parser of size tau+2, pairwise
  distinctness by domain byte and length, and the per-execution
  present-or-mention conclusion at mask time.
- [x] Prove uniqueness of the slope-relevant components of chained claims
  with one auxiliary digest in a digest-collision-free table, under explicit
  injective commitment/serializer hypotheses, and bound the digest-collision
  event by choose(budget,2)/|Digest| with stored collisions raising it.
- [x] Assemble the standalone slope-consistency bound on the product-valued
  oracle: a run whose named claim is chained, whose mask is stored and whose
  slopes differ with equal masked images has probability at most
  tau^2*budget*2^-s + choose(budget,2)*(tau+3)/2^(2*lambda), under explicit
  injective commitment/serializer hypotheses. Not yet joined to the cipher
  seed binding, the signature game or extraction.
- [x] Instrument the shared hash/cipher execution with the fresh-query log:
  exact projection onto the existing execution, traced/ordered/fresh
  invariants, and both trap bounds for a fixed family and the mixture.
- [x] Prove the unobserved-key double-match bound 1/(M-q)*1/(M-(q+1)) and
  its union over a finite key set, the cipher-side step for seed collisions
  against unqueried seeds.
- [x] Re-state the slope game in the shared model with CommitSeed through
  the hidden family: a winning run with a chained, queried claim raised a
  mask trap, the mention event, the digest-collision event, a witnessed
  pair collision or an unseen double match.
- [x] Assemble the shared-model slope-consistency bound from those five
  events: tau^2*budget*2^-s + choose(budget,2)*(tau+3)/2^(2*lambda) +
  choose(budget,2)*pairCost + tau*2^kappa*2^lambda/((2^lambda-budget)
  (2^lambda-budget-1)), with no commitment-injectivity hypothesis.
- [x] Instrument the two-phase shared execution with the log: exact
  projection, invariants through both phases, fresh-entry count bound, and
  both trap bounds with total budget q+k.
- [x] Execute the named claim's commitment calls as a second phase and
  prove the slope-consistency bound with no queried condition, with budget
  q+2*tau*2^kappa, through the two-phase projection and posterior lemma.
- [x] Instantiate the abstract game's other-state with the shared world and
  write Algorithm 4's verification as an executed oracle program with
  explicit middle/expansion parameters; prove the typed fork glue and the
  lifted-program evaluation correspondence.
- [x] Decompose a successful executed verification and prove that two of
  them with equal lines digests and differing hidden indices determine a
  unique complete seed vector unless a digest or recorded seed collision
  occurs.
- [x] Name a candidate verifier middle for Algorithm 12 lines 9–21 and
  prove it yields the affine share matrix of any complete seed vector
  agreeing with the reconstruction's revealed seeds, with the candidate
  base in masked-slope form.
- [x] Establish the submitted extension fields: exact modulus irreducibility,
  bases, cardinalities, coefficient isomorphisms, and byte-decoding round trips
  for explicitly supplied coefficient orderings.
- [x] Formalize SHAKE128/256, Keccak refinement, padding, absorption, squeezing,
  byte readers, AES-128 and Rijndael-256-256; check primary-source examples with
  kernel-checked certificates. Cryptographic security is not inferred from these.
- [x] Prove witness expansion, mixed-radix reconstruction, weight/length and
  encoding properties; connect partial integer sampling and actual cipher streams
  to key generation, including the precise consequences of missing source names.
- [x] Formalize BAVC commitment, literal opening and staged reconstruction;
  prove opening termination/safety and a submitted Category-I opening that the
  literal reconstruction rejects. General intended reconstruction correctness
  and commitment security remain open.
- [x] Formalize BLC folding, Gray encoding, corrections and consistency algebra;
  compose commitment, retry and the defined recomputation stages. Prove local
  identities and successful-return provenance at explicit source boundaries.
- [x] Compose both hash and cipher challenge paths with partial signing and
  verification. Preserve pending, undefined and rejected outcomes separately;
  prove return stability and exact missing-operation obstructions.
- [x] Prove detailed PIOP parsing, arithmetic evaluation, degree and batching
  properties, with explicit dimension premises; prove comparison probability
  bounds for the defined independent uniform experiments. These are not laws
  of concrete SHAKE/grinding challenges or full knowledge-soundness results.
- [x] Formalize the displayed SD-to-RSD computation, conditional return
  correctness, fixed-witness permutation probability and uniqueness step;
  refute its asserted equality with the instance-existence event.
- [x] Connect the SD-to-RSD joint experiment to the actual reduction output;
  derive the combinatorial-factor lower bound with its actual conditional
  probabilities. Give a correct selective solver whose conditional uniqueness
  probability is zero with positive return mass in the planted model. This
  refutes a proposed intermediate bound, not the final existential theorem.
- [x] Prove the density criterion and byte-aligned maximum-dimension arithmetic;
  check counterexamples to the printed floor/sign formulas. Keep the formulas
  literal; these results do not supply hardness estimates or a corrected scheme.
- [x] Check full binary parameter Tables 4/5, variant size formulas and numerical
  budgets; prove conditional key-encoding capacity bounds. Isolate Table-6
  timings as reported empirical data, not theorems about measured performance.
- [x] Prove scoped scaled-witness and scaled-arithmetic properties for the F256
  outline, including degree/probability bounds, missing nonzero enforcement and
  necessary packing capacity. Full variant protocols remain unfinished.
- [x] Run the source, build and transitive axiom audit over every project
  declaration. Current allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Remaining work, in priority and dependency order

1. [ ] **Work directly on the signature-security reduction.** The
   probability link from forgery to an actual uniform-index replay is proved,
   including useful-query selection, freshness, exact replay and oracle
   consistency. Deterministic commitment collision reductions are also proved
   through the actual BAVC reconstruction and verifier hash chain. The adaptive
   ROM bound now includes both executed BAVC row/outer verification computations
   and their query costs. Next connect the remaining complete signature/replay
   oracle executions and counts. The adaptive paired-cipher collision bound is
   now proved using the first matching observation pair and its unobserved
   companion, with source bit-flip/padding correspondence. Both chosen seed
   commitments are now executed on the same cipher, with their four calls,
   graph coverage and exact source collision predicate proved. Next compose
   actual seed/tree/reconstruction calls and the shared hash/cipher services
   with their signature/replay costs. The shared interleaved hash/cipher model
   now has checked joint laws, invariants and both bounds; source component
   programs embed exactly. Sequential composition after a mixed adversary now
   preserves both histories and both phases' collision flags, with q+k bounds.
   The source seed and hash checks have complete winning-to-collision proofs
   in that execution. The actual BAVC cipher expansion and row routines now
   execute with exact staged source values, error preservation and a proved
   budget. Both complete reconstructions now execute in source order, including
   line 30's hash after each row. Their actual hash/cipher coverage and total
   budget give a proved full/III bound on equal-root, common-revealed-seed
   disagreement. No source binding or query-coverage contract is assumed.
   The actual BLC Hashaux/Hashlines chain now executes on the shared oracle
   after the complete reconstruction, with its query cost and the equal-line-
   digest disagreement bound proved, and extraction of a unique complete
   leaf-seed vector from two chains with differing hidden indices is bounded
   by the same event, and the extracted vector folds under explicit
   bindings to an affine share in the hidden Gray row, and the suffix values
   and candidate two-challenge consistency identities are proved, with the
   uniform-mask kernel bound 2^-(lambda+B) for distinct slopes and its
   adaptive oracle-trap form budget*2^-(lambda+B), also for table-dependent
   predicates at fresh queries, and the fresh-answer-hits-earlier-input
   event is bounded, with both transferred to the product-oracle model.
   The standalone slope-consistency bound is proved and the shared model
   now carries the fresh-query log, with the unobserved-key double-match
   bound available, and the slope game is re-stated in the shared model
   with its probability bound and the named commitments executed, and the
   shared-model scheme skeleton exists with explicit middle/expansion
   parameters (a declared target is a recorded user decision), and two
   executed verifications yield the seed vector up to collisions, and a
   candidate middle yields the affine shares, and two candidate
   verifications of a fork force the masked slope to equal the plain check
   at a differing hidden index up to recorded collisions, and the honest
   signer's commitment phase is an executed program whose successful
   evaluation is Algorithm 7's commitment with every chain query recorded,
   and the abstract game's signing services are instantiated in the shared
   model with every honest signature traced to such a commitment, and the
   fork-to-slope outcome holds on the shared prefix table whenever both
   branches' verifications visit only prefix inputs, and the verifier's
   auxiliary, outer and row strings are in the fork cut whenever its lines
   string is, up to the mention event, and a stored value with a fixed
   target digest is in the cut or a post-fork fixed-target event occurred,
   bounded by budget·2^-2λ per run with the cut preserved along runs, and
   the cut at the snapshot's shared table holds at both branches' attempts
   of the shared game by service-wise preservation, and a successful
   verification's visited inputs are exactly the chain, mask and lines
   strings, and one branch's accepting verification visits only fork-table
   inputs unless a fixed-target, mention or mask-after-cut event occurred,
   and a successful fork of the shared game yields, at every execution
   with differing hidden indices, the slope outcome on the snapshot's
   table or a branch event or a digest collision, and a per-service event
   bound lifts to the attempt of a run or a fresh branch as the fuel times
   twice the service constant, and the fixed-target event of a fresh
   branch from a well-formed snapshot is at most remaining·2·bound·2^-2λ,
   and size-dependent per-service bounds lift the same way under a level
   on the size plus the remaining growth, and the mention event of a fresh
   branch is at most its snapshot indicator plus remaining·2·bound·(L+bound)·(τ+2)·2^-2λ.
   The same bound holds along the cut to the snapshot with the level
   premise preserved, and from key generation the prefix's mention and
   collision events are each at most fuel·2·ε(fuel·2·bound) with the
   snapshot meeting the branch level premise, and the fork experiment's
   charged events (prefix mention/collision, branch target/mention) are
   at most their summed bounds, and the fork's success is at most its
   success without charged events (which yields the slope outcome or a
   mask event at every differing execution) plus that bound, with the
   mask and seed completion uniform across executions. Two decisions are
   now recorded for the user: the treatment of a mask input first queried
   after the fork, and whether the target is a single fork (per-execution
   identities where hidden indices differ) or a multi-fork extractor.
   The candidate verifier's base agrees with the honest signer's base
   check for any mask and hidden indices, the fork outcomes carry the
   uniform slope data, and under separation at every execution the data
   gives equal masked images, hence a slope-game win or a common slope
   whose witness line has the extracted coordinate as constant term,
   recovered from the two branches' values at distinct merged challenges.
   The user settled the decisions on 2026-10-09 (simplest options, named
   candidate targets; see the review ledger). The candidate BAVC target
   and its executed reconstruction are in place with their evaluation,
   honest-key and budget lemmas, and the candidate scheme (verifier,
   opening service, components) with its evaluation and visited-input
   lemmas, and the fork-to-slope lemma over the candidate reconstruction.
   Branch accounting, the prefix restriction, the game invariants and the
   event bounds hold for it, and so do the attempt provenance, the
   deterministic and probabilistic fork outcomes and the good-fork
   outcome, and an honest candidate signature verifies on the signer's
   world to the committed lines digest, and an accepting transcript with
   a common slope makes the extracted lines' prover polynomial agree with
   the hashed coefficient polynomial at the challenge, and a good
   candidate fork with masks read before the fork and separated hidden
   indices yields a seed collision, a slope-game win, or a common slope
   with that vanishing, and the fork experiment's success is at most the
   named events' probabilities plus the extraction probability plus the
   charged-event bound, and the forgery advantage against the
   candidate scheme (with the honest signer) is bounded through the
   forgery-to-fork inequality by the random-index named events, the
   extraction probability, the charged-event bound and the guessing
   term, with the extraction probability split into the batching event
   and the solution event (an explicit solution of the public
   instance); the solver on any scheme of the same types outputs the
   extracted witness, the solution event is at most its success, and a
   uniform per-event simulation gap transfers the forgery bound to that
   scheme, and the named witness-free simulator (a direct scheme that
   programs the hash table) instantiates the bound, and the recomputed
   verification input of any executed commitment is the committed
   lines digest with the simulator's coefficient tuple, and simulated
   signatures have explicit provenance (executed commitment, chosen
   digest, programmed entry). Next: the simulator's failure event,
   hidden-share independence and PIOP zero knowledge, then bounds of
   the named events and the batching event; connect
   the executed chain to the fork's two accepted attempts at one hash
   input with signature/replay query accounting, and separate usable
   challenges between distinct digests. Preserve the
   supplied serialization and source binding boundaries; root consistency alone
   does not identify Algorithm 12's independent folding seed array with these
   reconstruction outputs. Establish the remaining commitment/challenge consistency needed
   to turn the accepted fork into extractable transcripts, then construct and
   prove RSD extraction. Distinct digests alone do not imply usable distinct
   algebraic challenges. Keep source defects and concrete correspondence explicit.
   In particular, Algorithm 12's supplied seed array is not identified with
   reconstruction output, its line 21 remains ill typed, and its Hashlines omits
   the signer's witness-correction field. These gaps still obstruct full binding.
   Prove the signing-oracle simulation and its query/probability costs. The game
   definition and first hash-query reduction step are done at the typed abstract
   level; the exact end-to-end target bound and full concrete correspondence
   remain to be established. Neither a supplied extractor with assumed success
   nor assumed protocol soundness may stand in for the missing argument. Further
   SD-to-RSD lemmas are a separate downstream component, not a substitute.
2. [ ] **Resolve the source-dependent specification boundaries.** Track the
   decisions below against exact PDF locations and affected declarations. Preserve
   the literal specification and its counterexamples. Any amended specification
   must be explicitly identified and justified; no silent substitutions.
3. [ ] **Complete concrete representations and execution.** After the relevant
   source decisions, implement raw key/signature/transcript codecs, byte orders,
   padding and malformed-input behavior; prove round trips and source size laws.
   Finish PRG/challenge interpretation and Algorithm-12 recomputation, then join
   the raw keygen, sign and verify paths without unresolved boundary arguments.
4. [ ] **Prove whole-protocol honest correctness for a well-defined target.**
   Connect valid generated witnesses, all commitment openings, recomputation,
   zero constant term, coefficient recovery and final verification. State retry
   termination/success conditions and handle counters. The refuted literal
   version cannot receive an unconditional correctness theorem.
5. [ ] **Complete cryptographic models and local security proofs.** Define
   adaptive adversaries, oracle access, query/runtime accounting and the exact
   distributions. Establish commitment hiding/binding, extraction/knowledge
   soundness and zero knowledge under explicit justified hypotheses. Do not
   assume these desired conclusions in order to prove them.
6. [ ] **Prove the signature-security reduction.** Connect the relevant SD/RSD
   distributions to actual key generation, prove Fiat–Shamir and grinding steps,
   and derive a quantitative EUF-CMA statement. Keep ideal-oracle assumptions
   distinct from deterministic SHAKE/cipher implementations. The source omits
   the detailed reduction; numerical budgets alone do not establish it.
7. [ ] **Complete the variant scope.** Formalize every specified F256, TCitH and
   simple-variant operation and proof. Obtain explicit source decisions where
   only outlines exist, including F256 nonzero enforcement, field embedding and
   packing. Tables and arithmetic fragments do not complete a variant.
8. [ ] **Finish the downstream SD reduction and secondary mathematics.** Complete
   §5.1 induced-distribution, quantitative success and runtime arguments before
   replacing its conditional factors by advertised parameters. The failed
   uniqueness heuristic cannot be assumed as a lemma. Address greedy arity
   selection and remaining §4.1 optimization. Keep empirical hardness calibration
   separate from mathematical conclusions.
9. [ ] **Close the coverage and review audit.** Reconcile every algorithm,
   equation, table and substantive claim with a proved statement, an explicit
   assumption, a checked refutation, or a documented human/empirical obligation.
   Keep the final theorem interface small and summarize its exact scope.

Work on independent proofs continues while source decisions are pending. The
dependency order is source decisions → concrete complete execution → honest
correctness; model development and independent reduction lemmas can proceed
alongside it. End-to-end security needs both a defined target and those proofs.

## Explicit terms of the composed forgery bound (state at continuation 100)

The composed bound `CandidateSimulator.forgery_le_simulator` is proved with
these terms explicit. Each line is a separate proof task or decision.
Review note (continuation 331): the current composed bound is
`NamedSimulatorTerms.forgery_le_final_named`; the open lines below are
the ones it still carries as named hypotheses (`DataClose`, `LeafHide`,
the retry bound `hretry`, `SimulatorTermBounds`), by the user's decision
to keep them as named cryptographic assumptions rather than idealize the
PRG and the challenge and batching expansions.

- [ ] Simulation gap: PIOP/BLC honest-verifier zero knowledge, hidden-share
  independence, programming failure. Completeness and provenance of the
  simulated transcript are proved, the prover polynomial's split into
  its mask part and its witness part is proved, and the hashed
  coefficients are the zero-randomness ones padded by the packed layer
  constants and slopes; packing a full width of uniform bits is uniform,
  the one-time-pad lemmas are proved, and the witness correction,
  randomness constants and plain check are translations by the hidden
  party's vector, and that triple is an affine bijection of the vector,
  so a uniform hidden vector reveals a witness-independent uniform
  triple, the honest committed arithmetic's triple is that map, and the
  hashed coefficients are padded by uniform packed layer constants of
  the hidden randomness coordinates; each execution's transmitted
  correction is translated by that execution's hidden vector; the top
  hashed coefficient depends only on the slopes (three or more layers);
  the revealed view (witness correction, packed layer constants, plain
  check) is an affine bijection of execution zero's hidden vector, and
  the hashed coefficients below the top are its packed layer constants
  plus witness-free slope terms; the honest signer's hashed coefficients
  and auxiliary components are stated in those terms, and under a
  uniform hidden vector the honest data is uniform and independent of
  the witness-dependent constants; the PRG hypothesis is the named
  predicate `PRGUniform` and gives the same over a uniform hidden seed;
  the committed arithmetic's signature data is the honest data map, and
  the executed signer's prepared state's data is the honest data map of
  the hidden seed's PRG vector, and the real and fake signers' data
  coincide in distribution under the PRG hypothesis and a uniform hidden
  seed (data-level simulation step); encryption under a never-used key
  is uniform over all blocks, and an expanded seed under a fresh parent
  key through an output-uniform layout is uniform, and both submitted
  layouts are output-uniform (the ideal-cipher input of the hidden leaf
  seed's uniformity); each positive execution's correction is a uniform
  pad of its hidden vector, and the joint transcript over all executions
  is a shear bijection of the hidden vectors, hence uniform; the fresh-
  parent leaf uniformity holds for the posterior family of the game's
  fixed-family model, and a tree node is the cipher image of its parent,
  determined by any family consistent with its recorded ancestry, and
  the commitment's tree expansion records every expanded node's
  ancestry; the per-signature hidden-share step is proved under the
  posterior family with the fresh-parent-key event and the PRG
  hypothesis explicit, and a uniform parent's key is not fresh with
  probability at most the history's length over the number of seeds;
  both submitted layouts have injective keys, so the bound applies to
  each; fresh hash answers are uniform whatever the input, in the oracle
  and in the shared world's public digest and mask queries; finished
  programs and single cipher queries run as expected. The random table's PRG is a deterministic parameter,
  so hidden-share independence needs an explicit PRG hypothesis; by the
  user's decision (continuation 316 onward) the run-level step is carried
  as the named hypotheses `DataClose` and `LeafHide` of the final
  statement, not proved from a PRG idealization.
- [x] Slope-game win: the stored-mask event (continuation 321), its
  derivation from the good fork (continuation 322), the fork-level coverage by the trace
  trap, the witnessed pair and the unseen match (continuation 323), the
  real-experiment bound of the trap (continuation 324), the family-dependent
  fork bound (continuation 325), the witnessed pair's bound through it
  (continuation 326), the unseen match's bound (continuation 327), the
  skeleton's regeneration (continuation 328), and the final statements with
  the slope term explicit (continuation 329).
- [x] Seed collision across the two branches: the posterior pair mass
  through the cut and the restored fork (continuations 317–320).
- [ ] Zero challenge, Schwartz–Zippel, non-separation, batching: not
  dischargeable with deterministic expansion parameters; by the user's
  decision carried as the named constants `εZero εSZ εSep εBatch` of
  `SimulatorTermBounds` (continuation 331), bounds on the witness-free
  simulator's event probabilities.
- [ ] Mask after fork (and the simulator's seed-collision event):
  hypothesis terms by decision 1, the named constants `εMask εSeed` of
  `SimulatorTermBounds` (continuation 331).
- [ ] Signing procedures' coupling (the remaining part of the simulation
  gap after the hidden-share step): (i) a run-splitting lemma for the
  traced run of a program bind with a deterministic stepping procedure,
  with fuel accounting through the boundedness predicate (proved, with
  fuel monotonicity for bounded programs); (ii) the
  commitment program's decomposition into a witness-free prefix (tree,
  commits, rows, outer, auxiliary, mask) and a witness-dependent tail
  (lines query and result) (proved, with the split run of the
  commitment); (iii) the lines-query freshness event for
  both signers and the uniform fresh answer (the uniform answer and the
  equal lines-digest distributions are proved, and a stored lines input
  mentions the auxiliary digest and differs from every prefix query, and
  the trace shape of three fresh hash queries is proved, and a stored
  lines input after the prefix's last three fresh queries raises the
  charged mention event, and the prefix's run splits into its head and
  those three queries, with the mention argument carried through the
  continuation; the auxiliary and mask inputs' freshness are mention
  events, and the outer input's freshness is a mention event after the
  last row query, the head splits at that query and its run splits with
  the fresh last-row shape placing that query's entry newest, and prefix
  events persist along runs and continuations, and the prefix's last
  three queries either raise the mention event or finish fresh with the
  lines input's stored case raising it, and the prefix run is assembled
  into one event-or-fresh statement under an explicit last-row-query
  freshness condition, and two witnesses' commitment runs have
  lines-digest distributions within the prefix's mention-event
  probability, itself bounded by the prefix trap bound, and the prefix
  statement is available from the head's initial result with pointwise
  cost binds, so two witnesses' commitment runs are within the mention
  event plus the named row-stored event unconditionally, and the honest
  signing is unfolded to the commitment run, the PIOP hash query and the
  opening with the fresh and stored query bindings, and is within the
  named input-present event of its digest-first form, and the simulated
  signing is the uniform mixture of its fixed-witness forms with the
  honest payload consistency named as an explicit hypothesis, under which
  the honest and simulated hash inputs coincide at a returned retry, with
  the retry-failure event named, and the digest-first form is within
  the retry-failure event of the fixed-witness simulated signing, so the
  honest signing is within the input-present and retry-failure events
  plus an explicit witness-swap term of the simulated scheme's signing,
  under any continuation of the signing's output; the row-stored,
  input-present and retry-failure events' bounds, the witness swap's
  bound, the proof of payload consistency are open; the hybrids over the
  game's run, cut, continuation, branch, fork, cut experiment and event
  experiment are proved, and the composed forgery bound is restated
  with the simulation gap discharged from uniform bounds on the
  input-present and retry-failure events and the witness-swap term,
  which remain the open terms; the table-support invariant for the
  input-present bound is defined, preserved by queries and both
  signings, and carried through all the hybrids, so the simulation gap
  holds with the three terms assumed only at worlds supported by twice
  the fuel plus three inputs and the shared world well formed, through
  the hybrids over an abstract counted invariant; the input-present
  bound is proved as the prefix's mention term plus the row-stored term
  plus the support count over the digest count; the mention event
  relative to the starting log and its indicator-free trap bound are
  proved, the chain's stored-mention lemmas and the three-query
  statement, the head and prefix assembly and the input-present bound
  are restated with it, the relative term being bounded by the mention
  steps alone, the trace-length budget is an invariant component along
  the game, and the simulation gap takes the input-present term as an
  explicit value: the mention steps from the trace budget, the
  row-stored term's bound and the support budget over the digest count;
  the row-stored, retry-failure and witness-swap bounds remain open;
  payload consistency is proved under the candidate encoding and at
  least one higher coefficient, and the composed bound is restated with
  it discharged; the per-world row-stored and witness-swap hypotheses
  are found unsatisfiable at a fixed family, and the lazy-resampling law
  of the cipher family is proved for the shared interpreter and the
  scheme's program runs as the tool for restating them over the
  resampled family, and the game run and advantage are proved equal to
  those of the scheme resampling before each signing query under the
  oracle commutation laws; the run hybrid is restated with a
  world-dependent signing charge summed in expectation along the run, to
  be averaged over the resampled family, and the mean charge from a
  resampled world is bounded by the fuel times the per-call average bound
  under the oracles' resampling laws, and the replay hybrids are restated
  with the charge, and the expected replay charges from a resampled key
  are bounded by the fuel and twice the fuel times the per-call average
  bound, with the shared scheme's resampling laws in the generic forms
  the oracles instantiate, and the candidate scheme's honest and simulated
  signing, public oracle and key generation obey them, and the simulation
  gap is restated with the row-stored term and the witness-swap slack as
  means over the resampled family, and the composed bound is restated
  with it; the fresh-input answer bounds under the posterior family are
  proved, and the head's initial run is split at its last commitment
  call, the partial row hashes' table support is proved, and the
  row-stored event is reduced to the last block's membership in a set
  fixed before the last call, and the blocks hitting the set are counted
  with the posterior bound at a fresh input, and the event after the last
  call lies in the fixed set, and the row-stored mean over the resampled
  family is bounded by the last call's staleness term plus an explicit
  term, and the tree expansion's run is split step by step with the form
  of its recorded entries, and one expansion step under the posterior
  family is bounded, and the tree's goodness along the expansion is
  bounded by induction, and the commitment phase's recorded entries are
  characterized, and a stale last call is shown to force the tree not to
  be good, and the staleness term is bounded by the root term plus the
  steps times the step bound, so the row-stored term is explicit and
  the composed bound is restated with it discharged under the named
  cipher-history hypothesis, with the extended counted invariant that
  discharges it, and the composed bound holds under the extended
  invariant with the row-stored term explicit; the witness-swap term
  needs the mean-form hybrid, whose run form is proved, with the run
  threaded with its final world and its resampling law, and the candidate
  verification preparation's resampling law; the mean-form swap bound
  over every continuation is found unsatisfiable as well, since the
  signer logs the hidden path, so the swap is to be an
  identical-until-bad bound against the hidden path over the game's
  oracle-access continuation, with the hidden entries and the pruned
  world named explicitly, and the hidden path, its parent keys, the
  pruned history and its fresh keys are defined, and the posterior's
  answer at a key outside the pruned keys has the same law under the
  pruned history, and a run from a history agrees with its run from the
  pruned history until a query hits the pruned keys, in both
  directions, lifted to the shared scheme's program runs and to the game
  run under the oracles' prune laws, with the generic prune laws of
  program-shaped oracles instantiated by the candidate and simulated
  schemes' oracles, so the game-level agreement holds for both schemes;
  the touching term's bound, the pruned-world equal law of the two
  signings and the events' insensitivity remain; the hidden keys with the
  leaf's key are defined, and the exchange of a node's value is a
  posterior-preserving involution under which the seed tree changes only
  at the exchanged node, and the tree expansion's run is in closed
  form, and under the exchange its tree changes only at the node while its
  entries pruned at the exchanged keys coincide, with the run congruence
  and finish-map laws for the commitment phase, whose rest queries only the
  leaves' keys and sees an internal node only in its final value, and a
  run only appends to its starting history, so the commitment run under the
  exchange is the base run with the node set and the exchanged expansion's
  history appended, whose pruned entries coincide, while the signature's
  payload and body do not read an internal node, so the commitment run's
  pruned view has the same law under the exchange, for both candidate
  post-processings, and the generic fiber counting under a
  measure-preserving exchange is proved, with bad exchange targets
  allowed, in one-sided form, and the commitment run records only the
  tree's keys, and the view pruned at a family's own hidden keys is the
  same under the exchange of a path node, and the posterior bound on a
  hidden node's block is proved for exchange-invariant weights and gives
  the touching bound at a node for the commitment view, with the union
  bound over the hidden path, the distinct-keys goodness and the
  sibling-keys step, and the probability that the tree's keys are not
  fresh and distinct is bounded, and the root's exchange is carried
  through the commitment run, the commitment view and the own view into
  the posterior and touching bounds at the root, the view-dependent
  pruning slices over the hidden tuples, the own-view exchange holds
  for the hidden keys of all executions, the node and root bounds are
  stated for any exchange-invariant view and instantiated there, and the
  touching probability for the signature's own hidden keys splits into
  root, leaf and internal path hits per tuple and execution and is
  assembled against the joint draw, with the distinctness failure and the
  path depth bounded, up to the leaf term, and the hidden keys are
  determined by the commitment run's recorded history for any matching
  family, the signing call followed by the game run is bridged to the
  resampled pruned run plus the touching indicator in both directions, the
  hybrid chain and composed bounds take the swap only for the game's
  continuations, the run and cut hybrids hold in mean form for them, and
  the history is only a log for the game run, the event experiment
  equals its end-resampled restored form, and the mean-form hybrid chain
  over the restored fork reaches the event experiment, and the composed
  forgery bound is stated with the per-call swap in mean form for the
  simulated scheme's continuations and the events' insensitivity to the
  second branch's history suffix and the attempts' embedded families as
  named hypotheses, and the pruned-run agreement holds in both directions
  for prune-compatible evaluations read at the actual result, which the
  game run, resampling, sampling, restoration, table updates and
  finalization preserve, so the fork continuation is compatible given the
  event's compatibility at the end, and the run, fresh-branch, fork and
  cut hybrids hold with the per-call bound restricted to compatible
  continuations, the cut carrying its final world, and the event
  experiment's hybrid follows with the event branch's compatibility, and
  both per-call swaps are discharged from the agreement and the named
  pruned equality up to the touching term, the composed forgery bound
  is restated with them discharged, the touching bound holds for a
  hidden tuple fixed by the digest with the post-processing invariant only
  on that tuple's paths, the simulated post-processing is invariant
  under setting any internal node, the swap's touching term is the
  touching total's probability with the expected recorded length bounded
  by the budget, both touching bounds follow uniformly up to the leaf
  term, and the final composed bound carries only the pruned equality,
  the leaf-term bounds, the retry bound, the fiber and size conditions
  and the events' requirements, of which seven are discharged and the
  seed-collision event's probability enters directly; the named
  hypotheses' content is recorded in the review ledger; the pruned
  equality is corrected to a pruned closeness with a slack, carried
  through the per-call bounds to the composed statement, and the slack
  is split into the pre-call hit term and the off-hit equality, both
  stated over the uniform salt, root and digest, the hit term is
  proved from the tree's distinctness failure, and the off-hit target is
  a closeness since the sibling's exclusion makes the equality inexact;
  the leaf exchange's generic relabelling tool, the commitment phase's
  leaf exchange, the commitment run's leaf exchange with its pruned
  history, the phase view's leaf exchange and the posterior bound for the
  phase view at the leaf are proved, the latter for any invariant weight
  and the view pruned at all executions' hidden keys, with distinctness
  and the other leaves' fibers kept by the exchange, and the joint
  one-sided uniformity of the hidden leaves' blocks, with the parent
  seeds summed out, the two-sided uniform-mixture comparison, and the
  tail's run as hash-only, and the signing-data identity slicing the
  off-hit pruned mean by the hidden tuple, with the sliced data invariant
  under the leaf exchange, and the mixture bound relative to the tuple
  probability with the off-hit setup, and the honest upper and fake lower
  sides of the off-hit chain, with the hidden tuple determined by the
  digest so that at most two tuples carry mass, the chain assembled at
  fixed draws under the named data-level closeness, and the pruned
  closeness derived from it so that the final statement carries the
  data-level closeness, and the leaf-term bounds derived from the named
  leaf hiding, and the posterior pair mass with its per-run bound as the
  start of the seed-collision bound, carried through the oracles, the
  game run, the cut, a fresh branch and the fork, so that the
  seed-collision bound is the explicit pair cost); (iv)
  the fresh-parent-key
  chain from the per-signature root; (v) composition over the signing
  game into the per-event gap.
- [x] The solver's success as the hardness term: relate the mux syndrome
  solution to the intended syndrome-decoding instance (source
  correspondence of the public key): a witness with zero mux residual
  and unitary selectors gives a weight-`w` solution of the key
  generation's instance (`SolutionRegular.isSolution_sd`), and the final
  statement carries the syndrome-decoding success
  (`ForgeryRSD.forgery_le_final_rsd`, continuation 330).

## Human/source decisions — separate from proof tasks

These are unresolved interpretation or correspondence obligations, not assumed
lemmas. Details, exact scope and existing evidence are in
[HUMAN_REVIEW.md](audit/HUMAN_REVIEW.md).

| Area | Required resolution or review |
|---|---|
| Sampler and keygen | Undefined `B` and `x_A`; systematic-matrix convention; relationship of seed-expanded keys to the hardness distribution. |
| PIOP and dimensions | Extra evaluation factor, Table-3 tensor/chunk mismatch, mux coordinate/index conventions and incorrect degree annotations. Checked counterexamples must remain visible. |
| BAVC and BLC | Opening padding versus reconstruction bounds/queue logic, undefined nodes/aliases, differing hash payloads, missing recomputation names and the ill-typed Algorithm-12 line 21. |
| PRG and challenges | Undefined block-size denominator, missing-tweak case, Category-III parse width, cipher material parsing, MapToBits/Extract, binary versus Gray interpretation, and counter behavior. |
| Serialization | Exact byte encodings, field order, transcript boundaries, padding and parser policy; Category III has four spare secret-key bits. |
| Parameters and reduction | Parameter prose contradicts Table 4; printed density floor/sign claims have counterexamples. §5.1 needs a valid probability argument and distribution/runtime correspondence; the event equality and universal conditional-uniqueness estimate cannot be assumed. |
| Variants | Full algorithms absent from the outlines; nonzero amplitudes, concrete scalar representation, embedding and packing must be specified. |
| Security assumptions | Adequacy of candidate hardness/oracle/machine models and their correspondence to the intended claim. The new abstract HashPiop domain is typed and separate from other oracle state; raw domain/encoding correspondence and faithful component instantiation remain unproved. Interaction fuel is not a runtime bound. No unproved reduction is an allowed assumption. |
| Empirical claims and trust | Benchmark reproduction, attack-cost estimates, implementation correspondence, source transcription, and Lean/toolchain/foundational trust. A Lean theorem cannot certify the reported measurements by transcription alone. |

## Completion gates

- [ ] Every source item has an accurate final disposition and all required
  formalizable work is finished; no partial component is advertised as a scheme.
- [ ] All source-dependent choices are explicit and reviewed. A change to the
  target is recorded as a change, and original discrepancies are retained.
- [ ] Complete algorithms and applicable correctness/security claims have proofs
  for that declared target; unsupported or false claims are clearly distinguished.
- [ ] Cryptographic assumptions remain explicit theorem parameters in the
  standalone assumption interface, with no circular correctness contracts.
- [ ] The final source/build/transitive-axiom audit passes, with no `sorry`,
  `admit`, custom axioms, unchecked native proofs or equivalent shortcuts.
- [ ] Human review of source correspondence, statement adequacy and the separate
  empirical/trust boundary is recorded. The persistent goal is marked complete
  only when its actual requirements have been met.

## How this file is maintained

Update this checklist after each verified workstream, including new blockers and
the latest audit counts. Do not check off a conditional fragment as an end-to-end
result. Detailed evidence lives in [COVERAGE.md](audit/COVERAGE.md); the chronological
record is [PROGRESS.md](audit/PROGRESS.md). Validation command:

```sh
python3 scripts/check.py
```
