# SDitH formalization plan and checklist

Last updated: 2026-10-15.

The latest full validation passed **3,757 build jobs and audited 19,261 project
declarations**. This checks the current development, not whole-scheme correctness
or security. See [validation output](audit/validation.log).

The work falls into two tracks with different kinds of blockers. Read the
two-track summary first; the detailed checklists follow it.

## Two-track summary

**Track A, the security reduction: complete modulo named assumptions.**
The composed EUF-CMA bound `SeedTermDischarge.forgery_le_final_hard_C` is
proved for the candidate scheme in the ideal hash-and-cipher model, and
`FullLayoutFinal.forgery_le_final_full` is its form at the submitted full
layout with the layout hypotheses discharged. Every term
of its right-hand side is either proved or one of five named hypotheses
(`DataClose`, `LeafHide`, `hretry`, `SimulatorTermBounds5`, `InstanceHard`), kept as explicit
cryptographic assumptions by the decision of 2026-10-12 rather than derived
from an idealization of the PRG or the challenge and batching expansions. No
further proof work is scheduled on this track unless that decision changes.
Two items stay open, neither of them proof work in the current model: relating
the key generation's instance to a hardness distribution, and the correspondence
of the candidate scheme to the submitted routines (blocked by Track B's source
defects).

**Track B, whole-scheme formalization: blocked on source decisions.** The
original brief asked for a complete formalization of the submission:
correctness, concrete byte-level execution, the variants and the §5.1
mathematics. The literal source is refuted in several places (checked
counterexamples) and undefined in others, so this track cannot proceed without
a human choosing a corrected target. Its items are listed below with their
blocker. They are not a measure of how much proof work remains; most of them
are decisions, and some cannot be proved as the source stands.

`[x]` means the stated, limited item is done; `[ ]` means work remains. The
items differ greatly in difficulty, so their count is not a completion
percentage.

## Track A — the security reduction

Status: complete modulo the named assumptions. Current final statement
`SepChain.forgery_le_final_full_enc` (single-execution extraction, full
layout, candidate encoding; generic form `SepChain.forgery_le_final_hard`).
The earlier chain is kept: `SeedTermDischarge.forgery_le_final_hard_C`,
`CandidateSerialization.forgery_le_final_full_enc` and
`DistributionalFinal.averaged_forgery_le_final`; its non-separation constant
`εSep` is not small for any model (continuation 338), so those statements
are weak against counter-grinding forgers. The per-term checklist is in
"Explicit terms of the composed forgery bound" below.

- [x] Forgery-to-fork with useful-query selection and replay; extraction from
  two accepted transcripts; the witness-free solver; the hybrids over the
  signing game; the honest signer's coupling with the witness-free simulator
  up to the named closeness and hiding hypotheses; the real-experiment bounds
  of the seed-collision and slope-game events; the extracted witness as a
  regular syndrome-decoding solution of the public instance.
- [ ] Named hypotheses, open by decision (each needs an idealization not
  adopted): `DataClose` and `LeafHide` (the PRG), `hretry` (the challenge
  expansion), `SimulatorTermBounds5` (mask-after-fork by decision 1; the
  other four need the challenge and batching expansions).
  If the decision changes, each is a well-scoped proof project that leaves the
  rest of the final statement untouched, with one qualification found at
  continuation 336: the four expansion-dependent constants and the retry
  bound cannot be made small by a hypothesis on the deterministic expansion
  parameter, because the forger evaluates it at every counter without a
  query; discharging them needs the challenge expansion modelled as a
  counted oracle of the digest and counter, a refactor of `SigningSetting`
  and `VerifierSetting` across the reduction.
- [x] Hardness as a named assumption: `InstanceHard` bounds every budgeted
  adversary's solver on the key generation's fixed instance by `εSD`, and
  the final statement carries `εSD` in place of the solver's success.
- [x] Single-execution extraction (continuation 338): the extraction needs
  the hidden tuples to differ at one execution; the bad event is their
  full agreement (`SepEvents.allAgree`), negligible under uniform
  expansion, in place of agreement at some execution, which a forger can
  force by grinding its counter. The Schwartz–Zippel and batching events
  carry the negations of the prior events and are named real-experiment
  constants (`SepChain.RealTermBounds`); the transferred constants are
  `SepChain.SimulatorTermBounds3`. Hypotheses `hencode` and `hlayoutV` are
  no longer needed.
- [ ] Bounds for `εSep`, `εZero`, `εR` (needs the challenge expansion as a
  counted oracle); for `εSZ` and `εBatch` (needs in addition the slope
  game generalized to partial claims, whose seed vector is known at the
  separated executions only, and the binding of the difference polynomial
  to the committed data).
- [ ] `DataClose` and `LeafHide` as stated look satisfiable only with slack
  near one (pointwise in the family; arbitrary continuations), and the
  signer's PRG is a supplied function, not a cipher call: restate in
  posterior-mean form with the adversary's own continuations, route the
  PRG through the ideal cipher, then prove (survey of 2026-10-15).
- [x] Hardness over a distribution: `DistributionalFinal` averages the bound
  over any distribution of instances under `DistributionHard` (mean-square
  form over any distribution; the averaged advantage on a finite index
  type).
- [ ] The key generation's own law (a decision, review table row "Sampler
  and keygen"): Algorithm 2's literal routine returns no key (`B`, `x_A`
  undefined), so its instance distribution is not formed and the
  distribution is a parameter; `SDitH.Assumptions.SDHardness` (planted
  uniform matrices) remains unconsumed, and no runtime model exists.
- [x] Encoding hypotheses discharged at the named candidate encoding
  (`CandidateSerialization`, one bit per coordinate); the encoding's
  agreement with the implementation's packing is a review item.
- [ ] Correspondence of the candidate scheme (`CandidateScheme`,
  `CandidateVerifier`, `CandidateBAVC`) to the submitted routines: blocked by
  the source defects of Track B (Algorithm 12's seed array and line 21, the
  `Hashlines` payload, the undefined bindings).
- Not in scope of the model: a runtime or machine model. The budget counts
  oracle actions, so the statement is not a concrete-time EUF-CMA bound.
- Not in scope of the settings: Category III's truncated cipher layout
  (block width 256 at λ = 192); the settings fix key and block width to λ.

## Track B — whole-scheme formalization

Each item carries its blocker. "Decision" means a human must choose a reading
of the source; "refuted" means the literal claim has a checked counterexample
and cannot be proved as written; "separate scope" means work independent of
the reduction that the source only outlines.

1. [ ] **Source-dependent specification boundaries.** Blocker: decision. The
   undefined bindings (`B`, `x_A`), the systematic-matrix convention, the PRG
   block-size denominator, the missing-tweak case, the Category-III parse
   width, MapToBits/Extract, binary versus Gray interpretation, counter
   behaviour, Algorithm 12's seed array and its ill-typed line 21, and the
   `Hashlines` payload. Each is tracked against its PDF location in the review
   table; the literal specification and its counterexamples are preserved.
2. [ ] **Concrete representations and execution.** Blocker: decision (item 1).
   Raw key, signature and transcript codecs, byte orders, padding and
   malformed-input behaviour, with round-trip and size laws; then the joined
   raw keygen, sign and verify paths.
3. [ ] **Whole-protocol honest correctness.** Blocker: refuted, then decision.
   The literal PIOP check rejects honest inputs
   (`Final.literal_piop_not_complete`) and the literal reconstruction rejects
   a valid opening (`Final.commitment_discrepancies`), so no unconditional
   correctness theorem exists for the literal scheme. A corrected target must
   be chosen before correctness can be stated; the candidate scheme of Track A
   is one such reading for the parts the reduction needs, not a complete
   corrected specification.
4. [ ] **Local security notions as standalone statements.** Largely absorbed
   by Track A: commitment hiding and binding, extraction and the simulation
   are proved inside the composed reduction, in the ideal model, modulo the
   named hypotheses. What is not done is restating them as standalone
   theorems with their own adversary interfaces; this is presentation work,
   not new proof content, and is not scheduled.
5. [ ] **Variant scope (F256, TCitH, simple variant).** Blocker: separate
   scope and decision. The source gives outlines, not full algorithms;
   nonzero enforcement, field embedding and packing must be specified before
   anything beyond the existing tables and arithmetic fragments can be proved.
6. [ ] **§5.1 downstream SD reduction and secondary mathematics.** Blocker:
   refuted and research. The printed density floor and sign claims have
   counterexamples, and the conditional-uniqueness heuristic cannot be
   assumed as a lemma. A valid induced-distribution and runtime argument
   would be new mathematics, not a transcription. Greedy arity selection and
   the §4.1 optimization are in the same position.
7. [ ] **Coverage and review audit.** Blocker: human review. Reconcile every
   algorithm, equation, table and substantive claim with a proved statement,
   an explicit assumption, a checked refutation, or a documented obligation.
   The inputs for this exist (`source/index.json`, `audit/COVERAGE.md`,
   `audit/HUMAN_REVIEW.md`), and `audit/DISPOSITIONS.md` tabulates a proposed
   disposition (proved, assumption, refuted, obligation) for every source
   item; the dispositions have to be reviewed by a person.

Dependency order within Track B: decisions (item 1) → concrete execution
(item 2) → honest correctness (item 3); items 5 and 6 are independent of that
chain; item 7 closes after the others.

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

## Explicit terms of the composed forgery bound

The final statement is `SeedTermDischarge.forgery_le_final_hard_C`. Each line
is one term of its right-hand side or one of its hypotheses.

- [x] Fork-and-extract core: forgery-to-fork at a uniform useful index, the
  prefix mention and collision events, the branch fixed-target and mention
  events, the digest-guessing term; all bounded explicitly.
- [x] Extraction: two accepted transcripts at one hash input with differing
  hidden indices give a seed collision, a slope-game win, or a common slope
  whose witness line yields the extracted coordinate; the extraction event is
  split into the batching event and the solution event.
- [x] The witness-free solver: runs the simulated scheme's fork experiment,
  outputs the extracted witness; its success bounds the solution event.
- [x] The hardness term: an extracted witness with zero mux residual and
  unitary selectors is a weight-`w` solution of the key generation's instance
  `instanceOf H' y` (`SolutionRegular.isSolution_sd`), so the solver's success
  is at most `rsdSuccess` (`ForgeryRSD`), which the named assumption
  `InstanceHard` bounds by `εSD fuel` (`InstanceHardness`).
- [x] Simulation gap, proved parts: the honest signing unfolds to the
  commitment run, the PIOP query and the opening; the input-present term is
  the prefix's mention steps plus the row-stored term plus the support count
  over the digest count; the row-stored term is bounded through the staleness
  of the last commitment call and the fresh-parent-key chain of the seed tree;
  payload consistency holds under the candidate encoding with at least one
  higher coefficient; the hybrids over the game's run, cut, continuation,
  branch, fork, cut experiment and event experiment hold in mean form over
  the posterior cipher family under the counted invariant; the witness swap
  is reduced to the data-level closeness and the leaf hiding through the
  hidden-leaf tuple, the touching bound and the off-hit chain.
- [ ] Simulation gap, named hypotheses:
  - `DataClose` (`OffHitAssembly`): with the hidden leaves' blocks replaced by
    a uniform tuple, the honest signing's sliced data is within an explicit
    slack of the fake signing's on the trees with fresh and distinct keys.
    The data-level hidden-share step is proved for the honest data map of a
    uniform hidden vector; the PRG of the hidden seed is a deterministic
    parameter, so the step from a uniform seed needs a PRG idealization
    (`PRGUniform` is the named predicate).
  - `LeafHide` (`LeafTermBound`): with the tuple's leaves replaced by uniform
    blocks, a continuation records a replaced block's key with probability at
    most δ on average. Same dependence on the PRG.
  - `hretry`: the candidate retry returns at the digest except with
    probability εR. Needs the challenge expansion's model.
- [x] Seed collision across the two branches: the explicit pair cost
  `εCollOf` through the posterior pair mass over the oracles, the game run,
  the cut, a fresh branch and the restored fork; the simulated copy of the
  event is not needed and no longer appears (`SeedTermDischarge`).
- [x] Slope-game win: the stored-mask event is covered by the mask trap, the
  witnessed pair and the unseen match; each is bounded in the real experiment
  (the trace trap bound, the family-dependent fork bound with the pair-mass
  chain, the unobserved-key bound), giving the slack
  `(fuel+1)·2·εTrap + εWitOf + unseenCost` under the verifier's identity
  layout.
- [ ] Expansion-dependent simulator events, carried as the named constants of
  `SimulatorTermBounds5`: mask-after-fork (`εMask`, decision 1),
  non-separation (`εSep`), zero challenge (`εZero`), Schwartz–Zippel
  (`εSZ`), batching (`εBatch`). Each is a probability of the witness-free
  simulator; with the challenge and batching expansions idealized the last
  four would be per-attempt small-support counts. Not dischargeable with
  the deterministic expansion parameters.
- [x] Layout and size conditions, stated as hypotheses: the signer's input
  injectivity and the fiber bounds of its key and output maps; the verifier's
  identity layout, injective input and key maps and output fiber bound;
  26 ≤ λ, four times the leaf count ≤ 2^24, the budget-dependent counts below
  the number of seeds. At the submitted full layout the seven layout
  hypotheses are discharged with fiber constants one
  (`FullLayoutFinal.forgery_le_final_full`). The settings fix the cipher's
  key and block width to λ, so the Category-III truncated layout (192-bit
  seeds in 256-bit blocks) is outside their type: the reduction covers
  Categories I and V as stated; Category III needs the settings extended
  to a separate block width (scope item, Track B).

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
| Serialization | Exact byte encodings, field order, transcript boundaries, padding and parser policy; Category III has four spare secret-key bits. The reduction's two injectivity hypotheses are discharged at the candidate bit-per-coordinate encoding (`CandidateSerialization`); its agreement with the implementation's packing is the review item. |
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
result. This file and the README describe the current state only; the
chronological record is [PROGRESS.md](audit/PROGRESS.md), the per-module detail
is [COVERAGE.md](audit/COVERAGE.md), and the review obligations are
[HUMAN_REVIEW.md](audit/HUMAN_REVIEW.md). The earlier narrative version of this
file is [PLAN_HISTORY.md](audit/PLAN_HISTORY.md). Validation command:

```sh
python3 scripts/check.py
```
