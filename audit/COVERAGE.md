# Coverage ledger

Status: incomplete. Every item below is required or requires an explicit source
resolution before the requested whole-submission formalization can be claimed.

| Source | Scope | Status |
|---|---|---|
| §2.1 (1)–(3) | General PIOP and literal verifier | Evaluation, degree derivation, exact uniform batching probability and two-challenge algebraic bound with d+1 checked, including randomized responses; printed d-based soundness bound and completeness refuted; commitment/knowledge soundness and ZK remain unresolved |
| §2.1 pp. 5–7 | AVC algebra, VOLE merge, consistency check, reciprocal encoding | AVC opening, explicit psi merge, consistency-base recovery, and reciprocal line evaluation checked; security arguments pending |
| §2.2 | Regular SD, tensor witness, constraint equivalence | Mixed-radix reconstruction, explicit flat coordinate order, omitted-selector recovery and tensor-coordinate identity checked; binary unitary characterization and actual packed-loop equivalence proved in Table-2 quotients; full constraint integration still obstructed by the mux discrepancy |
| Algorithm 1 | Witness expansion | Actual partial integer loop feeds the full deterministic suffix at the concrete cipher-stream boundary; returned-expansion weight/length, stability and literal nonempty no-return proved; successful finite PRG output gives equal traces within four bytes per attempt; earlier regularity/injectivity retained; PRG source gaps and complete source resolution remain unresolved |
| Algorithm 2 | Keygen | Independent seed PMF feeds partial witness expansion, concrete cipher-stream matrix, literal syndrome assignment and supplied serializers; returned-key provenance and exact generated-solution SD condition checked; missing B and x_A separately prevent returns, and every returned typed/encoded key has zero mass in literal observation PMFs; source binding/PRG gaps, raw codecs and complete execution unresolved |
| Algorithms 3–4 | Sign and verify | Verification is also an executed oracle program on the shared world with explicit middle/expansion parameters, and two successful verifications with equal lines digests and differing hidden indices yield a unique complete seed vector unless a digest or seed collision;  Actual BLC/PIOP preparation feeds partial signing; hash and staged cipher callers preserve expansion boundaries, pending/undefined/rejection, successful-return provenance and outer-fuel stability; concrete cipher extraction consumes actual xor and a return requires the final SHAKE integer sample; missing B blocks nonempty signing or verifier boundary/rejection after preceding interpretations are supplied; verifier stops before Algorithm-12 line 21, with suffix/hash comparison only for a supplied base; raw initialization/codecs, source resolutions and full correctness/security unresolved |
| Algorithm 5, §3.2.3 prefixes | Salt tweaking and domain input bytes | Typed bit-level specification; tweak/domain-bit recoverability and distinct-prefix input separation checked |
| Algorithm 6, remaining §3.2.1–3 | Concrete primitives and PRG | Seed cipher formulas, tweak bounds/separation and Category-III padding/truncation specified; Algorithm-6 parse-width mismatch proved; SHAKE128/256 body and bit-equation refinement implemented, with padding/block/reader correspondence and BAVC hash instantiation; AES-128/Rijndael-256-256 bodies, byte-field correspondence, key schedules, full keyed permutations, SDitH bit packing and concrete BAVC primitives proved, with primary-source examples checked; literal partial PRG body, least block count, finite loop/stream correspondence, bounded sampling and concrete BLC family checked; undefined denominator, absent-tweak case and Category-III parse remain unresolved |
| §3.2.2 pp. 18–19 | Field sampling, ExpandH and matrix/batching challenges | Byte sampling and increasing matrix loops formalized; full polynomial-basis decoding family with explicit byte order, round trips, used-byte recovery, binary/extension uniform laws and joint batching law connected to detailed PIOP; finite PRG output, actual SHAKE consistency bits and concrete two-call SHAKE batching layout/ranges checked; byte order, consumption policy and cryptographic distribution claims remain unresolved |
| §3.2.2 p. 18 | SampleIntegers | Full staged vector loop with optional fixed B binding, exact attempts and pending/undefined/returned outcomes; completion stability, literal nonempty no-return, universal acceptance for power-of-two ranges and exact fixed-binding output/cursor proved; previous bijection, threshold and uniform-prefix laws retained; B is not replaced by v |
| §3.2.2 pp. 19–20 | Hash/cipher evaluation challenges | Actual SHAKE, integer loop and binary grinding; hash missing-B, fixed-binding output and offsets proved; complete staged cipher body composes material read, optional parse/MapToBits/Extract interpretations, actual cipher xor and fresh final SHAKE; precise source boundaries, returned challenge provenance, fuel stability and missing-B obstructions checked through retry/signing/verifier callers; intended interpretations, counter representation and security remain unresolved |
| Algorithm 7 | Seed tree and BAVC commitment | Full construction, tree/initialization/recursive agreement proved; exact fixed-width serialization injectivity and computable two-layer hash-collision finder checked; adaptive hiding/binding probability bounds pending |
| Algorithm 8 | BAVC opening | Literal queue algorithm, termination, legal-input memory/queue safety, exact successful padded length, and concrete 35-step opening trace checked; general reveal/reconstruct correctness not established |
| Algorithm 9 | BAVC reconstruction | Full staged typed-input body through both hashes and exact row instrumentation checked; equal-root successful reconstructions with inconsistent commonly revealed seeds yield a computed hash collision or same-index seed-commitment collision. The seed collision gives two matching Enc* outputs under different seed keys at distinct tweaked inputs. Category-I opening rejection and undefined nodes/alias boundary remain; probabilistic binding and intended reconstruction correctness unresolved |
| §3.2.5, equations (4)–(5) | Gray encoding and optimized folding | Gray-row injectivity, consecutive and boundary one-bit transitions, prefix telescoping, optimized/direct fold equality; binary/Gray merge injectivity, exact pointwise equality iff all indices<2, common zero test/image/cardinality and uniform-index pushforward law checked in submitted fields; source encoding selection and concrete operation-cost accounting pending |
| Algorithm 10 | BLC commit | Composed seed tree, PRG-byte sampling, actual Gray folding, positive corrections, typed hashes, consistency-XOF sampling and line construction; constants/degrees derived; integrated evaluation agreement proved for phi-based challenge; actual cipher/SHAKE/PRG-stream family, finite PRG calls and submitted tweak bounds checked; typed-hash serialization, Category-III PRG parse and recomputation correspondence pending |
| Algorithm 11 | BLC random opening | Actual BAVC retry with partial hash and staged cipher expansion; refinement to prior partial/total models, genuine expansion/opening/header provenance and stable returns proved; source boundaries retain current counter; hash caller and cipher caller with earlier interpretations supplied reach missing B at counter zero; binary/Gray maps preserve retry observations; source repairs, overflow policy and security remain unresolved |
| Algorithm 12 | BLC recomputation | Staged prefix through line 20 and separate suffix lines 22–27; actual reconstruction, folds, sampling and hash layouts checked. Two successful prefixes and equal concrete suffix line digests give equal BAVC roots or collisions on exact Hashlines/Hashaux queries, without serializer injectivity. The Hashaux/Hashlines chain now executes as an oracle program after the complete ordered reconstruction on the shared hash/cipher model, with a proved full/III equal-line-digest disagreement bound including both chains' queries. Two successful chains with equal line digests and different hidden indices at an execution determine a unique complete leaf-seed vector by pointwise merge, except on that bounded event. Under explicit extractor bindings the lines 9–16 fold at any hidden index is affine in its Gray row, with the honest-correction slope equal to the committed accumulator. The suffix values under those bindings split into slope terms and intercept psi; under a candidate binary reading of line 21, two challenges differing at a Gray bit force the masked slope to equal the plain check. Over a uniform binary mask, a fixed nonzero vector is in the kernel of [I|M] with probability at most 2^-(lambda+B). An adaptive lazy-oracle procedure sees a mask annihilating the fixed nonzero vector of its own query input with probability at most budget*2^-(lambda+B). The trap bound extends to predicates depending on the table before each fresh query, with the fresh-entry correspondence and table growth proved. A fresh answer equals a value mentioned by an earlier fresh input with probability at most choose(budget,2)*m/|Output|. Hash and mask components of a product-valued lazy oracle carry the mask trap and digest mention bounds. A stored dependency chain is present before its sink was answered or a fresh digest hit a mentioned value. The concrete chain strings are pairwise distinct with a tau+2 mention parser, giving per-execution present-or-mention at mask time. Chained claims with one auxiliary digest are unique on slope-relevant components in a collision-free table, and digest collisions are bounded by choose(budget,2)/|Digest|. The standalone slope-consistency game has the bound tau^2*budget*2^-s + choose(budget,2)*(tau+3)/2^(2*lambda) under explicit injectivity hypotheses. The shared hash/cipher execution now carries the fresh-query log with exact projection and both trap bounds. An unobserved key matches both halves of a commitment with probability at most 1/(M-q)*1/(M-(q+1)), with the union over candidate keys. In the shared model with CommitSeed through the family, a winning slope-inconsistency run raised one of five bounded events. The shared-model slope-consistency bound is proved with no commitment-injectivity hypothesis. The instrumented two-phase shared execution carries the log invariants and both trap bounds with budget q+k. With the named commitments executed as a second phase, the slope-consistency bound needs no queried condition. A named candidate middle for lines 9–21 is proved to yield the affine share matrix and the masked-slope base. Line 21, missing seed/share bindings, omitted witness correction, raw/Gray interpretation, complete recomputation and full binding remain unresolved |
| Algorithms 13–14 | Flat witness parsing and masking formula | Typed array parsing and mask computation formalized; evaluation agreement and mask degree bound checked |
| Algorithms 15–16, equation (6) | Unitary arithmetic and packing | Computation, evaluation agreement and quadratic witness-line bound proved; D(Y)=0 iff at most one binary coordinate is nonzero; packed-loop equivalence and exact uniform cancellation probability proved in submitted fields; printed degree-one annotation refuted |
| Algorithms 17–18 | Mux tree | Displayed mathematical recurrence formalized with safe indices; evaluation/degree and commutation with linear batching proved; tensor coordinate order and pseudocode index discrepancies remain |
| Algorithms 19–20 | PIOP run | Full post-challenge composition with Algorithm 21 and flat parsing formalized under explicit chunk-size equality; evaluation/degree, exact constant-term batching law and detailed consistent-opening comparison bound proved; zero-constant claim refuted on a valid small SD instance; full signature/challenge integration unfinished |
| Algorithm 21, equations (7)–(9) | Block embedding and syndrome batching | Typed `[I | H′]` algorithm, zero-padded formula, residual identity and injectivity proved; exact 2^(-lambda) cancellation probability for each fixed nonzero residual under uniform coefficients in all Table-2 fields; concrete challenge/primitive integration pending |
| Table 2 | Concrete extension representation | Exact quotient polynomials, power bases, full coefficient linear isomorphisms, irreducibility, field instances and cardinalities checked; byte decoding bijections and sampling laws proved for an explicit ordering; selecting the external representation and concrete primitive integration remain unfinished |
| §4.1 | Parameter selection | Literal integer dimension formulas formalized; exact average-fiber density, logarithmic/ceiling criterion and byte-aligned maximum proved; SD floor and RSD theta-sign counterexamples checked; Table-4 tree-size/grinding disagreement with p. 39 prose retained; greedy arity optimality and full hardness calibration remain unfinished |
| §4.2–4.4, Tables 1–6 | Concrete parameters, dimensions, sizes, benchmarks | Complete Tables 4/5 key/signature size columns match printed formulas; all degree-four numerical budgets checked; necessary fixed-width injective key-codec capacity bounds proved for actual typed key spaces; four-bit Category-III key slack explicit; Table-6 reported timings/metadata isolated as empirical data with row correspondence checked; raw codecs, timing validation and security interpretation remain unresolved |
| §5.1 | SD-to-RSD reduction and bound | Actual joint input/permutation/solver experiment and output-law equality proved; exact conditional-product success bound and combinatorial first-factor lower bound connected to the reduction; conditional return correctness and fixed-witness counting retained; instance-event equality refuted; correct selective solver gives zero conditional uniqueness with positive return mass under planted-uniform inputs satisfying the density condition, so that heuristic is not a universal bound; final theorem, induced-distribution correspondence and runtime remain unproved |
| §5.2 | Concrete hardness estimates | Human/empirical boundary |
| §5.3 | Explicit models and end-to-end EUF-CMA reduction | Bounded adaptive game, typed record/final-test correspondence, exact cut/resume distribution, fresh-query provenance and uniform-index selection proved. With forgery e, positive action budget q, guessing term delta and actual fork mass F, max(e-delta,0)^2 <= q^2*(F+delta); typed SDitH delta=2^(-2*lambda). Successful forks give two accepted fresh-message attempts at one input with distinct tested digests. Honest signing secret is still used. Witness-free signing simulation, commitment security, usable challenge separation, RSD extraction, costs and concrete/ROM correspondence remain open; end-to-end EUF-CMA proof absent from source and unfinished here |
| §6, Tables 7–10 | F256, TCitH, simple variants | All tables/size formulas, rounding/percentage intervals and numerical budgets checked; scaled witness encoding/count/weight and composed arithmetic evaluation/degree/constant-term/uniform comparison bounds proved; zero amplitudes fail regularity but pass the all-zero arithmetic instance; injective Table-7 packing needs at least four large-field elements, so unchanged binary packing has a nonzero batching kernel; full variant protocols, nonzero-value enforcement, concrete field embedding/serialization and security remain unspecified or unfinished |
| §7 | Advantages and limitations | Human/empirical boundary |
| All final theorems | Kernel and transitive axiom audit | Three discrepancy statements; `scripts/check.py` audits all project declarations, not merely this interface |

`source/index.json` inventories all 21 numbered algorithms and their PDF/printed
page locations, with the actual specification/proof boundaries. A computation
being formalized does not certify every source annotation or its integration into
the signature scheme. No small fragment is marked as a whole algorithm.

`Proofs/UniformChallenges.lean` connects the root-count and linear-kernel results
to explicit PMF uniform samplers. `Proofs/BatchingProbability.lean` applies the
exact linear cancellation law to the actual padded Phi embedding and Algorithm
21 equation. It makes no claim that concrete hash/XOF challenges have this law.

`Proofs/PIOPChallenges.lean` derives the substitution/output degree bounds and
the equation-(3) cancellation probability. Its two-challenge PMF experiment
allows a randomized response after gamma, followed by a fresh uniform delta.
For fixed committed lines violating a constraint, bounded response degree and
consistent evaluations, acceptance is at most 1/q + (1-1/q)(d+1)/|S|. This
preserves the extra delta in the literal verifier. Commitment binding, knowledge
extraction, zero knowledge and Fiat–Shamir integration are not established.

`Proofs/PIOPSoundnessDiscrepancy.lean` proves that the printed d-based bound fails
for the introductory protocol. With f=1, P0=P1=X, d=2, P_alpha=gamma*X^2+X and S
the three cube roots of one, acceptance has probability one, while the printed
bound is strictly smaller. Degree conditions, binary constant coefficients,
binary origin of the constraint and absence of any valid witness are proved.
The cube-root set has cardinality three in each actual Table-2 field. This is
not a claim about the detailed BLC challenge domain or a signature execution.
`Proofs/SamplingModel.lean` still only proves solvability of the proposed
planted-instance distribution.

The detailed PIOP modules have no assumed correctness contracts for formatting,
unitary checks, mux trees, or syndrome batching. Their implementation formulas
are expanded and their properties are derived. The remaining source discrepancies
are still obstacles to transferring those local identities to the whole scheme.

The seed routines take only the cipher and hash as primitive function parameters;
their displayed seed expansion and commitment formulas are explicit. No security
properties of these functions are presumed. The modulo in `callTweak` is only
an extension outside the source's tweak precondition: `callTweak_exact` and
`submitted_tweak_bounds` certify that the source seed-call ranges need no reduction.
The Category-III padding/truncation formula does not claim the truncated cipher
is a permutation. Concrete SHAKE and AES/Rijndael bodies now instantiate this
boundary in `Spec/CipherPrimitives.lean`. `Spec/PRG.lean` and
`Spec/ConcreteBLC.lean` now supply the counter body and BLC primitive family,
with Algorithm-6 source gaps and structured serialization still explicit.

`Spec/BLCArithmetic.lean` explicitly starts with expanded PRG values and an
expanded consistency matrix. Its correctness lemmas use the Gray/phi row in
each execution and a nonzero merged challenge for inversion. They neither
assume that raw indices have that encoding nor establish that the literal
Algorithm 12 computes those corrected openings. `psi` is implemented by its
power sum and proved linear. `Proofs/ConcreteEncodings.lean` now proves its
injectivity in the exact Table-2 quotients when tau*kappa fits their dimension;
both submitted proof-parameter tables satisfy that bound. This does not resolve
the raw-index/Gray encoding discrepancy or establish that Algorithm 12 computes
the required challenge inversion.

`Spec/BLCRetry.lean` models finite observations of the literal retry loop. Fuel is
an observation limit, not a source abort rule. A returned result is the first
passing counter, and additional observation cannot change it. Legal BAVC inputs
exclude undefined tree/queue operations; the unspecified 32-bit overflow remains
explicit. Challenge expansion and raw-index encoding are still function inputs,
not assumed-correct implementations. Conditional success does not prove that
every input has a passing counter.

`Spec/ByteSampling.lean` takes an initialized byte stream, an explicit consumed
byte count and, for extension fields, a decoder. The matrix loop uses a common
specified count per row/column call. Its layout theorems do not choose a missing
consumption or buffering policy, instantiate a field basis, or prove randomness.
The binary encoding is checked by byte decomposition and whole-byte recoverability.
The full coefficient isomorphism and an explicit-order decoder family are now
proved for the submitted quotients, with the uniform-input integration described
below. Choosing the source's unstated byte-to-coefficient convention and proving
concrete PRG/XOF distributions remain separate obligations.

`Spec/WitnessExpansion.lean` transcribes Algorithm 1 after sampled positions are
available, retaining the final quotient rather than silently truncating positions.
The flat solution uses original positions and has length w*m. The mixed-radix
inverse fixes the first processed radix as least significant. Serialized witness
injectivity requires m at most the radix product; that inequality and whole-chunk
sizes are checked for Table 3, without asserting the false required equality.

`Proofs/WitnessPIOPDiscrepancy.lean` connects this expansion to the actual detailed
PIOP flat parser. With radices (3,3), one chunk, sampled position 0 and the
one-row systematic matrix [1,0,...,0], the generated solution is an exact-weight-one
SD solution. Its stored witness is [1,0,1,0]. Constant witness lines and zero
randomness yield P_alpha(0)=-1, for every field generator and unitary batching
challenge. This is a delimited arithmetic counterexample, not a submitted
parameter row, reachable-BLC-distribution claim, or full signature execution.

`Spec/FieldRepresentation.lean` defines the exact Table-2 quotient rings without
installing an unproved field instance. Monicity gives their power bases, which
are used to prove injectivity of both the actual psi map and the entire padded
Phi map. These proofs do not assume the encoding properties they establish.
`Proofs/FieldIrreducibility.lean` now proves irreducibility and installs the field
instances, with exact cardinalities. A general Frobenius factor-degree criterion
and a proved binary-polynomial interpreter connect the generated repeated-square
and Euclidean-remainder transcripts to that result. All certificate arithmetic
uses ordinary kernel-checked `decide`; the Python generator is untrusted.
Irreducibility is no longer an outstanding assumption or proof obligation.

`Spec/UnitaryPolynomial.lean` keeps the selector polynomial D(Y) distinct from
the witness-line polynomial in X. Its off-diagonal coefficients give the full
binary at-most-one characterization. Coefficient blocks of size 32 are proved
disjoint, and the packed polynomial has degree below each actual modulus under
the submitted bounds. The resulting equivalence is linked to the recursive
unitaryLayers computation in Algorithms 19/20. It is deterministic algebra;
its uniform batching distribution is now proved separately. End-to-end soundness
remains unfinished.

`Proofs/UnitaryProbability.lean` establishes exact 2^(-lambda) cancellation for
any fixed invalid binary selector collection. Its affine form also covers an
arbitrary fixed syndrome/mux offset. `Spec/PIOPComposition.lean` actually composes
Algorithm 21 with Algorithms 13/14 and 19/20 after challenge expansion. The
column address uses the explicit equality leafCount(widths)*w = r+k; Table 3
does not satisfy this premise. No padding or repaired dimensions are inserted.

`Proofs/MuxLinearity.lean` commutes linear batching with the literal mux
recurrence. The resulting base-field mux syndrome residual is computed, not
assumed to be the intended SD relation. `Proofs/PIOPComposition.lean` derives
the output's constant term as the sum of the syndrome and unitary batches.
Under two fresh independent uniform challenges, its probability of being zero
is exactly 2^(-lambda) whenever either constraint vector is nonzero, and is one
when both vanish. Polynomial evaluation agreement and degree bounds include
this actual composition.

`Spec/DetailedPIOPChallenges.lean` records a separate algebraic comparison
experiment for Algorithm 20's evaluation formula. With consistent openings,
an invalid literal constraint vector, line degrees at most one, and responses
of degree at most d, its acceptance is at most 2^(-lambda) +
(1-2^(-lambda))*d/|S|. Responses may be randomized after both batching vectors,
before a fresh uniform delta. `Proofs/DetailedPIOPChallenges.lean` proves this
from the preceding exact constant-term law and the root bound. The comparison
event includes a zero response constant; it does not implement the signature's
coefficient hash check or assume its binding. This detailed formula differs
from the literal introductory verifier with its extra delta. It does not undo
the refutation of the introductory bound or prove EUF-CMA security.

`Spec/CoefficientCompression.lean` implements the exact increasing coefficient
arrays, higher-degree evaluation sum and omitted alpha_1 recovery of Algorithms
3/4. `Proofs/CoefficientCompression.lean` proves that a degree-bounded polynomial
reconstructs alpha_1 + delta^(-1)*alpha_0 at nonzero delta. Recovered and hashed
tuples agree iff alpha_0=0; the transmitted nonconstant coefficients represent
the polynomial with its constant removed. `Proofs/CoefficientDiscrepancy.lean`
applies this to the already proved valid small SD witness counterexample, giving
different coefficient tuples at every nonzero challenge. This is not an assertion
that unequal typed inputs yield unequal serialized bytes or hash outputs.

`Spec/SignatureComposition.lean` records Algorithm 3's preparation/assembly and
Algorithm 4 after BLC recomputation, including actual PIOP evaluation and hash
comparison. Its signing observer uses the real Algorithm-11 implementation;
return/header and BAVC-opening properties are derived. Pending execution and
unspecified overflow stay distinct. Messages are arbitrary bit strings. Exact
committed evaluations are used only in clearly delimited comparison theorems,
not substituted for the actual unresolved Algorithm-12 result.

`Spec/BLCCommit.lean` composes Algorithm 10 from the actual BAVC seed tree,
initialized PRG byte streams, binary sampling, Gray rows, fold/corrections,
typed Hashaux input, consistency-XOF matrix and line construction. The transmitted
corrections contain precisely execution indices 1,...,tau-1. Hashlines includes
the printed witness correction. Typed hash serialization and concrete primitive
implementations remain boundaries; no cryptographic properties are assumed.
`Spec/Signing.lean` composes signing phases 1–3 from this commitment, and its
proofs derive line degrees and the coefficient/hash-input condition through the
actual construction. Decoded keys, expanded H', salt and root seed are supplied
at the initialization boundary. Full keygen/sign/verify and security are still
incomplete, including the recorded source contradictions.

`Spec/IntegerSampling.lean` executes SampleIntegers through its first accepted
candidate, before the undefined B % m assignment. The result is a candidate,
not a returned sampled integer or vector. Its four-byte little-endian encoding
is bijective and each original byte is recoverable. `Proofs/IntegerSampling.lean`
proves the largest-multiple threshold, discarded-word count below m and below
half the bound, exact four-byte cursor accounting and stability of a found
candidate. An all-zero stream reaches the undefined assignment after the first
read for every legal positive range; no PRG behavior is claimed by that example.

`Proofs/IntegerSamplingProbability.lean` proves that four independent uniform
bytes give a uniform word, exact threshold acceptance/rejection probabilities,
and equal-size residue classes below the threshold. The uniform law of v % m
on that accepted range is a separate mathematical theorem. It does not assign
a meaning to the source's B or certify the unfinished literal SampleIntegers,
position-vector generation, or concrete PRG/XOF distributions.

`Spec/RegularSupport.lean` records regular supports and the permutation action
on a fixed weight-w support in w chunks of size m. `Proofs/RegularSupport.lean`
counts them as m^w among choose(w*m,w) supports. `Proofs/PermutationProbability.lean`
constructs equal-size permutation fibers and derives the exact uniform image
law. No uniformity of the image is assumed. `Proofs/SDReductionProbability.lean`
transfers the ratio to flat finite-field vectors under the explicit coordinate
equivalence, and gives the resulting lower bound for regular-instance existence.

`Spec/SDReduction.lean` specifies all steps of the displayed randomized A_sd:
uniform permutation, column movement, last-row truncation, supplied randomized
solver, full syndrome check, failure propagation, and inverse coordinate movement.
`Proofs/SDReduction.lean` checks weight and syndrome preservation, exact removed
row count under source parameter inequalities, survival of full solutions under
truncation, successful-return characterization, correctness given regular solver
outputs, and the deterministic uniqueness step. The full randomized return
correctness theorem uses an explicit solver-correctness premise. It supplies
no unproved conditional success probability or uniqueness law.

`Proofs/SDReductionDiscrepancy.lean` separates the counted fixed-witness event
from regular-solution existence for an actual binary SD instance with H=0, y=0,
n=4, w=2, k=1. The latter has probability 1, strictly above the former's 4/6.
This is a counterexample to the pointwise instance-event equality, not a proof
or refutation of the final Theorem-5.1 inequality. Its heuristic conditional
uniqueness step, solver distribution, and runtime claims remain open.

`Proofs/FieldIsomorphism.lean` establishes the full linear isomorphism phi of
printed p. 34 in each Table-2 quotient, with both coefficient round trips.
`Spec/FieldBytes.lean` defines a family of polynomial-basis byte decoders whose
byte/bit-to-coefficient ordering is an explicit equivalence. The binary sampling
bit order is specified by the PDF; the extension-field byte ordering is not.
`Proofs/FieldBytes.lean` proves byte-pack bijectivity, exact power-sum formulas,
round trips, sampled-byte recovery and actual sequential batching layouts.
Its named little-endian order is only a comparison option, never a default.

`Proofs/UniformVectors.lean` proves joint uniformity after selecting distinct
positions of a finite uniform vector. `Proofs/FieldByteProbability.lean` uses
that law with the actual decoder and reader: single extension elements, vectors,
and both sequential batching vectors have the uniform law on their full spaces.
The consumption counts may include unused bytes; the proof checks disjointness
and stays inside the supplied finite array. `Proofs/FieldChallengeLaw.lean`
equates this byte-driven first stage with the existing detailed PIOP batching
model, preserving arbitrary later randomized computations.

`Proofs/BinarySamplingProbability.lean` also proves joint uniformity for the
binary sampling branch, including partial bytes and extra consumed bytes, and
for those bits interpreted as ZMod 2. These are explicit uniform-input laws.
They do not replace a concrete PRG/XOF by a random source or select an unstated
extension serialization or buffering convention.

`Spec/VariantParameters.lean` records Tables 8–10 and every displayed §6 size
formula, keeping tensor depth and constraint degree separate. The F256 sizes
match at degree four; using its three tensor layers as the degree does not
reproduce Table 8. TCitH and simple sizes match after byte ceiling; the simple
formula retains the printed final 32 bits despite the no-grinding prose.
`Proofs/VariantParameters.lean` checks all sizes and percentage intervals,
rounding properties, and the exact numerical error-budget inequalities. Those
budgets are proved equivalent to the rational error expressions; this is not a
claim that a protocol's soundness probability is bounded by them. Table 10 is
checked with explicit B=16, the value in the main proof-parameter table.

`Spec/ScaledWitness.lean` records §6.1 positions, nonzero values, their binary
position encoding and post-mux scaling. `Proofs/ScaledWitness.lean` identifies
these witnesses with all regular vectors, proves exact weight and selected-column
syndrome, recovers both positions and values, and counts (m*(q-1))^w regular
vectors. It connects to the existing tensor encoder, evaluation and linear
batching, and proves the extra degree from an amplitude line. The literal mux
convention is retained, with its known witness-indexing conflict unresolved.
`Proofs/ScaledMuxDegree.lean` gives an explicit [4,4,4]-arity example of degree
four over any field; its amplitude line has nonzero constant one.

The source calls §6's variants outlines for possible future formal instances.
It supplies no full variant keygen/sign/verify bodies, complete TCitH commitment
construction, or nonzero-amplitude constraint. These omissions remain visible
in the human-review ledger, with no invented implementation or assumed security.

`Spec/ScaledArithmetic.lean` specifies the outlined post-mux scaling with the
actual flat position/randomness parsers, unitary loops, mask and Algorithm-21
batching. Amplitude lines are separate from binary position lines; no scalar
bit decoder is invented. Tensor depth, mask degree and syndrome packing width
are separate parameters. The literal first-default mux is retained.

`Proofs/ScaledArithmetic.lean` proves raw-vector regularity iff every amplitude
is nonzero, evaluation agreement through the complete arithmetic composition,
degree at most the explicit degree parameter when it covers tensor depth plus
one, commutation with linear batching and the exact constant-term identity.
For zero syndrome, all-zero position/amplitude/randomness lines produce the
zero polynomial for every matrix and both challenges. For a positive number
of chunks the associated raw vector is not regular. This demonstrates the
missing arithmetic enforcement; it is not a full F256 verifier counterexample.

The fresh-uniform experiments fix all lines before sampling the two independent
batching challenges. `Proofs/ScaledArithmeticProbability.lean` derives exact
1/|F| cancellation if the packed syndrome residual or actual unitary vector is
nonzero, and probability one if both vanish. Its adaptive randomized polynomial
comparison bound is 1/|F| + (1-1/|F|)*degree/|S|. It derives the prover degree,
first-stage law and verifier evaluation from the implementations, but does not
claim the source's intended witness equivalence, injective F256 packing,
commitment extraction, a concrete XOF sampling law, or signature security.

`Proofs/ScaledPackingBoundary.lean` proves a representation-independent capacity
obstruction for all Table-7 rows. Any injective encoding into F_(2^lambda)
elements requires at least four such elements. The unchanged binary block-count
formula yields only one, so no map of that shape is injective. The actual
linear formula consequently has a nonzero kernel vector missed by every gamma.
The outline does not uniquely specify that adaptation: this is an obligation
for its missing packing definition, not an assertion of a full protocol attack.

`Spec/Keccak.lean` transcribes FIPS 202's 1600-bit, 24-round function, with
literal bit equations and a materialized 25-lane implementation. The proof module
checks lane/string round trips, rotations, the complete rho orbit and offset
table, the feedback-register recurrence, round-constant placement, all five step
mappings and their composition through all 24 rounds. No permutation-bijectivity
or cryptographic security theorem is asserted here.

`Spec/SHAKE.lean` supplies actual SHAKE128/256 for arbitrary bit strings, the
1111 suffix, rate/capacity choice, padding, absorption and squeezing. Its proofs
establish the integer padding formula, positive divisible padded length, exact
block reassembly, in-bounds block reads, capacity-bit preservation, fold/loop
correspondence, finite squeeze-loop/prefix agreement and output length
independence. Hash widths and the concrete byte reader are connected to the
existing binary sampler. `Spec/HashPrimitives.lean` instantiates BAVC's already
specified domain-prefix/array hashing with SHAKE and leaves Enc* explicit.
Structured field/counter/transcript serialization remains a separate boundary.

`Proofs/SHAKEExamples.lean` collects generated certificate modules for the NIST
empty, 5-bit and 1605-bit examples of each SHAKE function. Each checks the full
absorption trace (all five steps in all 24 rounds of each absorbed block) and
the first 64 output bytes using ordinary decide. The remaining published output
bytes are stored as source data; they are not part of these example theorems.
The generic squeeze-loop correspondence covers arbitrary output lengths.
`Proofs/KeccakConstants.lean` certifies the 169-state feedback-register orbit
and all 24 round constants once for reuse. `Proofs/SHAKEReading.lean` proves
the exact padding delimiter positions for efficient concrete input checks.
The example proofs use `decide +kernel` and disable asynchronous proof checking;
no native evaluation result is admitted into the logic. Source PDFs, hashes and
extraction metadata live in `source/standards/`.
Functional SHAKE conformance never substitutes for the explicit ideal-oracle
model or for a proof of the signature scheme's correctness/security.

The fifteenth full audit passed with 3258 build jobs and 8656 project declarations.
All six SHAKE example certificates passed; the axiom whitelist remains the three
foundational axioms. This is verified partial coverage, not completion.

`Spec/RijndaelByte.lean` records the exact X^8+X^4+X^3+X+1 quotient,
byte coefficient representation, xtime, distributive multiplication, affine
transform and literal FIPS S-box table. Its proof establishes the full byte/field
bijection, XOR/addition and multiplication correspondence, the root reduction
identity and every nonzero inverse. The quotient's 256-element field structure
is derived from kernel-checked inverse witnesses after the representation and
multiplication theorems, without assuming irreducibility. All 256 S-box entries
satisfy the unique inverse-and-affine relation; its affine bit formula and inverse
table are checked for every input. The generator proposes witnesses only.

`Spec/Rijndael.lean` contains the full AES-128 and Rijndael-256-256 byte bodies,
including distinct 4/8-column states, 10/14 rounds, 1/2/3 versus 1/3/4 row shifts,
44/120 expanded words, the wide-key extra SubWord step and omission of MixColumns
in the final round. Matrix identities over the actual byte field establish
inverse column mixing; every step and the entire fixed-key cipher are proved
bijective. `Proofs/RijndaelSchedule.lean` proves prefix preservation, the full
backward recurrence in the completed key schedule, initial-key recovery and
positive Rcon indices. No out-of-bounds read is given an invented value.

`Spec/CipherPrimitives.lean` supplies bit packing in the existing low-bit-first
convention, the explicit FIPS within-byte reversal, Table-1 Enc/Enc* choices and
BAVC primitives with actual ciphers and SHAKE. Its proof gives both packing round
trips, full-block keyed permutations, Enc injectivity in all categories, and
Category III's exact 192-bit prefix of its 256-bit output. Enc* in Category III
is not asserted to be a permutation. The 64 padding bits remain explicit.

`Proofs/AESExample.lean` checks the full FIPS Appendix-B key expansion and every
displayed SubBytes/ShiftRows/MixColumns/AddRoundKey state, then derives the final
ciphertext from the actual encryption function. `Proofs/Rijndael256Examples.lean`
checks both full-width designer-published Appendix-D.3 examples: encrypt zero
under zero key, then encrypt the result again. All checks use kernel reduction.
The three additional primary reference PDFs are hash-pinned and their visually
reviewed pages are listed in `source/standards/index.json`.

Functional cipher conformance does not establish uniform keyed-permutation laws,
PRG security, commitment binding/hiding, zero knowledge or signature security.
The source discrepancies and missing whole-protocol proofs remain open.

The sixteenth full audit passed with 3268 build jobs and 9142 project
declarations. All AES/Rijndael certificate and example modules passed, alongside
the prior SHAKE examples; the transitive axiom whitelist remains exactly
propext, Classical.choice and Quot.sound. Whole-submission coverage is incomplete.


`Spec/PRG.lean` transcribes the Algorithm-6 loop using actual Table-1 Enc.
Its positive `BlockSize` parameter supplies the undefined denominator without
choosing a default. `ParseShape` retains the printed byte count. `run` is only a
partial source transcription: missing salt/tweak data, a shape mismatch or an
undersized assignment yields no interpretation, not a submitted rejection.
The complete byte parse is impossible for every positive Category-III request.
The ciphertext stream is separately defined and is not called a repair.

`Proofs/PRG.lean` proves the least covering block count, exact byte packing,
indexed-vector/append-loop correspondence, output existence characterization,
prefix stability and Category-I/V execution for an explicit size bound.
`Proofs/PRGSampling.lean` proves bounded finite-reader agreement through binary
sampling, explicit-order field decoding, increasing row loops and ExpandH's
printed column loop. Every finite reader has its full length explicitly typed;
no proof reads its zero extension as if it were generated randomness.

`Proofs/PRGCounter.lean` derives block equality modulo 2^lambda from actual Enc
injectivity, counter uniqueness below that modulus and exact stream periodicity.
Tweak/counter pairs are jointly recoverable for counters below 2^16. Without
that bound, tweak 0/counter 2^16 and tweak 1/counter 0 give identical plaintexts
and ciphertexts. No signature attack or cryptographic distribution is inferred.

`Spec/ConcreteBLC.lean` instantiates the existing BLC interface with concrete
Enc*, SHAKE hashes/XOF and the PRG ciphertext stream. Hashaux/Hashlines preserve
the source's component order and include the witness correction at line 24.
Vector/matrix wire encoding functions remain explicit. The Nat execution
interface has a documented zero extension outside 0..255; all execution ranges
in Tables 4/5/8/9/10 are checked to avoid it. Successful finite PRG calls agree
with the folding table's bits, and consistency-matrix coordinates agree with
actual SHAKE bits. Category III's infinite stream is not identified with an
Algorithm-6 execution. No serializer contract or security property is assumed.

The seventeenth full audit passed with 3274 build jobs and 9348 project
declarations. The only transitive axioms remain propext, Classical.choice and
Quot.sound. Specification and assumptions remain separate entry points, and
Final.lean retains exactly three discrepancy statements. Whole coverage is
incomplete; this audit certifies the current proofs, not source completeness.


`Spec/KeyGeneration.lean` supplies staged Algorithm-2 definitions: independent
uniform seed draws, actual Algorithm-1 expansion after sampled positions,
concrete unsalted ExpandH, the [I|Hprime] syndrome assignment with an optional
external x_A binding, typed public/secret fields and explicit serializer
functions. None for missing x_A means an undefined source read, not a rejection.
The actual generated vector is retained and is not substituted for x_A.

`Proofs/KeyGeneration.lean` proves the seed-pair uniform law, point probability
2^(-2*lambda), and independence of arbitrary deterministic expansions as their
actual pushforward laws. No expanded matrix or witness distribution is declared
uniform. The concrete matrix has the proved column/byte layout and agrees with
successful finite PRG outputs. Generated witness length and exact vector weight
follow from the actual Algorithm-1 body. The flat length cast only requires
r+k=w*m, not the false Table-3 tensor-size equation.

The prose [Hprime|I] and algorithm [I|Hprime] are related by a named block swap,
which is not applied to the submitted routine. A 1-by-2 binary example proves
that keeping the same coordinate order can change the syndrome. For an actual
typed return with externally supplied x_A, the generated vector is an exact
weight-w SD solution iff [I|Hprime]*(x_A-x)=0. This necessary-and-sufficient
condition is derived, not assumed as an algorithm correctness contract.
Typed secret/public initialization reconstructs the same matrix using the same
seed and byte-consumption count. Raw deserialization, public-key reconstruction
inside Algorithm 3, whole-parameter integration and the source gaps remain open.

The follow-on key-generation audit passed with 3276 build jobs and 9490 project
declarations. All new modules are included in the root audit; the axiom whitelist
and three-statement final interface are unchanged. This remains partial coverage.


`Spec/BAVCReconstruction.lean` now transcribes the complete staged Algorithm-9
body from a typed opening. Prefill initializes an empty partial tree, traverses
the literal queue, checks the printed capacity guard, extracts exactly lambda
bits only when available, and tests the remaining padding. Termination uses
queue-address sum. Explicit capacity/padding rejection tags are distinct from
undefined queue, address, path, undeclared-array or empty-node operations.

Expansion tests the locally prefilled `tree` and separately reads/writes
`nodes`, exactly preserving the source's names. An optional external binding
exposes that missing variable without asserting its existence or an alias.
All loop bounds, parent/child addresses, interleaved leaf reads, hidden digest
selection, increasing leaf/row construction and two domain-separated hashes
are explicit. Length-indexed vectors prevent default-filled result entries.
The public `reconstruct` leaves nodes undeclared; `reconstructWithNodes` exposes
the binding as reviewable input without a correctness contract.

`Proofs/BAVCPrefill.lean` proves exact take/drop reassembly, complete-seed
consumption, legal queue/write safety and the padding predicate. The full-loop
result is stronger than the earlier first-branch check: at or above the printed
path bound, any successful traversal leaves the entire tree and path unchanged.
Consequently, any successful prefill of an actual Algorithm-8 padded opening
has an entirely empty tree and all-zero remaining bits.

`Proofs/BAVCReconstruction.lean` proves that expansion cannot invent a binding,
that every successful row/leaf is its actual ordered computation, that hidden
seeds are absent and their digests come from the opening, and that revealed
seeds/commitments come from actual node reads and CommitSeed calls. The complete
successful-output characterization carries the actual prefill, expansion and
row-run equations. With tau>0 and N>1, the literal undeclared-nodes body cannot
return a reconstruction: it rejects or reaches an undefined read. A checked
single-hidden-leaf case returns normally without ever reading nodes, showing
that this boundary is diagnosed at reads rather than turned into a blanket abort.

The Category-I 35-step opening trace is now connected to the full reconstruction
function's explicit capacity rejection, for all primitives, salts and supplied
nodes bindings. Final.commitment_discrepancies is strengthened to this full-body
statement; the interface still contains exactly three theorems. The rejection
occurs before any undeclared-array access, so it does not rely on how that later
source gap is interpreted. This is not a full signature execution or an attack
on a corrected reference implementation. Intended reveal/reconstruct correctness,
raw opening serialization and commitment security remain unresolved.

The eighteenth full audit passed with 3278 build jobs and 9749 project
declarations. The final commitment discrepancy now concerns the full staged
reconstruction body; the interface still has three statements and the same
three foundational axioms. Whole-submission coverage remains incomplete.


`Spec/BLCRecompute.lean` now executes Algorithm 12 through line 20 at typed
input and challenge-expansion/encoding boundaries. Its source environments
keep the undefined nodes, seed, rshare and phi_mu bindings explicit. Actual
reconstruction precedes ordered seed reads, binary PRG sampling and folding.
The initialized reval zero is distinct from the updated rshare. Positive-index
auxiliary corrections, Q concatenation, Hashaux, ExpandConsistencyChallenge
and multiplication by [I|M] follow the printed order.

`Proofs/BLCRecompute.lean` checks exact inner-loop sums from the real samples,
preservation of missing shares, outer-loop/concatenation coordinates and the
zero reval initialization. Its complete prefix-success characterization exposes
the actual reconstruction/folding/collection runs and constructed matrices;
header and inverse-challenge properties follow from those runs. The literal
absent-nodes prefix cannot reach line 21 for positive tau and more than one
leaf. Given the concrete Category-I hidden vector and a passing header, the
actual earlier opening fails at line 8 for every environment, with the exact
capacity-rejection cause retained as an undefined pair read.

Line 21 is an unresolved type boundary, not replaced by a chosen interpretation
of the scalar/binary-matrix subtraction. The independently specified suffix
computes lines 22–27 from an explicitly supplied base matrix. Its real SHAKE
hash layout has three components; the exact difference from the Algorithm-10
payload is the encoded witness-correction suffix. Raw/Gray challenge agreement,
missing source bindings, line-21 resolution, codecs, complete recomputation
and end-to-end correctness/security are still unproved.

The nineteenth full audit passed with 3280 build jobs and 10012 project
declarations, using only the same three foundational axioms. This count includes
generated/internal declarations and is a trust-audit scope, not a percentage of
submission coverage. Final.lean still has exactly three statements.


`Spec/IntegerSamplingVector.lean` now supplies the complete staged vector loop
around the existing four-byte candidate routine. States contain the actual
accumulated prefix, its checked length bound and the current reader. The loop
preserves rejected candidates, the read of undefined B on acceptance and the
source's final output condition. Pending observations, missing assignments and
returned vectors are distinct. No binding is supplied by the literal wrapper.

The new sampler proofs establish exact conversion of completed prefixes,
stability of returns, no literal return for nonempty requests, and threshold
equality to 2^32 for m=2^kappa with kappa<=32. Thus every first candidate passes,
for every stream. An external fixed B binding yields exactly n copies of B%m
after n attempts, with the reader advanced by 4*n bytes. This is a description
of that explicitly supplied environment, not the intended sampling law.

`Spec/ConcreteChallenges.lean` defines hash-based evaluation expansion using
actual SHAKE input concatenation, the full integer loop and the subsequent
binary grinding sampler. Its literal nonempty form cannot return; for the
submitted power-of-two ranges it reaches the missing assignment after the
first four-byte read. Under a supplied fixed B, exact returned hidden indices,
SHAKE grinding-bit offsets and reader positions are proved. Empty requests can
return without B, but no submitted row has zero executions.

The cipher path explicitly records its 4*lambda-byte material read, runs the
actual Enc* calls after a separately supplied parse, exposes the unspecified
single-subscript extraction and initializes the final SHAKE on all four source
components after supplied grinding bits. That index loop is retained even for
zero grinding. Counter-input dependence is proved for injective encodings;
no counter-independent material or hash-output inequality is assumed. Material
parsing, counter serialization/MapToBits and extraction remain review boundaries.

Concrete batching now uses the actual SHAKE and exact Table-2 coefficient
decoder, with an explicit byte-order equivalence. Both sequential sample
layouts, disjoint byte ranges and total cursor are proved. No deterministic
XOF is assigned the ideal uniform law. Partial evaluation outcomes are not
coerced into the existing total challenge function at the retry interface;
that caller integration, raw/Gray encoding, codecs, variants and complete
correctness/security remain unfinished.

The twentieth full audit passed with 3284 build jobs and 10217 project
declarations, with the unchanged foundational axiom whitelist and three-statement
final interface. The goal remains active and whole-submission coverage incomplete.


`Spec/ChallengeEncoding.lean` supplies named binary and Gray index-to-psi maps
with the source's most-significant-first row order and actual Table-2 generator.
`Proofs/ChallengeEncoding.lean` establishes binary row injectivity, a bijective
Gray relabeling of full index vectors, both merge injections under the basis
bound, and the exact pointwise equality condition: all indices must be below 2.
The inverse field points agree under the same condition. Constant index-2
vectors yield distinct nonzero points; both parameter-table families satisfy
the necessary bounds. These are explicit mathematical vectors, not asserted
outputs of challenge generation or complete signatures.

Both maps have exactly the all-zero vector as their zero preimage. The actual
BAVC retry attempt and all finite observations are consequently identical for
the same challenge sequence under either map, even where their nonzero points
differ. Their images coincide and have cardinality 2^(tau*kappa) under the
proved size bound. A separate uniform-index pushforward law follows by finite
relabeling. It does not make concrete SHAKE or grinding-selected outputs uniform.
The intended source encoding and Algorithm-12 line-21 conversion remain open.

`Spec/PartialBLCRetry.lean` integrates partial expansion into Algorithm 11 at
its actual call site. It preserves expansion pending/undefined states, invokes
the existing BAVC/encoding/grinding step only on returned challenges and retains
the bounded counter/overflow behavior. Refinement to the old total interface,
actual successful-return provenance and outer-fuel stability are proved.
The concrete hash-based caller starts at zero with the real SHAKE/integer body.
It cannot return for nonempty executions; with submitted-sized index ranges and
positive observation budgets it stops at counter zero's first missing-B read,
before any BAVC opening or retry. This is a literal-source result, not an ordinary
signature rejection or a claim about a repaired implementation. Full signing/
verification/cipher integration, codecs, variants and security remain unfinished.

The twenty-first full audit passed with 3288 build jobs and 10366 project
declarations. The three-statement final interface and foundational axiom whitelist
are unchanged. Whole-submission completion is still unproved and the goal is active.


Algorithms 3/4 now use the partial challenge and retry/recomputation interfaces
in Spec/PartialSignature. Signing's actual BLC/PIOP preparation feeds this caller.
Its returned signature contains exactly the prepared salt, digest, auxiliary,
higher coefficients and actual returned counter/opening. Returned challenge,
BAVC success and passed grinding/nonzero checks are proved as provenance; an
increase in outer observation fuel preserves a return. Supplying genuinely
returned challenges refines the earlier total signing interface.

The verifier prefix calls expansion at the parsed signature's digest/counter.
Returned expansion refines the existing staged Algorithm-12 prefix. Reaching
the consistency boundary implies the actual prefix succeeded and delta is
nonzero; absent source bindings prevent such a boundary on nonempty trees.
The explicit header-bottom outcome becomes Reject. Reconstruction errors remain
undefined tuple reads with their actual causes. They are not silently mapped
to the source rejection branch. The separate suffix combines Algorithm-12
lines 22–27 with Algorithm-4 PIOP, coefficient recovery and exact final digest
comparison, conditional on an externally supplied base matrix.

For nonempty execution sets, the concrete hash signer cannot emit a signature.
Its positive observation budgets and kappa<=32 reach missing B at counter zero.
The concrete verifier reaches the corresponding missing assignment at the
transmitted counter, before any header/reconstruction test; it neither reaches
the consistency boundary nor returns an explicit rejection for any finite fuel.
These are literal-source partial-execution results. Successful complete signing/
verification, Algorithm-12 line 21, cipher parsing/extraction, byte codecs,
variant protocols, and end-to-end correctness/security remain unresolved.

The twenty-second full validation passed: 3290 build jobs and 10511 project
declarations, with only propext, Classical.choice and Quot.sound in the
transitive axiom audit. No proof placeholders, custom axioms or unchecked
shortcuts were introduced. Whole-submission completion remains unproved;
the persistent goal stays active.


Spec/IntegerSamplingTrace projects complete finite sampler observations to their
actual result tags, values, cursors and offending candidate value. It omits the
unconsumed stream function rather than claiming equality of different infinite
tails. The trace depends only on four bytes per observed attempt, for arbitrary
ranges, fixed external bindings, prefixes and rejection sequences. Successful
finite Algorithm-6 outputs covering that bound yield equal traces with the
actual cipher stream. No zero-extension byte outside the bound is needed.

Spec/PartialKeyGeneration feeds that sampler into Algorithm 1's actual suffix
and Algorithm 2's matrix/syndrome/key stages. Returned expansions have exact
solution weight and witness length and remain stable under extra fuel. Returned
keys have actual sampled-position provenance and the exact earlier SD condition
for a supplied x_A. The separate missing B and missing x_A obstructions are
proved at the caller. The literal nonempty witness expansion cannot return for
any finite fuel, including the non-power-of-two Table-3 ranges 185, 252 and 191.
No first-candidate universal acceptance is asserted for those ranges.

Independent uniform seed draws now induce a PMF of the actual partial keygen
observations. Explicit serializers map only returned keys. Each returned typed
key and each returned encoded pair has zero mass in the literal wrappers; this
is a consequence of undefined source reads, not a security or rejection theorem.
Deterministic witness/matrix seed pushforwards remain independent without any
uniformity assumption on either output. PRG block size/Parse gaps, serialization
conventions, tensor/source discrepancies and complete correctness/security remain
unresolved. The three-statement final interface is unchanged.

The twenty-third full validation passed: 3294 build jobs and 10731 project
declarations. The transitive audit found only propext, Classical.choice and
Quot.sound. No proof placeholders, custom axioms or unchecked shortcuts were
introduced. Whole-submission completion is still unproved; the goal stays active.

The twenty-fourth validation, including the scaled arithmetic/probability and
packing-boundary modules, passed 3298 build jobs and audited 10791 project
declarations. Only propext, Classical.choice and Quot.sound occur transitively.
This certifies the current development's proof trust, not coverage completion.

`Spec/CipherEvaluation.lean` now composes the complete printed cipher challenge
body at explicit material-parse, MapToBits and Extract boundaries. The first
SHAKE consumes 4*lambda bytes and includes the counter as printed. Actual Enc*
calls supply both ciphertexts and their xor to the supplied Extract function.
The final SHAKE is reinitialized on hpiop/ctr/c0/c1 and feeds the full integer
loop. No counter factoring or all-zero-grinding shortcut changes those lines.
Each optional interpretation is a supplied function without a correctness or
security contract; absent interpretations remain source-resolution boundaries.

`Proofs/CipherEvaluation.lean` proves every returned challenge has this exact
provenance through the actual integer sample and is stable under extra sampling
fuel. Each missing interpretation has a distinct exact boundary result. Missing
B prevents every nonempty returned challenge at any finite fuel, even with the
preceding interpretations supplied. For kappa<=32, positive fuel reaches that
read on the first candidate of the actual final SHAKE stream. This diagnoses
the literal accepted assignment rather than a corrected sampler.

`Spec/CipherBLCRetry.lean` and `Proofs/CipherBLCRetry.lean` connect those outcomes to Algorithm 11. The
caller retains undefined source operations at their current counter and refines
the prior partial model when no preceding boundary is encountered. Successful
returns require actual expansion, BAVC opening and grinding/nonzero header checks;
extra outer fuel preserves them. The all-absent wrapper stops at the material
parse at counter zero, while supplied earlier interpretations expose missing B.

`Spec/CipherSignature.lean` and `Proofs/CipherSignature.lean` connect the existing prepared signature record
and verification input to those computations. Returned-signature provenance and
stability, exact verifier consistency-boundary/header-Reject provenance, and
the corresponding missing-B obstructions are checked. Only returned challenges
reach the existing BLC prefix; unresolved cipher interpretations are never
ordinary Reject or acceptance. Algorithm-12 line 21, raw codecs, source repairs,
and full protocol correctness/security remain unfinished. The three final
statements and separate assumptions interface are unchanged.

The twenty-fifth full validation passed: 3304 build jobs and 10924 project
declarations. All transitive axioms are propext, Classical.choice or Quot.sound.
No proof placeholders, custom axioms or unchecked shortcuts were introduced.
Whole-submission coverage remains incomplete and the goal is active.

`Spec/KeySizeBoundary.lean` separates the fixed witness-length input to the
secret-key parser from the existing unrestricted list representation. No byte
codec or padding rule is selected. `Proofs/KeySizeBoundary.lean` derives exact
cardinalities 2^(lambda+r) and 2^(lambda+r+witnessBits) for all typed parsed key
values. These are not counts or sampling laws of valid/generated SD keys.
An arbitrary injective encoding with fixed output bit length must meet these
capacity bounds; applying the proved byte-ceiling equivalence gives the required
minimum byte counts. Neither injectivity nor a length law is asserted about
the supplied Serialize functions. No new hypothesis is added to Assumptions.

The Category-I/III/V public payloads are 560/784/1056 bits and witness payloads
616/876/1144 bits. The reported secret-key byte allocations leave 0/4/0 bits
beyond those payload counts. In particular Category III's four bits have no
selected value, position or parser acceptance policy. These numerical facts
do not complete a Serialize/Deserialize implementation or round-trip theorem.

`Spec/MainParameterTables.lean` completes the Table-4/5 data including every
size column and records the p. 39 parameter-selection prose separately. Its
proof module checks correspondence to the earlier proof-parameter lists, all
public/secret/signature size formulas, and the degree-four numerical budgets.
The table's necessary codec lower bounds follow from actual key-space counts.
The same module proves discrepancies: Table 4 uses short kappa [11,11,11] rather
than [11,12,12], fast kappa 7 rather than 8, and grinding values which do not
match the prose's fast value 2 or its short-value set in all categories.
Neither source passage is silently corrected from the other.

`Spec/ReportedBenchmarks.lean` separately stores Table 6's reported medians,
10,000-run count and stated processor. Displayed Mc values are transcribed in
cycles at their reported precision. Only category/tradeoff row correspondence
to Tables 4/5 is proved. Raw measurements, reproducibility, implementation
correspondence and any runtime/security interpretation remain human/empirical
obligations; no empirical truth is asserted as a theorem or an axiom.

The twenty-sixth full validation passed: 3309 build jobs and 11088 project
declarations. All transitive axioms are propext, Classical.choice or Quot.sound.
No proof placeholders, custom axioms or unchecked shortcuts were introduced.
The root PLAN.md now provides the requested concise completed/remaining checklist
and separates source decisions from proof work. Whole-submission coverage is
incomplete and the persistent goal remains active.


Continuation 27 adds ParameterSelection: the literal integer dimension formulas,
exact average-fiber density, logarithmic and ceiling characterization of the
density target, and maximum byte-aligned dimension under explicit feasibility.
The printed SD floor gives density 3/2 for n=3,w=1,k=2. The printed RSD theta
sign gives density 2 for n=8,w=2,theta=2,k=5. Neither formula is repaired; greedy
arity optimality and security-cost calibration remain unfinished.

SDReductionGame now records input, permutation and actual solver output, and its
output law is proved equal to the existing randomized reduction. For solvable
input laws the full-regularity event has probability at least the combinatorial
factor. The conditional-product/uniqueness argument gives a success lower bound
with that factor and the actual conditional return/uniqueness probabilities.
No correspondence with an advertised epsilon_rsd or exponential estimate is
assumed. Solver output validity and nonzero conditioning events are explicit.

SDReductionConditioning proves an intermediate gap with an actual correct solver
that returns only for zero matrix/syndrome. In the planted-uniform binary model
at n=4,w=2,k_sd=k_rsd=1,theta=2, its return event has positive probability, but
conditional uniqueness is zero. This holds both for the source's return-only
conditioning and with full regularity included. The parameters satisfy the
stated dimension condition and density 1/2. The positive exponential heuristic
is therefore not a universal conditional lower bound. No final-theorem refutation,
seed-key security claim or runtime guarantee follows from this counterexample.

Following the user's concern about emphasis, PLAN.md now prioritizes the abstract
security argument and concrete correspondence. The overall EUF-CMA reduction is
still largely unfinished; supporting declaration counts are not its completion
metric. Final.lean retains three statements and Assumptions.lean is unchanged.

The twenty-seventh full validation passed: 3316 build jobs and 11204 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
The goal remains active. This is a checked component of the SD reduction,
not an EUF-CMA proof; the signature-security reduction is the next priority.


Continuation 28 directly addresses signature security. SignatureSecurity defines
the bounded adaptive signing/hash/public-oracle game, separate adversary and
world state, full signing-request log, and final hash equality/freshness test.
The lazy random-oracle implementation was moved unchanged into Spec/RandomOracle
and re-exported by Assumptions, preserving the standalone assumption interface.

AbstractSignature implements the source's abstract prepare/hash/open ordering.
The final-hash table starts empty, signing queries bind the requested message,
and the other services preserve that table by construction. The adaptive
invariant proving all table origins yields a concrete earlier adversarial hash
query for every table-present fresh winner. A separate lazy-sampling proof bounds
an absent-input winner by 1/|Digest|. The combined signature-game bound is the
prior-query winning event plus 2^(-2*lambda); this is the first reduction step,
not an extraction or end-to-end security theorem.

SignatureHashGame provides exact typed hash/signature record equivalences,
uses the existing verifier's PIOP/coefficient recovery in its final input, and
proves agreement with verifyPostRecompute when that input's answer is resolved.
No raw codec, complete concrete Scheme instance or cryptographic security of
components is assumed. Typed oracle-domain separation, source initialization,
Algorithm-12/type/dimension issues, replay/forking, signing simulation, binding,
extraction and full quantitative security remain explicit open obligations.

The twenty-eighth full validation passed: 3323 build jobs and 11538 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
The three-statement final interface is unchanged. The first signature-game
reduction step is checked; full EUF-CMA security and concrete correspondence
remain unproved, and the persistent goal is active.

Continuation 29 extends the signature reduction with actual replay experiments.
Spec/SignatureReplay saves the game before an indexed adversarial hash answer;
ended cuts retain the original terminal result. Proofs/SignatureReplay proves
exact equality with the original game after ordinary resumption, including
keygen, adversary initialization and finalization. A fresh branch has the same
checked-result marginal as resumption and a uniform sampled-answer marginal.

Proofs/SignatureFork proves the collision bound without assuming conditional
uniformity on success. At a fresh cut, epsilon^2 <= Pr[two target-winning
continuations with distinct answers] + epsilon/|Digest|. It derives the
weighted-square inequality for arbitrary PMFs and applies it to the actual
random-prefix experiment, including zero-success ended/nonfresh cuts. Epsilon
is selected-input success, not overall forgery probability. Useful-query
selection and its query loss remain unproved.

Proofs/SignatureReplayConsistency derives answer persistence through the
actual abstract services. Each target-winning branch has a fresh-message
accepted attempt at the saved input with its tested target equal to the branch
answer. A successful fork therefore gives two accepted attempts at that input
with distinct tested digests. This is not commitment consistency, usable
challenge separation or witness extraction. The snapshot still retains the
honest signing secret; no witness-free signing simulator or runtime bound is
claimed. All four new modules are in the specification/proof entry points and
source index. Assumptions and the three-statement final interface are unchanged.

The twenty-ninth full validation passed: 3327 build jobs and 11719 project
declarations. All transitive axioms remain propext, Classical.choice and
Quot.sound. Source-index paths, specification import separation and the three
final statements were also checked. Full signature security remains unfinished;
the persistent completion goal remains active.

Continuation 30 completes the useful-query probability link for the defined
abstract replay. Spec/SignatureQuerySelection records chronological adversarial
hash requests with their pre-query absence flags. Proofs/SignatureQuerySelection
proves exact terminal/finalized marginals, the request-count bound and equality
between an indexed marked event and the existing cut/resume single experiment.
Proofs/SignatureQueryProvenance proves signing-log monotonicity and origin of
every final table entry: initial, freshly queried, or a signed message's entry.
Empty initialization and fresh-message acceptance imply a marked fresh target
query below the action budget for each table-present winner.

Proofs/SignatureForgeryFork proves the finite event-cover bound, exact uniform
index averaging, e <= q*s + delta and s^2 <= F + s*delta for the actual experiments.
It derives max(e-delta,0)^2 <= q^2*(F+delta), where q is a positive full-action
budget. SignatureHashGame specializes the result to the source's typed records
and delta=2^(-2*lambda). The squared budget loss is not asserted to be optimal.
The distributional/cover premises are derived, not assumed as security contracts.
These are replay experiments using the honest signing key, not yet an SD/RSD
solver, commitment proof, challenge-separation argument or extractor. All source
implementation/model-correspondence boundaries remain in force.

The thirtieth full validation passed: 3331 build jobs and 11866 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Indexed source paths, specification import separation and the three final
statements were checked. No proof placeholders or unchecked trust shortcuts
were introduced. Full EUF-CMA security remains unproved and the goal is active.

Continuation 31 adds deterministic commitment collision reductions needed after
the signature replay. Spec/Proofs.BAVCBinding define exact Hashbavc query strings,
prove fixed-width serialization injectivity and give a computable finder. If
equal-root computations differ, a returned collision pair lies in their actual
query lists (tau+1 entries each); none means their salts and full commitment
arrays agree. It does not choose an arbitrary global hash collision.

Proofs/BAVCBindingReconstruction derives exact refinement of retained-row
instrumentation to the actual staged Algorithm-9 body. Inconsistent revealed
seeds at one common position under a shared root yield a computed hash collision
or a same-index seed-commitment collision. The latter means both cipher calls
match under distinct seed keys; the existing parameter bounds give distinct
plaintext tweaks. No ideal-cipher probability, especially for Category-III
truncation, is inferred from these equalities.

Spec/Proofs.BLCBinding retain Algorithm 12's actual three-field Hashlines and
Hashaux strings. Fixed-width leading digests give equal BAVC roots or collisions
on those exact query pairs. The hash-chain equations are discharged from the
actual successful prepareWithBindings prefixes and supplied-base suffixes.
The arbitrary vector/matrix serializers need no new injectivity premise for
this limited header recovery. All five modules are imported and indexed.

Full binding still needs adaptive ROM/ICM probability bounds and concrete-game
composition. Missing nodes/seed/share bindings, separate folding seed arrays,
the ill-typed line 21 and sign/verify Hashlines mismatch remain untouched.
No source repair, cryptographic assumption, hiding proof, usable-challenge
separation or RSD extractor was added. The assumptions and final interface
remain unchanged; the full formalization is incomplete.

The thirty-first full validation passed: 3336 build jobs and 11925 project
declarations. All transitive axioms are propext, Classical.choice or Quot.sound.
All 21 numbered algorithms and indexed paths, specification import separation
and the three final statements were checked. The completion goal remains active;
these collision reductions do not complete signature security.

Continuation 32 proves an adaptive birthday bound for the actual shared lazy
oracle. Spec/RandomOracleCollision retains a private table, full repeated-query
history and fresh-collision flag. The bound is choose(q,2)/|Output|, including
arbitrary answer-dependent query choices. Exact table/log correspondence and
collision-flag completeness are derived from execution, not state contracts.
An arbitrary final selector of stored collision pairs satisfies the same bound.

Spec/Proofs.BAVCBindingROM check both complete row/outer query lists in the final
table and run the existing source-string collision finder. Equal roots with
different salt or leaf-commitment data imply a returned stored collision. The
resulting probability is at most choose(q,2)/2^(2*lambda). This is a fully queried
hash-binding experiment, not yet the full BAVC or signature experiment: coverage
of full source execution, honest query accounting, finalization and cipher/seed
collision probabilities remain open. The default for missing table entries is
never used by a successful claim; coverage checks must not be imposed on source
verification to discard forgeries. All five new modules are imported/indexed;
Assumptions and the three Final statements are unchanged.

The thirty-second full validation passed: 3341 build jobs and 12063 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
No proof placeholders, cryptographic axioms or unchecked shortcuts were added.
The full signature-security reduction remains unproved; the persistent goal
is still active.

Continuation 33 closes the already-queried condition for the BAVC hash component.
Spec/Proofs.OracleProgram define finite adaptive query programs and prove budget
composition, ordered array evaluation and completion against the final stored
answers. Spec/Proofs.RandomOraclePipeline retain one shared oracle across the
adversarial and verification phases. History-length and flag invariants yield
the total bound choose(q+k,2)/|Output|, including collisions across phases.

Spec/Proofs.BAVCHashVerification execute both increasing-index row/outer hash
computations of Algorithms 7/9 after adaptive salt/commitment selection. All runs
finish within 2*(tau+1) queries, and every computed root matches the source's
rootHash evaluated from the final table. The resulting hash-binding event has
no already-queried guard and probability at most
choose(q+2*(tau+1),2)/2^(2*lambda). The proof derives query coverage and uses the
existing computable collision finder; it does not assume binding or discard
unqueried data. All six modules are imported/indexed. Full signature/replay
composition, seed/cipher binding, XOF correspondence, extraction and signing
simulation remain unfinished. Assumptions and Final are unchanged.

The thirty-third full validation passed: 3347 build jobs and 12199 project
declarations. All transitive axioms remain propext, Classical.choice or Quot.sound.
The 252 indexed Lean paths, six new module imports, standalone specification
separation and three final statements were also checked. The full signature
reduction remains unproved and the persistent goal is active.

Continuation 34 develops the ICM branch needed for seed binding. Spec/IdealCipher
defines adaptive encryption/decryption against one sampled keyed-permutation
family and a posterior-compatible-family interpreter. FinitePosterior's counting
identity yields their exact adaptive distributional equality and a link to the
existing standalone ICM definition. Repeated queries and cross-direction lookups
preserve one permutation's graph; trace consistency and budget length are proved.

UniformSymmetry, IdealCipherFresh and IdealCipherInverse derive fresh encryption
and decryption laws by explicit equivalences of compatible families. The answers
are uniform over unused outputs/inputs given the whole history. IdealCipherCapacity
derives unused cardinality at least M-q and conditional full-block target bound
1/(M-q); projected events are bounded by their full-block fiber size over M-q.
Spec/Proofs.IdealCipherSeed retain Category-III padding and full 256-bit private
observations, prove the exact Enc* projection equation and a fiber-size bound of
2^64, and obtain a fresh 192-bit target bound of 2^64/(2^256-q).

These are conditional single-query laws, not yet the adaptive two-call
seed-commitment collision bound. Repeated/previously queried constituent calls,
decryption, source tweaks and verification costs still need to be composed.
All ten new modules are imported/indexed. Cryptographic assumption definitions
and Final are unchanged; the assumption model-link comment is updated. Full
binding, extraction, signing simulation and end-to-end security remain unfinished.

The thirty-fourth full validation passed: 3357 build jobs and 12467 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
All 262 indexed Lean paths, ten new imports, specification separation and three
final statements were checked. No proof placeholders or unchecked shortcuts
were added. The complete signature reduction remains unfinished and the goal
remains active.

## Continuation 35 — paired-cipher collision probability

New modules: Spec/SeedPairing, Spec/IdealCipherJoint,
Spec/IdealCipherPairCollision; Proofs/SeedPairing, IdealCipherJoint,
IdealCipherComparison, IdealCipherPairCollision, IdealCipherPairProbability,
IdealCipherPairAdaptive and SeedPairBinding. All are root-imported and indexed.

The source companion-input relation, its padding compatibility and fixed-point
properties are proved. Joint posterior equality retains the hidden family for
terminal events. A consistent observed matching half with a matching hidden
companion is charged at its first appearance. Prior/repeated calls, inverse
queries and adaptive changes of keys are included. Conditional comparison and
adaptive composition prove choose(q,2)*C/(M-q)*C/(M-q-2), with checked full-output
and Category-III specializations. This is a derived bound, not an assumed
security contract, independence premise or security property of concrete ciphers.

Source collision-to-event coverage still has explicit left-half membership
premises. Complete seed verification must execute all four calls on the same
cipher and account for them. The generic adaptive event bound does not establish
that source execution correspondence or complete BLC/signature binding. No RSD
extractor, signing simulation, usable challenge separation, full runtime bound
or end-to-end EUF-CMA theorem has been obtained. Source defects remain unchanged.
The thirty-fifth full validation passed: 3367 build jobs and 12550 project
declarations. Only propext, Classical.choice and Quot.sound occur transitively.
All ten new modules are imported/indexed; 194 distinct indexed Lean paths,
standalone specification separation and three final statements were checked.
The persistent goal remains active; full source verification coverage and the
signature-security reduction are still incomplete.

## Continuation 36 — four-call verification and exact source collision law

Spec/Proofs.IdealCipherPipeline, Spec/Proofs.IdealCipherProgram,
Spec/Proofs.SeedVerification and Proofs/SourceSeedVerification are added and
indexed. Adaptive first-phase stopping/exhaustion still transfers to verification
on the same hidden cipher. The q+k paired-event bound is derived for that joint
execution. Both source commitments execute all four calls with an exact trace;
no run is discarded because an input was unqueried or repeated.

Returned pairs concatenate to the literal CommitSeed outputs. Distinct padded
keys are equivalent to distinct original seeds. Equality of the operational and
direct source collision laws removes any completion/freshness/membership
condition from the final source event. Full-output and Category-III bounds are
choose(q+4,2)*C/(M-(q+4))*C/(M-(q+6)), with checked capacities and source input
relations. Category-III source scope and all existing algorithm defects remain
separate human review obligations. No concrete cipher security is inferred.

The remaining composition gap is now at the shared hash/cipher and actual
seed-tree/reconstruction executions, not the four-call seed check. Their query
costs and the complete signature/replay relation are still unproved. No extractor,
signing simulation or EUF-CMA theorem is claimed. The thirty-sixth full validation
passed: 3374 build jobs and 12717 project declarations, with only propext,
Classical.choice and Quot.sound transitively. Specification separation, all
seven imports/index entries, 279 indexed references (201 distinct paths) and
three final statements were checked. The full signature reduction remains
incomplete and the persistent goal remains active.

## Continuation 37 — joint ROM/ICM execution

Spec/HashCipher and Spec/HashCipherProgram, and Proofs/HashCipher,
HashCipherHash, HashCipherPair, HashCipherSecurity, HashCipherProgram,
HashCipherSourcePrograms and HashCipherParameters are added and indexed.

One joint experiment now supports arbitrary interleaving, including repeated
hash/cipher calls and inverse queries. Its complete posterior/fixed-family law,
both graph invariants, hash-collision flag coverage and total query count are
proved. Both collision bounds apply to this one execution. Their joint bound
is choose(q,2)*(1/|Digest|+C/(M-q)*C/(M-q-2)), specialized at the source full-output
and Category-III widths/capacities. The generic event-transfer coverage premise
is an explicit caller proof obligation; it is not a binding assumption.

Finite mixed programs have additive bounds and checked completion. The existing
source hash and seed programs embed with exact operational laws. Complete
four-call seed execution and BAVC two-root hash computation retain their source
outputs and derive their actual collision-query coverage in this interpreter.
Sequential composition after a mixed adversary, full tree/reconstruction and
signature-service executions, query accounting, extraction and signing simulation
remain open. No prior source error is repaired and no concrete joint primitive
security is inferred. The candidate joint sampling choice is explicitly
re-exported in Assumptions.sharedOracleModel and is not inferred from uniform
marginals. Earlier model definitions and Final are unchanged. The final
thirty-seventh full validation passed: 3383 build jobs and 12971 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
All nine imports/index entries, 289 indexed Lean references (211 distinct
paths), standalone specification separation and exactly three final statements
were checked. No proof placeholder, cryptographic axiom or unchecked shortcut
was introduced. These results are supporting collision bounds, not a complete
signature reduction; the overall goal remains active and incomplete.

## Continuation 38 — sequential shared verification and cipher reconstruction

New modules: Spec/HashCipherPipeline, Spec/HashCipherVerification,
Spec/BAVCCipherProgram; Proofs/HashCipherPipeline, HashCipherPipelineSecurity,
HashCipherVerification, HashCipherSourceSeedVerification and BAVCCipherProgram.

The shared two-phase experiment retains the same table/family, both histories
and the OR of both collision flags. Verification runs after early stopping as
well as exhaustion. Exact joint-law equivalence and extension of the standalone
joint model are proved, along with both bounds using q+k mixed actions. The
source four-call seed checks and two root-hash checks run after mixed adversarial
queries with completion, exact values and collision-query coverage derived.
The source seed law has no membership/freshness/completion guard, including for
Category III. Bounds include q+4 and q+2*(tau+1) calls respectively.

Actual Algorithm-9 cipher expansion and leaf/row programs now have exact value
correspondence to the staged reconstructionRows, preserving every error, the
tree/nodes distinction and literal guards. Their budget is 2*(tau*N-1)+2*N*tau.
The full/III layouts have exact Enc* equations, and shared execution preserves
the existing hash table/log while appending the actual cipher graph. This is
the cipher projection: source line 30's hash after each row and the outer hash
still need operational composition. Both complete reconstructions, their
collision finder and full signature/replay costs remain to be connected. No
extractor, signing simulation or EUF-CMA theorem is claimed.

The thirty-eighth full validation passed: 3391 build jobs, 13158 declarations,
and only propext, Classical.choice and Quot.sound transitively. Checked 297
indexed references (219 distinct paths), all eight new modules' imports/index
entries, standalone specification separation and exactly three final discrepancy
statements. No placeholder, cryptographic axiom or unchecked shortcut was added;
Assumptions and Final are unchanged. The persistent goal remains active.

## Continuation 39 — complete ordered reconstruction and disagreement bound

New modules: Spec/HashCipherEvaluation, Spec/BAVCReconstructionProgram,
Spec/BAVCReconstructionGame; Proofs/HashCipherEvaluation,
BAVCReconstructionProgram, BAVCReconstructionCoverage, BAVCReconstructionGame
and BAVCReconstructionSecurity. All are imported and indexed.

The ordered program hashes each row immediately after its leaf calls, then
performs the outer hash. Exact source value correspondence holds for success
and every error. Operational evaluation derives each used hash lookup and
cipher graph entry; every revealed seed's commitment calls are covered.
Two selected reconstructions execute after a mixed adversary, retaining both
results and running the second even if the first errors. Equal-root successful
outputs with disagreeing common revealed seeds yield an actual stored hash
collision or a same-index seed collision with its graph coverage proved.

Full-output and Category-III specializations derive the joint bound with
Q=q+2*(2*(tau*N-1)+(2*N+1)*tau+1). The bound is
choose(Q,2)*(1/|Digest|+C/(M-Q)*C/(M-Q-2)), with explicit width/tweak premises
and discharged companion/padding/capacity facts. Q+2<M gives its useful finite
form. No assumed source binding or added coverage/freshness/completion guard
replaces execution. The event is successful reconstruction disagreement; it
is not signature acceptance and does not make undefined source execution into
rejection. The remaining chain is BLC Hashaux/Hashlines execution, source seed
linkage, signature/replay costs, usable challenges, extraction and signing
simulation. The main signature reduction remains incomplete.

The thirty-ninth full validation passed: 3399 jobs, 13351 declarations, and only
propext, Classical.choice and Quot.sound transitively. Checked 305 indexed Lean
references (227 distinct paths), eight new module imports/index entries,
standalone specification separation and exactly three final statements. No
placeholder, cryptographic axiom, resource/trust override or unchecked shortcut
was added. Assumptions and Final are unchanged; the persistent goal is active.

## Continuation 40 — verifier hash chain after complete reconstruction

New modules: Spec/BLCHashChain, Spec/BLCReconstructionChain;
Proofs/BLCHashChain, Proofs/BLCReconstructionChain. All are imported and
indexed under Algorithm 12.

The chain program makes the verifier's Hashaux query on the reconstructed root
and the supplied corrections tail, runs an explicit bounded intermediate
program for the base matrix, then makes the Hashlines query on the three-field
payload. Successful evaluation derives both actual table lookups. Equal line
digests give equal roots or a stored collision on one of the two exact query
pairs, using the fixed-width digest header. The source constructor reuses the
exact BLCBinding byte strings; its base program is the explicit line-21
boundary and is not claimed to implement that line.

The composed game runs the complete ordered Algorithm-9 reconstruction, the
supplied pre-Hashaux program and the chain for both selected inputs after a
mixed adversary, retaining all error values. Equal line digests with a
disagreeing commonly revealed seed reduce, through the previous reconstruction
collision result, to a stored hash collision or a covered seed collision. The
full-output and Category-III bounds are choose(Q,2)*(1/|Digest|+C/(M-Q)*C/(M-Q-2))
with Q=q+2*(B+p+m+2), where B=2*(tau*N-1)+(2*N+1)*tau+1 and p, m bound the
supplied programs. Q+2<M gives the useful finite form; width/tweak premises
remain explicit. No binding, coverage, freshness or completion guard was
added, and no source binding was repaired.

This connects reconstruction disagreement to the verifier's final line digest.
It does not identify Algorithm 12's separate seed array or rshare/phi_mu
bindings with reconstruction output, does not account signature/replay
costs, and does not provide usable algebraic challenges, extraction, signing
simulation or EUF-CMA.

The fortieth full validation passed: 3403 build jobs and 13501 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked all four new module imports and index entries, standalone
specification separation and exactly three final discrepancy statements. No
placeholder, cryptographic axiom or unchecked shortcut was introduced.
Assumptions and Final are unchanged. The persistent goal remains active and
the full signature reduction remains incomplete.

## Continuation 41 — seed-vector extraction from two chain executions

New modules: Spec/BLCSeedExtraction and Proofs/BLCSeedExtraction, imported and
indexed under Algorithm 12.

A successful literal reconstruction has a present seed at every leaf other
than its hidden one, derived from the staged row loop. For two successful
chain executions whose hidden indices differ at execution e, every leaf of e
is revealed by at least one side. If the commonly revealed seeds agree, the
pointwise merge agrees with both maps and is the unique such complete vector.
The failure event of the chain game (equal line digests, differing hidden
indices somewhere, no unique agreeing vector) implies the disagreement event
on the game's support, so its probability is bounded by the continuation-40
full-output and Category-III chain bounds with the same Q.

This is seed-vector extraction for the defined game. It does not derive the
hidden indices from digests, recover witness lines, account signature or
replay queries, separate challenges, or supply signing simulation.

The forty-first full validation passed: 3405 build jobs and 13520 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 42 — extractor bindings for the Algorithm-12 fold

New modules: Spec/BLCSeedFold and Proofs/BLCSeedFold, imported and indexed
under Algorithm 12.

The extractor's bindings fill the undeclared seed array from a complete seed
vector, start every share at zero and use the Gray row for phi_mu. From the
existing exact fold sum, the share at hidden index i is slope*phi(i)+intercept
in characteristic two: slope is the direct Algorithm-10 fold accumulator of
the extracted leaf randomness plus the transmitted correction, intercept is
the fold base. Reaching the line-21 operands under these bindings yields the
Q matrix in this form at the expanded hidden indices. Two hidden indices
differ by slope times the Gray-row difference. With Algorithm 10's honest
corrections computed from the same seeds, the slope is the committed common
accumulator at every execution.

These are deterministic identities under named bindings. They do not change
the literal absent-binding behavior, do not identify the extracted vector
with the signer's tree, do not resolve line 21, and do not claim witness
validity, challenge separation or signature security.

The forty-second full validation passed: 3407 build jobs and 13550 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 43 — suffix values and a candidate two-challenge consistency reading

New modules: Spec/BLCSeedLines and Proofs/BLCSeedLines, imported and indexed
under Algorithm 12.

psi of the affine share matrix equals the sum over executions of the slope
times that execution's Gray-row psi, plus psi of the intercept. Under the
extractor's bindings, the suffix witness value is the transmitted correction
plus delta times that quantity, and the randomness value is delta times it.
With a constant slope u and the Gray merge as encoding, delta cancels the
merged challenge and the witness value is correction+u plus delta times the
intercept psi. The consistency columns of the share matrix are the masked
slope times the hidden Gray row plus the intercept's columns. Under the
candidate binary reading of line 21 at two hidden vectors differing at one
Gray bit of execution e, the masked slope of e equals the plain check and the
intercept's columns equal the base at that coordinate.

These are deterministic identities. The candidate reading is a hypothesis
shape, not a source resolution; non-constant adversarial slopes, the random
consistency matrix argument, equal plain/base across forked attempts,
challenge separation and signature security remain open.

The forty-third full validation passed: 3409 build jobs and 13569 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 44 — uniform consistency-mask kernel probability

New modules: Spec/ConsistencyMatrix and Proofs/ConsistencyMatrix, imported
and indexed under Algorithm 12.

[I | M] applied to a vector is its top part plus M times its payload part.
For a surjective linear map into a finite module, every fiber has uniform
probability 1/|V|; M ↦ M·v is surjective for nonzero v. Hence a fixed vector
with nonzero payload part is annihilated with probability exactly |F|^(-s),
a vector with zero payload and nonzero top part never, and any nonzero
vector with probability at most |F|^(-s). Two distinct fixed vectors have
equal masked images with at most that probability; the binary instantiation
is 2^-(lambda+B). The masked slope of the previous continuation is this mask
applied to the slope vector.

The sampler is the explicit uniform matrix law. Its correspondence with the
XOF expansion of the auxiliary digest, the oracle ordering that fixes the
slopes before the mask, and adaptive corrections remain open.

The forty-fourth full validation passed: 3411 build jobs and 13596 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 45 — adaptive oracle trap for a fixed function of the query input

New modules: Spec/RandomOracleTrap and Proofs/RandomOracleTrap, imported
and indexed under Algorithm 12.

For the adaptive lazy oracle of the collision experiment and a trap
predicate on query/answer pairs: if a uniform answer satisfies the predicate
for a given input with probability at most epsilon, then some recorded pair
satisfies it after budget queries with probability at most budget*epsilon.
The per-query step uses the recorded-table invariant so that a repeated
query cannot create a new hit. A trapped pair stored in the final table is
in the history. For the mask trap, defined by a fixed vector-valued function
of the input being nonzero and annihilated by the returned mask, the uniform
kernel bound gives budget*|F|^(-s), hence budget*2^-(lambda+B) for binary masks.

The oracle here is a matrix-valued lazy oracle; identifying it with the XOF
expansion of the auxiliary digest and composing with the hcom-to-seeds
binding remain open, as do fork-attempt consistency, challenge separation,
signature/replay accounting, extraction and signing simulation.

The forty-fifth full validation passed: 3413 build jobs and 13622 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 46 — table-dependent trap on the instrumented oracle trace

New modules: Spec/RandomOracleTrace and Proofs/RandomOracleTrace, imported
and indexed under Algorithm 12.

The instrumented run records, at each fresh query only, the table before the
query, the input and the fresh answer. For a predicate with a uniform
per-answer bound epsilon at every table and input, the probability that some
fresh entry satisfies the predicate at its earlier table is at most
budget*epsilon. Repeated queries change nothing. The invariants: every
stored value has a fresh entry whose earlier table lacked it and is extended
by the final table; every fresh entry persists; tables only grow through
any continuation. A stored value whose trap holds at every earlier table
lacking it, extended by the final one, raises the trace event.

No law equality with the uninstrumented experiment is proved. Predicates at
the final table, the fresh-answer-hits-earlier-input event, the mask's XOF
correspondence and the hcom-to-seeds composition remain open, as do
fork-attempt consistency, challenge separation, signature/replay
accounting, extraction and signing simulation.

The forty-sixth full validation passed: 3415 build jobs and 13696 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 47 — fresh answers hitting values mentioned by earlier inputs

New modules: Spec/RandomOracleMention and Proofs/RandomOracleMention,
imported and indexed under Algorithm 12.

The prefix-dependent trap tests each fresh entry against the trace that
preceded it. With a per-query bound epsilon(n) after n fresh entries, the
event has probability at most the sum of epsilon over the fresh positions;
a repeated query spends a position without a fresh entry. The mention
predicate holds when a fresh answer lies in the mention set of an earlier
fresh input. The uniform membership mass is |S|/|Output|, the per-query
bound is n*m/|Output| for mention sets of size at most m, and the total is
choose(budget,2)*m/|Output|.

The mention map is a supplied parser whose correctness is a serialization
fact for later composition. The mask oracle model, the hcom-to-seeds
composition, fork-attempt consistency, challenge separation,
signature/replay accounting, extraction and signing simulation remain
open.

The forty-seventh full validation passed: 3417 build jobs and 13721 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 48 — product-valued oracle for hash and mask components

New modules: Spec/ProductOracle and Proofs/ProductOracle, imported and
indexed under Algorithm 12.

One lazy oracle returns a (digest, matrix) pair per fresh input. The
first and second marginals of the uniform pair law are the uniform digest
and matrix laws. The table-dependent mask trap on the matrix component is
bounded by budget*|F|^(-s), using the trace trap bound. The digest
component's membership mass is |S|/|D|; the per-query mention bound is
n*m/|D| after n fresh entries and the total is choose(budget,2)*m/|D|,
using the prefix trap bound.

This is an explicit modeling device for a standalone slope-consistency
statement. Its relation to the source XOF, the shared hash/cipher model of
the signature game, the hcom-to-seeds chain composition, fork-attempt
consistency, challenge separation, signature/replay accounting,
extraction and signing simulation remain open.

The forty-eighth full validation passed: 3419 build jobs and 13731 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 49 — ordered oracle log and dependency chains

New modules: Spec/OracleChain and Proofs/OracleChain, imported and indexed
under Algorithm 12.

The instrumented log satisfies, through any continuation: a newer entry's
earlier table extends an older entry's earlier table and stores the older
value; every entry's earlier table lacks its own input; the final table
extends every earlier table and stores every entry. An entry whose input
is stored in another entry's earlier table is the older one. For two stored
links where the newer input mentions the older's digest, either the older
input is present in the newer entry's earlier table or the older link was
answered later and its fresh digest hit the mentioned value. By induction
along a sink-first linked chain with distinct inputs, the whole chain is
present in the sink's earlier table or the mention event holds.

The concrete chain parser for BAVC/BLC inputs, the slope-difference vector
through the present chain, the injective-commitment hypothesis and the
assembled slope-consistency bound remain to be written, along with
fork-attempt consistency, challenge separation, signature/replay
accounting, extraction and signing simulation.

The forty-ninth full validation passed: 3421 build jobs and 13761 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 50 — concrete chain strings and the mention parser

New modules: Spec/BAVCChainInputs and Proofs/BAVCChainInputs, imported and
indexed under Algorithm 12.

The row, outer and auxiliary strings and the mask input are defined on one
string type, with the row and outer strings equal by definition to the
reconstruction program's inputs. Lengths are 8+2*lambda*N, 8+lambda+2*lambda*tau,
8+2*lambda+|tail| and 2*lambda. The fixed-offset window parser extracts
the root at offset 8 of the auxiliary string, each row digest at its
offset in the outer string and the digest of the mask input, with at most
tau+2 mentions per input. Distinctness follows from domain bytes, length
parity and positivity. The sink-first chain per execution is linked and
distinct, and the generic dichotomy yields: all three strings present in
the mask entry's earlier table for every execution, or the mention event.

The table-dependent slope vector through the present chain, the
injective-commitment hypothesis and the assembled slope-consistency bound
remain to be written, along with fork-attempt consistency, challenge
separation, signature/replay accounting, extraction and signing
simulation.

The fiftieth full validation passed: 3423 build jobs and 13824 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 51 — chained claims, uniqueness and digest collisions

New modules: Spec/SlopeConsistency and Proofs/SlopeConsistency, imported
and indexed under Algorithm 12.

A claim's chain strings are injective in their fields. In a table with no
two distinct inputs sharing a digest component, two claims chained with
the same auxiliary digest have equal salt, seeds, row digests, root and
corrections, given injective per-leaf commitments and an injective
corrections serializer; the slope depends on the auxiliary data only
through its corrections. The digest-collision prefix event (a fresh digest
equal to an earlier fresh digest) has per-query bound n/|Digest| and total
choose(budget,2)/|Digest|; two distinct stored inputs with equal digests
raise it, so its absence gives collision freeness of the final table and
of every earlier table.

The assembled slope-consistency bound (trap, mention and collision terms
through the table-dependent vector) remains to be written, together with
the join of the commitment-injectivity hypothesis to the cipher-model seed
binding, fork-attempt consistency, challenge separation, signature/replay
accounting, extraction and signing simulation.

The fifty-first full validation passed: 3425 build jobs and 13866 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 52 — the standalone slope-consistency bound

New modules: Spec/SlopeConsistencyGame and Proofs/SlopeConsistencyGame,
imported and indexed under Algorithm 12.

In the product-oracle game, the winning event is: the named claim is
chained in the final table, the mask at its auxiliary digest is stored,
and two executions' slopes differ with equal masked images. For each pair
of executions the trap vector is the slope difference of the claim chained
in the table before the mask query, chosen classically; uniqueness in a
collision-free earlier table makes it the named claim's difference. A
winning run therefore raised a pair trap, the mention event or the
collision event. The bound is the sum of tau^2 trap terms budget*2^-s, the
mention term choose(budget,2)*(tau+2)/|Digest| and the collision term
choose(budget,2)/|Digest|.

This is a standalone statement about the defined game with explicit
injective commitment and serializer hypotheses. Joining it to the cipher-
model seed binding, to the chain and seed-extraction games, to the fork's
accepted attempts, challenge separation, signature/replay accounting,
extraction and signing simulation remain open.

The fifty-second full validation passed: 3427 build jobs and 13904 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 53 — instrumented shared hash/cipher execution

New modules: Spec/HashCipherTrace and Proofs/HashCipherTrace, imported and
indexed under Algorithm 12.

The shared execution's run records, at each fresh hash query, the table
before it; cipher queries pass the table and log through. Forgetting the
log gives exactly `HashCipher.runFixed` and `HashCipher.jointExperiment`.
Through any continuation the log is traced, ordered and fresh, its earlier
tables are extended by the final one, its entries persist, and tables only
grow. The prefix-dependent trap bound is the sum of a position-dependent
epsilon over fresh positions (repeats and cipher queries spend a position
without a fresh entry), and the table-dependent bound is budget*epsilon;
both hold for each fixed family and for the uniform mixture.

Instantiating the digest as the product of hash digest and mask, re-stating
the slope game in this model with CommitSeed through the cipher family,
and replacing the injective-commitment hypothesis by the seed-collision
bound remain to be done, along with fork-attempt consistency, challenge
separation, signature/replay accounting, extraction and signing
simulation.

The fifty-third full validation passed: 3429 build jobs and 13963 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 54 — unobserved-key double match

New module: Proofs/IdealCipherUnseenMatch, imported and indexed under
Algorithm 12.

For the posterior family law of a world with at most q observations, a key
whose input and companion input are both unobserved matches two target
outputs with probability at most 1/(M-q)*1/(M-(q+1)); the proof conditions
on the first fresh answer and bounds the second fresh answer in the
observed world. Some key among a finite set of such keys matches with at
most the set size times that bound.

Re-stating the slope game in the shared model with CommitSeed through the
cipher family, the case split queried/unqueried for colliding seeds, and
the replacement of the injectivity hypothesis remain to be written, along
with fork-attempt consistency, challenge separation, signature/replay
accounting, extraction and signing simulation.

The fifty-fourth full validation passed: 3430 build jobs and 13968 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 55 — slope-consistency game in the shared model

New modules: Spec/SharedSlopeGame and Proofs/SharedSlopeGame, imported and
indexed under Algorithm 12.

Commitments are CommitSeed through the hidden cipher family at the claim's
salt. Uniqueness of chained claims with one auxiliary digest now needs only
that no other seed shares a named seed's commitment; under it the trap
vector at the named claim's mask input is its slope difference. If the
condition fails, the commitment equality gives equal cipher outputs at both
paired inputs, and the colliding seed is either queried at one of them,
yielding a witnessed pair collision with the named seed's recorded entry,
or unqueried at both, yielding the unseen double match. The traced joint
experiment's cipher history matches the family, by projection onto the
existing shared experiment. A winning run, with its named claim chained
and queried, raised a mask trap, the mention event, the digest-collision
event, a witnessed pair collision or an unseen double match.

The probability assembly of the five events, executing the named claim's
commitments to discharge the queried condition, Category III, fork-attempt
consistency, challenge separation, signature/replay accounting, extraction
and signing simulation remain open.

The fifty-fifth full validation passed: 3432 build jobs and 14025 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 56 — probability assembly of the shared-model slope bound

New module: Proofs/SharedSlopeBound, imported and indexed under Algorithm 12.

The five covering events are bounded: tau^2 family-dependent mask traps by
tau^2*budget*2^-s; the mention and digest-collision prefix events by
choose(budget,2)*(tau+2)/|Digest| and choose(budget,2)/|Digest|; the
witnessed pair collision by choose(budget,2)*pairCost through the
projection onto the existing shared experiment; and the unseen double
match by tau*2^kappa*|Bits|*1/(|Bits|-budget)*1/(|Bits|-budget-1) through
the posterior view, where an event of the family, final state and cipher
history is bounded by its posterior bound at the final world. The total is
the shared-model slope-consistency bound.

Discharging the queried-claim condition by executing the named
commitments, Category III, connecting the fork's accepted attempts,
challenge separation, signature/replay accounting, extraction and signing
simulation remain open.

The fifty-sixth full validation passed: 3433 build jobs and 14051 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 57 — instrumented two-phase shared execution

New modules: Spec/HashCipherTracePipeline and Proofs/HashCipherTracePipeline,
imported and indexed under Algorithm 12.

The second phase continues from the first's state, table, histories and
log. Forgetting the log gives exactly the existing two-phase execution and
joint experiment. The traced/ordered/fresh invariants, earlier-table
extension and entry persistence hold through both phases. A run adds at
most its fuel in fresh entries. The table-dependent trap bound is
(q+k)*epsilon and the prefix-dependent bound is the sum of epsilon over
q+k positions for monotone epsilon, both for a fixed family and the
mixture.

Executing the named claim's commitments as the second phase, with its
coverage of the cipher history and the transfer of the witnessed and
unseen bounds to the two-phase experiment, remains to be done, along with
Category III, fork-attempt consistency, challenge separation,
signature/replay accounting, extraction and signing simulation.

The fifty-seventh full validation passed: 3435 build jobs and 14075 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 58 — executed commitments in the slope game

New modules: Spec/SharedSlopeExec and Proofs/SharedSlopeExec, imported and
indexed under Algorithm 12.

The commitment program for a claim makes both CommitSeed calls at every
leaf position and returns the claim; it is bounded by 2*tau*2^kappa, and
its evaluation certificate records every call's entry. Run as the second
phase after the adversary, the final state is the finished program holding
the claim, with every named entry in the cipher history. A winning run
(chained claim, stored mask, differing slopes with equal masked images) is
covered by the five events as before, now with the queried facts derived.
The two-phase final-world posterior lemma, the two-phase pair bound and
the two-phase trap bounds give the total with budget q+2*tau*2^kappa.

Category III, connecting the fork's accepted attempts, challenge
separation, signature/replay accounting, extraction and signing
simulation remain open.

The fifty-eighth full validation passed: 3437 build jobs and 14126 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 59 — shared-model scheme skeleton

New modules: Spec/SharedScheme and Proofs/SharedScheme, imported and
indexed under Algorithms 3–4.

The shared world (hidden family, table, histories, log) is the abstract
game's other-state. The public oracle runs one program step and answers by
component. Verification runs the ordered reconstruction lifted to the
product-valued oracle, the Hashaux query, the supplied middle, the
Hashlines query, and the Algorithm-4 suffix through the existing
verificationInput. The fork's accepted attempts share the typed hash input,
and lifted programs evaluate against the digest projection.

The honest signing services, the proof that this verification's
reconstruction and chain are the executed-chain games, the challenge
separation under a declared expansion, the signature/replay accounting,
extraction and signing simulation remain open; the declared target for the
middle and expansion is a recorded user decision.

The fifty-ninth full validation passed: 3439 build jobs and 14252 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 60 — executed verification and the chain games

New module: Proofs/SharedSchemeChain, imported and indexed under
Algorithms 3–4.

A successful executed verification gives a successful reconstruction
evaluation on the digest projection of the table, the Hashaux lookup, the
middle's evaluation and the Hashlines lookup, with the recovered record
assembled from them. Two such verifications with equal lines digests have
equal roots in a digest-collision-free table. Viewing the projected table
as a shared-model result, a disagreeing commonly revealed seed gives a
digest collision or a seed collision with recorded entries, and hidden
indices differing at an execution give the unique complete seed vector by
the seed-extraction lemma.

Relating the middle's value to the fold and slope identities, the honest
signer program, challenge separation under a declared expansion,
signature/replay accounting, extraction and signing simulation remain
open.

The sixtieth full validation passed: 3440 build jobs and 14259 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 61 — candidate verifier middle

New modules: Spec/CandidateVerifier and Proofs/CandidateVerifier,
imported and indexed under Algorithm 12; the verifier middle's signature
in SharedScheme now receives salt, auxiliary data and hidden indices.

The literal leaf fold never reads the hidden index, so with the
reconstruction's revealed seeds bound to the seed array it computes the
prefix sums of any complete seed vector agreeing with them; the fold of
each execution is the affine share, and the collected shares form the
affine share matrix. The candidate middle queries the mask at the
auxiliary digest, folds, reads line 21 as the binary base equation and
returns delta, the suffix values and the base; a successful evaluation
records the mask lookup and returns exactly these for the agreeing vector,
and the base equals (maskedSlope − plain)⊗Gray(hidden) plus the
intercept's columns.

Composing this with the two-verification seed vector and the slope game,
the honest signer program, challenge separation under a declared
expansion, signature/replay accounting, extraction and signing simulation
remain open.

The sixty-first full validation passed: 3442 build jobs and 14286 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 62 — fork to slope claim

New module: Proofs/ForkSlope, imported and indexed under Algorithm 12.

Two successful candidate-middle verifications on one collision-free table
with equal lines digests share the auxiliary digest, mask, plain check,
base, corrections, root and salt; where the hidden indices differ, either
a recorded seed collision occurs or the merge completions agree and the
masked slope of that execution equals the plain check. Supporting lemmas:
salt recovery from equal roots through the outer lookup, congruence of
the fold's slope and intercept in the seed vector at one execution, and
a differing Gray bit for distinct indices.

Feeding this into the probabilistic slope game, the honest signer
program, challenge separation under a declared expansion,
signature/replay accounting, extraction and signing simulation remain
open.

The sixty-second full validation passed: 3443 build jobs and 14295 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 63 — honest signer commitment program

New modules: Spec/SharedSigner and Proofs/SharedSigner, imported and
indexed under Algorithm 10.

The honest signer's commitment phase is an executed program in the shared
model: full seed-tree expansion and leaf commitments as cipher calls, row
and outer hashes, PRG table and corrections, Hashaux, the mask-oracle
consistency matrix, the commit arithmetic and Hashlines with a parameter
tail (literal and verifier readings named). A successful evaluation is
Algorithm 7's commitment under the induced primitives with every chain
query stored, every leaf's commitment entries recorded and the result
equal to the commit arithmetic at the stored mask; the program is bounded.

The PIOP, retry and opening phases as signing services, feeding the fork
into the probabilistic slope game, challenge separation under a declared
expansion, signature/replay accounting, extraction and signing simulation
remain open.

The sixty-third full validation passed: 3445 build jobs and 14377 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 64 — shared-model signing services

New modules: Spec/SharedSigning and Proofs/SharedSigning, imported and
indexed under Algorithm 3.

The abstract game's components are instantiated in the shared model:
preparation (uniform salt and root, executed commitment, PIOP prover),
opening (Algorithm 11 observed on the HashPiop digest, optional body),
verification (executed verifier on existing bodies), key generation
(witness sampler at a fixed instance, uniform family). Support lemmas:
a program run on the world ends in a value evaluating on the final world;
every prepared state is read from an evaluating commitment; the opening
service is deterministic; every honest signature with a body carries the
state's fields and has its digest stored at the typed HashPiop input.

Query accounting from the fork to the executed chain games, challenge
separation under declared expansions, feeding the fork into the
probabilistic slope game, extraction and signing simulation remain open.

The sixty-fourth full validation passed: 3447 build jobs and 14445 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 65 — fork branches on a common prefix

New module: Proofs/ForkSlopePrefix, imported and indexed under Algorithm 12.

Visited hash inputs of an evaluation; restriction of an evaluation to a
prefix table containing all visited inputs; monotonicity in the cipher
history; the fork-to-slope outcome for one verification per branch on the
prefix table with the union of histories.

Bounding visits outside the prefix by the chain-mention and fresh-digest
bounds, the fork's query accounting, challenge separation under declared
expansions, feeding the slope game, extraction and signing simulation
remain open.

The sixty-fifth full validation passed: 3448 build jobs and 14464 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 66 — chains across the fork cut

New module: Proofs/ForkCut, imported and indexed under Algorithm 12.

The cut property of a branch log relative to the fork table; a stored
chain with its sink in the cut is present in the cut or mention-bad; the
Hashlines string's mention of the auxiliary digest and its separation
from the chain strings; the verifier's chain for every execution in the
cut whenever its lines string is, up to the mention event.

Charging the lines string's fixed-target event, the mask input's
position across the fork, deriving the cut property from the forking
construction, challenge separation, extraction and signing simulation
remain open.

The sixty-sixth full validation passed: 3449 build jobs and 14483 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 67 — fixed-target event along a branch

New module: Proofs/ForkCutRun, imported and indexed under Algorithm 12.

Cut preservation along a traced shared run; the fixed-target predicate
and its per-query mass; the run-level bound budget·|Digest|⁻¹ plus the
initial indicator; vanishing of the indicator on a pre-cut fresh log; a
stored target value is in the fork table or the event occurred.

Deriving the cut from the forking construction, summing over a branch's
service runs, the mask input's position across the fork, challenge
separation, extraction and signing simulation remain open.

The sixty-seventh full validation passed: 3450 build jobs and 14503 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 68 — shared-world invariants along the game

New module: Proofs/SharedGameInvariant, imported and indexed under
Algorithm 3.

Service-wise preservation of other-state predicates along the abstract
run, cut and fork; the shared services preserve program-run-preserved
predicates; well-formedness from key generation; cut preservation; the
snapshot's world is pre-cut and both branches' attempts are cut at it.

Summing branch events over service runs, the mask input's position,
challenge separation, extraction and signing simulation remain open.

The sixty-eighth full validation passed: 3451 build jobs and 14571 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 69 — visited inputs of the verification

New module: Proofs/VisitedInputs, imported and indexed under Algorithm 12.

Visited-input composition along binds and lifts; the row loop's and the
reconstruction's visited inputs; the candidate middle's single mask
input; the verification's visited inputs as chain, auxiliary, middle and
lines strings.

Composing into the fork's deterministic outcome, summing branch events
over service runs, the mask input's position across the fork, challenge
separation, extraction and signing simulation remain open.

The sixty-ninth full validation passed: 3452 build jobs and 14623 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 70 — one branch accounted

New module: Proofs/BranchAccounting, imported and indexed under
Algorithm 12; VisitedInputs' reconstruction and verification lemmas
return the reconstruction record and the observed coverage.

The mask-after-cut event; on a cut, well-formed branch, an accepting
candidate verification with the fixed target as lines value visits only
fork-table inputs, or the fixed-target, mention or mask event occurred.

Combining both branches into the slope outcome, summing branch events
over service runs, charging or settling the mask event, challenge
separation, extraction and signing simulation remain open.

The seventieth full validation passed: 3453 build jobs and 14628 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 71 — deterministic fork outcome

New module: Proofs/ForkOutcome, imported and indexed under Algorithm 12.

Budget-free evaluation of a run ending in a value; attempt provenance
from the verification service along the run and the fresh branch; the
shared verification call's executed verification and lines value; the
branch events and slope outcome; the composed fork outcome theorem.

Charging the branch events, the mask event, hidden-index separation,
feeding the slope game, extraction and signing simulation remain open.

The seventy-first full validation passed: 3454 build jobs and 14664 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 72 — game-level event bound

New module: Proofs/GameEventBound, imported and indexed under Algorithm 3.

Service bounds; the composed sign, verification and oracle bounds of the
abstract scheme; the run-level bound by induction on fuel; finalization
keeps the terminal; the fresh-branch bound.

Instantiating the constants for the shared services' fixed-target and
mention events, the mask event, hidden-index separation, feeding the
slope game, extraction and signing simulation remain open.

The seventy-second full validation passed: 3455 build jobs and 14703 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 73 — fixed-target event over the shared game

New module: Proofs/SharedTargetBound, imported and indexed under
Algorithm 3.

The fixed-target event on shared worlds; the program-run bound; the
service bound of the shared components with a common budget bound; the
absence of the event at a well-formed snapshot; the fresh-branch bound.

The mention event's bound, the mask event, hidden-index separation,
feeding the slope game, extraction and signing simulation remain open.

The seventy-third full validation passed: 3456 build jobs and 14739 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 74 — size-dependent game-level bound

New module: Proofs/GameEventBoundLen, imported and indexed under
Algorithm 3.

Log-length growth of a traced run; size-dependent service bounds; the
composed service bounds under a level; the run-level and fresh-branch
bounds with the remaining-growth invariant.

The mention event's instance, the mask event, hidden-index separation,
feeding the slope game, extraction and signing simulation remain open.

The seventy-fourth full validation passed: 3457 build jobs and 14785 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 75 — mention event over the shared game

New module: Proofs/SharedMentionBound, imported and indexed under
Algorithm 3.

The mention event on shared worlds; the per-run bound at a length and its
monotonicity; the program-run bound and log growth; the size-dependent
service bound of the shared components; the fresh-branch bound.

Charging the prefix's mention event, the mask event, hidden-index
separation, feeding the slope game, extraction and signing simulation
remain open.

The seventy-fifth full validation passed: 3458 build jobs and 14820 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 76 — event bound along the cut

New module: Proofs/CutEventBound, imported and indexed under Algorithm 3.

The cut event reader; the size-dependent event bound along the cut; the
snapshot's level premise.

Assembling the prefix and branch bounds for the mention and collision
events from key generation, the mask event, hidden-index separation,
feeding the slope game, extraction and signing simulation remain open.

The seventy-sixth full validation passed: 3459 build jobs and 14850 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 77 — collision event and prefix bounds

New module: Proofs/SharedCollisionBound, imported and indexed under
Algorithm 3.

The collision event, its per-run bound and service bound; collision
freedom without the event; key generation's empty log; the generic
prefix bound of the cut experiment; the snapshot's level premise; the
prefix mention and collision bounds.

The fork experiment's union of events, the mask event, hidden-index
separation, feeding the slope game, extraction and signing simulation
remain open.

The seventy-seventh full validation passed: 3460 build jobs and 14887 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 78 — charged events of the fork experiment

New module: Proofs/ForkEventUnion, imported and indexed under
Algorithm 12.

Boolean union bounds; the snapshot's remaining fuel; the branch and fork
bad events and their experiment; the snapshot's well-formedness; the
one-branch bound; the fork experiment's charged-event bound.

Combining with the deterministic fork outcome, the mask event,
hidden-index separation, feeding the slope game, extraction and signing
simulation remain open.

The seventy-eighth full validation passed: 3461 build jobs and 14923 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 79 — fork experiment split by charged events

New module: Proofs/ForkGoodOutcome, imported and indexed under
Algorithm 12.

Pointwise bind and image split bounds; the good fork experiment; the
success split; the deterministic good-fork outcome (slope outcome or a
mask event); the composed bound.

Charging the seed-collision member of the slope outcome, the mask event,
hidden-index separation, feeding the slope game, extraction and signing
simulation remain open.

The seventy-ninth full validation passed: 3462 build jobs and 14936 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 80 — uniform fork-to-slope data

New module: Proofs/ForkSlopeUniform, imported and indexed under
Algorithm 12.

The fork-to-slope lemma with the reconstructions, auxiliary digest and
stored mask shared across executions.

The two recorded decisions (mask after the fork; single versus multi-
fork), the seed-collision charge, feeding the slope game, extraction and
signing simulation remain open.

The eightieth full validation passed: 3463 build jobs and 14937 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 81 — candidate verifier against the honest signer

New module: Proofs/HonestCandidate, imported and indexed under
Algorithm 12.

Honest auxiliary data; the honest slope, masked slope and intercept
identities; the candidate base equals the honest base check.

Executed completeness (honest opening reconstruction under a declared
nodes binding, tail and expansion agreement), the two recorded
decisions, the seed-collision charge, the slope game, extraction and
signing simulation remain open.

The eighty-first full validation passed: 3464 build jobs and 14946 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 82 — fork outcomes with uniform data

New module: Proofs/ForkOutcomeUniform, imported and indexed under
Algorithm 12.

The uniform slope data; the uniform prefix restriction, deterministic
fork outcome and good-fork outcome.

The two recorded decisions, executed completeness, the seed-collision
charge, the slope game, extraction and signing simulation remain open.

The eighty-second full validation passed: 3465 build jobs and 14952 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 83 — from uniform fork data to slope consistency

New module: Proofs/SlopeConsistencyLink, imported and indexed under
Algorithm 12.

Masked slope as masked image; all executions' plain images under
separation; the slope dichotomy; the candidate witness value under a
common slope.

Reduction to the slope experiment, the two recorded decisions, the seed-
collision charge, the PIOP extraction step, and signing simulation remain
open.

The eighty-third full validation passed: 3466 build jobs and 14956 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 84 — witness line recovery

New module: Proofs/WitnessLineRecovery, imported and indexed under
Algorithm 12.

The constant term from two evaluations; the witness coordinate from the
two branches' candidate values.

All remaining reduction steps depend on the five recorded decisions or
on the reduction architecture for cipher-side bounds.

The eighty-fourth full validation passed: 3467 build jobs and 14959 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 85 — candidate BAVC target

New modules: Spec/CandidateBAVC and Proofs/CandidateBAVC, imported and
indexed under Algorithm 9 as the named candidate target.

The candidate opening and reconstruction; the leaf program's evaluation;
the reconstruction's evaluation; the honest key's commitments; the budget.

The candidate verifier and signing components, the fork chain for them,
executed completeness, the signing simulator, the PIOP extraction step
and the composed final theorem remain open.

The eighty-fifth full validation passed: 3469 build jobs and 14997 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 86 — candidate scheme

New modules: Spec/CandidateScheme and Proofs/CandidateSchemeChain,
imported and indexed under Algorithm 3.

The candidate verifier, opening service and components; the
verification's decomposition and visited inputs.

The fork chain for the candidate scheme, executed completeness, the
signing simulator, the PIOP extraction step and the composed final
theorem remain open.

The eighty-sixth full validation passed: 3471 build jobs and 15039 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 87 — candidate fork-to-slope lemma

New module: Proofs/CandidateForkSlope, imported and indexed under
Algorithm 12.

The completion of an opening by another; the uniform fork-to-slope
lemma over the candidate reconstruction.

Branch accounting and fork outcomes for the candidate scheme, its game
invariants and event bounds, executed completeness, the signing
simulator, the PIOP extraction step and the composed final theorem remain
open.

The eighty-seventh full validation passed: 3472 build jobs and 15044 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 88 — candidate branch accounting

New module: Proofs/CandidateBranch, imported and indexed under
Algorithm 12.

Branch accounting, the uniform slope data and the prefix restriction for
the candidate scheme.

The candidate components' game invariants, event bounds and fork
outcomes, executed completeness, the signing simulator, the PIOP
extraction step and the composed final theorem remain open.

The eighty-eighth full validation passed: 3473 build jobs and 15050 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 89 — candidate game bounds

New module: Proofs/CandidateGameBounds, imported and indexed under
Algorithm 3.

Preservation, snapshot and branch invariants, service bounds and prefix
bounds for the candidate components.

Attempt provenance and fork outcomes for the candidate components,
executed completeness, the signing simulator, the PIOP extraction step
and the composed final theorem remain open.

The eighty-ninth full validation passed: 3474 build jobs and 15093 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 90 — candidate fork outcomes

New module: Proofs/CandidateForkOutcome, imported and indexed under
Algorithm 12.

Attempt provenance, the fork outcome, the charged events and bound, the
success split and the good-fork outcome for the candidate scheme.

Executed completeness, the signing simulator, the PIOP extraction step
and the composed final theorem remain open.

The ninetieth full validation passed: 3475 build jobs and 15123 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 91 — candidate executed completeness

New module: Proofs/CandidateCompleteness, imported and indexed under
Algorithm 9 with the candidate target.

Constructive evaluation lemmas; fold and share collection success; the
candidate middle, leaf and reconstruction evaluations; an honest
candidate signature verifies to the committed lines digest.

The signing simulator, the PIOP extraction step and the composed final
theorem remain open.

The ninety-first full validation passed: 3476 build jobs and 15158 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 92 — PIOP extraction step

New module: Proofs/PIOPExtraction, imported and indexed under
Algorithm 12.

The affine randomness value; the extracted witness and lines; the
composed verifier as the lines' prover polynomial; the restored-tuple
identity; the vanishing difference.

The Schwartz–Zippel and batching steps, the signing simulator and the
composed final theorem remain open.

The ninety-second full validation passed: 3477 build jobs and 15172 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 93 — deterministic fork extraction

New module: Proofs/ForkExtraction, imported and indexed under
Algorithm 12. The per-execution fork-slope disjunct and the uniform
slope data now carry the completion agreement of the two branches, and
the fork outcomes carry the accepted transcript's coefficient tuple.

The good-fork extraction: seed collision, or slope-game win at the
stored mask, or a common slope with the vanishing difference polynomial
at the first branch's challenge.

The Schwartz–Zippel and batching steps, the signing simulator and the
composed final theorem remain open.

The ninety-third full validation passed: 3478 build jobs and 15174 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 94 — event-union skeleton of the composed reduction

New module: Proofs/CandidateReduction, imported and indexed under
Algorithm 12.

The named events and the extraction event of a fork result; the event
experiment and its union bound; a winning fork without the charged
events is a named event or an extraction; the good-fork and fork
experiments bounded by the events' sum and the charged-event bound; the
extraction's vanishing constant term.

The bounds of the named events (mask after fork, separation, seed
collision, slope game, zero challenge, Schwartz–Zippel), the batching
step, the signing simulator and the composed final theorem remain open.

The ninety-fourth full validation passed: 3479 build jobs and 15228 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 95 — composed forgery bound skeleton

New module: Proofs/ForgeryReduction, imported and indexed under
Algorithm 12.

The union event; the fork experiment bounded by the union event and the
charged-event bound; the random-index event experiment and its union
bound; the random-index fork experiment as the uniform mixture of the
fork experiments; the forgery advantage bound through the
forgery-to-fork inequality.

The named events' probabilities, the batching step, the signing
simulator and the final RSD statement remain open.

The ninety-fifth full validation passed: 3480 build jobs and 15240 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 96 — extraction split into batching and solution events

New module: Proofs/ExtractionSplit, imported and indexed under
Algorithm 12.

The solution predicate (zero mux syndrome residual and unitary
selectors); the solution and batching events; extraction is one of
them; the solution event names an explicit solution; the batching
event is an exact cancellation of the batched residual and unitary
checks at the signature's batching challenges; event monotonicity at a
random index; the forgery bound with the split events.

The named events' probabilities, the batching event's bound, the
signing simulator and the witness-free solver remain open.

The ninety-sixth full validation passed: 3481 build jobs and 15259 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 97 — solver and simulated statement

New module: Proofs/SimulatedSolver, imported and indexed under
Algorithm 12.

A scheme's random-index event experiment; the solver's output and the
solver; the solver's success; the solution event yields the solver's
output as a solution; the solution event is at most the solver's
success; the forgery bound transferred to a scheme's events and the
solver's success under a uniform per-event simulation gap.

The named simulator and its gaps, the named events' probabilities and
the batching event's bound remain open.

The ninety-seventh full validation passed: 3482 build jobs and 15280 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 98 — named witness-free simulator

New modules: Spec/CandidateSimulator (imported by the specification root)
and Proofs/CandidateSimulator, indexed under Algorithm 3.

The recomputed coefficient tuple of a committed transcript; the simulated
signing (fake witness, honest commitment, digest first, candidate retry,
programmed answer); the simulated scheme; witness-freeness of its
signing; its other components are the candidate scheme's; the forgery
bound instantiated at the simulated scheme under the gap hypothesis.

The simulation gap, the named events' probabilities and the batching
event's bound remain open.

The ninety-eighth full validation passed: 3484 build jobs and 15297 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 99 — simulated transcript completeness

New module: Proofs/SimulatedCompleteness, imported and indexed under
Algorithm 3.

The candidate verification of an executed commitment opened at hidden
indices evaluates to the inverted challenge, the affine share values on
the committed seeds and the committed lines digest; the recomputed
verification input hashes the committed lines digest and the simulator's
coefficient tuple.

The simulator's programming step in the game, its failure event, the
hidden-share independence, the PIOP honest-verifier zero knowledge, the
named events' probabilities and the batching event's bound remain open.

The ninety-ninth full validation passed: 3485 build jobs and 15299 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 100 — provenance of simulated signatures

New module: Proofs/SimulatedSign, imported and indexed under Algorithm 3.

Every simulated signature comes from an executed commitment with a fake
witness and a chosen digest; a body carries the candidate retry's return
and the programmed table entry at the recomputed input, absent before;
a bodiless signature leaves the table unchanged.

The simulator's failure event, hidden-share independence, PIOP
honest-verifier zero knowledge, the named events' probabilities and the
batching event's bound remain open.

The hundredth full validation passed: 3486 build jobs and 15308 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 101 — summary of the composed bound

Documentation only: the composed reduction summary in README and the
explicit-terms checklist in PLAN, recording which remaining terms are
proof tasks and which need a modelling decision on the challenge and
batching expansions. No Lean source changed; the hundredth validation
(3486 jobs, 15308 declarations) remains current. Assumptions and Final
are unchanged. The persistent goal remains active and the full signature
reduction remains incomplete.

## Continuation 102 — prover polynomial mask split

New module: Proofs/PIOPMaskSplit, imported and indexed under Algorithm 19.

Additivity and zero of the formatted mask and randomness; the arithmetic
body as mask times point plus a mask-free part; the prover polynomial as
its zero-randomness value plus the mask times X; adding randomness adds
its mask; the difference of two prover polynomials with the same
randomness is mask-free.

The packed mask constants' uniformity, the one-time-pad step and the
rest of the simulation gap remain open.

The hundred-and-second full validation passed: 3487 build jobs and 15316 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 103 — mask coefficients

New module: Proofs/PIOPMaskCoeff, imported and indexed under Algorithm 19.

The packed layer polynomial; the mask as a sum of shifted packed layers;
the generic coefficient formula; constant, linear and vanishing higher
coefficients of a packed line; the mask coefficients for randomness lines
(constant of layer d-2-k plus slope of layer d-1-k); the hashed prover
coefficients as zero-randomness coefficients padded by the mask.

The packed constants' uniformity from the hidden share and the
one-time-pad step remain open.

The hundred-and-third full validation passed: 3488 build jobs and 15333 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 104 — packing uniformity and one-time pad

New module: Proofs/PackingUniform, imported and indexed with the field
representation.

The full-width coefficient encoding is a bijection; the packing
equivalence; uniform bits pack to a uniform element; a uniform pad on a
fixed value, on a distributed value, and on a pair coordinate.

Relating the honest randomness lines' constants to the hidden share, and
the one-time-pad step on the hashed coefficients, remain open.

The hundred-and-fourth full validation passed: 3489 build jobs and 15339 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 105 — hidden-share translation

New module: Proofs/HiddenShareTranslation, imported and indexed under
Algorithm 10.

The execution fold's accumulator as a sum; the common accumulator as the
hidden party's vector plus the others; the witness correction, the
randomness lines' constants and the plain check as translations.

The affine bijection of the revealed triple, the PRG hypothesis and the
one-time-pad step on the transcript remain open.

The hundred-and-fifth full validation passed: 3490 build jobs and 15348 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 106 — revealed triple bijection

New module: Proofs/RevealedBijection, imported and indexed under
Algorithm 10.

The plain check as check coordinates plus the mask image of the payload;
the revealed map and its inverse; the bijection; a uniform hidden vector
reveals a uniform triple; independence of the constants.

Connecting the honest transcript to the revealed map, the PRG
hypothesis, the hashed-coefficient pads and the full gap remain open.

The hundred-and-sixth full validation passed: 3491 build jobs and 15362 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 107 — honest transcript as the revealed map

New module: Proofs/TranscriptRevealed, imported and indexed under
Algorithm 10.

The other parties' constants; the honest base-ring triple as the
revealed map of the hidden vector; the randomness lines' constants as
algebra images of the accumulator; a uniform hidden vector makes the
honest triple uniform and witness-independent.

The PRG hypothesis, the hashed-coefficient pads, the top coefficient's
witness independence and the full simulation gap remain open.

The hundred-and-seventh full validation passed: 3492 build jobs and 15368 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 108 — pads on the hashed coefficients

New module: Proofs/HashedPads, imported and indexed under Algorithm 19.

The hashed tuple as the zero-randomness tuple plus the mask
coefficients; the mask coefficient of bit-constant lines as a packed
layer constant plus a slope term; the packed constant as the coefficient
encoding in the submitted field; uniform layer bits give a uniform
packed constant and a uniform pad.

The per-execution corrections' translation, the joint pad statement, the
top coefficient's witness independence and the PRG hypothesis remain
open.

The hundred-and-eighth full validation passed: 3493 build jobs and 15374 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 109 — corrections as translations

New module: Proofs/CorrectionTranslation, imported and indexed under
Algorithm 10.

The other parties' sum at an execution; an execution's accumulator as
its hidden vector plus the others; the correction as a translation; the
transmitted corrections.

The joint pad statement across executions, the top coefficient's witness
independence and the PRG hypothesis remain open.

The hundred-and-ninth full validation passed: 3494 build jobs and 15379 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 110 — top coefficient from slopes

New module: Proofs/TopCoefficient, imported and indexed under
Algorithm 19.

The slope mux and slope tree; the top coefficient of a mux and of the
mux tree; the unitary layers below the top for at least three layers;
the prover arithmetic's top coefficient as the mask's top coefficient
plus the chunks' slope trees.

The joint pad statement, the PRG hypothesis and the assembled
zero-knowledge statement remain open.

The hundred-and-tenth full validation passed: 3495 build jobs and 15406 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 111 — the revealed view as a bijection

New module: Proofs/ViewBijection, imported and indexed under Algorithm 10.

The block index as the product equivalence; the layers re-indexing
equivalence; the view map; the middle equivalence (layers, packing,
translation); the view equivalence and its explicit form; a uniform
hidden vector gives a uniform view; independence of the constants.

Connecting the view to the actual hashed tuple and auxiliary data of the
honest signer, the PRG hypothesis, and the assembled simulation gap
remain open.

The hundred-and-eleventh full validation passed: 3496 build jobs and 15416 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 112 — hashed coefficients from the view

New module: Proofs/HashedView, imported and indexed under Algorithm 19.

Additivity of the packed constant; the mask coefficient below the top as
one layer's packed constant plus one layer's slope term; the
accumulator's layer as the hidden party's layer plus the others'; the
honest randomness lines' formatted shape.

The assembled honest-view statement (auxiliary data and hashed tuple as
functions of the view), the PRG hypothesis and the simulation gap remain
open.

The hundred-and-twelfth full validation passed: 3497 build jobs and 15427 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 113 — the honest view

New module: Proofs/HonestView, imported and indexed under Algorithm 19.

The honest hashed coefficient below the top as zero-randomness
coefficient, hidden packed layer, others' packed layer and slope term;
the witness correction and plain check as revealed-map components.

The PRG hypothesis and the assembled simulation gap remain open.

The hundred-and-thirteenth full validation passed: 3498 build jobs and 15431 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 114 — honest data uniform under a uniform hidden vector

New module: Proofs/HonestViewUniform, imported and indexed under
Algorithm 10.

The layer reversal and its involutivity; the honest data as the view
post-processed by reversal and translation; the post-processing
equivalence; the honest data uniform under a uniform hidden vector;
independence of the witness-dependent constants.

The PRG hypothesis, the corrections of positive executions, the top
coefficient's identity across honest and simulated transcripts, and the
assembled simulation gap remain open.

The hundred-and-fourteenth full validation passed: 3499 build jobs and 15442 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 115 — the PRG hypothesis

New module: Proofs/PRGHypothesis, imported and indexed under Algorithm 10.

A party's vector as the PRG vector of its seed; the random table's row
as that vector; the named PRG-uniformity predicate; the honest data
uniform and witness-independent over a uniform hidden seed under it.

Linking the committed signature data to the honest data, the simulated
transcript's distribution, the unqueried-seed condition and the
assembled gap remain open.

The hundred-and-fifteenth full validation passed: 3500 build jobs and 15450 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 116 — committed signature data as the honest data

New module: Proofs/SignatureData, imported and indexed under
Algorithm 10.

The other parties' packed layers, the zero-randomness hashed
coefficients and the slope terms as named constants; the hashed
coefficients below the top as the honest data's middle component; the
witness correction and plain check as its outer components.

Lifting to the executed commitment and the prepared signing state, the
simulated transcript's distribution, the unqueried-seed condition and the
assembled gap remain open.

The hundred-and-sixteenth full validation passed: 3501 build jobs and 15467 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 117 — the prepared state's data

New module: Proofs/PreparedData, imported and indexed under Algorithm 3.

The hidden party's vector as the PRG vector of its seed; the prepared
state's auxiliary components, lines and hashed coefficients as the
committed arithmetic's over the random table of the committed seeds.

Composing with the honest data map over the hidden seed, the simulated
transcript's distribution, the unqueried-seed condition and the
assembled gap remain open.

The hundred-and-seventeenth full validation passed: 3502 build jobs and 15469 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 118 — the prepared state's data as honest data

New module: Proofs/PreparedHonestData, imported and indexed under
Algorithm 3.

The prepared state's hashed coefficients below the top, witness
correction and plain check as the honest data map of the hidden seed's
PRG vector, with explicit constants.

The simulated transcript's matching form, the unqueried-seed condition
and the gap over the signing game remain open.

The hundred-and-eighteenth full validation passed: 3503 build jobs and 15471 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 119 — data-level simulation step

New module: Proofs/DataSimulation, imported and indexed under Algorithm 3.

A signer's revealed data as a function of the hidden vector; the real and
fake signers' data share all witness-free constants; equal distributions
under a uniform hidden vector; equal distributions over the hidden seed
under the PRG hypothesis and a uniform seed.

The hidden leaf seed's uniformity, the lifting to the signing game's
distributions (salt, root, table) and the gap composition remain open.

The hundred-and-nineteenth full validation passed: 3504 build jobs and 15475 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 120 — fresh-key encryption uniform

New module: Proofs/FreshKeyUniform, imported and indexed with the ideal
cipher.

A fresh key; fresh key implies fresh input and fresh output; the unused
outputs of a fresh key are all blocks; encryption under a fresh key is
uniform over all blocks.

The application to the hidden leaf seed (parent seed unused as a key),
the accounting of that event, and the lifting of the data-level
simulation to the signing game remain open.

The hundred-and-twentieth full validation passed: 3505 build jobs and 15480 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 121 — leaf seed uniform through the layout

New module: Proofs/LeafSeedUniform, imported and indexed with the ideal
cipher.

An output-uniform layout; the full layout is output-uniform; the
expansion of a fresh parent key through an output-uniform layout is a
uniform seed.

The truncated layout's output uniformity, the fresh-parent-key event's
accounting and the lifting of the data-level simulation to the signing
game remain open.

The hundred-and-twenty-first full validation passed: 3506 build jobs and 15484 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 122 — the truncated layout is output-uniform

New module: Proofs/TruncatedLayoutUniform, imported and indexed with the
ideal cipher.

The coordinate embedding of the first 192 positions and its injectivity;
the projection of a uniform block is uniform; the truncated layout is
output-uniform.

The fresh-parent-key event's accounting and the lifting of the data-level
simulation to the signing game remain open.

The hundred-and-twenty-second full validation passed: 3507 build jobs and 15490 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 123 — corrections as one-time pads

New module: Proofs/CorrectionUniform, imported and indexed under
Algorithm 10.

Subtracting a uniform pad from a fixed value is uniform; an execution's
correction as a function of its hidden vector; the correction equals that
function at the hidden vector; a uniform hidden vector gives a uniform
correction.

The joint statement over all executions' hidden vectors, the
fresh-parent-key accounting and the lifting to the signing game remain
open.

The hundred-and-twenty-third full validation passed: 3508 build jobs and 15494 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 124 — joint pads over all executions

New module: Proofs/JointPads, imported and indexed under Algorithm 10.

The joint map and its shear equivalence; a uniform joint transcript under
independent uniform hidden vectors; independence of the bijection and
constants; the honest data map as an equivalence; the joint transcript of
execution zero's data and the positive executions' corrections is
uniform.

The game-level lift (salt, root and hash answers), the fresh-parent-key
accounting and the composition over the signing game remain open.

The hundred-and-twenty-fourth full validation passed: 3509 build jobs and 15502 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 125 — leaf seed uniform under the posterior family

New module: Proofs/PosteriorLeafUniform, imported and indexed with the
ideal cipher.

The lazy query's answer as the posterior family's answer; the posterior
family's leaf expansion through an output-uniform layout is a uniform
seed under a fresh parent key.

Locating the hidden leaf's expansion in the commitment program's trace,
the fresh-parent-key event's accounting and the composition over the
signing game remain open.

The hundred-and-twenty-fifth full validation passed: 3510 build jobs and 15504 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 126 — the hidden leaf in the seed tree

New module: Proofs/HiddenLeafNode, imported and indexed with the ideal
cipher. The README also gained a simulation-gap status section.

The tree expansion through the layout; a node's tweak; a node below the
root as the cipher image of its parent; a node's recorded expansion entry;
recorded ancestry and its heredity to the parent; every consistent family
computes a node whose ancestry is recorded.

Relating the recorded ancestry to the commitment program's cipher
history, the fresh-parent-key event's accounting and the composition over
the signing game remain open.

The hundred-and-twenty-sixth full validation passed: 3511 build jobs and 15522 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 127 — the tree expansion's recorded entries

New module: Proofs/TreeEntries, imported and indexed with the ideal
cipher.

The tree expansion records every expanded internal node's expansion
entries at its tree value; every node within the expanded range has its
ancestry recorded.

The fresh-parent-key event (the parent key unused before its expansion),
its accounting over the signing game and the composition into the gap
remain open.

The hundred-and-twenty-seventh full validation passed: 3512 build jobs and 15529 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 128 — the hidden-share step under the posterior family

New module: Proofs/HiddenShareStep, imported and indexed with the ideal
cipher.

A node below the root with recorded parent ancestry and a fresh parent
key is a uniform seed under the posterior family; the honest data of the
hidden leaf's PRG vector is uniform under the fresh-parent-key event and
the PRG hypothesis.

The fresh-parent-key event's probability, the history prefix at the
expansion call, and the composition over the signing game remain open.

The hundred-and-twenty-eighth full validation passed: 3513 build jobs and 15531 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 129 — the fresh-parent-key probability

New module: Proofs/FreshKeyProbability, imported and indexed with the
ideal cipher.

The seeds whose key is used in a history inject into the history's
entries; a uniform parent's key is not fresh with probability at most the
history's length over the number of seeds.

The history prefix at the expansion call, the uniformity of the parent
itself (recursively along the path from the root), and the composition
over the signing game remain open.

The hundred-and-twenty-ninth full validation passed: 3514 build jobs and 15533 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 130 — injective layout keys

New module: Proofs/LayoutKeyInjective, imported and indexed with the ideal
cipher. The README's simulation-gap status was updated through this
continuation.

The full layout's key is injective; the zero extension is injective, so
the truncated layout's key is injective; the fresh-parent-key bound for
each submitted layout.

The parent's uniformity along the path from the root, the history prefix
at the expansion call, the signing procedures' coupling and the
composition over the signing game remain open.

The hundred-and-thirtieth full validation passed: 3515 build jobs and 15539 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 131 — fresh hash answers uniform

New module: Proofs/FreshHashUniform, imported and indexed with the random
oracle.

A fresh answer is uniform; a stored answer is returned; a fresh query
stores its answer; two fresh queries have the same answer distribution.

The signing procedures' coupling and the composition over the signing
game remain open.

The hundred-and-thirty-first full validation passed: 3516 build jobs and 15543 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 132 — the public hash answer at a fresh input

New module: Proofs/PublicHashFresh, imported and indexed with the random
oracle.

The one-step run of a single-hash program as the oracle query followed by
the terminal state; the public hash answer at an absent input is the
uniform digest.

The signing procedures' coupling and the composition over the signing
game remain open.

The hundred-and-thirty-second full validation passed: 3517 build jobs and 15559 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 133 — the public mask answer at a fresh input

New module: Proofs/PublicMaskFresh, imported and indexed with the random
oracle.

The public mask answer at an absent input is the uniform mask component.

The signing procedures' coupling and the composition over the signing
game remain open.

The hundred-and-thirty-third full validation passed: 3518 build jobs and 15562 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 134 — single-step runs

New module: Proofs/SingleStepRuns, imported and indexed with the random
oracle.

A finished program's run; a single cipher query's run.

The signing procedures' coupling and the composition over the signing
game remain open.

The hundred-and-thirty-fourth full validation passed: 3519 build jobs and 15572 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 135 — fuel monotonicity of the traced run

New module: Proofs/RunFuel, imported and indexed with the random oracle.
The plan gained the signing-coupling checklist.

A bounded program's traced run does not change with extra fuel.

The run-splitting lemma over a program bind, the commitment program's
decomposition, the lines-query freshness, the fresh-parent chain and the
composition over the signing game remain open.

The hundred-and-thirty-fifth full validation passed: 3520 build jobs and 15597 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 136 — the run-splitting lemma

New module: Proofs/RunBind, imported and indexed with the random oracle.

The continuation of a split run and its interaction with the collision
mark; the traced run of a bind as the first program's run continued.

The commitment program's prefix/tail decomposition, the lines-query
freshness, the fresh-parent chain and the composition over the signing
game remain open.

The hundred-and-thirty-sixth full validation passed: 3521 build jobs and 15609 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 137 — the commitment program's decomposition

New module: Proofs/CommitDecomposition, imported and indexed under
Algorithm 10.

Associativity of the program bind; the prefix data; the witness-free
prefix; the witness-dependent tail; the commitment program as the prefix
bound to the tail.

The lines-query freshness, the fresh-parent chain and the composition
over the signing game remain open.

The hundred-and-thirty-seventh full validation passed (after a proof fix and
relaunch): 3522 build jobs and 15614 project declarations, with only propext,
Classical.choice and Quot.sound transitively. Checked the new module import
and index entry, standalone specification separation and exactly three
final discrepancy statements. No placeholder, cryptographic axiom or
unchecked shortcut was introduced. Assumptions and Final are unchanged. The
persistent goal remains active and the full signature reduction remains
incomplete.

## Continuation 138 — the commitment's split run

New module: Proofs/CommitSplitRun, imported and indexed under
Algorithm 10.

The prefix budget and its relation to the commitment budget; the prefix
and tail bounds; the traced run of the commitment as the prefix run
continued; the shared-world form.

The lines-query freshness in the tail, the fresh-parent chain and the
composition over the signing game remain open.

The hundred-and-thirty-eighth full validation passed: 3523 build jobs and 15622 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 139 — the tail's lines digest

New module: Proofs/TailLinesDigest, imported and indexed under
Algorithm 10.

The lines input and committed result of a witness's tail; the tail as a
single hash query; the committed lines digest of a run result; the
tail's lines digest uniform at a fresh lines input; equal lines-digest
distributions for two witnesses with fresh lines inputs.

The freshness of the lines inputs as a bounded event, the rest of the
tail's data, the fresh-parent chain and the composition over the signing
game remain open.

The hundred-and-thirty-ninth full validation passed: 3524 build jobs and 15639 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 140 — the lines query's mentions

New module: Proofs/LinesMention, imported and indexed under Algorithm 10.

The lines query's window at offset eight; the auxiliary digest among the
lines query's mentions; the lines query differs from the mask input.

Relating a stored lines input to the trace's mention event, the fresh-
parent chain and the composition over the signing game remain open.

The hundred-and-fortieth full validation passed: 3525 build jobs and 15643 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 141 — byte-prefix separation of the chain queries

New module: Proofs/QueryPrefixes, imported and indexed under Algorithm 10.

The byte-bit encoding is injective; lists with different byte prefixes
differ; the lines query differs from the auxiliary query, the outer
string and the row queries.

The prefix run's trace shape, the stored-lines-input mention argument and
the composition over the signing game remain open.

The hundred-and-forty-first full validation passed: 3526 build jobs and 15649 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 142 — a fresh hash step at the support level

New module: Proofs/ThreeHashRun, imported and indexed with the random
oracle.

A fresh hash step's run results as the continuation's runs at a stored
fresh answer with the entry recorded; the collision mark preserves the
other fields.

The three-step iteration for the prefix's final queries, the
stored-lines-input mention argument and the composition over the signing
game remain open.

The hundred-and-forty-second full validation passed: 3527 build jobs and 15658 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 143 — three fresh hash queries' trace shape

New module: Proofs/ThreeHashShape, imported and indexed with the random
oracle.

The zero-fuel run of a finished program; the three fresh hash queries'
stored answers, recorded entries and finished state.

Applying the shape to the commitment prefix's final queries, the
stored-lines-input mention argument and the composition over the signing
game remain open.

The hundred-and-forty-third full validation passed: 3528 build jobs and 15661 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 144 — a stored lines input is a mention event

New module: Proofs/StoredLinesMention, imported and indexed with the
random oracle.

A stored input differing from the two newest entries' inputs and
mentioning the auxiliary answer raises the mention event.

Applying this to the commitment prefix's actual run (the three-query
shape with the prefix's inputs and the traced invariant), the fresh-parent
chain and the composition over the signing game remain open.

The hundred-and-forty-fourth full validation passed: 3529 build jobs and 15663 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 145 — the lines input after the prefix

New module: Proofs/PrefixLinesFresh, imported and indexed under
Algorithm 10.

The head's data; the prefix's last three queries; the auxiliary input of
the head's data; a stored lines input of the auxiliary answer after the
three fresh queries raises the mention event.

The freshness of the three queries themselves as charged events, the
split of the prefix into head and last three queries, the fresh-parent
chain and the composition over the signing game remain open.

The hundred-and-forty-fifth full validation passed: 3530 build jobs and 15667 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 146 — the prefix's head split

New module: Proofs/PrefixHeadSplit, imported and indexed under
Algorithm 10.

The head; the prefix as the head bound to its last three queries; the
head budget and its relation to the prefix budget; the head and last-
three-queries bounds; the prefix's traced run as the head's run
continued.

The three queries' freshness as charged events, the fresh-parent chain
and the composition over the signing game remain open.

The hundred-and-forty-sixth full validation passed: 3531 build jobs and 15676 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 147 — the lines input after a whole prefix run

New module: Proofs/PrefixLinesFreshRun, imported and indexed under
Algorithm 10.

A continuation result at a finished state as a run of the continuation
with the flag combined; a stored lines input of the auxiliary answer
after the prefix's last three fresh queries from a head result with the
run invariants raises the mention event.

The three queries' freshness as charged events, the head's run
invariants from the starting world, the fresh-parent chain and the
composition over the signing game remain open.

The hundred-and-forty-seventh full validation passed: 3532 build jobs and 15678 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 148 — the auxiliary and mask inputs' freshness

New module: Proofs/ChainFresh, imported and indexed under Algorithm 10.

A stored input older than the newest entry mentioning the newest answer
raises the mention event; the auxiliary query differs from the mask
input; a stored auxiliary query after the outer query, and a stored mask
input after the auxiliary query, are mention events.

The outer input's freshness through the head's trace shape, the fresh-
parent chain and the composition over the signing game remain open.

The hundred-and-forty-eighth full validation passed: 3533 build jobs and 15684 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 149 — splitting a collection at its last call

New module: Proofs/CollectLast, imported and indexed under Algorithm 10.

The collector over an initial segment followed by a final call.

The head's split at the last row query, its fresh-run shape, the outer
input's mention argument, the fresh-parent chain and the composition over
the signing game remain open.

The hundred-and-forty-ninth full validation passed: 3534 build jobs and 15688 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 150 — the outer input's freshness

New module: Proofs/OuterFresh, imported and indexed under Algorithm 10.

The outer string differs from every row query by length parity; a stored
outer string after the last row query is a mention event; the row hashes'
collection splits at its last execution.

The head's run split at the last row query, the assembly of all
freshness conditions into one per-signature statement, the fresh-parent
chain and the composition over the signing game remain open.

The hundred-and-fiftieth full validation passed: 3535 build jobs and 15695 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 151 — the head split at its last row query

New module: Proofs/HeadLastSplit, imported and indexed under Algorithm 10.

The head's initial part; the last row query; the head as the initial
part bound to the last row query.

The initial part's bound, the run split, the last row query's fresh-run
shape with the outer string's mention argument, the assembly of the
per-signature freshness statement, the fresh-parent chain and the
composition over the signing game remain open.

The hundred-and-fifty-first full validation passed: 3536 build jobs and 15698 project declarations audited, every transitive axiom allowlisted.

## Continuation 152 — the head's run split at its last row query

New module: Proofs/HeadLastRun, imported and indexed under Algorithm 10.

The initial part's bound (head budget less one) and the last row query's
bound (one); the head's traced run as the initial part's run continued by
the last row query's run; a fresh last row query's run shape (state,
trace and table); a stored outer string over the recorded row hashes
raising the mention event after the head.

The assembly of the per-signature freshness statement across the head,
prefix-tail and tail splits, the fresh-parent chain and the composition
over the signing game remain open.

The hundred-and-fifty-second full validation passed: 3537 build jobs and 15707 project declarations audited, every transitive axiom allowlisted.

## Continuation 153 — the mention event persists along a run

New module: Proofs/TraceSuffix, imported and indexed under Algorithm 10.

A prefix event on a log is raised on any extension of the log; the
recorded log is the log with at most one new entry in front; a run's
trace is its starting log with new entries in front; a prefix event on
the starting log is raised on the run's trace and on the trace of any
continuation from a finished result.

The assembly of the per-signature freshness statement (each chain query
and the lines query fresh when asked unless the mention event is raised
on the final trace), the fresh-parent chain and the composition over the
signing game remain open.

The hundred-and-fifty-third full validation passed: 3538 build jobs and 15717 project declarations audited, every transitive axiom allowlisted.

## Continuation 154 — the prefix's last three queries: event or fresh shape

New module: Proofs/PrefixTailOrMention, imported and indexed under
Algorithm 10.

A fresh query's updated table is traced by the recorded entry; three hash
queries either raise the prefix event on the run's trace or were all
fresh with the three-entry shape (generic over the inputs, with the
stored cases supplied as hypotheses); the auxiliary query's tail of the
head's data; the prefix's last three queries from a head result either
raise the mention event or finish with the three answers and a stored
lines input raising the event.

The outer string's stored case from the head's run, the assembly over the
head and tail runs, the fresh-parent chain and the composition over the
signing game remain open.

The hundred-and-fifty-fourth full validation passed: 3539 build jobs and 15722 project declarations audited, every transitive axiom allowlisted.

## Continuation 155 — the prefix run: mention event or fresh lines input

New module: Proofs/PrefixOrMention, imported and indexed under
Algorithm 10.

A bounded program's run with its bound as fuel finishes; the head's run
finishes and, with the last row query fresh at the initial part's result
(explicit condition), a stored outer string raises the mention event; the
prefix run either raises the mention event on its trace or finishes with
the head's data and the three answers, where a stored lines input of the
auxiliary answer raises the event.

The bound on the last row query's stored case (the leaf commitments'
freshness), the tail's lines query under this disjunction, the
fresh-parent chain and the composition over the signing game remain
open.

The hundred-and-fifty-fifth full validation passed: 3540 build jobs and 15730 project declarations audited, every transitive axiom allowlisted.

## Continuation 156 — the commitment run's lines digest up to the event

New module: Proofs/CommitLinesEvent, imported and indexed under
Algorithm 10.

Two continuations that agree off an event are within the event's
probability (generic); each prefix result either raises the mention
event or finishes with the lines input of any witness fresh; two
witnesses' commitment runs have lines-digest distributions within the
prefix's mention-event probability.

The bound on the last row query's stored case (the leaf commitments'
freshness), the bound on the prefix's mention-event probability by the
mention trap bound, the fresh-parent chain and the composition over the
signing game remain open.

The hundred-and-fifty-sixth full validation passed: 3541 build jobs and 15733 project declarations audited, every transitive axiom allowlisted.

## Continuation 157 — the prefix's mention-event probability

New module: Proofs/PrefixMentionBound, imported and indexed under
Algorithm 10.

The per-query mention step (log length times tau + 2 over the digest
count); the prefix run's mention event bounded by the prefix-dependent
trap bound over the prefix budget; two witnesses' commitment runs'
lines-digest distributions within that bound.

The bound on the last row query's stored case (the leaf commitments'
freshness), the fresh-parent chain and the composition over the signing
game remain open.

The hundred-and-fifty-seventh full validation passed: 3542 build jobs and 15736 project declarations audited, every transitive axiom allowlisted.

## Continuation 158 — the prefix statement from the head's initial result

New module: Proofs/PrefixFromHead, imported and indexed under
Algorithm 10.

The bind bound with pointwise costs (generic); a continuation from a
finished result keeps the run invariants; from a head-initial result
with the run invariants and the last row query fresh, the rest of the
prefix either raises the mention event or finishes with the three
answers and a stored lines input raising the event.

The named row-stored event on the head's initial result and the
three-term lines-digest comparison, the fresh-parent chain and the
composition over the signing game remain open.

The hundred-and-fifty-eighth full validation passed: 3543 build jobs and 15739 project declarations audited, every transitive axiom allowlisted.

## Continuation 159 — the commitment run's lines digest up to two events

New module: Proofs/CommitLinesEvents, imported and indexed under
Algorithm 10.

The row-stored event on the head's initial result; the mention event on
a prefix result; from a head-initial result with the last row query
fresh, the rest-of-commitment runs of two witnesses within the mention
event's probability; two witnesses' commitment runs within the mention
event's probability plus the row-stored event's probability, with no
further condition.

The bound on the row-stored event's probability, the fresh-parent chain
and the composition over the signing game remain open.

The hundred-and-fifty-ninth full validation passed: 3544 build jobs and 15748 project declarations audited, every transitive axiom allowlisted.

## Continuation 160 — status ledgers for the signing procedures' coupling

No new module. The README's simulation-gap status now covers the
coupling results of continuations 131–159 and the remaining items; the
human-review ledger records the named row-stored event; the plan's
checklist is unchanged in substance.

The hundred-and-sixtieth full validation passed: 3544 build jobs and 15748 project declarations audited, every transitive axiom allowlisted.

## Continuation 161 — the per-signature sign step

New module: Proofs/SignStep, imported and indexed under Algorithm 3.

A hash query at an absent input binds like a uniform digest with the
table programmed; at a present input like the stored answer; the
prepared data of a commitment run's result; the honest signing
preparation as the commitment run mapped by the prepared data; the
honest scheme's signing unfolded to salt, root, the commitment run, the
PIOP hash query and the opening.

The comparison of the honest and simulated signing at a fixed world
(the input-present event and the commitment run's witness swap), the
row-stored event's bound, the fresh-parent chain and the composition
over the signing game remain open.

The hundred-and-sixty-first full validation passed: 3545 build jobs and 15755 project declarations audited, every transitive axiom allowlisted.

## Continuation 162 — the honest signing against its digest-first form

New module: Proofs/SignCompare, imported and indexed under Algorithm 3.

The first-order fresh query binding; the digest-first honest signing;
the input-present event; the honest signing within the input-present
event's probability of its digest-first form.

The digest-first form against the simulated signing (witness swap and
recomputed coefficients), the input-present event's bound, the
row-stored event's bound, the fresh-parent chain and the composition
over the signing game remain open.

The hundred-and-sixty-second full validation passed: 3546 build jobs and 15761 project declarations audited, every transitive axiom allowlisted.

## Continuation 163 — the simulated signing at a fixed witness

New module: Proofs/SimulatedWith, imported and indexed under Algorithm 3.

The simulated signing at a given witness; the simulated signing as the
uniform mixture over the fake witness of the fixed-witness forms; the
named payload-consistency hypothesis of the honest signer.

The digest-first honest signing against the fixed-witness simulated
signing (retry failure event and payload consistency), the proof of
payload consistency, the commitment run's witness swap for the full
committed result, the events' bounds and the composition over the
signing game remain open.

The hundred-and-sixty-third full validation passed: 3547 build jobs and 15772 project declarations audited, every transitive axiom allowlisted.

## Continuation 164 — the bodies at a returned retry

New module: Proofs/DigestFirstBody, imported and indexed under
Algorithm 3.

A ready candidate attempt's certificate; a returned observation's
certificate; the honest prepared payload equal to the simulator's payload
at the returned counter under payload consistency; the named
retry-failure event and its negation's returned observation.

The digest-first honest signing against the fixed-witness simulated
signing (assembling these bodies with the input-present and
retry-failure events), the proof of payload consistency, the commitment
run's witness swap for the full committed result, the events' bounds and
the composition over the signing game remain open.

The hundred-and-sixty-fourth full validation passed: 3548 build jobs and 15778 project declarations audited, every transitive axiom allowlisted.

## Continuation 165 — the digest-first honest signing against the simulated one

New module: Proofs/DigestFirstVsSimulated, imported and indexed under
Algorithm 3.

The bind bound with a bind-shaped event (generic); a map inside a bind
commuting with the outer bind (generic); the retry-failure event over the
honest preparation and a uniform digest; the digest-first honest signing
within the retry-failure event's probability of the fixed-witness
simulated signing, under payload consistency and a solution witness.

The chaining of the honest signing to the simulated signing at the
honest witness, the witness swap of the fixed-witness simulated signing
(the commitment run's coupling for the full output), the events' bounds,
the proof of payload consistency and the composition over the signing
game remain open.

The hundred-and-sixty-fifth full validation passed: 3549 build jobs and 15802 project declarations audited, every transitive axiom allowlisted.

## Continuation 166 — the honest signing against the simulated scheme's signing

New module: Proofs/HonestToSimulated, imported and indexed under
Algorithm 3.

A distribution within a constant of every continuation is within that
constant of their mixture (generic); the honest signing within the
input-present and retry-failure events of the simulated signing at the
honest witness; with the witness swap as an explicit term, the honest
signing within the two events plus the swap term of the simulated
scheme's signing.

The witness swap's bound (the commitment run's coupling for the full
output), the events' bounds, the proof of payload consistency and the
composition over the signing game remain open.

The hundred-and-sixty-sixth full validation passed: 3550 build jobs and 15805 project declarations audited, every transitive axiom allowlisted.

## Continuation 167 — the per-signature comparison under any continuation

New module: Proofs/SignComparePost, imported and indexed under
Algorithm 3.

The simulated signing's body; the fixed-witness simulated signing under a
continuation with the digest drawn after the run; the honest signing
under a continuation within the input-present event of its digest-first
form; the digest-first form under a continuation within the retry-failure
event of the fixed-witness simulated signing; their chaining; and the
bound against the simulated scheme's signing with the witness swap as an
explicit term, all under continuations.

The composition over the signing game (the hybrid over signing calls of
the cut and fork experiments), the witness swap's bound, the events'
bounds and the proof of payload consistency remain open.

The hundred-and-sixty-seventh full validation passed: 3551 build jobs and 15843 project declarations audited, every transitive axiom allowlisted.

## Continuation 168 — the hybrid over signing calls of the game's run

New module: Proofs/RunHybrid, imported and indexed under the signature
game.

Two continuations within a constant pointwise are within that constant
after a bind (generic); schemes agreeing off signing; the run hybrid:
with a per-call signing bound under continuations for good secret keys,
the runs are within the fuel times the bound.

The same hybrid for the cut run, the continuation, the fresh branch and
the fork, their assembly into the simulation gap of the composed bound,
the per-call bound's uniform events, the witness swap's bound and the
proof of payload consistency remain open.

The hundred-and-sixty-eighth full validation passed: 3552 build jobs and 15867 project declarations audited, every transitive axiom allowlisted.

## Continuation 169 — the hybrid over the replay experiments

New module: Proofs/CutHybrid, imported and indexed under the signature
game.

The cut hybrid (fuel times the bound); the continuation hybrid and the
fresh-branch hybrid (the snapshot's remaining fuel times the bound); the
fork hybrid (twice it); the cut-experiment hybrid for good generated
keys.

The event experiments' hybrid (the simulation gap of the composed bound
from a uniform per-call bound), the per-call bound's uniform events, the
witness swap's bound and the proof of payload consistency remain open.

The hundred-and-sixty-ninth full validation passed: 3553 build jobs and 15887 project declarations audited, every transitive axiom allowlisted.

## Continuation 170 — the hybrid over the event experiment

New module: Proofs/EventHybrid, imported and indexed under the signature
game.

A saved snapshot of the cut carries the cut's secret key; the event
experiment of a scheme; the event-experiment hybrid within three times
the fuel times the per-call bound for good generated keys.

The simulation gap of the composed bound (the event-experiment hybrid
instantiated at the candidate scheme and the witness-free simulator with
the per-signature comparison under uniform event bounds), the events'
uniform bounds, the witness swap's bound and the proof of payload
consistency remain open.

The hundred-and-seventieth full validation passed: 3554 build jobs and 15904 project declarations audited, every transitive axiom allowlisted.

## Continuation 171 — the simulation gap of the composed bound

New module: Proofs/SimulationGap, imported and indexed under the
signature game.

The candidate and simulated schemes agree off signing; good keys (the
public key with a solution witness) and the generated keys' goodness
under a solution-yielding sampler; the simulation-gap hypothesis of the
composed forgery bound from uniform bounds on the input-present event,
the retry-failure event and the witness-swap term, with three times the
fuel plus one times their sum.

The uniform bounds of the three terms, the row-stored event's bound and
the proof of payload consistency remain open; the composed forgery bound
now takes the simulation gap in this explicit form.

The hundred-and-seventy-first full validation passed: 3555 build jobs and 15908 project declarations audited, every transitive axiom allowlisted.

## Continuation 172 — the composed forgery bound with the gap explicit

New module: Proofs/ForgeryBoundExplicit, imported and indexed under the
signature game.

The composed forgery bound against the candidate scheme with the
simulation gap replaced by three times the fuel plus one times the sum
of the uniform bounds on the input-present event, the retry-failure
event and the witness-swap term, under payload consistency and a
solution-yielding witness sampler.

The uniform bounds of the three terms, the row-stored event's bound and
the proof of payload consistency remain open.

The hundred-and-seventy-second full validation passed: 3556 build jobs and 15909 project declarations audited, every transitive axiom allowlisted.

## Continuation 173 — hash tables supported by at most n inputs

New module: Proofs/TableSupport, imported and indexed under the signature
game.

Tables supported by at most n inputs, monotone, with the empty table and
an update adding at most one input (generic); a query's table is the old
table or its update; a query adds at most one input; the honest signing's
table is a query's table and adds at most one input; the simulated
signing adds at most one input.

The invariant along the game's run with the hybrids refined to worlds
satisfying it, the input-present bound from the invariant and the lines
digest's freshness, the retry-failure and witness-swap bounds, the
row-stored event's bound and the proof of payload consistency remain
open.

The hundred-and-seventy-third full validation passed: 3557 build jobs and 15919 project declarations audited, every transitive axiom allowlisted.

## Continuation 174 — the run hybrid under the table-support invariant

New module: Proofs/RunHybridInv, imported and indexed under the signature
game.

The run hybrid with the per-call signing bound assumed only at worlds
supported by at most a global budget, the signing's support growth and
the public oracle's table preservation as hypotheses, for runs whose
starting support plus fuel is within the budget.

The cut, continuation, branch, fork, cut-experiment and
event-experiment hybrids under the invariant, the saved snapshot's
support bound, the input-present bound, the retry-failure and
witness-swap bounds, the row-stored event's bound and the proof of
payload consistency remain open.

The hundred-and-seventy-fourth full validation passed: 3558 build jobs and 15932 project declarations audited, every transitive axiom allowlisted.

## Continuation 175 — the replay hybrids under the table-support invariant

New module: Proofs/CutHybridInv, imported and indexed under the signature
game.

A saved snapshot's world supported by the starting support plus the
cut's fuel; the cut, continuation, fresh-branch, fork and cut-experiment
hybrids under the invariant, with the per-call bound assumed only at
worlds supported by the global budget.

The event-experiment hybrid under the invariant and the simulation gap
with the per-call terms assumed only at supported worlds, the
input-present bound, the retry-failure and witness-swap bounds, the
row-stored event's bound and the proof of payload consistency remain
open.

The hundred-and-seventy-fifth full validation passed: 3559 build jobs and 15958 project declarations audited, every transitive axiom allowlisted.

## Continuation 176 — the simulation gap at supported worlds

New module: Proofs/SimulationGapInv, imported and indexed under the
signature game.

The event-experiment hybrid under the invariant (budget twice the fuel
plus one); the candidate scheme's public oracle keeps the table; the
generated keys' empty tables; the honest signing at any public-key
component unfolded, and its support growth for every secret key; the
simulation gap with the input-present, retry-failure and witness-swap
terms assumed only at worlds supported by twice the fuel plus three.

The three terms' bounds at supported worlds, the row-stored event's
bound and the proof of payload consistency remain open.

The hundred-and-seventy-sixth full validation passed: 3560 build jobs and 15966 project declarations audited, every transitive axiom allowlisted.

## Continuation 177 — the hybrids under an abstract counted invariant

New modules: Proofs/RunHybridGen and Proofs/CutHybridGen, imported and
indexed under the signature game.

The run hybrid under an abstract counted invariant (monotone, growing by
one along a query or a signing call, kept by the public oracle); the
saved snapshot's invariant count; the cut, continuation, branch, fork
and cut-experiment hybrids under the invariant, with a programmed input
growing the count by one.

The simulation gap under the combined invariant (table support with the
shared world's well-formedness), the three terms' bounds, the row-stored
event's bound and the proof of payload consistency remain open.

The hundred-and-seventy-seventh full validation passed: 3562 build jobs and 16005 project declarations audited, every transitive axiom allowlisted.

## Continuation 178 — the simulation gap under the combined invariant

New module: Proofs/SimulationGapGen, imported and indexed under the
signature game.

The event-experiment hybrid under an abstract counted invariant; the
combined invariant (table support and shared-world well-formedness);
the candidate services' preservation of well-formedness; the simulated
signing's shared world as a commitment run's world; the invariant's
monotonicity and preservation by queries, programmed inputs, the public
oracle, both signings and key generation; the simulation gap with the
three terms assumed only at worlds satisfying the combined invariant.

The input-present bound at such worlds (from the lines digest's
freshness and the table's support), the retry-failure and witness-swap
bounds, the row-stored event's bound and the proof of payload
consistency remain open.

The hundred-and-seventy-eighth full validation passed: 3563 build jobs and 16036 project declarations audited, every transitive axiom allowlisted.

## Continuation 179 — hitting a supported table and the tail's output

New module: Proofs/HitCount, imported and indexed under Algorithm 3.

A uniform digest through an injective map hits a table supported by n
inputs with probability at most n over the digest count; the committed
output of a run result through a function; at a fresh lines input the
tail's committed output is that function at a uniform lines answer.

The input-present bound's assembly (the injective hash-input map and the
event split over the prefix run), the retry-failure and witness-swap
bounds, the row-stored event's bound and the proof of payload
consistency remain open.

The hundred-and-seventy-ninth full validation passed: 3564 build jobs and 16046 project declarations audited, every transitive axiom allowlisted.

## Continuation 180 — the input-present event over the tail

New module: Proofs/InputPresentTail, imported and indexed under
Algorithm 3.

A Boolean bind bounded off an event by a constant (generic); the honest
signing's hash input at a prefix result's data as a function of the
lines digest, depending on the lines answer only through its digest and
injective in it; at a fresh lines input the tail stores the input with
probability at most the support count over the digest count.

The input-present bound's assembly over the prefix run (mention and
row-stored events), the retry-failure and witness-swap bounds, the
row-stored event's bound and the proof of payload consistency remain
open.

The hundred-and-eightieth full validation passed: 3565 build jobs and 16062 project declarations audited, every transitive axiom allowlisted.

## Continuation 181 — the input-present bound

New module: Proofs/InputPresentBound, imported and indexed under
Algorithm 3.

A Boolean bind bounded pointwise by two bind-shaped events plus a
constant (generic); the prefix's mention term and the row-stored term of
a world over a uniform salt and root; the input-present bound at a
well-formed, supported world: the mention term plus the row-stored term
plus n over the digest count.

A uniform bound for the mention term (the mention event relative to the
starting log, since the trap bound carries the starting trace's event
indicator), the row-stored event's bound, the retry-failure and
witness-swap bounds and the proof of payload consistency remain open.

The hundred-and-eighty-first full validation passed: 3566 build jobs and 16070 project declarations audited, every transitive axiom allowlisted.

## Continuation 182 — the mention event relative to a base log

New module: Proofs/NewMention, imported and indexed under the oracle
model.

The prefix event over the first k entries; its split at a list boundary,
monotonicity and persistence; the event relative to a base log, its
cons law and vanishing on the base; the stored-mention lemmas in
relative form (the newest and the second newest answers); two Boolean
maps agreeing on the support; the relative event's trap bound over a
run as the per-query steps alone.

The chain's restatement with the relative event (through the prefix
run's event-or-fresh statement to the input-present bound), the
row-stored event's bound, the retry-failure and witness-swap bounds and
the proof of payload consistency remain open.

The hundred-and-eighty-second full validation passed: 3567 build jobs and 16105 project declarations audited, every transitive axiom allowlisted.

## Continuation 183 — the chain's mention events relative to a base log

New module: Proofs/NewMentionChain, imported and indexed under
Algorithm 10.

The relative event's persistence under new entries, along runs and
continuations; the newest and second-newest entry's event relative to a
base the log extends; three hash queries' event-or-shape with the
relative event; the auxiliary, mask and outer stored inputs raising the
relative event; the prefix's last three queries' event-or-fresh
statement with the relative event.

The head and prefix assembly with the relative event (through the
from-head statement, the events and the input-present bound), the
row-stored event's bound, the retry-failure and witness-swap bounds and
the proof of payload consistency remain open.

The hundred-and-eighty-third full validation passed: 3568 build jobs and 16120 project declarations audited, every transitive axiom allowlisted.

## Continuation 184 — the head and prefix statements with the relative event

New module: Proofs/NewMentionPrefix, imported and indexed under
Algorithm 10.

A run's trace and a continuation's trace are at least as long as their
starting logs; after a fresh last row query a stored outer string raises
the relative event; from a head-initial result with the last row query
fresh, the rest of the prefix either raises the relative event or
finishes with the lines input fresh unless stored, which raises it.

The input-present bound with the relative mention term, the relative
term's indicator-free bound, the shared trace's length bound along the
game, the row-stored event's bound, the retry-failure and witness-swap
bounds and the proof of payload consistency remain open.

The hundred-and-eighty-fourth full validation passed: 3569 build jobs and 16125 project declarations audited, every transitive axiom allowlisted.

## Continuation 185 — the input-present bound with the relative mention term

New module: Proofs/InputPresentUniform, imported and indexed under
Algorithm 3.

The prefix's relative mention term of a world; the input-present bound
with the relative term, the row-stored term and the support count over
the digest count; the relative term bounded by the per-query mention
steps over the prefix budget from the trace's length, with no indicator.

The shared trace's length bound along the game (to make the steps' sum
uniform), the row-stored event's bound, the retry-failure and
witness-swap bounds and the proof of payload consistency remain open.

The hundred-and-eighty-fifth full validation passed: 3570 build jobs and 16131 project declarations audited, every transitive axiom allowlisted.

## Continuation 186 — trace growth and the uniform input-present bound

New module: Proofs/TraceLength, imported and indexed under Algorithm 3.

A run adds at most one trace entry per unit of fuel; the mention step is
monotone in the trace length; the input-present bound with a
trace-length budget (the mention steps from the budget, the row-stored
term and the support count over the digest count).

The trace-length budget as an invariant component along the game (with
the public oracle also counted), the row-stored event's bound, the
retry-failure and witness-swap bounds and the proof of payload
consistency remain open.

The hundred-and-eighty-sixth full validation passed: 3571 build jobs and 16142 project declarations audited, every transitive axiom allowlisted.

## Continuation 187 — trace growth along the game's services

New module: Proofs/TraceGrowth, imported and indexed under the signature
game; the generic hybrids (Proofs/RunHybridGen, Proofs/CutHybridGen,
Proofs/SimulationGapGen) now let the public oracle advance the
invariant's count.

A shared run's world has at most the budget more trace entries; the
honest and simulated signings add at most the commitment budget; the
public oracle adds at most one entry; the commitment budget is at least
one.

The trace-length budget as an invariant component and the uniform
input-present term in the simulation gap, the row-stored event's bound,
the retry-failure and witness-swap bounds and the proof of payload
consistency remain open.

The hundred-and-eighty-seventh full validation passed: 3572 build jobs and 16161 project declarations audited, every transitive axiom allowlisted.

## Continuation 188 — the simulation gap with the input-present term discharged

New module: Proofs/SimulationGapTrace, imported and indexed under the
signature game.

The counted invariant with a trace-length budget; its monotonicity and
preservation by queries, programmed inputs, the public oracle, both
signings and key generation; the input-present term at the budget; the
simulation gap with the input-present term discharged, under the
row-stored term's bound, the retry-failure bound and the witness-swap
term as explicit hypotheses.

The row-stored event's bound, the retry-failure bound, the witness-swap
term and the proof of payload consistency remain open.

The hundred-and-eighty-eighth full validation passed: 3573 build jobs and 16174 project declarations audited, every transitive axiom allowlisted.

## Continuation 189 — the bridge to the verifier's share matrix

New module: Proofs/PayloadBridge, imported and indexed under Algorithm
10 and 12.

The packaged positive corrections at a positive execution; the
verifier's slope at every execution as the common accumulator; the share
matrix at the hidden indices as the corrected opening; the honest
witness and randomness lines at the inverse challenge as the verifier's
recomputed values.

The constant term's vanishing for a solution witness, the assembly of
payload consistency, the row-stored event's bound, the retry-failure
bound and the witness-swap term remain open.

The hundred-and-eighty-ninth full validation passed: 3574 build jobs and 16182 project declarations audited, every transitive axiom allowlisted.

## Continuation 190 — the constant term vanishes for a solution

New module: Proofs/ConstantTermZero, imported and indexed under
Algorithms 13 and 14.

A nonzero bit is one; a binary at-most-one vector's unitary check
vanishes; the unitary layers vanish on binary at-most-one selectors; the
composed prover polynomial's constant term vanishes for a solution
witness.

The assembly of payload consistency, the row-stored event's bound, the
retry-failure bound and the witness-swap term remain open.

The hundred-and-ninetieth full validation passed: 3575 build jobs and 16189 project declarations audited, every transitive axiom allowlisted.

## Continuation 191 — payload consistency

New module: Proofs/PayloadConsistent, imported and indexed under
Algorithms 3, 4, 10 and 12.

A line has degree at most one; payload consistency under the candidate
encoding and at least one higher coefficient: for a solution witness and
an executed commitment, the honest hashed coefficients equal the
simulator's recomputed tuple at every hidden vector with nonzero
encoding.

The row-stored event's bound, the retry-failure bound and the
witness-swap term remain the simulation gap's open terms.

The hundred-and-ninety-first full validation passed: 3576 build jobs and 16194 project declarations audited, every transitive axiom allowlisted.

## Continuation 338 — single-execution extraction

New modules: Proofs/SepEvents and Proofs/SepChain, imported and indexed
under the signature game.

SepEvents: the separation predicate (`SepAt`), the full-agreement event
(`allAgree`), the chosen separated execution (`sepIndex`, `sepIndex_sep`),
the extracted slope and witness (`uOf`, `xOf`), the lines' slope
coefficient (`mCoef`), the extracted lines (`witnessLineM`,
`randomnessLineM`, `witnessLineM_constant`) and the difference polynomial
(`differenceM`); the first branch's values are the lines at its inverted
challenge by construction (`verifier_eq_lines`) and vanish there on
acceptance (`differenceM_vanishes`); the events with the prior events'
negations (`priorOK`, `realOK`, `szPlus`, `batchingPlus`, `rsdSolvedPlus`,
`priorBad`, `unionEvent`); the union (`good_implies_events`,
`fork_le_union`, `random_fork_le_union`, `forgery_le_events`); the
requirements (`eventOKP_allAgree`, `eventOKP_rsdSolvedPlus`); the solver
(`solverOutput`, `solver`, `solverSuccess`, `rsdSolvedPlus_output`,
`solverSuccess_ge`, `rsdSuccess`, `solverSuccess_le_rsd`).

SepChain: the chain for these events (`forgery_le_simulated_events`,
`forgery_le_final_close`, `_data`, `_hide`, `_coll`, `_rsd`), the named
constants (`SimulatorTermBounds3`, `RealTermBounds`, `forgery_le_final_named`),
the hardness assumption and the final statements (`InstanceHard`,
`forgery_le_final_hard`, `forgery_le_final_full_enc`).

The three-hundred-and-thirty-eighth full validation passed: 3757 build jobs and 19261 project declarations audited, every transitive axiom allowlisted.

## Continuation 337 — assumption-boundary docstring refreshed

No new module. The module docstring of `SDitH/Assumptions.lean` now states
the current boundary: the three final statements, their named hypotheses
(`DataClose`, `LeafHide`, `hretry`, `SimulatorTermBounds5`, `InstanceHard`
or `DistributionHard`), the reason the expansion-dependent constants stay
named, and why `SDHardness` is still unconsumed. No declaration changed.

The three-hundred-and-thirty-seventh full validation passed: 3755 build jobs and 19173 project declarations audited, every transitive axiom allowlisted.

## Continuation 336 — the candidate encoding and the distributional bound

New modules: Proofs/CandidateSerialization and Proofs/DistributionalFinal,
imported and indexed under the signature game.

The candidate wire encoding, one bit per coordinate in index order
(`bitVector`, `bitBase`, `candidateSerialization`), its injectivity facts
(`bitVector_injective`, `bitBase_injective`, `flatten_ofFn_inj`,
`sourceTail_injective`, `lines_injective`) and the composed bound at the
full layout with the candidate encoding in place of the two encoding
hypotheses (`forgery_le_final_full_enc`).

The explicit terms of the bound as a function of the hardness term
(`rhsTerms`, affine in it: `rhsTerms_add`), the averaged advantage and
solver success over a distribution of instances (`averagedAdvantage`,
`averagedRSD`), the distributional hardness assumption
(`DistributionHard`), the mean-square form of the bound over any
distribution (`forgery_le_final_meanSquare`) and, on a finite index type,
the bound on the averaged advantage through the weighted power-mean
inequality (`averaged_forgery_le_final`).

The three-hundred-and-thirty-sixth full validation passed: 3755 build jobs and 19173 project declarations audited, every transitive axiom allowlisted.

## Continuation 335 — the final statement at the full layout

New module: Proofs/FullLayoutFinal, imported and indexed under the
signature game.

The full layout's input and key injectivity and the one-element fibers of
its key, key-of-output and output maps, stated for any layout equal to it
(`input_injective_of_eq`, `key_injective_of_eq`,
`keyOutput_fiber_le_one_of_eq`, `key_fiber_le_one_of_eq`,
`output_fiber_le_one_of_eq`), and the composed bound with both layouts
the full layout and the fiber constants one (`forgery_le_final_full`).

The three-hundred-and-thirty-fifth full validation passed: 3753 build jobs and 19149 project declarations audited, every transitive axiom allowlisted.

## Continuation 334 — the simulator's seed-collision term discharged

New module: Proofs/SeedTermDischarge, imported and indexed under the
signature game.

The per-event simulation-gap statement with the seed collision bounded in
the real experiment instead of transferred to the simulator
(`forgery_le_simulated_events_C`), the regenerated chain of final
statements with that summand the explicit pair cost
(`forgery_le_final_close_C`, `_data_C`, `_hide_C`, `_coll_C`,
`_rsd_C`, `_named_C`), the five-constant simulator hypothesis
(`SimulatorTermBounds5`) and the final statement
(`forgery_le_final_hard_C`).

The three-hundred-and-thirty-fourth full validation passed: 3752 build jobs and 19143 project declarations audited, every transitive axiom allowlisted.

## Continuation 333 — the hardness assumption on the instance

New module: Proofs/InstanceHardness, imported and indexed under the
signature game.

The named hardness assumption on the key generation's instance
(`InstanceHard`: every budgeted adversary's solver returns a weight-`w`
solution of the public instance with probability at most `εSD` of the
budget) and the final statement with the hardness term replaced by it
(`forgery_le_final_hard`). The source index's Algorithm-12 entry gained a
`reduction_status` field with the current state; Algorithms 3 and 4 point
to it.

The three-hundred-and-thirty-third full validation passed: 3751 build jobs and 19134 project declarations audited, every transitive axiom allowlisted.

## Continuation 332 — review pass

No new module. The README status summary, the plan's open lines of the
composed bound, the review ledger's continuation-292 record and the
docstring of `SDitH/Assumptions.lean` are reconciled with
`NamedSimulatorTerms.forgery_le_final_named` (named hypotheses,
hardness term, interface state). `SDitH/Final.lean` keeps its three
theorems.

The three-hundred-and-thirty-second full validation passed: 3750 build jobs and 19132 project declarations audited, every transitive axiom allowlisted.

## Continuation 331 — the expansion-dependent simulator terms named

New module: Proofs/NamedSimulatorTerms, imported and indexed under the
signature game.

The six simulator event bounds as one named hypothesis
(`SimulatorTermBounds`) and the final statement with the named
constants in place of the simulator's event probabilities
(`forgery_le_final_named`).

The three-hundred-and-thirty-first full validation passed: 3750 build jobs and 19132 project declarations audited, every transitive axiom allowlisted.

## Continuation 330 — the hardness term as syndrome decoding

New modules: Proofs/MuxSelect, Proofs/SolutionRegular, Proofs/ForgeryRSD,
imported and indexed under the signature game.

The selected column of a unitary binary layer (`selectCol`,
`mux_select`), the selected leaf address of a chunk (`selectAddress`,
`muxTree_select`), the chunk-and-leaf addressing (`chunkEquiv`,
`flatEquiv`), the solution vector with a one at each chunk's selected
leaf (`solutionVector`, `mulVec_solutionVector`, `mulVec_eq_of_residual`,
`hammingWeight_solutionVector`), the extracted witness as a weight-`w`
solution of the key generation's instance (`isSolution_sd`), the
syndrome-decoding success (`rsdSuccess`, `solverSuccess_le_rsd`) and the
final statement with the hardness term on the instance
(`forgery_le_final_rsd`).

The three-hundred-and-thirtieth full validation passed: 3749 build jobs and 19130 project declarations audited, every transitive axiom allowlisted.

## Continuation 329 — the final statements with the slope term explicit

New module: Proofs/ForgerySlope, imported and indexed under the
signature game.

The four final statements regenerated with the slope summand replaced by
the explicit slack and the verifier layout's identity
(`forgery_le_final_close_S`, `forgery_le_final_data_S`,
`forgery_le_final_hide_S`, `forgery_le_final_coll_S`).

The three-hundred-and-twenty-ninth full validation passed: 3746 build jobs and 19070 project declarations audited, every transitive axiom allowlisted.

## Continuation 328 — the composed bound's skeleton with the three events

New module: Proofs/SlopeChainReduction, imported and indexed under the
signature game.

The union event with the trap, the witnessed pair and the unseen match
(`unionEventS`), the fork-to-union step (`fork_le_union_S`), the
random-index step (`random_fork_le_union_S`), the forgery skeleton
(`forgery_le_events_S`), the extraction split (`forgery_le_events_split_S`)
and the per-event simulation gaps with the three events kept in the real
experiment (`forgery_le_simulated_events_S`).

The three-hundred-and-twenty-eighth full validation passed: 3745 build jobs and 19066 project declarations audited, every transitive axiom allowlisted.

## Continuation 327 — the unseen match's bound in the real experiment

New module: Proofs/ForkUnseenBound, imported and indexed under the
signature game. Redefined in place: `SlopeCoverFork.unseenFork` (with the
named seed's two recorded halves) and `covered`'s third disjunct.

The claim of two branches (`claimOf`), the unseen predicate (`unseenΦ`)
with its set, shift and family invariances and its identity with the
shared game's unseen event, the event's properties (`unseenFork_none`,
`unseenFork_left`, `unseenFork_famL`, `unseenFork_union`), the attempt
embedding the final world exactly (`freshBranchW_attempt_eq`), the
transport of a uniform bound across finiteness instances
(`uniform_le_congr`), the end-resampled bound (`unseen_le_cost`), the fork
bound (`fork_unseen_bound`) and the real-experiment bound (`unseenFork_le`).

The three-hundred-and-twenty-seventh full validation passed: 3744 build jobs and 19059 project declarations audited, every transitive axiom allowlisted.

## Continuation 326 — the witnessed pair's bound in the real experiment

New module: Proofs/ForkWitnessedBound, imported and indexed under the
signature game.

A fresh branch's history growth (`freshBranchW_history`), the checked
first branch's attempt history (`attemptHistory_checked`), the
end-resampled witnessed event on a sub-history (`union_le_pairMass`), the
union within the second branch's final history (`union_subset_final`), the
restored chain's pair mass (`restored_chain_le`), the fork bound for a
family-dependent witnessed event (`fork_witnessed_bound`), the event's
properties (`witnessedFork_none`, `witnessedFork_left`, `witnessedFork_famL`,
`witnessedFork_union`), the slack (`εWitOf`) and the real-experiment bound
(`witnessedFork_le`).

The three-hundred-and-twenty-sixth full validation passed: 3743 build jobs and 19004 project declarations audited, every transitive axiom allowlisted.

## Continuation 325 — the fork bound for family-dependent events

New module: Proofs/PairForkFamily, imported and indexed under the
signature game.

The union of attempt histories as the same set under the two shifts
(`union_shift_iff`) and the fork bound for family-dependent events
(`fork_family_bound`).

The three-hundred-and-twenty-fifth full validation passed: 3742 build jobs and 18962 project declarations audited, every transitive axiom allowlisted.

## Continuation 324 — the mask trap's bound in the real experiment

New module: Proofs/SlopeTrapBound, imported and indexed under the
signature game.

The trap on a shared world (`trapBad`, with `slopeTrap_eq`), the trap cost
(`εTrap`, monotone in the budget), the per-run bound
(`runProgram_trap_bound`), the service bound (`trap_service_bound`), the
prefix bound over the cut experiment (`prefix_trap_bound`) and the random
event experiment's bound (`slopeTrap_le`).

The three-hundred-and-twenty-fourth full validation passed: 3741 build jobs and 18954 project declarations audited, every transitive axiom allowlisted.

## Continuation 323 — the fork-level coverage of the slope event

New module: Proofs/SlopeCoverFork, imported and indexed under the
signature game.

The mask trap on the snapshot's trace (`slopeTrap`), the witnessed pair
in the union of the histories (`witnessedFork`), the unseen match
(`unseenFork`), the coverage at the attempts (`covered`), the snapshot's
family matching both branches' histories (`fork_consistent`), and the
good fork implying the named events with the three in place of the slope
event (`good_implies_events_D`).

The three-hundred-and-twenty-third full validation passed: 3740 build jobs and 18944 project declarations audited, every transitive axiom allowlisted.

## Continuation 322 — the stored-mask slope event from the good fork

New module: Proofs/SlopeChainFork, imported and indexed under the
signature game. Extended in place: `CandidateForkSlope.fork_masked_slope`
and `CandidateBranch.UniformSlope` (the chain's auxiliary query with the
mask digest and the equal commitment arrays), `ForkExtraction.fork_extracts`
(the salt equality, both reconstructions on the snapshot's table, the
equal commitments, the auxiliary query and the stored mask in place of the
existential mask) and `CandidateReduction.good_implies_events` (adapted).

The good fork implies the named events with the stored-mask slope event
(`good_implies_events_C`), under the identity layout.

The three-hundred-and-twenty-second full validation passed: 3739 build jobs and 18923 project declarations audited, every transitive axiom allowlisted.

## Continuation 321 — the stored-mask slope event

New module: Proofs/SlopeEventSetting, imported and indexed under the
signature game.

The shared slope game's setting from the signer and verifier
(`slopeSetting`), the identity layout's commitment and expansion entries
in the shared form (`induced_commitSeed`, `expandEntries_fullLayout`),
the stored-mask slope event (`slopeWinC`, `slopeWinC_none`), the branch
slope as the shared game's slope (`slopeOf_eq`) and the implication to
the existential-mask event (`slopeWin_of_slopeWinC`).

The three-hundred-and-twenty-first full validation passed: 3738 build jobs and 18922 project declarations audited, every transitive axiom allowlisted.

## Continuation 320 — the seed-collision bound and the final statement with its explicit slack

New modules: Proofs/SeedCollisionWitness, Proofs/SeedCollisionBound and
Proofs/ForgeryColl, imported and indexed under the signature game.

The layout's transport of the seed-pairing companion (`inputEquiv`,
`companionL`, `companionL_input`, `companionL_involutive`,
`companionL_ne`), the event off without a fork result
(`seedCollision_none`), the recorded seed collision witnessed by every
matching family (`seedCollision_witnessed`); the cost's monotonicity in
the length (`callCost_mono_len`), the seed-collision slack (`εCollOf`) and
the bound (`seedCollision_le`); and the composed forgery bound with the
explicit seed-collision slack (`forgery_le_final_coll`).

The three-hundred-and-twentieth full validation passed: 3737 build jobs and 18905 project declarations audited, every transitive axiom allowlisted.

## Continuation 319 — the pair mass through the fork

New module: Proofs/PairFork, imported and indexed under the signature
game.

The attempt history of a branch (`attemptHistory`) with its shift and
family-setting lemmas, the fresh branch with its final world as the shift
of the branch from the empty-history base (`freshBranchW_shift`), the
attempt embedding the final world (`freshBranchW_attempt`), the invariant
along the run and a fresh branch (`runW_inv'`, `freshBranchW_inv`), the
pointwise step from the plain second branch's event to the restored
second branch's pair mass (`event_le_shifted`), and the fork bound
(`fork_pair_bound`).

The three-hundred-and-nineteenth full validation passed: 3734 build jobs and 18869 project declarations audited, every transitive axiom allowlisted.

## Continuation 318 — the pair mass through the oracles and the run

New modules: Proofs/PairOracles and Proofs/PairRun, imported and indexed
under the signature game.

One call's pair cost (`callCost`, monotone in the budget), resampling
keeping the pair mass (`mean_resampleW_pairMass`), the program-shaped
oracle bounds (`run_mean_bound`, `runOracle_pair_bound`) and the three
candidate oracles' bounds under the counted invariant
(`honest_pair_bound`, `public_pair_bound`, `prepare_pair_bound`); the
resampling law in mean form (`postLaw_mean`), the game run's bound
(`runW_pair_bound`), the cut's mass (`cutMass`) and bound
(`cut_pair_bound`), and the fresh branch's bound
(`freshBranchW_pair_bound`), all generic in the invariant and the
per-call bounds.

The three-hundred-and-eighteenth full validation passed: 3733 build jobs and 18834 project declarations audited, every transitive axiom allowlisted.

## Continuation 317 — the posterior pair mass

New module: Proofs/PairMass, imported and indexed under the signature
game.

The posterior pair mass of a cipher history (`pairMass`) with its bounds
(`pairMass_le_one`, `pairMass_nil`, `pairMass_eq_one`), the history law
as the pair mass (`historyLaw_eq`), the pair cost's monotonicity
(`pairCost_mono`), and the per-run bound: a shared program run from a
resampled world raises the pair mass by at most the adaptive pair cost of
its budget (`runProgram_pair_bound`).

The three-hundred-and-seventeenth full validation passed: 3731 build jobs and 18783 project declarations audited, every transitive axiom allowlisted.

## Continuation 316 — the leaf hiding and the leaf term

New modules: Proofs/LeafSliced, Proofs/LeafTermBound and
Proofs/ForgeryHide, imported and indexed under the signature game.

The sliced data without the hit factor and its lemmas (`slicedView`,
`sliced_eq_view`, `slicedView_congr`, `slicedView_blocks`,
`slicedView_le_one`, `slicedView_eq_zero_of_not_mem`,
`slicedView_exchanged`); the key-recording functional (`keyFun`), the
leaf hit as sliced data (`leafHit_eq_slicedView`), the leaf hit's mixing
family (`leafFct` with its blocks, bound, invariance and vanishing), the
leaf hiding (`LeafHide`), the leaf-term slack (`εLeafOf`), the leaf term
from the leaf hiding (`leafTerm_le`) and the two leaf-term bounds
(`leafR_of_leafHide`, `leafC_of_leafHide`); and the composed forgery bound
with the leaf hiding (`forgery_le_final_hide`).

The three-hundred-and-sixteenth full validation passed: 3730 build jobs and 18772 project declarations audited, every transitive axiom allowlisted.

## Continuation 315 — the off-hit closeness and the final statement under the data-level closeness

New modules: Proofs/OffHitClose and Proofs/ForgeryData, imported and
indexed under the signature game.

The scaling at the budget and the off-hit slack (`scaleAt`, `εOff`), the
number of block tuples (`card_tuples_eq`), the chain cancelled, divided
and bounded uniformly (`fixed_cancel`, `fixed_div`, `fixed_total`), the
off-hit closeness for the pre-call hit (`prunedCloseOff_of_dataClose`),
the pruned closeness from the data-level closeness
(`prunedClose_of_dataClose`), and the composed forgery bound with the
data-level closeness (`forgery_le_final_data`).

The three-hundred-and-fifteenth full validation passed: 3727 build jobs and 18734 project declarations audited, every transitive axiom allowlisted.

## Continuation 314 — the off-hit chain assembled at fixed draws

New module: Proofs/OffHitAssembly, imported and indexed under the
signature game.

The two tuples carrying mass (`tuples`, `card_tuples_le`), the sliced
data and the mixing family vanishing outside them
(`sliced_eq_zero_of_not_mem`, `Fct_eq_zero_of_not_mem`, `sum_tuples`),
the data-level closeness hypothesis (`DataClose`), the honest side with
the closeness (`honest_side`) and the fake side over the two tuples
(`fake_side`).

The three-hundred-and-fourteenth full validation passed: 3725 build jobs and 18721 project declarations audited, every transitive axiom allowlisted.

## Continuation 313 — the hidden tuple of the digest

New module: Proofs/TupleOfDigest, imported and indexed under the
signature game.

The attempt's decision and the first passing counter (`passes`,
`firstPassing`), the attempt loop returning the first passing counter
whatever the key (`observe_eq_firstPassing`), the default tuple and the
digest's tuple (`defaultTuple`, `hiddenOfDigest`), and a simulated
signature's hidden tuple as the digest's or the default
(`sigHidden_simPost`).

The three-hundred-and-thirteenth full validation passed: 3724 build jobs and 18712 project declarations audited, every transitive axiom allowlisted.

## Continuation 312 — the off-hit chain's two sides

New module: Proofs/OffHitChain, imported and indexed under the signature
game.

The mixing and bound families (`Fct`, `Bnd`), their invariance under the
exchange (`Fct_inv`, `Bnd_inv`), the mixing family at the own blocks
(`Fct_blocks`), the honest upper bound (`honest_upper`) and the fake lower
bound relative to the tuple probability (`fake_lower`).

The three-hundred-and-twelfth full validation passed: 3723 build jobs and 18677 project declarations audited, every transitive axiom allowlisted.

## Continuation 311 — the relative mixture bound and the off-hit setup

New modules: Proofs/LeafMixtureGen and Proofs/OffHitSetup, imported and
indexed under the signature game.

The difference-to-a-bound identity and the mixture lower bound relative
to a bound function (`mean_sub_add`, `mixture_lower_gen`); the off-hit
pruned mean as the posterior mean of the inner mean
(`prunedMeanOff_eq_posterior`), the bounds by one (`sliced_le_one`,
`inner_le_one`), the tuple probability (`slicedOne`,
`sliced_le_slicedOne`, `sum_slicedOne_le_one`, `sum_slicedOne_eq`), the
hit mass and its complement (`hitMass`, `inner_one_add_hitMass`), and
the distinct-tree and hit terms over the uniform draws
(`badTree_mean_le`, `hitMass_mean_le`).

The three-hundred-and-eleventh full validation passed: 3722 build jobs and 18665 project declarations audited, every transitive axiom allowlisted.

## Continuation 310 — the sliced data under the leaf exchange

New module: Proofs/SlicedInvariance, imported and indexed under the
signature game.

A tree with the tuple's leaves replaced (`treeWith`, `treeWith_leaf`,
`treeWith_other`), the sliced data's dependence on the allocated
addresses (`sliced_congr`), the replaced tree at the own blocks
(`treeWith_blocks`, `sliced_blocks`), the hit factor under the exchange
(`touches_tupleKeys_exchanged`) and the sliced data under the exchange
(`sliced_exchanged`).

The three-hundred-and-tenth full validation passed: 3720 build jobs and 18643 project declarations audited, every transitive axiom allowlisted.

## Continuation 309 — the signing-data identity

New module: Proofs/SigningData, imported and indexed under the signature
game.

The trivial family and a tuple's keys (`trivialFamily`, `tupleKeys`), the
tuple's data after the phase (`tailData`), the inner mean of the off-hit
pruned mean (`inner`), the tuple-sliced data (`sliced`), the oracle as
the phase run continued by the tail then the post-processing
(`commitOracle_eq`), constants through means and sums
(`mean_const_mul`, `sum_const_mul_mean`, `sum_select`) and the identity
(`inner_eq_sum`).

The three-hundred-and-ninth full validation passed: 3719 build jobs and 18620 project declarations audited, every transitive axiom allowlisted.

## Continuation 308 — the tail's run

New module: Proofs/TailRun, imported and indexed under the signature
game.

A hash-only program's run keeps the cipher history
(`runFixed_hashOnly_history`) and does not depend on the family
(`runFixed_hashOnly_family`), the continuation from a finished run
(`continueRun_done`), the tail as hash-only (`queriesIn_commitTail_empty`),
and the tail's history and family facts (`commitTail_history`,
`commitTail_family`).

The three-hundred-and-eighth full validation passed: 3718 build jobs and 18593 project declarations audited, every transitive axiom allowlisted.

## Continuation 307 — the uniform-mixture comparison

New module: Proofs/LeafMixture, imported and indexed under the signature
game.

The hidden blocks of a family and the distinct-tree indicator (`blocks`,
`distInd`), the block indicators selecting the own blocks
(`prod_blockInd`), the block weights summing to the function at the own
blocks (`sum_blockWeight`), the upper mixture bound (`mixture_upper`), the
complement identity (`mean_compl_add`) and the lower mixture bound
(`mixture_lower`).

The three-hundred-and-seventh full validation passed: 3717 build jobs and 18580 project declarations audited, every transitive axiom allowlisted.

## Continuation 306 — the joint block bound

New module: Proofs/LeafBlockBound, imported and indexed under the
signature game.

The block and parent indicators and the block weight (`blockInd`,
`parentInd`, `blockWeight`, their bounds and the insertion rule), the
parent indicators summing to one (`sum_parentInd`), the fiber as parent
and block (`parentInd_mul_blockInd`), the block weight with the parent
fixed under the exchange (`blockWeight_parent_exchanged`), the label test
with the parent fixed (`blockWeight_label`), one more block fixed
(`blockWeight_step`) and the joint block bound (`blockWeight_bound`).

The three-hundred-and-sixth full validation passed: 3716 build jobs and 18569 project declarations audited, every transitive axiom allowlisted.

## Continuation 305 — the joint uniformity of the hidden leaves

New module: Proofs/LeafJointBound, imported and indexed under the
signature game.

The hidden leaf of an execution with its bounds and distinctness (`leaf`,
`leaf_bounds`, `leaf_ne`), the fiber indicator and the joint weight
(`fiberInd`, `jointWeight`, their bounds and the insertion rule), the
joint weight under the exchange at a leaf outside the fixed set
(`jointWeight_exchanged`), the label test as the fiber test on the
distinct trees (`jointWeight_label`), the empty fibers
(`fiberInd_eq_zero_of_not_fresh`), one more execution fixed
(`jointWeight_step`) and the joint bound (`jointWeight_bound`).

The three-hundred-and-fifth full validation passed: 3715 build jobs and 18550 project declarations audited, every transitive axiom allowlisted.

## Continuation 304 — distinctness and the other leaves under the exchange

New module: Proofs/LeafExchangeDistinct, imported and indexed under the
signature game.

The exchange's side conditions from distinctness and a target that is not
bad (`conditions_of_distinct`), the exchanged tree's keys fresh and
distinct (`distinct_exchanged`), and another leaf's parent seed and block
kept under the exchange (`other_leaf_exchanged`).

The three-hundred-and-fourth full validation passed: 3714 build jobs and 18526 project declarations audited, every transitive axiom allowlisted.

## Continuation 303 — the all-executions phase view and the generic leaf bound

New module: Proofs/PhaseViewLeafAll, imported and indexed under the
signature game.

The phase view under the exchange at a family-dependent key list
(`phaseView_exchanged_of_mem`), at the hidden keys of all executions
(`phaseView_exchanged_all`), the weight on the fresh fiber for any view
function (`weightA`, `weightA_le_one`, `weightA_exchanged`), the posterior
bound at the leaf for an invariant bounded weight (`honest_leaf_bound_gen`),
the all-executions phase view (`phaseViewAll`) and the invariance of its
means under the exchange on the good fiber (`phaseViewAll_mean_exchanged`).

The three-hundred-and-third full validation passed: 3713 build jobs and 18508 project declarations audited, every transitive axiom allowlisted.

## Continuation 302 — the posterior bound at the leaf

New module: Proofs/HonestLeafBound, imported and indexed under the
signature game.

The weight of a bounded function of the phase view on the fresh fiber of
a parent seed (`weightL`, `weightL_le_one`), the phase view's independence
of the world's family (`phaseView_setFamily`), the weight under the
exchange of the leaf's block on the good fiber (`weightL_exchanged`) and
the posterior bound at the leaf (`honest_leaf_bound`).

The three-hundred-and-second full validation passed: 3712 build jobs and 18490 project declarations audited, every transitive axiom allowlisted.

## Continuation 301 — the phase view's leaf exchange

New module: Proofs/PhaseViewLeaf, imported and indexed under the
signature game.

The commitments of a finished phase and their invariance under
relabelling (`commitsOf`, `commitsOf_mapKeys`), the view of a phase result
(`viewOf`), the phase's run and view from a world (`phaseRun`,
`phaseView`), the views at lists with the same members
(`phaseView_congr_mem`), the keys the phase records (`phaseRun_keys`),
the view at a fresh key added (`phaseView_cons_of_fresh`), the phase at
agreeing trees (`commitPhase_congr`), the phase at the exchanged
expansion's tree (`commitPhase_baseTree_exchanged`), the view under the
exchange pruned at a list containing the exchanged keys
(`phaseView_exchanged_of_subset`) and at the families' own hidden keys
(`phaseView_exchanged`).

The three-hundred-and-first full validation passed: 3711 build jobs and 18480 project declarations audited, every transitive axiom allowlisted.

## Continuation 300 — the commitment run's leaf exchange

New module: Proofs/CommitRunLeaf, imported and indexed under the
signature game.

The phase's budget and the rest's budget as the phase's plus the tail's
(`phaseBudget`, `restBudget_eq`), the phase and the tail bounded
(`commitPhase_bounded`, `commitTail_bounded`), the rest's run as the
phase's run continued by the tail (`commitRest_run`), the exchanged
expansion's tree for any node (`exchanged_tree_eq'`), the commitment run
under the exchange at a leaf (`commitRun_leaf_exchanged`), pruning at a
superset (`pruneAt_of_subset`) and the pruned history before the tail
under the exchange (`leaf_history_pruned`).

The three-hundredth full validation passed: 3710 build jobs and 18457 project declarations audited, every transitive axiom allowlisted.

## Continuation 299 — the commitment phase's leaf exchange

New module: Proofs/CommitPhaseLeaf, imported and indexed under the
signature game.

The leaf commitments as a phase (`commitPhase`, `commitRest_eq`,
`queriesIn_commitPhase`), relabelling a collection and a commitment call
(`mapKeys_collect`, `mapKeys_commitCall`), the swap of the leaf's old and
new keys (`leafSwap`), a leaf's value in the expansion's tree
(`baseTree_leaf`), the exchanged family through the swap at the leaves'
keys (`exchanged_leafSwap`), the phase at the exchanged tree as the
swapped phase (`commitPhase_exchanged`) and the run of the exchanged phase
as the relabelled run (`commitPhase_run_exchanged`).

The two-hundred-and-ninety-ninth full validation passed: 3709 build jobs and 18444 project declarations audited, every transitive axiom allowlisted.

## Continuation 298 — programs under a key relabelling

New module: Proofs/ProgramRelabel, imported and indexed under the
signature game.

Requests, entries and programs with their keys relabelled (`mapKey`,
`mapEntry`, `mapKeys`, `mapKeys_bind`), the answer and entry under the
relabelling (`answer_mapKey`, `entry_mapKey`, `keyOf_mapKey`), the
relabelled result (`mapResult`), the run of a relabelled program against
a family agreeing through the relabelling on the queried keys
(`runFixed_mapKeys`), and the invariance of the pruned history under a
relabelling permuting the pruned keys (`pruneAt_map`).

The two-hundred-and-ninety-eighth full validation passed: 3708 build jobs and 18427 project declarations audited, every transitive axiom allowlisted.

## Continuation 297 — the off-bad closeness

Modified module: Proofs/SwapCloseSplit. The off-bad pruned closeness
(`PrunedCloseOff`), the equality as the closeness with no slack
(`prunedCloseOff_of_equalOff`), and the pruned closeness from the bad
term and the off-bad closeness with the two slacks added
(`prunedClose_of_split'`).

The two-hundred-and-ninety-seventh full validation passed: 3707 build jobs and 18401 project declarations audited, every transitive axiom allowlisted.

## Continuation 296 — the hit term

New module: Proofs/HitTerm, imported and indexed under the signature
game.

The hit bound (`εHit`, the first part of the uniform touching bound,
`εHit_le_εTouch`); a hidden-path key is a tree node's key below twice the
leaf count (`hidden_path_node`); a pre-call hit is a distinctness failure
(`not_goodTree_of_hitPre`, `indicator_hitPre_le`); the signing call keeps
the family (`commitOracle_family`); and the bad term for the pre-call hit
at the counted invariant's budget (`badTerm_hitPre`), from the
distinctness failure bound under the joint draw.

The two-hundred-and-ninety-sixth full validation passed: 3707 build jobs and 18397 project declarations audited, every transitive axiom allowlisted.

## Continuation 295 — the closeness over the uniform draws

Modified modules: Proofs/SwapClose (`PrunedClose` over the uniform salt,
root and digest; `prunedClose_of_equal`; `swap_core_close` averaging the
forward agreement, the closeness and the reverse agreement over the
draws; the per-call bounds applying the averaged closeness) and
Proofs/SwapCloseSplit (`hitPre`; the bad event as a parameter; `BadTerm`,
`prunedMeanOff`, `PrunedEqualOff`, `prunedMean_le_off`,
`off_le_prunedMean`, `prunedClose_of_split`).

The two-hundred-and-ninety-fifth full validation passed: 3706 build jobs and 18381 project declarations audited, every transitive axiom allowlisted.

## Continuation 294 — the closeness slack split

New module: Proofs/SwapCloseSplit, imported and indexed under the
signature game.

The pre-call hit (`hitPre`), the hit term (`HitPre`), the pruned mean
restricted to the calls without a hit (`prunedMeanOff`), the off-hit
pruned equality (`PrunedEqualOff`), the two comparison lemmas
(`prunedMean_le_off`, `off_le_prunedMean`) and the closeness from the hit
term and the off-hit equality (`prunedClose_of_split`), with the small
indicator facts `indicator_le_one` and `le_off_add_event`.

The two-hundred-and-ninety-fourth full validation passed: 3706 build jobs and 18374 project declarations audited, every transitive axiom allowlisted.

## Continuation 293 — the pruned closeness

New module: Proofs/SwapClose, imported and indexed under the signature
game.

The pruned closeness of the two signings (`PrunedClose`), the equality as
the closeness with no slack (`prunedClose_of_equal`), the swap's core
under the closeness (`swap_core_close`), the two per-call bounds
(`signRunW_meanP_close`, `signCutW_meanP_close`), the per-event gap
(`hgap_meanP_close`), the simulation term with the slack beside the
touching terms (`εSimP'`), the per-event gap under the final hypotheses
(`hgap_final_close`) and the composed forgery bound (`forgery_le_final_close`).

The two-hundred-and-ninety-third full validation passed: 3705 build jobs and 18365 project declarations audited, every transitive axiom allowlisted.

## Continuation 292 — the named hypotheses recorded

No new module. The review ledger gained a section stating the content of
each named hypothesis of `forgery_le_final'` (pruned equality, leaf-term
bounds, retry bound, seed-collision bound, layout and structural
conditions) with what is proved towards each; the plan's status lines
and the README's status header were updated to match.

The two-hundred-and-ninety-second full validation passed: 3704 build jobs and 18347 project declarations audited, every transitive axiom allowlisted.

## Continuation 291 — the events' requirements

New module: Proofs/EventRequirements, imported and indexed under the
signature game.

A constant indicator is compatible with any functional dominating the
touching indicator (`pruneCompat_const`); the event at the end-resampled
family is its value for an event not reading the snapshot world's family
(`rightEval_eq`); the events' requirements for an event of the two
attempts reading the snapshot only outside its world's family and
history and the attempts' worlds only outside their families and
histories (`eventOKP_of`); the requirements of the mask, non-separation,
slope-game, zero-challenge, Schwartz–Zippel, batching and
solved-extraction events; the simulation gap for one event under the
final hypotheses (`hgap_final`); and the composed forgery bound with
those seven events discharged and the seed-collision probability entering
directly (`forgery_le_final'`).

The two-hundred-and-ninety-first full validation passed: 3704 build jobs and 18347 project declarations audited, every transitive axiom allowlisted.

## Continuation 290 — the final composed bound

New module: Proofs/ForgeryFinal, imported and indexed under the signature
game; the events' insensitivity to the attempts' embedded worlds weakened
to replacements of the family and the cipher history (`adjust`,
`finalize_terminal` in Proofs/PruneCompatClosure; the hypotheses of
Proofs/ForkPruneCompat, Proofs/MeanHybridCompat, Proofs/EventCutCompat
and `EventOKP` in Proofs/SimulationGapCompat restated).

The uniform touching bound is monotone in the end budget (`εTouch_mono`),
the run's touching bound in its bound (`touchR_mono`), and the composed
forgery bound with the touching bounds instantiated (`forgery_le_final`).

The two-hundred-and-ninetieth full validation passed: 3703 build jobs and 18334 project declarations audited, every transitive axiom allowlisted.

## Continuation 289 — the touching bounds

New module: Proofs/TouchBound, imported and indexed under the signature
game; the per-call hypotheses of Proofs/MeanHybridCompat and
Proofs/MeanCutCompat, their discharges in Proofs/SwapDischarge and the
touching bounds in Proofs/SimulationGapCompat restated with the world's
count and the fuel within the budget (Proofs/EventCutCompat adjusted to
the dropped monotonicity argument).

The uniform touching bound (`εTouch`); a history's key count is at most
its length; a pair of the joint draw has a family from the posterior; the
swap's touching term is at most the uniform bound for a game process
keeping the invariant to the end budget and a bounded leaf term
(`touchMean_le`); the extended invariant along the simulated scheme's cut
with its world (`cutW_inv_sim`); the leaf-term bounds as named hypotheses
(`LeafR`, `LeafC`); and the two touching bounds (`touchR_of`,
`touchC_of`).

The two-hundred-and-eighty-ninth full validation passed: 3702 build jobs and 18326 project declarations audited, every transitive axiom allowlisted.

## Continuation 288 — the touching term as the touching total

New module: Proofs/TouchIdentity, imported and indexed under the signature
game.

The touching total's post-processing, hidden tuple, continuation and
recorded entries for the swap (`postT`, `hiddenT`, `contT`, `newT`); the
swap's touching term over the uniform root equals the touching total's
probability (`touchInner_eq_touchAll`); a world with another consistent
family keeps the extended invariant (`invC_setFamily`); and the
continuation's expected recorded length is at most the commitment budget
times the end budget when the game's process keeps the invariant to it
(`expLen_le`).

The two-hundred-and-eighty-eighth full validation passed: 3701 build jobs and 18286 project declarations audited, every transitive axiom allowlisted.

## Continuation 287 — preparations for the touching bound

New module: Proofs/TouchPrep, imported and indexed under the signature
game.

A leaf's address is at least the leaf count; the candidate opening does
not read an internal node of the key's tree (`openKey_setTree`); the
simulated post-processing is invariant under setting an internal node of
the committed tree (`simPost_setTree`); pruning keeps the extended
invariant (`invC_pruneW`); and the signing-shaped oracle with the
simulated post-processing keeps the extended invariant, being one branch
of the simulated signing (`invC_commitOracle`).

The two-hundred-and-eighty-seventh full validation passed: 3700 build jobs and 18273 project declarations audited, every transitive axiom allowlisted.

## Continuation 286 — the touching bound for a constant hidden tuple

New module: Proofs/TouchConst, imported and indexed under the signature
game.

The root and node hits of a slice other than the constant tuple vanish
(`hitVR_const_ne`, `hitV_const_ne`); the root and node terms for the
constant tuple need the post-processing's invariance only at the root and
at the node (`root_term_const`, `node_term_const`); the assembled touching
bound and the touching total for a constant hidden tuple
(`touch_assembly_const`, `touch_total_const`), with the invariance
hypothesis restricted to the root and the internal paths of the tuple's
leaves.

The two-hundred-and-eighty-sixth full validation passed: 3699 build jobs and 18258 project declarations audited, every transitive axiom allowlisted.

## Continuation 285 — the composed bound with the swaps discharged

New module: Proofs/SimulationGapCompat, imported and indexed under the
signature game.

An event's requirements (`EventOKP`: false without a fork result,
insensitive to the snapshot world's cipher history and to the checked
terminals' embedded worlds, compatible with pruning at the end for the
touching indicator), the derived insensitivities to the branches'
embedded families and to the second branch's history suffix; the touching
bounds for the run's and the cut's continuations (`TouchR`, `TouchC`);
the pruned equality of the two signings (`PrunedEqual`); the simulation
gap for one event with the per-call swaps discharged (`hgap_meanP`); and
the composed forgery bound (`εSimP`, `forgery_le_meanP`).

The two-hundred-and-eighty-fifth full validation passed: 3698 build jobs and 18240 project declarations audited, every transitive axiom allowlisted.

## Continuation 284 — the per-call swaps discharged

New module: Proofs/SwapDischarge, imported and indexed under the
signature game.

The verification preparation keeps consistency; a signature's hidden tuple
(`sigHidden`); the fixed-witness simulated signing as a uniform salt, root
and digest followed by the signing-shaped oracle with the simulated
post-processing (`simulatedSignWith_eq`); the call followed by a function
of the signature and the resampled world pruned at the output's hidden
keys (`prunedMean`), the touching terms (`touchInner`, `touchMean`); the
swap's core from the forward and reverse agreements and the pruned
equality (`swap_core`); and the per-call bounds for compatible
continuations of the run and of the cut with its world (`signRunW_meanP`,
`signCutW_meanP`), with the pruned equality and the touching bound as
hypotheses.

The two-hundred-and-eighty-fourth full validation passed: 3697 build jobs and 18214 project declarations audited, every transitive axiom allowlisted.

## Continuation 283 — the event experiment for compatible continuations

New module: Proofs/EventCutCompat, imported and indexed under the
signature game; Proofs/MeanCutCompat restated with the cut's per-call
bound for cuts within the budget and reachable cuts (`ReachC`).

The event branch's process on a cut with its world (`cutProc`) and its
value (`branchEval`); the fork from a snapshot as a compatible pair from
the closure steps (`fork_pruneCompat`); the inner evaluation and the
fork's process ignore the snapshot world's cipher history
(`innerEval_hist`, `forkProc_hist`); touching persists along the fork's
and the event branch's processes (`forkProc_touches`,
`cutProc_touches`); the event branch read on the cut with its world is
compatible with pruning at any keys (`eventBranch_pruneCompatC`), given
that the event is false without a fork result and ignores the snapshot
world's cipher history; the process keeps the invariant within four times
the budget plus three on reachable cuts (`cutProc_inv`); and the
end-resampled event experiment's hybrid for compatible continuations
(`eventExpE_le_meanP`).

The two-hundred-and-eighty-third full validation passed: 3696 build jobs and 18175 project declarations audited, every transitive axiom allowlisted.

## Continuation 282 — the cut with its final world

New modules: Proofs/CutWorld and Proofs/MeanCutCompat, imported and
indexed under the signature game.

The cut with its final world (`cutW`), projecting to the replay's cut
(`cutW_fst`); a cut with its world replaced (`withWorldC`); touching
persists along it (`touchesG_cutW`); prune-compatible evaluations of a cut
with its world (`PruneCompatC`) and their complements; the pruned-run
agreement for it in both directions (`cutW_le_prune_gen`,
`prune_le_cutW_gen`); and the per-call bound for compatible continuations
of the cut with its world (`SignCutWMeanP`) with the cut hybrid in mean
form for it (`cutW_le_cutW_mean_contP`).

The two-hundred-and-eighty-second full validation passed: 3695 build jobs and 18136 project declarations audited, every transitive axiom allowlisted.

## Continuation 281 — the hybrid chain for compatible continuations

New module: Proofs/MeanHybridCompat, imported and indexed under the
signature game.

The per-call bound in mean form for compatible continuations of the run
with its final world (`SignRunWMeanP`: compatible with pruning at every
key list, with the touching functional of a process on the result keeping
the invariant within an end budget); the run hybrid for it
(`runW_le_runW_mean_contP`); the fresh branch's hybrid with its
continuation's compatibility supplied (`freshBranchW_le_meanP`); the
second branch's continuation's compatibility (`rightCont_pruneCompat`);
the fork continuation's process (`forkProc`), its compatibility in the
hybrid's form (`forkCont_pruneCompat'`) and its invariant keeping
(`forkProc_inv`); the inner evaluation after the first branch
(`innerEval`) and the fork hybrid's two steps (`stepA_core`, `stepA`,
`stepB`); and the end-resampled event fork hybrid for compatible
continuations (`forkEventE_le_meanP`).

The two-hundred-and-eighty-first full validation passed: 3693 build jobs and 18062 project declarations audited, every transitive axiom allowlisted.

## Continuation 280 — the fork continuation's compatibility

New module: Proofs/ForkPruneCompat, imported and indexed under the
signature game.

Compatibility transfers along pointwise equal evaluations; the event read
at the end-resampled family of the second branch's final world
(`rightEval`), the second branch from the restored world followed by the
event (`leftEval`), the fork continuation after the first branch's run
(`forkCont`) and the corresponding touching functionals (`leftTouch`,
`forkTouch`) are defined, and the fork continuation is compatible with
pruning at any keys (`forkCont_pruneCompat`) given the scheme's laws, the
event's compatibility at the end and its insensitivity to the checked
terminals' embedded worlds.

The two-hundred-and-eightieth full validation passed: 3692 build jobs and 18025 project declarations audited, every transitive axiom allowlisted.

## Continuation 279 — closure of prune compatibility

New module: Proofs/PruneCompatClosure, imported and indexed under the
signature game.

Prune compatibility closed under the steps of the hybrid's continuations:
resampling twice is resampling once; a family-free and prune-free
evaluation is compatible with the touching indicator; compatibility is
kept by resampling the world before the evaluation, by averaging over a
sample, by restoring a world's family and history into a base world, by
updating the hash table, and by the terminal's finalization (which reads
only the hash table), for an evaluation of the checked result not reading
the checked terminal's embedded world.

The two-hundred-and-seventy-ninth full validation passed: 3691 build jobs and 18015 project declarations audited, every transitive axiom allowlisted.

## Continuation 278 — prune-compatible evaluations

New module: Proofs/GamePruneGen, imported and indexed under the signature
game.

The pruned-run agreement generalised from a family-free evaluation read at
the pruned result to a prune-compatible evaluation with a touching
functional (`PruneCompat`: at most one, the functional dominates the
touching indicator, and the mean over the resampled world is below the
mean over the resampled pruned world plus the functional's, and
conversely), read at the actual result: the complement of a compatible
evaluation is compatible, the game run from the resampled world is below
the run from the resampled pruned world with the functional added, the
reverse agreement, and the game run with a compatible evaluation is a
compatible evaluation with the run's mean of the functional.

The two-hundred-and-seventy-eighth full validation passed: 3690 build jobs and 18001 project declarations audited, every transitive axiom allowlisted.

## Continuation 277 — the composed bound in mean form

New modules: Proofs/ForgeryEvents and Proofs/SimulationGapMean2, imported
and indexed under the signature game.

The forgery reduction with the simulation gap taken per event; the
per-call bound in mean form for an arbitrary continuation of the signing
output, from the input-present, retry and swap bounds; the simulation gap
for one event in mean form over the restored fork at the budget three
times the fuel plus two; and the composed forgery bound with the per-call
witness swap in mean form for the simulated scheme's run and cut
continuations, the retry bound, and the eight events' insensitivity to the
second branch's history suffix and to the attempts' embedded families
(`EventOK`) as named hypotheses.

The two-hundred-and-seventy-seventh full validation passed: 3689 build jobs and 17975 project declarations audited, every transitive axiom allowlisted.

## Continuation 276 — the event experiment's mean-form hybrid

New modules: Proofs/MeanForkCont2, Proofs/MeanEventCont,
Proofs/CandidateKeepsFamily and Proofs/InvCExtra, imported and indexed
under the signature game.

The end-resampled event fork's hybrid and the event experiment's hybrid in
mean form; family keeping of the candidate and simulated oracles; the
counted invariant under restoration and under the verification
preparation.

The two-hundred-and-seventy-sixth full validation passed: 3687 build jobs and 17959 project declarations audited, every transitive axiom allowlisted.

## Continuation 275 — the branch hybrid in mean form

New module: Proofs/MeanForkCont, imported and indexed under the signature
game.

The counted invariant along the run with its final world and the fresh
branch with its final world within the remaining fuel times the per-call
bound, from a resampled snapshot world.

The two-hundred-and-seventy-fifth full validation passed: 3683 build jobs and 17931 project declarations audited, every transitive axiom allowlisted.

## Continuation 274 — the end-resampled event experiment

New modules: Proofs/ForkRestoreEnd and Proofs/EventRestore, imported and
indexed under the signature game.

Terminals and branches with their embedded family replaced, finalization
of such a terminal, an attempt's embedded world as the final world, the
second branch's resampling law, the end-resampled event fork and its
agreement with the restored one; a boolean distribution determined by its
probability of true, and the event experiment's equality with its
end-resampled restored form from a resampled key.

The two-hundred-and-seventy-fourth full validation passed: 3682 build jobs and 17914 project declarations audited, every transitive axiom allowlisted.

## Continuation 273 — the fork restoration and the run-with-world hybrid

New modules: Proofs/ForkRestoreEq and Proofs/MeanHybridContW, imported
and indexed under the signature game.

The restored event fork, the common form of both forks, the shared and
restored forks' reductions to it, and their equality from a resampled
snapshot world for events insensitive to the second branch's history
suffix; the mean-form hybrid of the run with its final world for its
continuations.

The two-hundred-and-seventy-third full validation passed: 3680 build jobs and 17867 project declarations audited, every transitive axiom allowlisted.

## Continuation 272 — the fork restoration's supporting facts

New modules: Proofs/ForkRestoreLemmas and Proofs/ForkRestoreShift,
imported and indexed under the signature game.

The game run's history extension, the resampled world as the world with
its family replaced, the shifted branch and the finalization of a shifted
terminal; the run's resampling law in mean form, the fresh branch through
the run with its final world and under a history shift, and the shifted
forms of the world with a family and of the restored world.

The two-hundred-and-seventy-second full validation passed: 3678 build jobs and 17846 project declarations audited, every transitive axiom allowlisted.

## Continuation 271 — the shift laws and the restored fork

New modules: Proofs/CandidateShift and Proofs/ForkRestore, imported and
indexed under the signature game.

The candidate and simulated oracles' shift laws and their game runs'
shifts; family keeping along the game run; the fresh branch with its final
world; the restored fork.

The two-hundred-and-seventy-first full validation passed: 3676 build jobs and 17817 project declarations audited, every transitive axiom allowlisted.

## Continuation 270 — the history as a log for the game run

New module: Proofs/HistoryShiftGame, imported and indexed under the
signature game.

The shift law of program-shaped oracles, its closure under sampling and
pure answers, and the game run with its final world from a world with
entries appended to its inner history.

The two-hundred-and-seventieth full validation passed: 3674 build jobs and 17786 project declarations audited, every transitive axiom allowlisted.

## Continuation 269 — the reverse instantiations and the mean-form hybrids

New modules: Proofs/CandidateGamePruneReverse and Proofs/MeanHybridCont,
imported and indexed under the signature game.

The candidate and simulated schemes' reverse pruned-run agreements; the
run and cut hybrids in mean form with the per-call bound for the run's
and the cut run's continuations.

The two-hundred-and-sixty-ninth full validation passed: 3673 build jobs and 17767 project declarations audited, every transitive axiom allowlisted.

## Continuation 268 — the reverse pruned-run agreement

New module: Proofs/GamePruneReverse, imported and indexed under the
signature game.

The mean of a bounded function's complement, and the game run from the
resampled pruned world below the run from the resampled world on the
pruned result plus the touching indicator under the pruned run.

The two-hundred-and-sixty-eighth full validation passed: 3671 build jobs and 17736 project declarations audited, every transitive axiom allowlisted.

## Continuation 267 — the hybrid chain for the game's continuations

New modules: Proofs/ChargeRunCont, Proofs/ChargeCutCont and
Proofs/SimulationGapCont, imported and indexed under the signature game.

The run hybrid, the replay hybrids and the event-experiment hybrid with
the per-call signing bound stated for the run and cut continuations; the
simulation gap and the composed forgery bound with the witness swap
hypotheses in that shape.

The two-hundred-and-sixty-seventh full validation passed: 3670 build jobs and 17734 project declarations audited, every transitive axiom allowlisted.

## Continuation 266 — the per-call bridge to the pruned run

New module: Proofs/SignBridge, imported and indexed under the signature
game.

The signing-shaped oracle, its resampling law and consistency, the
output's hidden keys and their invariance under a consistent resampling,
and the bridge from the call followed by the game run to the call followed
by the resampled pruned run with the touching indicator.

The two-hundred-and-sixty-sixth full validation passed: 3667 build jobs and 17678 project declarations audited, every transitive axiom allowlisted.

## Continuation 265 — the commitment run's recorded expansion

New module: Proofs/CommitHistoryContains, imported and indexed under the
signature game. The import lines of Proofs/TouchAssembly,
Proofs/TouchTotal and Proofs/TreeOfMatches, missing since their
continuations, were added to the library root; this continuation's
validation is the first to cover them.

The commitment run's final history contains the expansion's entries and
the starting history, and any family matching a history extending it
computes the signature's hidden keys.

The two-hundred-and-sixty-fifth full validation passed: 3666 build jobs and 17668 project declarations audited, every transitive axiom allowlisted.

## Continuation 264 — the tree of any matching family

New module: Proofs/TreeOfMatches, indexed under the signature game;
its import line was missing from the library root until continuation
265, so this continuation's validation did not cover it.

The children's expansion entries and their membership in the recorded
expansion; the tree and the hidden keys of all executions for any family
matching a history containing the expansion's entries.

The two-hundred-and-sixty-fourth full validation passed: 3662 build jobs and 17592 project declarations audited, every transitive axiom allowlisted.

## Continuation 263 — the total touching bound

New module: Proofs/TouchTotal, indexed under the signature game; its
import line was missing from the library root until continuation 265, so
this continuation's validation did not cover it.

The path depth bound by the binary logarithm, the probability of a
decided event as the mean of its indicator, the distinctness failure
probability under the joint draw, and the total touching bound.

The two-hundred-and-sixty-third full validation passed: 3662 build jobs and 17592 project declarations audited, every transitive axiom allowlisted.

## Continuation 262 — the assembled touching bound

New module: Proofs/TouchAssembly, indexed under the signature game;
its import line was missing from the library root until continuation
265, so this continuation's validation did not cover it.

The mean under the joint draw as an iterated mean, distinctness giving
goodness and freshness at the root, the leaf term, the sliced expected
lengths summing to the expected length, the root and internal node terms
in divided form, and the assembled touching bound on the good pairs.

The two-hundred-and-sixty-second full validation passed: 3662 build jobs and 17592 project declarations audited, every transitive axiom allowlisted.

## Continuation 261 — the instantiated bounds and the touching split

New modules: Proofs/AllViewBounds and Proofs/TouchSplit, imported and
indexed under the signature game.

The view pruned at all executions' hidden keys for a fixed tuple, its
exchange invariance and touching bounds; the view pruned at the
signature's own hidden keys, its touching probability, expected recorded
length and leaf hit, the split of a leaf's path, and the bound of the
touching probability by the per-tuple, per-execution hits.

The two-hundred-and-sixty-first full validation passed: 3662 build jobs and 17592 project declarations audited, every transitive axiom allowlisted.

## Continuation 260 — the node and root bounds for an abstract view

New modules: Proofs/ViewNodeBound and Proofs/ViewRootBound, imported and
indexed under the signature game.

The honest node bound and the touching bound at a node, and the honest
root bound and the touching bound at the root, for any view chosen from
the family (and the root) that is the same under the exchange on the good
fiber.

The two-hundred-and-sixtieth full validation passed: 3660 build jobs and 17562 project declarations audited, every transitive axiom allowlisted.

## Continuation 259 — the own-view exchange for all executions' keys

New modules: Proofs/OwnViewExchangeGen, Proofs/HiddenKeysAllExchange and
Proofs/OwnViewExchangeAll, imported and indexed under the signature game.

The own-view exchange of a node and of the root for an abstract key list
chosen from the family (membership of the moved keys and equal members of
the enlarged lists); these facts for the hidden keys of all executions;
the instantiated exchanges.

The two-hundred-and-fifty-ninth full validation passed: 3658 build jobs and 17527 project declarations audited, every transitive axiom allowlisted.

## Continuation 258 — the hidden tuples and the sliced view

New modules: Proofs/HiddenTuple and Proofs/HiddenSlice, imported and
indexed under the signature game.

The hidden keys of all executions and the union bound over the
executions; the view pruned at keys chosen from the signature and the
family, its mean as a sum over the choices with the view factor, and the
continuation restricted to a choice with its hit weights and recorded
length.

The two-hundred-and-fifty-eighth full validation passed: 3655 build jobs and 17500 project declarations audited, every transitive axiom allowlisted.

## Continuation 257 — the root's posterior and touching bounds

New modules: Proofs/RootPosteriorBound, Proofs/RootHonestBound and
Proofs/RootTouchBound, imported and indexed under the signature game.

The joint draw of a uniform root and the posterior family, its invariance
under the root exchange, the bad targets' count under a fiber bound on
the layout's key, the posterior bound on the root; the own-keys view's
weight at the root and its monotonicity under the root exchange; the
touching bound at the root. The fiber bound on the layout's key is an
explicit hypothesis of these bounds.

The two-hundred-and-fifty-seventh full validation passed: 3653 build jobs and 17478 project declarations audited, every transitive axiom allowlisted.

## Continuation 256 — the root's exchange through the own view

New modules: Proofs/KeySwap, Proofs/RootCommitRun, Proofs/RootCommitView
and Proofs/RootOwnView, imported and indexed under the signature game;
Proofs/RootExchange and Proofs/RootHistoryExchange restated over the key
swap without the dummy key.

The swap of two keys on a family, its involutivity, matching and the
posterior's invariance; the commitment run, the commitment view pruned at
the root keys and the view pruned at a family's own hidden keys under the
root exchange.

The two-hundred-and-fifty-sixth full validation passed: 3650 build jobs and 17423 project declarations audited, every transitive axiom allowlisted.

## Continuation 255 — the distinctness bridge and the root's exchange

New modules: Proofs/DistinctBridge, Proofs/RootExchange,
Proofs/ProductSwap and Proofs/RootHistoryExchange, imported and indexed
under the signature game.

The family's distinct keys from the run's and its probability bound; the
root exchange on families and the tree under it; the product of two
distributions, its invariance under a product map and the uniform
draw's invariance under a transposition; the root keys, the seed tree's
run and the recorded entries under the root exchange.

The two-hundred-and-fifty-fifth full validation passed: 3646 build jobs and 17387 project declarations audited, every transitive axiom allowlisted.

## Continuation 254 — the distinct-keys bound

New module: Proofs/TreeDistinctBound, imported and indexed under the
signature game.

The tree's keys fresh and distinct up to a step, the keys so far and
their count, the not-distinct event, the distinctness step, the
expansion's recorded keys among the tree so far, and the probability
bound by induction over the steps.

The two-hundred-and-fifty-fourth full validation passed: 3642 build jobs and 17354 project declarations audited, every transitive axiom allowlisted.

## Continuation 253 — the union bound, distinct keys and sibling keys

New modules: Proofs/PathUnion, Proofs/TreeDistinct and
Proofs/SiblingKeys, imported and indexed under the signature game. The
goodness hypotheses of the exchange chain (Proofs/TreeExchange through
Proofs/NodeTouchBound) now require positive addresses.

The hidden path's address set and the union bound over it; distinct and
fresh tree keys and the goodness of every internal node they give; and
the bound on two outputs of a fresh key sharing a layout key.

The two-hundred-and-fifty-third full validation passed: 3641 build jobs and 17322 project declarations audited, every transitive axiom allowlisted.

## Continuation 252 — the touching bound at a hidden node

New modules: Proofs/HonestNodeBound, Proofs/KeyWeightSum and
Proofs/NodeTouchBound, imported and indexed under the signature game.
Proofs/PosteriorNodeBound's invariance hypothesis is now one-sided.

The freshness of a family at a node, the restricted weight of the
own-keys view and its monotonicity under the exchange, the posterior
bound for the commitment view; the count of blocks whose key is recorded
and the sum of hit weights; the hit weight, the good families, the hit
and the expected recorded entries, the single-term bound, the pair bound,
and the touching bound at the node.

The two-hundred-and-fifty-second full validation passed: 3638 build jobs and 17303 project declarations audited, every transitive axiom allowlisted.

## Continuation 251 — the posterior bound on a hidden node's block

New module: Proofs/PosteriorNodeBound, imported and indexed under the
signature game.

The fiber, goodness and bad targets of a family, the exchange with a
target as a fixed map and its agreement with the node exchange on the
fiber, the goodness hypotheses on the good fiber, the label and its
exchange, the bad targets' count, the set-restricted counting lemma, and
the posterior bound on the node's block.

The two-hundred-and-fifty-first full validation passed: 3635 build jobs and 17271 project declarations audited, every transitive axiom allowlisted.

## Continuation 250 — the own-keys view under the exchange

New module: Proofs/OwnViewExchange, imported and indexed under the
signature game.

The commitment view at a key list, its invariance under adding a key no
recorded entry uses and under key lists with the same members, and its
invariance under the exchange of a path node when pruned at each family's
own hidden keys.

The two-hundred-and-fiftieth full validation passed: 3634 build jobs and 17238 project declarations audited, every transitive axiom allowlisted.

## Continuation 249 — the hidden keys under the exchange

New module: Proofs/HiddenKeysExchange, imported and indexed under the
signature game.

Pruning's dependence on a key list's members, a path address's bound,
and the members of the exchanged family's hidden keys with the old key
added against the family's with the new key added.

The two-hundred-and-forty-ninth full validation passed: 3633 build jobs and 17230 project declarations audited, every transitive axiom allowlisted.

## Continuation 248 — the keys the commitment run records

New module: Proofs/CommitHistoryKeys, imported and indexed under the
signature game.

The expansion's recorded keys as the expanded nodes' keys, and the
commitment run's recorded entries at the tree's keys over the starting
history.

The two-hundred-and-forty-eighth full validation passed: 3632 build jobs and 17223 project declarations audited, every transitive axiom allowlisted.

## Continuation 247 — the keys a run records

New module: Proofs/RunKeys, imported and indexed under the signature
game.

The key of a recorded entry, and the keys a run querying within a set
records over its starting history.

The two-hundred-and-forty-seventh full validation passed: 3631 build jobs and 17211 project declarations audited, every transitive axiom allowlisted.

## Continuation 246 — the one-sided fiber exchange

New module: Proofs/FiberCountingSided, imported and indexed under the
signature game.

The one-sided fiber exchange under an invariant distribution, and
pruning at a key none of the history's entries uses.

The two-hundred-and-forty-sixth full validation passed: 3630 build jobs and 17204 project declarations audited, every transitive axiom allowlisted.

## Continuation 245 — fiber counting with bad targets

New module: Proofs/FiberCountingBad, imported and indexed under the
signature game.

The split of a weighted mass along a predicate, the sum of bad-target
masses as the mass weighted by the number of bad targets, and a label
value's mass bound when exchanged with all but a bounded number of bad
targets.

The two-hundred-and-forty-fifth full validation passed: 3629 build jobs and 17202 project declarations audited, every transitive axiom allowlisted.

## Continuation 244 — fiber counting under a measure-preserving exchange

New module: Proofs/FiberCounting, imported and indexed under the
signature game.

The equal weighted masses of two label values under an invariant
distribution and an exchanging bijection (also in involutive form), the
indicator sum over a finite set, the sum of weighted label masses, its
bound by the total weight, and the mass of one value over the set's size.

The two-hundred-and-forty-fourth full validation passed: 3628 build jobs and 17198 project declarations audited, every transitive axiom allowlisted.

## Continuation 243 — the candidate post-processings under the exchange

New module: Proofs/HonestViewExchange, imported and indexed under the
signature game.

An internal node is no leaf, and the honest and simulated
post-processings do not read an internal node of the committed tree.

The two-hundred-and-forty-third full validation passed: 3627 build jobs and 17192 project declarations audited, every transitive axiom allowlisted.

## Continuation 242 — the commitment run's view under the exchange

New module: Proofs/CommitViewExchange, imported and indexed under the
signature game.

The world with its family stripped, and the equal law of the commitment
run's pruned view under the exchanged family and the family for
post-processings that do not read an internal node.

The two-hundred-and-forty-second full validation passed: 3626 build jobs and 17181 project declarations audited, every transitive axiom allowlisted.

## Continuation 241 — what the exchange leaves unchanged

New module: Proofs/CommitPruned, imported and indexed under the signature
game.

The expansion's entries pruned at any key list containing the exchanged
keys, the opening and the retry attempts of a key with an internal node
set, and the payload's and body's independence from an internal node.

The two-hundred-and-forty-first full validation passed: 3625 build jobs and 17176 project declarations audited, every transitive axiom allowlisted.

## Continuation 240 — the commitment run under the exchange

New module: Proofs/CommitRunExchange, imported and indexed under the
signature game.

The rest's budget and boundedness, the commitment run as the rest's run
from the expansion's tree and history, the rest's dependence on the tree
within the allocated addresses, the base tree, the exchanged expansion's
tree as the tree with the node replaced, the exchanged family's agreement
at the leaves' keys, and the commitment run under the exchange.

The two-hundred-and-fortieth full validation passed: 3624 build jobs and 17158 project declarations audited, every transitive axiom allowlisted.

## Continuation 239 — a run only appends to its starting history

New module: Proofs/RunHistoryShift, imported and indexed under the
signature game.

The result with a history appended, and the run from a history as the
run from the empty history with the history appended.

The two-hundred-and-thirty-ninth full validation passed: 3623 build jobs and 17137 project declarations audited, every transitive axiom allowlisted.

## Continuation 238 — the commitment phase after the expansion

New module: Proofs/CommitPhaseExchange, imported and indexed under the
signature game.

The four chain queries, the row hashes with them, the rest of the
commitment program, the program as expansion then rest, the leaves' keys,
the query locality of the rest, the committed value with a node set, and
the rest with an internal node replaced as the rest with a finish.

The two-hundred-and-thirty-eighth full validation passed: 3622 build jobs and 17130 project declarations audited, every transitive axiom allowlisted.

## Continuation 237 — run congruence and the finish map

New module: Proofs/RunCongr, imported and indexed under the signature
game.

The procedure's steps, programs querying within a key set and their
binds, the answers of families agreeing on the queried keys, the run
congruence of such families, and the run of a program with a pure finish
as the mapped run.

The two-hundred-and-thirty-seventh full validation passed: 3621 build jobs and 17112 project declarations audited, every transitive axiom allowlisted.

## Continuation 236 — the expansion's run and entries under the exchange

New module: Proofs/TreeHistoryExchange, imported and indexed under the
signature game.

The three exchanged keys, the seed tree's run under the exchange on the
allocated addresses, and the recorded entries pruned at the exchanged
keys coinciding.

The two-hundred-and-thirty-sixth full validation passed: 3620 build jobs and 17093 project declarations audited, every transitive axiom allowlisted.

## Continuation 235 — the tree expansion's run in closed form

New module: Proofs/TreeRunClosed, imported and indexed under the
signature game.

The entries recorded by the tree expansion through a number of steps and
the expansion's run as the point at the seed tree's run and those
entries over the starting history.

The two-hundred-and-thirty-fifth full validation passed: 3619 build jobs and 17074 project declarations audited, every transitive axiom allowlisted.

## Continuation 234 — the seed tree under the exchange

New module: Proofs/TreeExchange, imported and indexed under the signature
game.

A node's parent key and expansion block, the exchanged family, the
distinct tweaks of siblings, and the tree under the exchange: the same
tree except at the exchanged node.

The two-hundred-and-thirty-fourth full validation passed: 3618 build jobs and 17063 project declarations audited, every transitive axiom allowlisted.

## Continuation 233 — the exchange of a node's value

New module: Proofs/NodeExchange, imported and indexed under the signature
game.

The exchange of a node's value on families, its values at the parent key,
the two keys and other keys, its involutivity, the permutation of
families, the preservation of matching for histories with the three keys
fresh, the exchange on candidates, and the invariance of the posterior.

The two-hundred-and-thirty-third full validation passed: 3617 build jobs and 17049 project declarations audited, every transitive axiom allowlisted.

## Continuation 232 — the hidden keys with the leaf

New module: Proofs/HiddenKeys, imported and indexed under the signature
game.

The hidden keys of a leaf (root, proper ancestors, leaf), their
membership characterization, the root's and the leaf's membership, a path
node's parent as root or path node, the path's parent keys among the
hidden keys, their freshness in the pruned history, and the pruning at
the parent keys absorbed by the pruning at the hidden keys.

The two-hundred-and-thirty-second full validation passed: 3616 build jobs and 17034 project declarations audited, every transitive axiom allowlisted.

## Continuation 231 — the game-level agreement for both schemes

New module: Proofs/CandidateGamePrune, imported and indexed under the
signature game.

The game run's agreement with its pruned run for the candidate scheme
and for the simulated scheme.

The two-hundred-and-thirty-first full validation passed: 3615 build jobs and 17022 project declarations audited, every transitive axiom allowlisted.

## Continuation 230 — the candidate oracles' prune laws

New module: Proofs/CandidatePrune, imported and indexed under the
signature game.

The public oracle's three cases and the verification preparation's two
cases as program-shaped oracles, and the prune law, growth and
consistency keeping of the honest and simulated signings, the public
oracle and the verification preparation.

The two-hundred-and-thirtieth full validation passed: 3614 build jobs and 17020 project declarations audited, every transitive axiom allowlisted.

## Continuation 229 — prune laws of program-shaped oracles

New module: Proofs/PruneLawRun, imported and indexed under the signature
game. Proofs/GamePrune now carries the consistency invariant (`Possible`,
`Consistent`, `Keeps`, `consistent_of_mem_resampleW`) in its prune law
and theorem.

The pruned shared world touches nothing, a run's result history is
matched by its family, the program-shaped oracle with its growth,
consistency keeping and prune law, and the sampling and pure-answer
closures of all three.

The two-hundred-and-twenty-ninth full validation passed: 3613 build jobs and 16964 project declarations audited, every transitive axiom allowlisted.

## Continuation 228 — the game run agrees with its pruned run

New module: Proofs/GamePrune, imported and indexed under the signature
game.

The pruned game world, its family replacement and touching event,
family-free functions of oracle results and of terminals with worlds, an
oracle's prune law and growth, the persistence of touching along the run,
the hash step from a resampled world, and the game run's agreement with
its run from the pruned world up to the final touching indicator.

The two-hundred-and-twenty-eighth full validation passed: 3612 build jobs and 16931 project declarations audited, every transitive axiom allowlisted.

## Continuation 227 — the pruned-run agreement for shared program runs

New module: Proofs/SharedPrune, imported and indexed under the signature
game.

The pruned shared world, its touching event, family-free functions of a
program result, and both directions of the pruned-run agreement for the
shared scheme's program runs from resampled worlds.

The two-hundred-and-twenty-seventh full validation passed: 3611 build jobs and 16897 project declarations audited, every transitive axiom allowlisted.

## Continuation 226 — the reverse pruned-run agreement

New module: Proofs/PrunedRunReverse, imported and indexed under the
signature game.

The run from the pruned history below the run from the history plus the
pruned run's touching term.

The two-hundred-and-twenty-sixth full validation passed: 3610 build jobs and 16889 project declarations audited, every transitive axiom allowlisted.

## Continuation 225 — the run agrees with its pruned run until a hit

New module: Proofs/PrunedRun, imported and indexed under the signature
game.

The posterior cipher step, the posterior's support, the entry's key, the
pruning of a cons, the pruned result, the touching event, the mean over
the answer's law, and the one-sided agreement of a run with its run from
the pruned history up to the touching indicator.

The two-hundred-and-twenty-fifth full validation passed: 3609 build jobs and 16884 project declarations audited, every transitive axiom allowlisted.

## Continuation 224 — the posterior factorises over keys

New module: Proofs/PosteriorPrune, imported and indexed under the
signature game.

The law of a uniform draw's image, the coordinate update of a matching
family, the entries at an unpruned key, the fiber exchange bijection, the
fibers' proportionality, and the equal laws of the coordinate and of the
answer at a key outside the pruned keys under the posterior of a history
and of its pruned history.

The two-hundred-and-twenty-fourth full validation passed: 3608 build jobs and 16867 project declarations audited, every transitive axiom allowlisted.

## Continuation 223 — the hidden path's entries and the pruned history

New module: Proofs/HiddenEntries, imported and indexed under the
signature game.

The hidden path's addresses and their characterization, the path's parent
keys, the entries at a list of keys and the pruned history, their
append, idempotence and fresh-history laws, the split of matching, the
pruned world, the freshness of the path's parent keys in it, and the
hidden entries.

The two-hundred-and-twenty-third full validation passed: 3607 build jobs and 16843 project declarations audited, every transitive axiom allowlisted.

## Continuation 222 — finding: the swap needs oracle-access continuations

No module was added. The finding and the corrected route are recorded in
audit/HUMAN_REVIEW.md; the mean-form swap bound over every continuation
is unsatisfiable, since the signer logs the hidden path. The latest full
validation (continuation 221) stands.

## Continuation 221 — the candidate verification law

New module: Proofs/CandidatePrepLaw, imported and indexed under the
signature game.

The candidate scheme's verification answer and its verification
preparation's resampling law.

The two-hundred-and-twenty-first full validation passed: 3606 build jobs and 16803 project declarations audited, every transitive axiom allowlisted.

## Continuation 220 — the run with its final world

New module: Proofs/RunWorld, imported and indexed under the signature
game.

The run threaded with its final world, the run as its first component,
the replacement of an attempt's embedded world, and the run with world's
resampling law.

The two-hundred-and-twentieth full validation passed: 3605 build jobs and 16789 project declarations audited, every transitive axiom allowlisted.

## Continuation 219 — the run hybrid in mean form

New module: Proofs/MeanHybrid, imported and indexed under the signature
game.

The run hybrid with the per-call signing bound in resampled form for a
fixed continuation, proved by moving the resampling along the run with
the oracles' resampling laws.

The two-hundred-and-nineteenth full validation passed: 3,604 build jobs and 16,747 project declarations audited, every transitive axiom allowlisted.

## Continuation 218 — the composed bound under the extended invariant

New module: Proofs/SimulationGapCipher, imported and indexed under the
signature game.

The simulation gap in mean form under the extended counted invariant
and the composed forgery bound with the row-stored term explicit and no
cipher-history hypothesis.

The two-hundred-and-eighteenth full validation passed: 3,603 build jobs and 16,733 project declarations audited, every transitive axiom allowlisted.

## Continuation 217 — the cipher-history invariant

New module: Proofs/CipherInvariant, imported and indexed under the
signature game.

Cipher-consistency of a shared world, its preservation with budgets by a
program run, the honest and simulated signings and the public oracle,
and the extended counted invariant with its step, key-generation,
resampling and consequence lemmas.

The two-hundred-and-seventeenth full validation passed: 3,602 build jobs and 16,729 project declarations audited, every transitive axiom allowlisted.

## Continuation 216 — the row-stored term explicit in the composed bound

New module: Proofs/RowBoundExplicit, imported and indexed under the
signature game.

The explicit row bound, the row-stored term's mean at an invariant
world within it, and the composed forgery bound with the row-stored
term discharged under the named cipher-history hypothesis.

The two-hundred-and-sixteenth full validation passed: 3,601 build jobs and 16,695 project declarations audited, every transitive axiom allowlisted.

## Continuation 215 — the staleness term's bound

New module: Proofs/StaleTermBound, imported and indexed under the
signature game.

A uniform draw's event probability as a count, the seeds whose key lies
in a set, the uniform root's key bound, and the staleness term bounded
by the root term plus the steps times the step bound.

The two-hundred-and-fifteenth full validation passed: 3,600 build jobs and 16,690 project declarations audited, every transitive axiom allowlisted.

## Continuation 214 — a stale last call forces the tree not to be good

New module: Proofs/StaleNotGood, imported and indexed under the
signature game.

The commitment phase from the tree with its budget and boundedness, the
run before the last call split at the tree, the first call's entry, the
commitment phase's run support, the staleness of the last call putting
the last leaf's key among the starting keys, and the staleness event
bounded by the tree's not-good event.

The two-hundred-and-fourteenth full validation passed: 3,599 build jobs and 16,682 project declarations audited, every transitive axiom allowlisted.

## Continuation 213 — the commitment calls' run

New module: Proofs/CommitEntries, imported and indexed under the
signature game.

The commitment call and entry of a pair, the inputs recorded by the
commitment calls over a list, the no-duplicates of the leaf pairs with
the initial segment's pairs differing from the last, and the commitment
addresses' bound.

The two-hundred-and-thirteenth full validation passed: 3,598 build jobs and 16,659 project declarations audited, every transitive axiom allowlisted.

## Continuation 212 — the tree's goodness along the expansion

New module: Proofs/TreeGoodInduction, imported and indexed under the
signature game.

The tree at a run's result, the not-good event, the expansion step's
pure run, and the induction bounding the probability that the tree
expansion's result is not good for the starting keys by the root's
indicator plus the steps times the step bound.

The two-hundred-and-twelfth full validation passed: 3,597 build jobs and 16,648 project declarations audited, every transitive axiom allowlisted.

## Continuation 211 — one expansion step under the posterior family

New module: Proofs/TreeStepFresh, imported and indexed under the
signature game.

The keys of a history, the goodness of a tree for a key set, the count
of outputs whose key lies in a set, the posterior key bound at a fresh
input, the freshness of a node's two expansion calls, the step's union
bound, and the goodness step.

The two-hundred-and-eleventh full validation passed: 3,596 build jobs and 16,625 project declarations audited, every transitive axiom allowlisted.

## Continuation 210 — the tree expansion's run step by step

New module: Proofs/TreeRunEntries, imported and indexed under the
signature game.

The node's expansion step, the tree expansion through one more step as
a bind, its boundedness and traced-run split, an expansion call's run
support, and the form of the entries the tree expansion records.

The two-hundred-and-tenth full validation passed: 3,595 build jobs and 16,610 project declarations audited, every transitive axiom allowlisted.

## Continuation 209 — the row-stored mean bounded by the staleness term

New module: Proofs/RowStoredPosterior, imported and indexed under the
signature game.

The family matching a run's cipher history and the history's length
bound, the posterior support's matching, the staleness of the last call
at a split point, the bound after the last call under the posterior
family, the staleness term, and the row-stored term's mean over the
resampled family bounded by the staleness term plus the explicit bound.

The two-hundred-and-ninth full validation passed: 3,594 build jobs and 16,594 project declarations audited, every transitive axiom allowlisted.

## Continuation 208 — the row-stored event after the last call

New module: Proofs/RowStoredAfter, imported and indexed under the
signature game.

Monotonicity of a map's truth, the constant map's indicator, the
pointwise monotonicity of binds at a value, the last call's staleness in
a history, the fixed set with its size bound and its independence of the
last block, and the row-stored event's membership in the fixed set.

The two-hundred-and-eighth full validation passed: 3,593 build jobs and 16,562 project declarations audited, every transitive axiom allowlisted.

## Continuation 207 — counting the last blocks that hit a fixed set

New module: Proofs/RowStoredCount, imported and indexed under the
signature game.

Instance-independence of the finite cardinality, the count of cipher
outputs whose row query lies in a finite set through the layout's output
fibers, and the posterior bound of the row query's membership at a fresh
input.

The two-hundred-and-seventh full validation passed: 3,592 build jobs and 16,551 project declarations audited, every transitive axiom allowlisted.

## Continuation 206 — the row-stored event reduced to the last block

New module: Proofs/RowStoredReduce, imported and indexed under the
signature game.

The last leaf pair as the last execution's last leaf, the last block and
the completed commitments, the reduction of the row-stored event after
the last call to the last execution's row query being defined before or
equal to another execution's, and the row query's injectivity in the
last block.

The two-hundred-and-sixth full validation passed: 3,591 build jobs and 16,544 project declarations audited, every transitive axiom allowlisted.

## Continuation 205 — the rows' table support

New module: Proofs/RowsSupport, imported and indexed under the
signature game.

The procedure's steps at a hash call, a cipher call and a finished
program, a hash call bound to a continuation, the defined inputs after a
run of hash calls over a list with a pure finish, and the finished state
of a run of a program bound to a pure finish.

The two-hundred-and-fifth full validation passed: 3,590 build jobs and 16,529 project declarations audited, every transitive axiom allowlisted.

## Continuation 204 — the head split at the last commitment call

New module: Proofs/HeadCommitSplit, imported and indexed under the
signature game.

The nonempty leaf pairs and their last pair, the commitments'
collection split at it, the last call's address and key, the head's
initial part before and after the last leaf's second cipher call, their
budgets and boundedness, and the traced run's split.

The two-hundred-and-fourth full validation passed: 3,589 build jobs and 16,517 project declarations audited, every transitive axiom allowlisted.

## Continuation 203 — fresh-input answers under the posterior family

New module: Proofs/PosteriorFresh, imported and indexed under the
signature game.

The posterior family's answer as the lazily sampled answer, and the
event, target and finite-set bounds of a fresh-input answer under the
posterior family in terms of the remaining block count.

The two-hundred-and-third full validation passed: 3,588 build jobs and 16,497 project declarations audited, every transitive axiom allowlisted.

## Continuation 202 — the composed bound with the mean-form gap

New module: Proofs/ForgeryBoundMean, imported and indexed under the
signature game.

The composed forgery bound against the candidate scheme with the
simulation gap in mean form: the row-stored term's mean over the
resampled world and the witness-swap slack's mean replace the per-world
hypotheses.

The two-hundred-and-second full validation passed: 3,587 build jobs and 16,493 project declarations audited, every transitive axiom allowlisted.

## Continuation 201 — the simulation gap in mean form

New module: Proofs/SimulationGapMean, imported and indexed under the
signature game.

The per-world charge of a signing query, the counted invariant kept by
resampling, and the simulation gap with the row-stored term and the
witness-swap slack as means over the resampled family, through the
charged replay hybrids and the expected-charge bounds with the candidate
oracles' resampling laws.

The two-hundred-and-first full validation passed: 3,586 build jobs and 16,492 project declarations audited, every transitive axiom allowlisted.

## Continuation 200 — the candidate oracles' resampling laws

New module: Proofs/CandidateResample, imported and indexed under the
signature game.

The payload, signed state and body of a commitment result, the honest
and simulated post-processings, the honest and simulated signing in the
program-running shape with their resampling laws, the public oracle's
law, instance congruence of the uniform distribution, and key generation
as a resampled world.

The two-hundredth full validation passed: 3,585 build jobs and 16,486 project declarations audited, every transitive axiom allowlisted.

## Continuation 199 — the shared scheme's resampling laws

New module: Proofs/SharedResample, imported and indexed under the
signature game.

The support-restricted bind congruence, the cipher-history suffix of a
run, the identity posterior of an impossible history, the program-run
resampling law without the possibility hypothesis, idempotent
resampling, the law under prior sampling, the law of a program-running
oracle with outer post-processing, and the uniform posterior of the
empty history.

The hundred-and-ninety-ninth full validation passed: 3,584 build jobs and 16,396 project declarations audited, every transitive axiom allowlisted.

## Continuation 198 — the expected replay charges

New module: Proofs/ChargeCutExpect, imported and indexed under the
signature game.

The mean of a scaled function, the mean over a resampled world with a
hash-table update, the resampling of a cut result at a saved snapshot,
the cut's resampling law, the expected cut charge, and the bounds of the
cut experiment's charge and of the fork charge from a resampled key.

The hundred-and-ninety-eighth full validation passed: 3,583 build jobs and 16,382 project declarations audited, every transitive axiom allowlisted.

## Continuation 197 — the replay hybrids with the charge

New module: Proofs/ChargeCut, imported and indexed under the signature
game.

The cut run's, branch's, cut experiment's and fork charges, and the cut,
continuation, fresh-branch, fork, cut-experiment and event-experiment
hybrids within them, mirroring the counted replay hybrids with the
world-dependent per-call bound.

The hundred-and-ninety-seventh full validation passed: 3,582 build jobs and 16,340 project declarations audited, every transitive axiom allowlisted.

## Continuation 196 — the expected charge from a resampled world

New module: Proofs/ChargeExpect, imported and indexed under the
signature game.

The mean of a function under a distribution and its laws, the joint-law
form of an oracle's resampling law with its continuation and mean forms,
the resampled world's hash table and its commutation with a hash-table
update, the charge's recursion in mean form, and the bound of the mean
cumulative charge from a resampled world by the fuel times the per-call
average bound.

The hundred-and-ninety-sixth full validation passed: 3,581 build jobs and 16,289 project declarations audited, every transitive axiom allowlisted.

## Continuation 195 — the run hybrid with a world-dependent charge

New module: Proofs/ChargeRun, imported and indexed under the signature
game.

The expected cumulative signing charge along a run and the run hybrid
with it: with a per-call signing bound under continuations whose term
depends on the world, at worlds satisfying the counted invariant within
the budget, the runs are within the expected cumulative charge of the
first scheme's run.

The hundred-and-ninety-fifth full validation passed: 3,580 build jobs and 16,263 project declarations audited, every transitive axiom allowlisted.

## Continuation 194 — the game under resampling

New module: Proofs/GameResample, imported and indexed under the
signature game.

The resampling of a game world's other-state, the scheme whose signing
oracle resamples before signing, the lift of idempotence to worlds, and
the game equalities: the run from a resampled world equals the
resampling scheme's run (induction on the fuel, with the oracle
commutation hypotheses at signing and public queries), and with key
generation yielding a resampled world the terminal laws and the
advantages coincide.

The hundred-and-ninety-fourth full validation passed: 3,579 build jobs and 16,233 project declarations audited, every transitive axiom allowlisted.

## Continuation 193 — the cipher resampling law

New module: Proofs/CipherResample, imported and indexed under the
signature game.

The posterior family of a cipher history, the resampling law of the
shared hash/cipher interpreter (a run against a posterior family then a
continuation equals the run then a fresh posterior draw at the resulting
history), and the shared scheme's program-run form with the world's
family resampled from its cipher history (`resample`,
`resample_bind_resample`, `runProgram_resample`).

Finding: the composed bound's per-world row-stored and witness-swap
hypotheses are unsatisfiable below one (a fixed family can make the last
execution's commitment row constant). The restatement over the resampled
family is the named correction; the game-level resampling equality is
next.

The hundred-and-ninety-third full validation passed: 3,578 build jobs and 16,212 project declarations audited, every transitive axiom allowlisted.

## Continuation 192 — the composed bound with payload consistency discharged

New module: Proofs/ForgeryBoundTrace, imported and indexed under the
signature game.

The composed forgery bound against the candidate scheme with payload
consistency discharged (the signer's candidate encoding and at least one
higher coefficient), the input-present term explicit, and the row-stored,
retry-failure and witness-swap bounds at worlds satisfying the counted
invariant as the remaining explicit hypotheses.

The row-stored event's bound, the retry-failure bound and the
witness-swap term remain open.

The hundred-and-ninety-second full validation passed: 3,577 build jobs and 16,195 project declarations audited, every transitive axiom allowlisted.
