# Completion goal checkpoint

The persistent completion goal remains active. The full formalization is not
complete, and no completion status has been asserted.

The initial user-triggered goal turn established the pinned Lean project,
transcribed the fragments listed in `COVERAGE.md`, proved three source discrepancy
statements and supporting algebra, and ran the build/axiom audit. See
`validation.log` for the last actual result.

The first automatic continuation also made concrete progress: it implemented the
detailed PIOP arithmetic and flat parsing, proved evaluation agreement and the
output degree bound, implemented Algorithm 21 and proved equation (8), implemented
Algorithm 5/domain prefixes with recoverability proofs, and proved two further
source discrepancies. Both goal turns are classified as progress, not as a wait
or a no-progress restatement. The global source obstruction remains, but there
was meaningful independent work, so no blocked status was asserted.

The second automatic continuation added the seed-tree loop and its initialization
invariant, Algorithm 7's commitment and ordered bit serialization, the literal
Algorithm 8 queue loop with termination and output-length proofs, and explicit
cipher formulas for the seed routines with checked tweak-domain bounds. It also
connected a complete 35-step opening trace to Algorithm 9's first-iteration
rejection for a submitted parameter set. This turn also made independent progress;
it is not a third consecutive no-progress turn. Full reconstruction, the BLC
algorithms, concrete primitives, and the security reductions remain unfinished.
The resulting build passed with 3171 jobs, and the transitive audit covered all
681 project declarations using only the three documented foundational axioms.

The third automatic continuation proved preservation of valid node addresses and
exclusion of undefined-operation outcomes for all legal BAVC opening inputs. It
formalized the BLC arithmetic body, including the initialized fold loop, actual
psi power sum, corrections, consistency fields and typed line slices, and proved
integrated line evaluation and consistency recovery for the displayed phi-based
challenge. Gray encoding/injectivity, one-bit transitions (including the zero
boundary), and optimized/direct folding equality are also checked. This is
another progress turn, not a no-progress recurrence of the source obstruction.
The final check passed with 3176 build jobs and a transitive audit of all 856
project declarations. No proof placeholders or non-allowlisted axioms were found.

The user asked whether Lean MCP and Lean Search MCP were being used. Neither
was exposed in the callable tool inventory when checked in this turn. Builds
and proof diagnostics use the pinned Lean CLI, and lemma discovery uses the
local mathlib sources. Recheck MCP availability if the session tools change.

The fourth automatic continuation added Algorithm 11's retry body using the
actual BAVC opening, with finite observations and explicit undefined counter
overflow. First-success, stable/unique returns, legal-input safety, and agreement
with Algorithm 12's header are proved. Cipher grinding's prepared keys/plaintexts
and both calls are transcribed, including counter-dependent material expansion;
input separation and encoded-counter recovery are checked. Byte/field sampling
and the matrix/batching sampling loops are formalized at explicit source,
consumption-count and decoder boundaries. Byte decomposition, whole-byte
recoverability, cursor movement and exact layouts are proved. The Category-III
Algorithm-6 parse-width discrepancy was also checked and documented after PDF
inspection. This is another substantive progress turn. The final validation
passed with 3182 build jobs and all 1174 project declarations audited. Only the
documented foundational axioms occur; no proof placeholders were introduced.

Lean MCP and Lean Search MCP were checked again against the callable tool
inventory in the fourth continuation; neither is exposed, and no tool-discovery
connector is exposed. The mathlib dependency named LeanSearchClient does not
mean its MCP service was used. This run used the pinned Lean CLI and local source
searches. No MCP usage is claimed.

Next independent obligations include concrete challenge expansion and field
representations, PRG behavior on its coherent domains, source-correspondent
serialization, and the remaining coherent signature computations. The retry
theorems are conditional and do not settle sampling distributions, passing-counter
existence, the raw-index/Gray encoding discrepancy, or counter overflow. Keep
these boundaries explicit and retain the three-statement final interface.

The fifth automatic continuation formalized Algorithm 1's entire deterministic
body after sampling. Its quotient/remainder state, increasing append loops and
original-position flat solution are explicit. Proofs establish mixed-radix
round trips, bounded digit injectivity, last-coordinate recovery, exact witness
length and solution Hamming weight, binary regularity, and injectivity of the
actual concatenated witness. Table-3 position ranges fit the radix products,
although their required equality still fails. Every produced selector satisfies
the printed unitary arithmetic for every challenge.

This continuation also connected the actual generated witness to the detailed
PIOP's flat parser on a coherent small SD instance: two arity-three layers, one
chunk of length nine, position zero, matrix [1,0,...,0] and syndrome one. The
generated solution is proved to satisfy the exact-weight-one SD relation. Its
constant witness lines and zero randomness nevertheless produce a PIOP polynomial
with nonzero constant term, independently of the field generator and unitary
batching challenge. This is a scoped arithmetic counterexample, not a submitted
parameter set or claim about a concrete BLC output distribution. It strengthens
the existing mux discrepancy without repairing the source.

The fifth continuation is a progress turn. Validation passed with 3186 build
jobs and all 1309 project declarations covered by the transitive axiom audit.
Only the same three foundational axioms occur, and no placeholders were used.
The three-statement final interface and standalone specification/assumption
entry points remain intact. Remaining useful mathematical work includes the
unitary-check converse/packed-polynomial argument and the concrete field basis,
in addition to the integration obligations already recorded above.

The sixth automatic continuation proved the full binary unitary-polynomial
characterization for every stored selector length: D(Y)=0 exactly when at most
one coordinate is nonzero. The proof expands the actual arithmetic and recovers
off-diagonal bit products from its coefficients. It also proves the degree bound,
disjoint 32-coefficient packing, and equivalence of the actual recursive
unitaryLayers loop with those checks for the submitted dimensions.

Table 2's three modulus polynomials were transcribed after visual PDF inspection.
Their monicity, exact degrees, quotient power bases, low-degree evaluation
property and coefficient-encoding injectivity are checked. These are explicitly
quotient rings; no unproved field instance or irreducibility assumption was
introduced. The actual BLC psi map is proved injective for tau*kappa <= lambda,
and the actual full zero-padded Phi embedding is injective, including partial
final blocks. Kernel computations check the required dimensions in Tables 3–5.

An exploratory Python computation returned the expected Frobenius/gcd results
for all three modulus polynomials (degrees 128, 192, 256). This is discovery
evidence only, not a formal proof or trusted certificate. Irreducibility remains
unfinished. A local library search did not find a ready Rabin criterion; further
work may require proving that criterion and checking modular-power/Bezout
certificates in Lean, rather than trusting the external computation.

This is another progress turn. The final validation passed with 3192 build jobs
and all 1420 project declarations audited, using only the same three foundational
axioms. The standalone specification and assumption entry points and the
three-statement final interface remain intact. Full field/byte integration,
randomized batching and PIOP soundness, concrete primitives and missing security
reductions remain unfinished; the source contradictions have not been repaired.

The exact-source requirement now encounters proved source contradictions. A
source-policy question was sent to the user (literal source with refutations,
explicit corrected specification, or an authoritative replacement). No answer
has yet been received. No correction is authorized by the passage of time.
The current policy remains literal transcription and explicit discrepancy reports.

For further work, retain the no-placeholder/no-new-axiom policy and the small
final interface. Do not turn the heuristic §5.1 bound or missing §5.3 EUF-CMA
proof into assumptions. Do not mark an algorithm complete merely because a
fragment has been formalized. Resolve source ambiguity before choosing a repaired
algorithm. If the completion goal remains at an impasse across three consecutive
goal turns, report that status honestly rather than claiming completion.

The seventh automatic continuation completed the irreducibility proofs for all
three exact Table-2 polynomials. `Proofs/BinaryIrreducibility.lean` proves the
factor-degree/Frobenius criterion using an auxiliary quotient field only for an
already-proved irreducible factor. `Proofs/BinaryPolynomialCertificate.lean`
proves the meaning of binary coefficient-list addition, multiplication, squaring
and Euclidean remainder checks. The generated category files check all 576
repeated-square steps and four coprimality transcripts with ordinary `decide`.
The Python generator supplies untrusted data, not assumed arithmetic facts.

`Proofs/FieldIrreducibility.lean` connects those certificates to the standalone
specification, proves each modulus irreducible, installs the resulting field
instances and proves cardinalities 2^128, 2^192 and 2^256. No custom axiom,
unchecked native proof or placeholder was introduced. Generated coefficient
vectors and transcript chunks are separate definitions to keep Lean's kernel
and compiler reductions manageable. A symbolic certificate-transfer lemma
avoids expanding enormous powers while comparing equivalent algebra instances.

The seventh continuation is a progress turn. Full validation passed with 3198
build jobs and all 3434 project declarations covered by the transitive axiom
audit. Only the same three foundational axioms occur. The standalone
specification and assumption entry points and three-statement final interface
are intact. Coverage and human-review records now distinguish the completed
irreducibility proofs from unfinished byte decoding and concrete algorithm
integration. Randomized batching/PIOP soundness, concrete primitive integration
and missing security reductions remain unfinished. The source contradictions
and pending source-policy question remain unchanged; this is not completion of
the whole submission. Further independent work can use the now-proved finite
fields for precise uniform-challenge probability bounds without silently
repairing the source algorithms or assuming missing security proofs.

The eighth automatic continuation defined explicit uniform challenge experiments
and proved their probability laws. Uniform linear batching of a fixed nonzero
vector vanishes with probability exactly 1/|F|. This is connected to Algorithm
21's actual padded embedding and scalar equation, giving exactly 2^(-lambda)
in each submitted field for a fixed invalid input equation. Finite-set root
sampling and the polynomial substitution degree bounds are also kernel checked.

For the literal introductory PIOP verifier, the derived residual has degree at
most d+1. With fixed invalid committed constants and consistent openings, the
checked uniform experiment has acceptance probability at most
1/|F| + (1-1/|F|)*(d+1)/|S|. The response can depend on the first challenge and
can itself be randomized, provided its support satisfies the response degree
bound. These are explicitly fresh uniform samplers. They do not establish a
concrete hash/XOF distribution, commitment binding, knowledge extraction, zero
knowledge or a Fiat-Shamir security reduction.

`Proofs/PIOPSoundnessDiscrepancy.lean` additionally refutes the introductory
protocol's printed d-based bound in every submitted field. Take d=2, f=1,
P0=P1=X, response gamma*X^2+X, and S the three cube roots of one. The constraints
have binary coefficients and admit no witness; the prescribed degree bounds
hold and the literal verifier accepts every sampled challenge. Existence of
exactly three cube roots is proved from the concrete field cardinalities and
cyclic multiplicative groups. Acceptance probability is one, whereas the
printed expression is strictly less than one. The source formulas and sampling
set allowance were visually rechecked. This concerns the generic introductory
PIOP, not an instantiated signature attack. No source correction was made.

The eighth continuation is a progress turn. Full validation passed with 3205
build jobs and all 3502 project declarations covered by the transitive axiom
audit, using only propext, Classical.choice and Quot.sound. The standalone
specification and assumption entry points and exactly three final statements
are preserved. Remaining independent work includes the unitary batching
distribution, field/byte and concrete primitive integration; full protocol
security remains unfinished, with source contradictions and the pending
source-policy question recorded separately. No missing conclusion was promoted
to an assumption and no proof placeholder was used.

The ninth automatic continuation completed the uniform unitary batching
argument and composed the detailed PIOP with its actual syndrome batching.
`Proofs/UniformChallenges.lean` now proves equal probabilities for every fiber
of a surjective linear form, so a fixed offset does not alter cancellation.
`Proofs/UnitaryProbability.lean` applies this to the actual recursive unitary
loop and the flat prover polynomial's constant term: an invalid binary selector
collection cancels with probability exactly 2^(-lambda), even in the presence
of a fixed syndrome/mux offset.

`Spec/PIOPComposition.lean` transcribes Algorithms 19/20 after challenge
expansion, composing Algorithm 21 with the real chunk indexing and flat parsers.
Its required equality leafCount(widths)*w = r+k is explicit. It is not proved
or assumed for the inconsistent Table-3 parameters. `Proofs/MuxLinearity.lean`
proves that batching commutes with the literal mux recurrence, deriving its
base-field syndrome residual without identifying it with the conflicting
omitted-last-coordinate witness encoding.

The composed routines now have checked evaluation agreement, output degree and
an exact constant-term identity. The constant is the sum of the syndrome and
unitary batches. Under the two independent uniform coefficient vectors its
probability of being zero is exactly 2^(-lambda) when either computed constraint
vector is nonzero, and one when both vanish. This completes the local uniform
batching argument rather than assuming it as a protocol correctness contract.

`Spec/DetailedPIOPChallenges.lean` keeps Algorithm 20's consistent-evaluation
comparison separate from the introductory verifier with its extra delta.
`Proofs/DetailedPIOPChallenges.lean` proves the detailed algebraic bound
2^(-lambda) + (1-2^(-lambda))*d/|S| for invalid literal constraints, line degrees
at most one and responses of degree at most d. A response may be randomized
after both batching vectors and before a fresh uniform evaluation point.
The experiment explicitly checks a zero response constant and supplies consistent
openings. It does not implement or assume the signature coefficient hash check,
BLC binding, knowledge extraction or concrete XOF distributions. It does not
repair the introductory soundness/completeness counterexamples. Equation (6)
and Algorithm 19 were visually rechecked in the PDF.

This is another progress turn. Full validation passed with 3211 build jobs and
all 3554 project declarations covered by the transitive axiom audit; only
propext, Classical.choice and Quot.sound occur. Exactly three final statements
and the separate specification/assumption entry points are preserved. The
coverage and human-review records distinguish these completed local proofs from
the remaining source contradictions, concrete primitive/byte integration,
full keygen/sign/verify composition and missing security reductions. The
source-policy question remains unanswered and no source correction was made.
Further independent work remains possible; the whole-submission goal is active
and is not complete or blocked.

The tenth automatic continuation formalized coefficient compression and
composed the signing phases with the actual commitment and retry routines.
`Spec/CoefficientCompression.lean` retains the source's alpha_1,...,alpha_d
hash tuple, alpha_2,...,alpha_d transmitted tuple and exact recovery sum.
`Proofs/CoefficientCompression.lean` proves recovery is
alpha_1 + delta^(-1)*alpha_0 for nonzero delta. Recovered and hashed tuples
coincide iff the actual degree-bounded polynomial has zero constant term.
`Proofs/CoefficientDiscrepancy.lean` connects the already proved valid small
SD witness counterexample to different tuples at every nonzero challenge.
It does not assert unequal hash outputs or a reachable signature execution.

`Spec/SignatureComposition.lean` records the ordered typed hash/signature
fields, post-commit preparation, actual Algorithm-11 retry/opening and
Algorithm 4 after BLC recomputation. Pending observations and unspecified
overflow are preserved, not turned into source aborts. Returned signatures
have checked counter/header agreement and actual successful BAVC openings.
The coefficient/hash-input comparison theorem explicitly uses mathematical
committed evaluations; it does not assume Algorithm 12 returns those values.
Messages are arbitrary bit strings, with no byte-alignment restriction.

`Spec/BLCCommit.lean` composes Algorithm 10 through the real BAVC seed tree,
per-leaf/per-execution PRG byte sampling, actual Gray folding, positive-index
corrections, typed Hashaux call, consistency-XOF matrix, checks and polynomial
line construction. Hashlines retains the printed witness correction. The
positive-index range is proved, as are witness constants and degree-at-most-one
properties. Concrete cipher/hash/PRG/XOF implementations, hash serialization
and the source's unspecified consumption policy remain explicit boundaries.
These functions have no assumed correctness or cryptographic contracts.

`Spec/Signing.lean` composes phases 1–3 from that commitment, the detailed
PIOP, coefficient compression and actual retry loop. Its proofs derive the
required polynomial degree through the actual line construction, without
passing it as a commitment interface assumption. The exact zero-constant
condition for hash-input agreement is retained. Decoded key data, expanded H',
salt and root seed enter at the initialization boundary. The printed algorithms
3, 4 and 10 were visually checked, including coefficient order, recovery powers,
auxiliary indexing, matrix orientation and the witness-correction hash field.

This continuation is progress. Full validation passed with 3220 build jobs and
all 3816 project declarations covered by the transitive axiom audit, using only
propext, Classical.choice and Quot.sound. The standalone specification and
assumption entry points and exactly three final statements remain intact.
No source correction, hidden assumption or proof placeholder was introduced.
Key generation, raw initialization/serialization, the unresolved reconstruction
algorithms, concrete primitives, variants and security reductions remain
incomplete. Source-policy clarification is still pending. The full objective
remains active; this is not a completion or blocked turn.

The eleventh automatic continuation formalized the integer-sampling prefix on
printed p. 18. `Spec/IntegerSampling.lean` assembles the four little-endian bytes,
computes the largest-multiple threshold, repeats rejected reads, and stops at the
first accepted candidate before line 7. It does not bind the undefined B in
B % m to the assembled v or manufacture a sampled-position vector. The rendered
PDF page was rechecked and confirms the unbound identifier.

`Proofs/IntegerSampling.lean` proves the exact byte formula, bijectivity and byte
recovery, threshold maximality and remainder identity, positive threshold and
the discarded-word bound below half the range for 1 <= m <= bound. A found
candidate has exact four-byte cursor accounting, satisfies the acceptance
threshold, preserves the input stream and is stable under further observation.
For every legal positive m, an all-zero stream reaches the unresolved assignment
after its first four-byte read. This last result concerns a concrete stream,
not a claim about any cryptographic PRG distribution.

`Proofs/IntegerSamplingProbability.lean` gives explicit uniform laws: four
independent uniform bytes produce a uniform word; acceptance and rejection have
their exact finite-range probabilities; each residue class below q*m has q
elements; and v % m on the uniform accepted range has probability 1/m per value.
The residue theorem is kept separate from the literal source's undefined B.
No uniform concrete-PRG law or returned-position distribution is assumed.

The loop's generic operational helper is instantiated with the actual four-byte
reader and proved cursor equation. This avoids eagerly reducing the concrete
2^32 word encoding inside kernel comparisons. Generic Nat.card probability
lemmas also avoid mismatched finite-enumeration instances for arithmetic
predicates; all transformations remain ordinary kernel-checked proofs.

This is a progress turn. Full validation passed with 3223 build jobs and all
3964 project declarations covered by the transitive axiom audit. Only propext,
Classical.choice and Quot.sound occur. The standalone specification/assumption
entry points and exactly three final statements remain unchanged in scope.
The missing accepted-value binding still prevents literal integer-sampler and
key-generation completion; other concrete primitive, serialization, variant
and security-reduction work also remains. No source repair was chosen, no
placeholder or unapproved axiom was introduced, and the whole goal stays active.

The twelfth automatic continuation formalized the exact part of §5.1's
SD-to-RSD reduction. The printed pages 42–43 were visually inspected. The
first ratio display uses an undefined d in n/d; subsequent formulas use n/w.
The formal support-counting result uses n=w*m explicitly, without silently
repairing the first display or assuming the later heuristic argument.

`Spec/RegularSupport.lean` defines supports with exactly one occupied position
per chunk. `Proofs/RegularSupport.lean` establishes the graph characterization,
weight w, count m^w, and total weight-w support count choose(w*m,w).
`Proofs/PermutationProbability.lean` constructs ambient permutations between
equal-size supports, bijections of their permutation fibers, and the resulting
uniform image/event law. The exact regularization probability is derived from
these constructions, not supplied as a distributional assumption.

`Spec/SDReduction.lean` specifies the displayed randomized algorithm through
the supplied solver, preserving the full-syndrome-only check, failure result
and inverse permutation. `Proofs/SDReduction.lean` proves support/weight and
syndrome permutation identities, correspondence of nonzero support regularity
to the field-valued regular-vector definition, flat-coordinate weight, exact
row removal, truncation of solutions, return characterization and correctness
for a regular candidate. The deterministic uniqueness step is also proved:
a full regular solution survives truncation and must equal a correct solver
output if that truncated instance has only one regular solution.

`Proofs/SDReductionProbability.lean` transports the exact support law through
the concrete chunk/flat coordinate equivalence. It proves the ratio as a lower
bound for existence of some regular solution, and proves that every nonfailure
result of the full randomized reduction is an SD solution under the explicit
premise that all possible solver results are RSD solutions. It does not insert
an extra weight check into the source or assume a conditional success rate.

`Proofs/SDReductionDiscrepancy.lean` distinguishes the fixed-witness and
instance-existence events on a genuine binary SD instance: n=4,w=2,k=1,H=0,y=0.
The instance remains regularly solvable after every permutation, with probability
1, whereas its fixed weight-2 witness becomes regular with probability 4/6.
This refutes the pointwise instance-event equality, not by itself the final
Theorem-5.1 inequality or an assertion about seeded systematic public keys.
The heuristic uniqueness estimate, conditioning on solver success, input-law
correspondence and runtime accounting remain human/proof obligations.

Full validation passed with 3230 build jobs and all 4065 project declarations
covered by the transitive axiom audit. Only propext, Classical.choice and
Quot.sound occur. Specification and assumption entry points remain separate;
the final interface still contains exactly three statements. This continuation
made verified progress. No source-policy answer has arrived, no source repair
or hidden assumption was made, and the whole formalization remains incomplete
with its loop active.

The thirteenth automatic continuation connected field representations to byte
sampling without selecting an undocumented extension-field wire order. The
rendered printed p. 18 was rechecked: binary sampling gives little-endian bit
coefficients, while the extension branch only describes consecutive byte packs.
This missing byte-to-polynomial ordering is now recorded as a specific human
correspondence obligation, with no default inserted into the specification.

`Proofs/FieldIsomorphism.lean` establishes the full linear isomorphism phi of
printed p. 34 for each exact Table-2 quotient, proving surjectivity and both
coefficient round trips as well as the existing injectivity. The construction
uses the proved monic power basis and requires no additional field hypothesis.

`Spec/FieldBytes.lean` gives a polynomial-basis decoder family whose coefficient
ordering is an explicit equivalence between basis indices and byte/bit positions.
Its sampler and batching wrappers call the existing actual byte readers.
`Proofs/FieldBytes.lean` proves bit/byte bijections, the exact field power-sum
formula, both pack round trips, recovery of all used sampled bytes, and the
actual sequential batching layouts. Its named little-endian ordering is a
comparison choice, not an assumed source convention.

`Proofs/UniformVectors.lean` proves that distinct coordinate selection preserves
the joint uniform law, using an explicit decomposition into selected and unused
coordinates. `Proofs/FieldByteProbability.lean` derives uniform field elements,
vectors and both sequential batching vectors from the explicit finite uniform
byte sample. The proof accommodates extra consumed bytes, establishes disjoint
used ranges, and never reads the finite reader's zero extension. The arithmetic
field instances are the previously checked submitted quotients.

`Proofs/FieldChallengeLaw.lean` identifies the resulting batching law with the
existing detailed PIOP two-vector law. That equality preserves every subsequent
randomized computation. It does not identify a concrete XOF with uniform bytes.
`Proofs/BinarySamplingProbability.lean` proves joint uniformity of the actual
binary sampling branch, including partial bytes and unused consumed bytes,
and of its conversion to ZMod 2. Consumption counts are still explicit and
no buffering policy or PRG/XOF independence assumption was silently added.

Full validation passed with 3237 build jobs and 4164 project declarations
covered by the transitive axiom audit. Only propext, Classical.choice and
Quot.sound occur. The specification and assumption entry points stay separate,
and the final interface remains exactly three statements. This continuation
made verified progress. Source ambiguities, concrete cryptographic primitives,
serialization, variants and end-to-end security/correctness obligations still
prevent whole-submission completion. The source-policy question remains
unanswered, no source repair was selected, and the full goal remains active.

The fourteenth automatic continuation formalized the specified mathematical
content of the §6 variants. Printed pages 45–48 were rendered and visually
inspected. The source describes these as outlines for possible future formal
instances; absent complete algorithms were not replaced by invented protocols.

`Spec/VariantParameters.lean` transcribes Tables 8–10 and all displayed variant
key/signature formulas, with explicit field-bit width, constraint degree and
consistency slack where appropriate. `Proofs/VariantParameters.lean` checks every
reported size, byte/granularity rounding, percentage intervals and numerical
error budget. The budget predicates are proved equivalent to the exact rational
expressions d/N^tau/2^grinding and (d/N)^tau/2^grinding. This arithmetic does not
assert a protocol soundness theorem. The simple formula retains its printed
32-bit term; Table 10's size theorem explicitly uses B=16 from the main table.

F256 Table 7 has three [4,4,4] tensor factors, while Table 8's signature sizes
match constraint degree four. Using the tensor depth as the degree does not
match that table. The formalization separates these parameters and records the
source's overloaded d notation for human review. It does not silently change
the tensor arities or pretend a full variant PIOP was supplied by the source.

`Spec/ScaledWitness.lean` records positions, nonzero amplitudes, unchanged binary
position encoding and post-mux scaling. `Proofs/ScaledWitness.lean` proves exact
regular-vector correspondence, unique recovery, weight w, selected-column
syndrome, and count (m*(q-1))^w for a finite q-element field. It also connects the
scaled tensor to the actual mixed-radix encoding and proves evaluation, linear
batching and degree behavior for the literal mux. The known mux selector-order
conflict remains unresolved. The nonzero amplitude type is a witness-relation
requirement, not a proof that an unspecified verifier enforces it.

`Proofs/ScaledMuxDegree.lean` checks a [4,4,4]-arity example over any field with
all selector inputs of degree at most one and amplitude X+1, whose nonzero
constant is one. Its output is exactly X^4+X^3, of degree four. Thus the extra
degree can occur and explains the degree value used in the Table-8 size checks.
Concrete F256 representation/embedding, amplitude serialization and nonzero
constraints, full variant algorithms, TCitH commitment/security and runtime
claims remain explicit obligations. The regular-vector count also sharpens
the already recorded nonbinary counting gap in the §5.1 heuristic.

Full validation passed with 3242 build jobs and all 4416 project declarations
covered by the transitive axiom audit. Only propext, Classical.choice and
Quot.sound occur. Standalone specification and assumption entry points and
exactly three final statements are preserved. This was a verified progress turn,
not a blocked or completed turn. The whole goal remains active; source-policy
clarification has not arrived, and no source correction or hidden assumption
was used to bridge missing proofs.

The fifteenth automatic continuation added the concrete SHAKE primitives selected
by Table 1. The final August-2015 FIPS 202 and six NIST worked-example PDFs were
retrieved, pinned by hash and recorded in source/standards/index.json. Relevant
standard pages and each example's input/output pages were rendered and inspected.
The existing exact SDitH source policy and all recorded discrepancies remain.

Spec/Keccak.lean records literal bit equations and an executable 25-lane,
64-bit implementation for the required 1600-bit, 24-round function. Proofs/Keccak
checks both state-string round trips, rotation indexing, the full rho orbit and
source offset table, the feedback register, round-constant bit positions, all
five step refinements, and their round/24-round composition. Keccak bijectivity
and security properties are not asserted by this functional refinement.

Spec/SHAKE.lean implements arbitrary-bit-input SHAKE128/256, with the exact
four-bit suffix, padding, block absorption, arbitrary-length squeeze stream and
finite append/permutation loop. Proofs cover the integer padding formula,
positive divisible length, exact full block reassembly, in-bounds reads, unchanged
capacity bits on injection, absorption-fold agreement and every finite output
prefix of the squeeze loop. The concrete byte stream is connected to the existing
binary sampler, including partial-byte requests and explicit byte consumption.

Spec/HashPrimitives instantiates BAVC's existing domain-byte/array input hashing
with the Table-1 SHAKE choice, while leaving Enc* explicit. Hash is proved to be
the exact 2*lambda-bit prefix of the same SHAKE reader. This does not choose any
missing typed-transcript, extension-field or counter serialization and does not
identify deterministic SHAKE outputs with independent uniform challenges.

The six generated example modules check NIST's empty, 5-bit and 1605-bit messages
for both SHAKE strengths. Each checks every step of every absorption round and
the first 64 output bytes. The generator extracts proposed certificate data;
no generator or native-evaluation result is admitted into the logic. The other
published output bytes are retained as unproved source data. Proofs/KeccakConstants
certifies a proposed 169-state LFSR orbit by checked one-step transitions and
induction, then derives all 24 round constants for reuse. Proofs/SHAKEReading
proves exact padding delimiter positions to simplify concrete input checks.

Initial simultaneous and repeated-reduction certificate builds caused memory
contention. Certificate proofs now use kernel-only decide, shared proved constants
and synchronous checking. scripts/check.py builds them sequentially before the
full project/axiom audit. This changes verification cost, not definitions or the
trust whitelist. No native proof shortcut, new axiom or source repair was used.

Full validation passed: 3258 build jobs, all six example certificates and all
8656 project declarations in the transitive axiom audit. Only propext,
Classical.choice and Quot.sound occur. Specification and assumption entry points
remain standalone, and Final.lean still contains exactly three statements.
The whole formalization remains incomplete and the goal remains active. This
turn made verified progress; it is not a blocked or completed goal turn. The
source-policy question remains unanswered. AES/Rijndael, PRG integration, missing
serializations/algorithm definitions and the correctness/security reductions
remain explicit work or source-resolution obligations.


## Automatic continuation 16 — concrete block ciphers and byte-field proofs

The sixteenth continuation added complete byte-oriented AES-128 and
Rijndael-256-256 bodies, using the exact profiles selected by SDitH Table 1.
The primary references are the final 2023 FIPS 197-upd1 and the designers'
version-2 original Rijndael proposal. Their PDFs are pinned by SHA-256 in the
check script and indexed with URLs and visually reviewed pages. The designers'
2002 book is additionally pinned for its two full-width Rijndael test vectors.

Spec/RijndaelByte defines the exact binary polynomial quotient, low-coefficient
byte representation, xtime, distributive multiplication, affine transformation
and literal 256-entry S-box. Proofs/RijndaelByte establishes monicity/degree,
the full basis/byte bijection, generator reduction, XOR/addition and
multiplication preservation. Every nonzero inverse witness is checked in the
kernel and transported through the decoder to derive a 256-element field
structure, without a field or irreducibility assumption. The literal S-box is
proved equivalent to the unique inverse-and-affine relation. Both S-box inverse
directions and the exact affine bit equation are checked for every byte.

Spec/Rijndael defines 4/8-column states, 10/14 rounds, column-first byte layout,
1/2/3 versus 1/3/4 shifts, 44/120 key words, the wide-key extra SubWord step and
the final round without MixColumns. Expansion uses length-indexed vectors and
safe reads. Proofs/Rijndael proves the field matrix identities for column mixing,
invertibility of all component steps and bijectivity of the entire cipher for
every fixed key. Proofs/RijndaelSchedule proves prefix preservation, completed
schedule recurrence, initial-key recovery and positive Rcon call indices.
Rijndael-256-256 is not replaced by AES-256.

Spec/CipherPrimitives implements byte packing in the existing SDitH low-bit-first
convention and names the within-byte reversal for FIPS displayed bitstrings.
Both packing round trips and that conversion's bit formula are proved. Table-1
Enc/Enc* choices use the actual ciphers, preserving Category III's zero padding
and low-192-bit truncation. Full Enc is injective in all categories. Enc* is
proved bijective only for I/V; no such claim is made for III. BAVC's primitive
family now uses these actual cipher bodies and the actual SHAKE hash.

Proofs/AESExample checks the full key expansion and every intermediate state
in FIPS Appendix B, then proves that the actual encrypt function returns the
published ciphertext. scripts/generate_aes_example.py only extracts proposed
source data; the kernel checks it. Proofs/Rijndael256Examples directly checks
both published 256/256 vectors from the designers' Appendix D.3: zero under
zero, then the result again under zero. All certificates use ordinary kernel
reduction, including decide +kernel; no native result is accepted as a proof.
Fresh-build cipher certificates are checked sequentially by scripts/check.py.

Proof-engineering notes: explicit BitVec literals such as 0#8 avoid ring-numeral
unification issues. Default norm_num simplification on expanded byte formulas
can recurse indefinitely; controlled norm_num only plus separately proved
constant decoding works. Fin-indexed and Nat-indexed vector reads need explicit
conversion, and numeral Fin indices sometimes need an explicit constructor.
For dependent push lengths, exact Vector.getElem_push_lt/getElem_push_eq works
where simp fails to match. AES certificate build took about 12 seconds and the
two direct wide-Rijndael checks about 50 seconds on this machine.

Full validation passed: 3268 build jobs and 9142 project declarations, with
only propext, Classical.choice and Quot.sound in the transitive axiom audit.
The separate specification/assumption interfaces and three final discrepancy
statements remain intact. No custom axioms, proof placeholders, unsafe code,
native decisions or unchecked assumptions were introduced.

The whole-submission goal remains active and incomplete. This continuation made
verified progress and was not blocked. The earlier source-policy question has
no recorded answer; the literal source and explicit discrepancies are retained.
PRG integration (undefined nblock-bitsize and Category-III parse mismatch),
missing structured serialization, undefined algorithm variables, complete
commitment/opening/recomputation and the absent security proofs remain open.
The fixed-key permutation and conformance results do not imply an ideal-cipher
law, pseudorandomness, commitment security, zero knowledge or EUF-CMA security.


## Automatic continuation 17 — counter-mode PRG and concrete BLC primitives

The seventeenth continuation formalized Algorithm 6 as a partial literal
transcription, using the actual Table-1 ciphers. The undefined block-size
symbol is an explicit positive parameter without a selected default. Optional
salt/tweak preparation preserves the zero-salt comment and leaves present salt
without a tweak unresolved. Complete byte parsing retains line 5's lambda/8
byte count; a positive Category-III request cannot satisfy it. None denotes
an unresolved source assignment, not an invented algorithm rejection.

Spec/PRG exposes the materialized block vector, byte vector, append loop,
infinite ciphertext stream and reader. Proofs/PRG establishes the least block
count, byte packing and injectivity, loop/vector/stream correspondence, exact
successful-run characterization, coordinate recovery and prefix stability.
Categories I/V execute for an explicit denominator bound. The fixed-width
LittleEndian total convention and intended counter range remain in the human
correspondence ledger; no unspecified exhaustion policy is certified.

Proofs/PRGCounter connects actual Enc injectivity to counter equality modulo
2^lambda, proves no-wrap injectivity and stream periodicity, and recovers the
low 16 counter bits and next 8 tweak bits. Joint separation requires counters
below 2^16. A concrete overlapping pair is proved without cipher computation:
tweak 0/counter 2^16 and tweak 1/counter 0 give the same plaintext and ciphertext
for every salt, key, category and grinding variant. This is a local encoding
identity, not a signature attack or a pseudorandomness theorem.

Proofs/PRGSampling proves finite-output agreement for readBytes, binary and
extension sampling, the explicit-order Table-2 field decoder, increasing row
loops and ExpandH's column loop. All accesses stay inside the actual output;
finiteReader's length is supplied explicitly. During elaboration, leaving that
implicit allowed Lean to infer a shorter count from an access bound, so every
new occurrence now names the full output length. No zero-extension byte is
used as generated data. Byte-consumption policy remains an explicit parameter.

Spec/ConcreteBLC instantiates the existing Algorithm-10 interface with actual
Enc*, SHAKE hashes/XOF and the ciphertext stream. Hashaux concatenates hcom
and positive-index corrections in order. Hashlines retains haux, plain check,
base check and witness correction, preserving the existing Algorithm-12
mismatch. Vector/matrix serialization functions remain an explicit structure,
without a claimed correctness, injectivity or length contract. The Nat-indexed
PRG interface has a documented zero extension outside the source's tweak range;
all Tables 4/5/8/9/10 execution indices are proved within that range.

Proofs/ConcreteBLC connects finite Category-I/V calls to the stream, actual
successful finite calls to folding-table bits, BAVC primitive families to the
existing concrete implementation, and consistency-matrix coordinates to SHAKE
bits. Category III's infinite stream is not identified with its inconsistent
finite Parse. The spec-only entry point imports the two new specification
modules; the root imports all four proof modules. Source/index, README and
coverage/human-review ledgers were updated. Printed page 17 was visually
reviewed again against the literal assignments.

Full validation passed: 3274 build jobs and 9348 project declarations. The
recursive axiom audit still admits only propext, Classical.choice and Quot.sound.
No custom axioms, proof placeholders, unsafe/native decisions, hidden security
contracts or silent source repairs were introduced. Final.lean is unchanged
with exactly three statements, and assumptions remain separately defined.

The whole-submission goal remains active and incomplete. This continuation
made verified progress and was not blocked. The earlier source-policy question
has no recorded answer; literal formulas and explicit source gaps are retained.
Initialization/keygen, integer-sampler accepted output, structured serialization,
full BAVC reconstruction and BLC recomputation, the known algebraic/source
contradictions, complete variant protocols, and correctness/security reductions
remain outstanding. Concrete deterministic primitive integration does not
establish hiding, binding, zero knowledge, ideal-oracle/cipher laws or EUF-CMA.


### Continuation 17, continued after the user's progress question — key generation

The user requested current progress while the goal was active. A concise status
was supplied and work continued, preserving the original formalization goal.
Spec/KeyGeneration and Proofs/KeyGeneration now cover independent uniform seed
sampling, the actual post-position witness expansion, the concrete unsalted
cipher-stream ExpandH column loop, the literal [I|Hprime] syndrome assignment,
typed keys, explicit serializer functions and typed matrix initialization.

The key-generation PDF page (physical 14, printed 12) was visually inspected.
Its undefined x_A remains an optional external binding; no substitution of the
generated x is performed, and an absent binding is undefined source semantics,
not a new rejection. The two identity-block orientations are both defined,
related by an explicit swap and proved different on a small binary example
without that swap. This example is not claimed to arise from the concrete PRG.
Physical 15/printed 13 was also visually checked: signing line 7 uses pk while
its explicit input is sk. Exact raw public-key reconstruction remains a source/
serialization interface obligation, not an assumed decoder law.

The seed pair has the exact uniform joint law and point probability
2^(-2*lambda). Deterministic expansions preserve independence as their actual
pushforward distributions; uniform expanded matrices/witnesses are not assumed.
ExpandH coordinates and finite-PRG correspondence reuse the bounded proofs.
Actual generated witness length and exact weight are derived from Algorithm 1.
The flat cast into r+k coordinates uses only r+k=w*m, without the false tensor
size equality. For a typed key returned from any supplied x_A binding, the
actual generated vector is a weight-w SD solution iff [I|Hprime]*(x_A-x)=0.
That necessary-and-sufficient condition is proved from the real assignment and
weight theorem, rather than accepted as a correctness assumption.

Typed secret/public initialization reproduces the generation matrix for the
same seed and byte-consumption count. It starts after decoding and does not
implement a parser. Serialization functions carry no injectivity, length or
round-trip contract. Undefined integer output, x_A, Category-III PRG parsing,
consumption policy and full initialization/signing integration stay explicit.

Both modules are imported by their corresponding entry points; the source
inventory, README, coverage and human-review ledgers have been updated. The
new full validation passed with 3276 build jobs and 9490 project declarations.
Only propext, Classical.choice and Quot.sound occur in the recursive axiom
audit. Final.lean still has exactly three statements. No proof placeholders,
custom axioms, native proof shortcuts or silent source corrections were used.

The goal is still active and incomplete. This follow-on work made verified
progress; no blocked-turn counter applies. The source-policy question remains
unanswered. Remaining priorities include full reconstruction/recomputation,
challenge/serialization integration, complete variant protocols and the absent
correctness/security reductions, while preserving all checked source conflicts.


## Automatic continuation 18 — full staged BAVC reconstruction

The preceding turn was verified progress: the authoritative starting audit
passed 3276 build jobs and 9490 project declarations. This continuation expanded
Spec/BAVCReconstruction from the initial queue/branch fragment to all 32 lines
of the typed-input Algorithm-9 body. The physical-page-26 image was visually
reviewed again. No source corrections were selected.

The prefill loop keeps the post-dequeue length>=2 test and the printed strict
remaining-path upper-bound guard. It terminates by queue-address sum, updates
a partial tree, extracts exact lambda-bit prefixes only when present and checks
remaining padding. Explicit capacity/padding bottom returns are distinct from
undefined queue, zero/out-of-range address, short-path and node-read faults.
Partial node arrays have explicit empty cells; no default seed is fabricated.

Expansion preserves the source's separate names: tree is the prefilled array
used by the guard, while nodes is read and updated. An optional NodesBinding
exposes the missing declaration as an external environment value with no
correctness contract or aliasing rule. The literal reconstruct leaves it absent.
Safe parent/child addresses follow from the printed increasing range. Subsequent
length-indexed leaf/row loops retain interleaved reads, hidden digest order,
CommitSeed calls, both Hashbavc levels and salt serialization. The existing
typed Opening is the boundary; no raw opening decoder is claimed.

Proofs/BAVCPrefill establishes take/drop reassembly, exact complete-seed
consumption, legal queue/address safety and equivalence of the zero-padding
test. For every path at least Topen*lambda bits long, a successful full loop
leaves its entire tree and path unchanged: no extraction branch can be entered.
A successful prefill of an actual Algorithm-8 padded opening consequently has
an empty tree and all-zero remaining bits. This is a full-loop result, beyond
the earlier first-branch discrepancy.

Proofs/BAVCReconstruction proves that expansion cannot create an undeclared
binding, exact coordinate correspondence for successful leaf/row loops, the
origin of revealed seeds/commitments, hidden-seed absence and a complete
successful-output characterization in terms of the actual run equations.
With tau>0 and N>1, the unbound-nodes literal body cannot return; it rejects or
reaches an undefined read. A degenerate single-hidden-leaf example does return
without reading nodes, so the model diagnoses actual reads rather than globally
replacing the algorithm by failure. Padded successful reconstruction is also
characterized as reading exclusively from the external nodes binding, since
its empty prefill causes no expansion updates.

The Category-I 35-step successful Algorithm-8 opening now reaches an explicit
capacity rejection in the full reconstruction body, for all cipher/hash
primitives, salts and possible nodes bindings. This occurs before any missing
array read. Final.commitment_discrepancies was strengthened to that full-body
result while retaining exactly three final statements. It still does not
execute a signature or make a claim about a corrected reference implementation.

The specification entry point already imports the expanded reconstruction
module. Both proof modules are explicitly in the root and the stronger final
interface imports them. README, source/index and coverage/human-review ledgers
were updated with the exact boundary. Full validation passed: 3278 build jobs
and 9749 project declarations; only propext, Classical.choice and Quot.sound
occur in the transitive axiom audit. No custom axioms, proof placeholders,
unsafe/native shortcuts or silent source repairs were used.

The whole formalization remains incomplete and the goal remains active. This
was verified progress, not a blocked turn. The earlier source-policy question
remains unanswered. Whole BLC recomputation and challenge/serialization
integration, complete variant protocols and the missing correctness/security
reductions remain outstanding. Intended reconstruction correctness itself
requires source resolution and is not inferred from these literal-body results.


## Automatic continuation 19 — staged BLC recomputation

The authoritative starting audit passed 3278 build jobs and 9749 project
declarations. The active goal was confirmed while answering the user's progress
request. Lean MCP and Lean Search MCP remain unavailable in the exposed tool
inventory; compilation and local mathlib search continue through the CLI.
No sub-agents were used. The earlier source-policy question remains unanswered.

The physical-page-32 Algorithm-12 image was reviewed. Spec/BLCRecompute now
transcribes the prefix through line 20 and the independent suffix lines 22–27.
The prefix uses typed auxiliary/decomposition inputs and the existing challenge
expansion/raw-index encoding boundary. It preserves the initial header check,
then invokes the actual full BAVC reconstruction with an explicit nodes binding.
An error at that call yields no hcom/seeds pair; the prefix records an undefined
pair read with the original cause, not an invented Algorithm-12 rejection rule.

The separate seed, rshare and phi_mu names have explicit optional bindings with
no existence, initialization, alias or correctness contract. The literal prefix
supplies absent bindings. Line 10's reval zero remains separate from rshare.
Increasing leaf loops skip the hidden index before reading seed or sampling,
use actual PRG.SampleFieldElements binary values, and add the literal Gray
difference. Positive executions use the transmitted correction at slot e-1
and the supplied phi_mu. The outer execution loop and subsequent Q collection
preserve their source order. Hashaux, consistency expansion and [I|M]*Q are
constructed from those actual results.

The line-21 operands are held in a stopped ConsistencyBoundary state. The
extension-field scalar is not silently converted to a binary matrix or replaced
with a Gray-based challenge. This stopped state is not an Algorithm-12 return.
The suffix takes an explicitly supplied binary base matrix and computes the
printed witness/randomness slices and three-component Hashlines. Its concrete
hash uses actual SHAKE/domain 3; it does not append Algorithm 10's witness
correction. No supplied base is asserted to implement the undefined operation.

Proofs/BLCRecompute establishes seed-read correspondence, preservation of
missing shares, exact inner-loop sums from actual samples, the full correction
term including externally supplied initial shares/phi_mu, zero reval retention,
outer-loop and collection coordinates, and a complete prefix-success
characterization with real subroutine run equations. Reaching that state yields
the actual nonzero inverse header challenge. With absent bindings and tau>0,
N>1, the literal prefix cannot reach line 21. For the concrete Category-I
opening, every external binding yields the exact line-8 failure after a passing
header with that hidden vector. This does not assert that concrete challenge
expansion produces that vector or that a full signature has been executed.

The exact concrete commit/recompute hash-message difference is the encoded
witness correction; message inequality is proved under its explicit nonempty
encoding condition. No hash-output inequality or serializer law is assumed.
The new specification and proof modules are imported by the appropriate entry
points. Final.lean still contains exactly three statements. README, the source
inventory, coverage and human-review records have been updated. The full audit
passed with 3280 build jobs and 10012 project declarations. Only propext,
Classical.choice and Quot.sound occur in the transitive audit. No placeholders,
custom axioms, unsafe/native proof shortcuts or silent source corrections were
used. The final interface remains the same three statements.

Whole recomputation still requires resolving line 21, missing variable bindings
and raw/Gray challenge correspondence. Raw challenge/serialization integration,
complete variant protocols and whole correctness/security reductions also remain
open. This is verified progress, not a blocked turn or a completion claim.


## Automatic continuation 20 — full integer loop and concrete challenges

The previous turn was verified progress. The authoritative initial audit passed
3280 build jobs and 10012 project declarations. The physical-page-21/22 images
were reviewed for §3.2.2 challenge expansion and its conflicting cipher prose.
No source corrections were selected; the earlier source-policy question is
still unanswered. No sub-agents or Lean/Lean Search MCP tools were used.

Spec/IntegerSamplingVector now models the entire SampleIntegers vector loop
around the existing actual four-byte candidate reader. A partial prefix carries
its length bound and reader. Fuel counts observed attempts, with completed,
pending and undefined-assignment outcomes kept distinct. The literal wrapper
leaves B absent. A separate fixed natural-number binding has no relationship
asserted to v and is not a silent implementation of the intended correction.

The proofs show completion-prefix correspondence, stable returns and no literal
return for any nonempty request. For m=2^kappa, kappa<=32, the threshold equals
2^32, so every candidate from every stream is accepted. The missing assignment
is reached after the first four-byte read for any positive observation budget.
With an external fixed B, enough fuel instead returns the exact repeated residue
vector with 4*n bytes consumed. All source loop reads and output bounds remain
explicit. Small step helpers avoid expansion of large recursive proof terms;
they do not introduce an opaque sampler or a correctness assumption.

Spec/ConcreteChallenges replaces further primitive boundaries with actual
SHAKE, Enc* and Table-2 byte decoding. Hash evaluation initializes SHAKE on
hpiop followed by a supplied 32-bit counter encoding, executes the actual full
integer loop and samples grinding only after a returned integer vector. For
the fixed-B comparison, hidden indices are constant and grinding begins at
SHAKE bit 32*tau. Exact subsequent cursor and the zero-tau case are checked.
The literal nonempty subroutine cannot return, and every Tables-4/5 index range
reaches the missing assignment on its first read.

The cipher material stage reads the printed 4*lambda bytes. Its missing parser
is kept separate from the four lambda-bit windows needed by the established
input-preparation stage; their unequal total lengths are checked without
asserting that the source uniquely requires that parser. Actual Enc* calls
produce both ciphertexts and their XOR. Single-subscript Extract remains an
explicit gap. After supplied extraction output, a fresh SHAKE over
(hpiop, ctr, c0, c1) runs the actual integer loop regardless of whether grinding
is zero. Counter input separation is conditional on the supplied encoding's
injectivity and makes no claim about SHAKE output inequality.

The concrete batching function samples gamma then gamma-prime from actual
SHAKE, decodes in the submitted polynomial basis with explicit ByteOrder and
preserves both consumption counts. Exact coefficient-byte locations, disjoint
pack ranges and cursor are proved. No concrete hash distribution is identified
with the earlier uniform-byte or ideal-challenge experiments.

Both new specification/proof pairs are included in their corresponding entry
points. README, source/index, coverage and human-review ledgers were updated.
The full audit passed: 3284 build jobs and 10217 project declarations, using
only propext, Classical.choice and Quot.sound. No proof placeholders, custom
axioms, unsafe/native shortcuts or silent source corrections were used.
Final.lean remains exactly three statements. Whole caller integration, raw/Gray
encoding, codecs, source ambiguities, variant protocols and correctness/security
reductions remain unfinished. This is verified progress and the goal stays active.


## Automatic continuation 21 — challenge encodings and partial retry caller

The previous goal turn was verified progress. The authoritative starting audit
passed 3284 build jobs and 10217 project declarations. The active source policy
is still literal formulas with explicit gaps; the earlier clarification remains
unanswered. No sub-agents or unavailable Lean/Lean Search MCP tools were used.

Spec/ChallengeEncoding now names the binary and Gray row interpretations of
Algorithm-11/12 indices, both composed with the actual psi and Table-2 generator.
The binary map follows the displayed bin_kappa order. Neither interpretation
is silently selected as the source meaning. Proofs show binary-row injectivity,
Gray relabeling bijectivity, both concrete merge injections and the exact equality
condition: every index is 0 or 1. Inverse evaluation points have the same equality
condition. A constant index-2 vector separates nonzero points; both submitted
proof-parameter families satisfy the required range/basis bounds.

Both merges vanish exactly on the all-zero vector, so the existing BAVC retry
attempts and all finite observations agree under these two encodings for the
same challenge sequence. Their images are equal and have 2^(tau*kappa) elements
when the basis-size bound holds. Equal pushforward laws for explicitly uniform
index vectors follow from the finite relabeling. No pointwise equality follows
from that distribution statement, and no concrete SHAKE or adaptive-grinding
law is asserted. The actual source interpretation remains a human obligation.

Spec/PartialBLCRetry integrates the partial challenge observation at Algorithm
11 line 3. Pending inner sampling preserves the counter, and an undefined
assignment is never converted to a grinding retry. Only a returned challenge
reaches the actual existing BAVC opening/header/counter step. The recursive
outer observation preserves counter overflow and opening-error payloads.
The new loop is proved equal to the old total interface whenever expansion
returns at each counter. Every successful return has an actual returned
challenge, actual successful BAVC opening and passing header at the reported
counter; increasing outer fuel preserves it.

The hashOpen wrapper starts at counter zero and uses the concrete SHAKE/full
integer loop with B absent. It cannot return an opening for any nonempty
execution set. For kappa<=32, positive inner/outer observation budgets reach
the exact missing-B read at counter zero before BAVC.Open or a retry. This is
a literal-source undefined operation, not an invented signature rejection or
a claim that a corrected implementation behaves this way.

Both new specification/proof pairs are in their entry points. README, the source
inventory and coverage/human-review ledgers were updated. The full audit passed
3288 build jobs and 10366 project declarations, with only propext,
Classical.choice and Quot.sound. No placeholders, custom axioms, unsafe/native
shortcuts or silent source corrections were used. Final.lean remains three
statements. Whole signing/verification integration, cipher source gaps, codecs,
variant protocols and correctness/security reductions remain unfinished.
This continuation is verified progress and the whole goal remains active.

## Automatic continuation 22 — partial signing and verification callers

The starting full audit passed 3288 jobs and 10366 project declarations. The
whole-formalization goal remains active. The user requested current progress;
the verified scope and outstanding work were reported. The callable tool
inventory still contains neither Lean MCP nor Lean Search MCP. This continuation
uses the pinned Lean CLI and local sources, without sub-agents. Algorithms 3/4
were rechecked against the rendered PDF pages before composing their callers.

Spec/PartialSignature connects actual BLC/PIOP preparation to the partial retry
loop. Only a returned opening constructs the typed signature; outer pending,
inner pending, undefined expansion and opening/overflow faults remain distinct.
Proofs establish every returned signature's prepared fields, actual returned
challenge, successful BAVC opening and passing grinding/nonzero checks. Returns
are stable under increased outer fuel, and total returned expansion refines the
earlier total signing interface. The actual SHAKE/integer hash wrapper cannot
emit a signature for nonempty executions at any finite observation budget.
Positive inner/outer budgets with kappa<=32 expose missing B at counter zero.

The partial verifier calls expansion on the parsed signature's digest/counter.
Only returned expansion runs the existing staged Algorithm-12 prefix. Its
consistency-boundary characterization and nonzero delta follow from actual
prefix execution, while absent bindings cannot reach that boundary on nonempty
trees. Explicit header bottom becomes source Reject; BAVC errors remain
undefined tuple reads with their original cause. The actual hash caller cannot
reach the consistency boundary or an explicit rejection for nonempty execution
sets; positive integer fuel and kappa<=32 reach the exact first missing-B read.

The separately defined suffix executes Algorithm-12 lines 22–27 followed by the
actual detailed PIOP, coefficient recovery and final digest comparison. Its
acceptance equivalence is checked for an explicitly supplied base matrix. No
relationship to the ill-typed line 21 is inserted or assumed. Successful whole
signing/verification, raw codecs, the other primitive/source ambiguities,
variant protocols and correctness/security reductions remain unfinished.

The new specification/proof pair is included in the entry points. README,
source/index, coverage and human-review ledgers were updated. Final.lean remains
exactly three statements and Assumptions.lean gains no new assumptions. This
continuation made verified progress, not a repeated no-progress obstruction.

The twenty-second full validation passed: 3290 build jobs and 10511 project
declarations, with only propext, Classical.choice and Quot.sound in the
transitive axiom audit. No proof placeholders, custom axioms or unchecked
shortcuts were introduced. Whole-submission completion remains unproved;
the persistent goal stays active.


## Automatic continuation 23 — witness sampling and partial key generation

The previous turn made verified progress and passed the full audit: 3290 jobs,
10511 declarations and only the three allowlisted foundational axioms. The goal
remains active. Algorithms 1/2 were rechecked against rendered source pages.
The user requested progress during this turn; the latest verified checkpoint
and the still-running proof work were reported separately.

Spec/IntegerSamplingTrace retains finite sampler outcomes, values, cursors and
the offending integer while projecting away unconsumed infinite reader tails.
Its proof covers arbitrary ranges and rejection sequences, using only four
bytes per observation attempt. A successful finite Algorithm-6 output covering
that bound gives the same trace as the actual cipher stream. The initial large
proof hit kernel recursion limits. Splitting checked step lemmas and supplying
explicit state arguments resolved it without changing the statement, relaxing
the kernel check or changing the sampler.

Spec/PartialKeyGeneration composes actual integer sampling, Algorithm-1 witness
expansion, Algorithm-2 cipher-stream matrix, syndrome/key computation and the
supplied serializers. The two source bindings B and x_A remain separate and
absent in literal wrappers. Returned expansions have exact weight/length and
stable returns; returned keys expose actual sampled positions and the precise
existing SD condition for a supplied x_A. Finite PRG trace correspondence extends
through the actual witness suffix. The literal nonempty expander cannot return
at any finite fuel, including all Table-3 non-power-of-two ranges.

The independent seed draws now feed the actual partial key-generation PMF.
Returned typed keys and encoded pairs have zero mass in the literal wrappers,
because undefined source reads cannot manufacture a return. This is not a
security, rejection or corrected-implementation claim. Independent deterministic
expansion laws remain actual pushforwards without uniform output assumptions.

Both new specification/proof pairs are included in the entry points. README,
source/index and the coverage/human-review ledgers were updated. No changes were
made to the three final statements or the assumptions interface. PRG source
gaps, raw codecs, variants, source contradictions and complete correctness/
security remain unresolved. This continuation made verified progress.

The twenty-third full validation passed: 3294 build jobs and 10731 project
declarations. The transitive audit found only propext, Classical.choice and
Quot.sound. No proof placeholders, custom axioms or unchecked shortcuts were
introduced. Whole-submission completion is still unproved; the goal stays active.


## Automatic continuation 24 — scaled arithmetic and packing obligations

The intervening status turn inspected the latest audit and answered the user's
remaining-effort question without changing code; it was a no-progress status
checkpoint, not a verified wait. Resuming work found concrete available proof
tasks. Section 6.1 and Table 7 were rechecked against the local source. The
previous scaled-arithmetic specification draft was completed with delimited
uniform-challenge experiments. This continuation makes verified progress.

Spec/ScaledArithmetic keeps position and amplitude arrays separate, uses the
actual flat parsers, mask, unitary loops and post-mux multiplication, and composes
the actual Algorithm-21 batching. Mask degree and packing width remain separate
from tensor depth. There is no invented scalar/bit codec or nonzero constraint.
Proofs/ScaledArithmetic derives evaluation agreement, degree bounds, commutation
with batching and the exact constant-term identity. Raw-vector regularity holds
iff all amplitudes are nonzero. All-zero arrays produce the zero polynomial for
zero syndrome and arbitrary matrices/challenges, whereas positive chunk counts
make that raw vector nonregular. This is an arithmetic enforcement boundary,
not a full signature-verifier counterexample.

Proofs/ScaledArithmeticProbability proves exact 1/|F| cancellation when either
computed packed syndrome or unitary vector is nonzero, and probability one when
both vanish. The consistent-evaluation comparison experiment allows randomized
responses after both batching challenges and before a fresh evaluation point.
Its bound is 1/|F| + (1-1/|F|)*degree/|S|, with the prover degree and first-stage
law derived from the defined routines. Nonzero packing is not inferred from
an invalid regular witness, and SHAKE/grinding is not given this uniform law.

Proofs/ScaledPackingBoundary checks all Table-7 rows by cardinality: any injective
syndrome encoding needs at least four retained large-field elements. Reusing the
binary packing width gives one and is necessarily noninjective. The actual
linear packing formula has a nonzero kernel vector annihilated by every batching
challenge. The outline does not uniquely specify that reuse, so this identifies
a necessary source-completion obligation rather than claiming a full attack.

The specification and three proof modules are included in the entry points.
README, source/index, coverage and human-review ledgers record their actual scope.
Final.lean still has exactly three statements; Assumptions.lean is unchanged.
Full variant bodies, scalar codecs/embeddings, nonzero enforcement, the existing
source discrepancies and complete correctness/security remain unfinished.

The twenty-fourth full validation passed: 3298 build jobs and 10791 project
declarations. Every transitive axiom is one of propext, Classical.choice and
Quot.sound. No proof placeholders, custom axioms or unchecked shortcuts were
introduced. The source index still records all 21 numbered algorithms. This
audit verifies the current development, not whole-submission completion; the
persistent goal remains active.


## Automatic continuation 25 — cipher expansion and caller integration

The previous continuation made verified progress and passed the full audit
(3298 jobs, 10791 declarations). This turn rechecked printed p. 19 against the
rendered PDF and completed the staged cipher-based challenge path and callers.
There is meaningful progress; the whole-submission goal remains active.

Spec/CipherEvaluation composes the actual SHAKE material read, supplied optional
material parse, optional MapToBits, actual prepared Enc* calls, optional Extract
applied to their xor, fresh final SHAKE and complete integer loop. The three
interpretation boundaries keep their distinct payloads. They are not operational
rejections or assumed implementations. The undefined integer B stays a separate
optional fixed value. The literal wrapper supplies none of these interpretations.

Its proofs give exact return provenance through the actual integer sample,
return stability under additional integer fuel, each preceding source boundary,
the missing-B obstruction for nonempty requests, and the first missing assignment
on the actual fresh final SHAKE stream when kappa<=32. A supplied fixed B gives
the previously established constant-residue result, with actual extracted xor
bits and exact cursor; it is not asserted to implement a uniform sampler.

Spec/CipherBLCRetry composes expansion with the actual Algorithm-11 BAVC/retry
body, preserving a source boundary at its current counter. Refinement to the
earlier partial retry, genuine expansion/opening/header provenance and return
stability are proved. The literal caller stops at the first material parse.
Supplying the preceding interpretations but no B still cannot yield a returned
opening and, for submitted-sized nonempty requests and positive budgets, exposes
the exact missing assignment at counter zero before any BAVC call.

Spec/CipherSignature connects the existing BLC/PIOP prepared records to cipher
opening and carries the parsed signature's digest/transmitted counter into the
partial verifier. Proofs establish returned-signature provenance/stability and
exact expansion/BLC provenance for the consistency boundary and explicit header
Reject. An unresolved cipher stage is neither outcome. Missing B prevents
nonempty signing and verifier boundary/rejection even when preceding cipher
interpretations are supplied. The independent Algorithm-12 line-21 boundary and
supplied-base suffix remain unchanged; no prefix acceptance is invented.

All three specification/proof pairs are in the project entry points. README,
source/index and both review ledgers distinguish these results from completed
source interpretation or scheme correctness/security. All 21 numbered algorithms
remain indexed, and every indexed Lean file exists. Final.lean still has only
three statements; Assumptions.lean has no changes or additional hypotheses.

The twenty-fifth full validation passed: 3304 build jobs and 10924 project
declarations, with only propext, Classical.choice and Quot.sound in the
transitive axiom audit. No proof placeholders, custom axioms or unchecked
shortcuts were introduced. Whole-submission completion is still unproved;
the persistent goal stays active.


## Automatic continuation 26 — key capacity, full parameter tables and plan

Algorithms 2–4 and the key-size prose were inspected for raw codec details.
They name Serialize/Deserialize and order fields but do not specify a complete
byte encoding or padding policy. No codec was invented. KeySizeBoundary instead
uses the existing typed key spaces, including a fixed witness-length subtype,
and proves their exact cardinalities and necessary capacity for an explicitly
injective fixed-length encoding. The predicates are theorem hypotheses, not
assumptions about the source serializers. The submitted Category-III secret-key
allocation has four spare bits whose interpretation remains unresolved.

Rendered printed pages 39–41 were checked. MainParameterTables transcribes the
full Table-4/5 rows and proves every key/signature size formula, correspondence
with existing proof-parameter lists and the degree-four numerical budgets. The
parameter-selection prose is separately represented; its tree-size and grinding
values disagree with Table 4. Neither passage is silently repaired.

ReportedBenchmarks isolates Table 6's displayed cycle medians, run count and
processor as reported data. Only row-label correspondence to Tables 4/5 is
proved. Empirical validation, runtime interpretation and implementation
correspondence remain human obligations; the reports are not new axioms.

The two specification/proof pairs and reported-data specification are included
in the entry points. Source index, README and both review ledgers record their
limited scope. Final.lean retains exactly three statements and Assumptions.lean
is unchanged. Raw codecs, source resolutions, variant protocols, reduction
obligations and full correctness/security remain unfinished.

The user asked what remains and then requested a plan file showing completed
and remaining items. Root PLAN.md records the checked components, remaining
workstreams and dependencies, human/source decisions and completion gates, with
links to the detailed evidence. README links to it. It must be maintained as
work proceeds; checkbox counts are not a measured completion percentage.

The twenty-sixth full validation passed: 3309 build jobs and 11088 project
declarations, with only propext, Classical.choice and Quot.sound in the
transitive axiom audit. No proof placeholders, custom axioms or unchecked
shortcuts were introduced. This continuation made verified progress. The
whole-submission goal remains incomplete and active.

## Automatic continuation 27 — density and actual SD reduction probabilities

The previous goal turn created the requested plan and recorded verified work;
it was progress, not a verified wait. This continuation inspected the worktree,
local source and rendered printed page 38, then completed ParameterSelection.
It keeps both literal integer floor formulas, derives density as average fiber
size and proves the exact logarithmic/ceiling target and byte-alignment optimum
with feasibility hypotheses. Concrete SD-floor and RSD-theta-sign examples
refute the printed density claims without changing the specification.

The user correctly challenged the emphasis on infrastructure and supporting
components. I acknowledged that the main EUF-CMA proof is still largely absent
and that declaration/build counts are not completion metrics. Work then moved
to the actual §5.1 reduction probability experiment. SDReductionGame samples the
explicit input law and permutation, calls the real solver input and maps the
actual finish function. Its output equals the existing randomized reduction.
For solvable inputs, the full-regularity event is lower-bounded by the exact
combinatorial factor. A success bound follows with actual conditional return
and uniqueness probabilities, with no invented success or heuristic assumption.

SDReductionConditioning constructs a correct selective solver returning only
for zero matrix/syndrome. Under the explicit planted-uniform binary input law,
the returned event has positive mass. Two distinct regular witnesses ensure
that conditional uniqueness is zero, both under return alone and under return
plus full regularity. Parameters n=4,w=2,k_sd=k_rsd=1,theta=2 satisfy the source
inequality and density 1/2. The positive exponential heuristic cannot be a
universal conditional lower bound. This is an intermediate-step refutation;
it does not refute the final existential Theorem 5.1, and no runtime statement
is made. In this example no rows are removed and reduction return succeeds.

The user asked about abstract versus concrete algorithms. I explained that
both exist but the prior work favors concrete representation; a complete
abstract signature-security proof and proved concrete correspondence remain
missing. The user then correctly emphasized that SD-to-RSD is still not the
signature-security reduction. PLAN.md now makes the signature oracle/forgery
experiment and actual simulation/extraction argument the immediate priority.
A game definition, a supplied extractor, or more SD-to-RSD lemmas must not be
reported as completing that reduction. The entire scope remains unchanged.

The five new modules are in the specification/proof entry points; source index,
README, PLAN and review/coverage ledgers distinguish their exact scope. The three
final statements and Assumptions.lean are unchanged. The twenty-seventh full
validation passed: 3316 build jobs and 11204 project declarations, with only
propext, Classical.choice and Quot.sound transitively. No proof placeholders,
custom axioms or unchecked shortcuts were introduced. This is verified progress
on components, not completion of signature security. The goal remains active.

## Automatic continuation 28 — first abstract signature-game reduction step

Continuation 27 made verified component progress and passed the full audit;
it was not a wait or an impasse. This turn followed the user's explicit emphasis
on signature security and inspected the actual signing/verification interfaces,
source §5.3 and current proof boundaries before editing. No more density or
SD-to-RSD work was substituted for the signature reduction.

Spec/SignatureSecurity defines a bounded adaptive chosen-message game. The
adversary gets the public key and its own state, requests signatures or public
oracle answers, and eventually supplies a message/signature. All signing requests
are logged. Finalization compares the actual lazy HashPiop answer with the
claimed digest and requires a message absent from that log. Exhaustion, abort
and verification rejection remain distinct. Fuel is an action budget, not runtime
or a bound on honest internal calls. The partial literal source is not silently
instantiated as these complete abstract services.

Spec/RandomOracle now owns the unchanged lazy query definition re-exported by
Assumptions.randomOracleQuery. Proofs/SignatureSecurity derives the fresh-input
1/|Digest| guessing probability, its bound under any adaptive terminal law,
winning-event decomposition and the resulting table-present-plus-guess bound.
No commitment, simulation or extraction hypothesis is used.

Spec/AbstractSignature makes the message-bound prepare/hash/open signing order
explicit. It initializes an empty HashPiop table and retains the public key in
the signing key; other components operate only on their separate Other state.
Proofs/AbstractSignature derives the lazy-update origin lemma and its invariant
through all adaptive actions. Each stored input came from an adversarial hash
query or a signing request for its message. A fresh winning message excludes
the latter. The proved first signature-game reduction is forgery probability
at most the prior-adversarial-query winning event plus 1/|Digest|. A previous
query is not an extracted RSD witness and is not reported as one.

Spec/SignatureHashGame gives exact typed record equivalences to the existing
HashInput and Signature and constructs the terminal input from the actual
verificationInput (including PIOP evaluation and coefficient recovery).
Proofs/SignatureHashGame proves resolved final-test correspondence with
verifyPostRecompute, message separation from logged signing inputs, and the
source-shaped specialization with guessing term 2^(-2*lambda). The full Scheme
components, bytes/domain correspondence and unresolved recomputation/dimensions
remain open. Typed equivalences do not establish an executable implementation
or repair source contradictions.

The seven new modules are in the entry points. Source index, README, PLAN and
audit ledgers record this first signature step and its limits. Assumptions has
only the shared-definition refactor and updated scope comments; no new assumption
or axiom was introduced. Final.lean retains exactly three discrepancy statements.
Replay/forking, faithful signing simulation, commitment consistency, RSD extraction,
full cost accounting and complete concrete correspondence remain the priority.

The twenty-eighth full validation passed: 3323 build jobs and 11538 project
declarations. Every transitive axiom is propext, Classical.choice or Quot.sound.
No proof placeholders, custom axioms or unchecked shortcuts were introduced.
The goal remains incomplete and active; this is the first checked signature-game
reduction step, not an end-to-end EUF-CMA theorem.

## Continuation 29 — actual signature replay and quantitative fork bound

Continued the signature-security priority. Spec/SignatureReplay defines a cut
before the indexed adversarial hash answer, retaining early termination and
all signing/public-oracle actions. The snapshot stores the remaining action
fuel, keys, world, logs, input and continuation. Proofs/SignatureReplay proves
ordinary resumption equals the actual run, terminal law and full finalized
experiment. No behavior of the adversary or supplied services is assumed.

At a fresh cut, freshBranch samples one uniform answer and runs the remaining
game with that entry fixed. Its checked-result marginal equals ordinary
resumption and its answer marginal is uniform. forkAt uses two independent
continuations from the saved state and refuses nonfresh cuts. The success event
requires both to win at the selected input with distinct answers.

Proofs/SignatureFork proves independent-success multiplication, the uniform
answer collision upper bound and the resulting epsilon^2 <= fork +
epsilon/|Digest| inequality. A PMF weighted-square proof handles arbitrary
state spaces and yields the same bound after averaging over the actual random
prefix. Ended and nonfresh cuts have zero selected-input success. There is no
uniformity assumption conditional on winning and no finite-state restriction.

Proofs/SignatureReplayConsistency proves that previously stored answers persist
through actual lazy queries, signing, the full adaptive run and verification
preparation. A successful branch's tested target equals its sampled answer.
Thus the actual fork yields two accepted fresh-message attempts at one typed
hash input with distinct tested digests. Different digests are not asserted to
give useful distinct algebraic challenges or an RSD witness.

The critical remaining probability link is useful-query selection: relating
the selected-input epsilon to overall prior-query forgery mass. The replay
experiment also still has the honest signing secret; signing simulation must
remove this dependence with proved distribution and cost bounds. Commitment
security, challenge separation, extraction, concrete correspondence and the
end-to-end EUF-CMA theorem remain open. No desired security contract or new
assumption was added, and Final.lean still has exactly three discrepancy
statements. The four new modules are indexed and imported; README, PLAN and
human-review/coverage ledgers record these boundaries.

The twenty-ninth full validation passed: 3327 build jobs and 11719 project
declarations. The only transitive axioms are propext, Classical.choice and
Quot.sound. Source-index paths, standalone specification import separation and
the three final statements were checked. No proof placeholders or unchecked
shortcuts were introduced. The end-to-end signature-security proof and whole
formalization remain incomplete, and the persistent goal remains active.

## Continuation 30 — useful-query selection and forgery-to-replay probability

The previous continuation made concrete progress (exact replay, quantitative
fork bounds and answer consistency), verified by the current authoritative
validation log. Continued directly with the missing probability link, without
substituting primitive or SD-to-RSD work for signature security.

Spec/SignatureQuerySelection instruments the actual game with a chronological
request log containing each input's freshness immediately before its query.
The adversary does not see this instrumentation. Proofs/SignatureQuerySelection
proves exact original terminal and finalized marginals, the action-budget
request-count bound, and equality of each marked-index law with the defined
cut/resume single-success experiment.

Proofs/SignatureQueryProvenance proves signing-log monotonicity and typed
verification-message correspondence. Every final stored input came from the
initial table, a genuinely fresh adversarial request, or a logged signing
message. Key generation starts an empty table and winning-message freshness
excludes the signing origin. Thus every table-present winner has an eligible
fresh target request at an index below the action budget. Repeated queries
remain in the log and are not silently resampled or marked fresh.

The explicit random-index experiment samples Fin(fuel+1) uniformly before
executing fuel+1 actions. Proofs/SignatureForgeryFork derives the event-cover
bound and exact index averaging. With e=forgery, s=selected target success,
F=distinct-answer replay success, q=fuel+1 and delta=1/|Digest|, it proves
e <= q*s+delta and s^2 <= F+s*delta, hence max(e-delta,0)^2 <= q^2*(F+delta).
SignatureHashGame specializes delta to 2^(-2*lambda) for the source typed record
shapes. This action-budget loss is explicit and is not claimed to be optimal or
to be a theorem stated numerically in the submission.

The four new modules are imported/indexed; specification, assumption and proof
boundaries remain separate. Assumptions and the three final discrepancy
statements are unchanged. The replay still executes honest signing with its
secret. Next are commitment/challenge consistency, usable transcript separation
and RSD extraction, with faithful signing simulation and costs also required.
No extractor/simulator success contract or cryptographic axiom was added.

The thirtieth full validation passed: 3331 build jobs and 11866 project
declarations. All transitive axioms remain propext, Classical.choice and
Quot.sound. Source-index paths, standalone specification imports and the three
final statements were also checked. There are no proof placeholders or
unchecked shortcuts. The full signature-security reduction and complete
formalization remain unfinished; the persistent goal remains active.

## Continuation 31 — commitment collision reductions from actual source code

Classified the previous continuation as progress and checked its authoritative
full audit (3331 build jobs, 11866 declarations). Continued with the commitment
consistency needed after forgery replay, inspecting actual Algorithms 7/9/10/12
and their cipher/hash call layouts. No desired binding property was assumed.

Spec/Proofs.BAVCBinding implement a computable collision finder on exact outer
and row query strings, including the domain byte, salt and ordered arrays.
Fixed-width serialization injectivity is proved. Under equal roots, a returned
pair is an actual hash collision with one query from each computation's list;
none implies equal salts and complete leaf-commitment arrays. Each hash-query
list has tau+1 entries; this is not a total runtime or cipher-query cost claim.

Spec.BAVCBinding instruments the exact reconstruction to retain its intermediate
rows and runs the finder after the two actual computations. The proof module
BAVCBindingReconstruction establishes exact refinement, including all errors,
and derives leaf commitments from successful revealed-seed computations.
Inconsistent seeds at a commonly revealed position with a common root yield
a computed hash collision or a same-index seed-commitment collision. The latter
is equivalent to equality of both Enc* outputs; existing tweak bounds give
distinct plaintexts under distinct seed keys. This includes the correct limited
meaning for Category III (truncated outputs, not full permutation outputs).

Spec/Proofs.BLCBinding follow the verifier's concrete Hashlines/Hashaux chain.
They recover only the leading fixed-width digests, without inventing serializer
injectivity for the remaining fields. Equal suffix line digests give equal BAVC
roots or collisions on the exact line/aux query pairs. The auxiliary equations
are derived from actual successful prepareWithBindings calls, and a combined
two-prefix theorem discharges them. The supplied base matrix stays an explicit
source boundary, not an implementation of the ill-typed line 21.

All five modules are imported/indexed. README, PLAN, coverage and human-review
ledgers distinguish deterministic collision reductions from probabilistic
binding/security. Adaptive ROM/ICM bounds, full binding, challenge separation,
RSD extraction and signing simulation remain unfinished. The separate folding
seed array is not silently aliased to reconstruction output; no source guard,
missing binding or Hashlines payload is repaired. Assumptions and the three
Final discrepancy statements are unchanged.

The thirty-first full validation passed: 3336 build jobs and 11925 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
All 21 numbered source algorithms, indexed paths, standalone specification
imports and the three final statements were checked. No proof placeholders,
new assumptions or unchecked shortcuts were introduced. Full security and
whole-submission formalization remain incomplete; the persistent goal is active.

## Continuation 32 — adaptive collision probability for queried BAVC hash views

Continued the hash-collision probability step needed by the signature binding
argument. The end-to-end signature reduction remains incomplete: the honest-key
replay is not a witness-free SD solver, and no simulator or extractor contract
has been substituted for a proof.

Spec/RandomOracleCollision defines adaptive stop/query procedures on the same
lazy oracle used by the signature model. A private log records all requests,
including repeats; a flag records fresh answers matching earlier output values.
Proofs/RandomOracleCollision derives choose(q,2)/|Output| by induction on this
actual execution. The existing finite Boolean union bound was moved unchanged
to ChallengeMixtures; its original SignatureForgeryFork name delegates to it.
No independence of adversarial query choices is assumed.

Proofs/RandomOracleCollisionInvariant derives table/log correspondence and
preservation of collision freedom when no flag occurs. Every distinct stored
pair with a common answer therefore triggers the flag. Even arbitrary final
selectors inspecting the complete result obey the same birthday bound. This
does not include unqueried guesses.

Spec/Proofs.BAVCBindingROM totalize the final table for the exact row/outer
Hashbavc computations and check that all required entries exist. Equal roots
with different salt/leaf-commitment data make the existing computable finder
return a genuine stored collision. The fully queried binding experiment has
probability at most choose(q,2)/2^(2*lambda), with q counting every shared-oracle
call. Successful claims never depend on a default for a missing lookup.

This is a limited binding experiment. Full source executions must still be
embedded and all honest internal calls counted; the coverage checks here cannot
be added to the source verifier to throw away forgeries. Seed/cipher collisions,
Category-III truncation, full BLC binding, challenge separation, RSD extraction
and signing simulation remain unfinished. All five modules are imported/indexed;
standalone specification/assumption separation and the three final discrepancy
statements are retained.

The thirty-second full validation passed on 2026-10-04: 3341 build jobs and
12063 project declarations. All transitive axioms are propext, Classical.choice
or Quot.sound. No proof placeholders, cryptographic axioms or unchecked
shortcuts were added. The full signature-security reduction remains unproved;
the persistent goal is still active.

## Continuation 33 — execute and count the BAVC verification hash queries

The previous turn made verified progress (3341 build jobs, 12063 declarations).
Inspected the current files and audit, then worked on the remaining query-coverage
gap in the hash-binding component. Rechecked Algorithm 7 lines 8–9 and Algorithm 9
lines 30–31 against the pinned local source. The missing end-to-end EUF-CMA proof
in section 5.3 remains a proof task, not a newly permitted assumption.

Spec/Proofs.OracleProgram implement finite adaptive query syntax, bind and ordered
array traversal. Bounded programs finish under the existing lazy-oracle runner.
An inductive evaluation relation is derived from actual supported executions,
including stored-answer persistence; it is not an assumed program contract.

Spec/Proofs.RandomOraclePipeline compose an adaptive first phase and a state-
dependent second phase against the same table and complete history. The initial
history length is bounded by q; the second phase's collision estimate includes
matches against this history. Combining both flags gives choose(q+k,2)/|Output|.
The table/log and collision-detection invariants hold across the composition.

Spec/Proofs.BAVCHashVerification execute the two exact row/outer query layouts
after adaptive selection of salt/leaf-commitment data. The proof derives a
2*(tau+1) query budget, completion on every supported execution, complete query
coverage, and equality of returned roots with the source hash equations. Its
event tests equal roots for different data; it has no already-queried condition.
The existing actual collision finder gives a binding probability bounded by
choose(q+2*(tau+1),2)/2^(2*lambda), including verification's previously missing
queries and repetitions. The success event's unfinished branch is unreachable.

All six modules are imported/indexed, and the plan and review boundary distinguish
this completed hash-component coverage proof from the remaining full signature
composition. Cipher/seed binding, Category-III truncation, BLC source gaps, XOF
correspondence, challenge separation, extraction and signing simulation remain
unfinished. No extra cryptographic assumption, source repair or success contract
was added. Assumptions and the three Final statements remain unchanged.

The thirty-third full validation passed: 3347 build jobs and 12199 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked 252 indexed Lean paths, all six new module imports, specification import
separation, and exactly three final statements. No proof placeholders or unchecked
shortcuts were added. Full signature security and the entire formalization remain
incomplete; the persistent goal remains active.

## Continuation 34 — adaptive ICM equivalence and conditional fresh-query laws

Classified the previous turn as verified progress and inspected its authoritative
audit (3347 jobs, 12199 declarations). Continued with the seed/cipher side of
the reconstruction collision reduction. Rechecked Table 1 and Category-III
padding/truncation on printed page 15, seed routines on pages 18/21, and the
ICM statement on page 44 of the pinned submission.

Spec/IdealCipher defines both one-family execution and posterior sampling from
compatible keyed permutations, with encrypt/decrypt actions sharing the same
graph. World.possible is a constructed nonempty-sample-space invariant. The
FinitePosterior counting identity and IdealCipher proof establish exact adaptive
equivalence, including randomized procedures, changing keys, repeats and inverse
queries. The resulting law is linked to Assumptions.idealCipherFamily, without
assuming conditional independence. Recorded answers and transcript lengths are
derived from actual execution in IdealCipherTrace.

UniformSymmetry constructs uniform images from transposition equivalences.
IdealCipherFresh swaps unused ciphertexts while preserving every observation to
derive fresh encryption's uniform unused-range law. IdealCipherInverse reverses
the same families and histories for the corresponding decryption law. Capacity
counting gives at least M-q unused points and the conditional target bound
1/(M-q), including all history entries rather than only calls at the current key.

Spec/Proofs.IdealCipherSeed implement the source Category-III padding and answer
projection while retaining the full cipher observation privately. The projection
equals the existing encStarIII body. Its fiber injects into 64 residual bits,
giving the bound 2^64/(2^256-q) for a fresh chosen 192-bit target. The final
cardinality lemma is representation-independent, avoiding evaluation of the
huge finite block enumeration; no computation-trust shortcut is used.

All ten modules are imported/indexed. The assumptions' cryptographic definitions
and Final's three statements are unchanged; only the ICM model-link comment is
updated. These results do not yet bound the complete two-call seed-collision
event: its adaptive graph constraints, prior calls, source tweaks and additional
verification queries remain to be composed. BLC/source gaps, full signature
composition, extraction and signing simulation remain open.

The thirty-fourth full validation passed: 3357 build jobs and 12467 project
declarations. All transitive axioms remain propext, Classical.choice or Quot.sound.
Checked 262 indexed Lean paths, all ten new imports, standalone specification
separation and exactly three final statements. No cryptographic axiom, proof
placeholder or unchecked shortcut was introduced. Full seed binding and the
signature-security reduction remain unproved; the persistent goal is active.

## Continuation 35 — adaptive paired-cipher collision reduction

The preceding user-facing status turn made no new proof progress. Revalidated
continuation 34's checked state and resumed the signature seed-binding component;
there is no repeated external blocker. Rechecked the source CommitSeed formula
on printed page 21 against its indexed two-call representation.

Added ten imported/indexed modules. SeedPairing proves that the two source
plaintexts differ by a fixed lowest-bit flip, that the flip has no fixed points
and is involutive, and that Category-III padding commutes with it. IdealCipherJoint
strengthens posterior equivalence to retain the full hidden-family/transcript
joint law, without providing that family to the procedure. IdealCipherComparison
uses an auxiliary other-key exposure to bound projected comparison when either
side is unobserved.

IdealCipherPairCollision proves the first-matching-pair decomposition on actual
consistent graphs: a newly witnessed half has an unobserved companion, or a
companion pair already witnessed the collision. Repeated observations cannot
create a first witness. IdealCipherPairProbability derives the two conditional
factors for arbitrary forward/inverse requests, with freshness checked as part
of the event rather than assumed of the adversary. IdealCipherPairAdaptive
composes the local bound over all earlier entries and adaptive query positions.
The result, for projection fibers at most C and full block cardinality M, is
choose(q,2)*C/(M-q)*C/(M-q-2). It is stated both via the joint posterior interpreter
and directly against one initially sampled cipher family. The useful finite
form requires q+2<M; no optimal-loss or machine-runtime claim is made.

SeedPairBinding instantiates full-output and Category-III bounds with checked
capacities 1 and 2^64. Its source collision-to-event lemmas use the exact
commitSeed equality theorem and padded-key injectivity. They currently require
the two left-half graph entries to be present. Deriving that coverage by executing
both complete chosen commitments and counting their four calls is the next task;
no success guard or assumed freshness replaces it. Full source BLC/signature
composition, extraction and signing simulation remain unfinished. Assumptions'
definitions and the three-statement Final interface are unchanged.

The thirty-fifth full validation passed: 3367 build jobs and 12550 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked all ten new imports/index entries, 194 distinct indexed Lean paths,
standalone specification separation and exactly three final statements. No
proof placeholder, cryptographic axiom or unchecked shortcut was introduced.
The full signature reduction remains incomplete and the persistent goal is active.

## Continuation 36 — fully queried source seed binding

Classified continuation 35 as progress and revalidated its authoritative audit:
3367 jobs, 12550 declarations. Continued its explicit missing coverage obligation
by executing both selected commitments on the adversary's shared cipher.

Added seven imported/indexed modules. IdealCipherPipeline defines sequential
adaptive phases sharing the same sampled family; even early stopping starts the
second phase. Exact posterior/fixed-family equivalence and the paired-collision
bound with q+k total queries are proved. IdealCipherProgram gives an actual
interpreter for finite programs and proves exact completion under a proved bound.

SeedVerification executes the literal two explicit inputs under each selected
seed key, with exactly four recorded calls. Completion, output values and the
entire appended graph are derived, including for repeated queries. Winning
runs yield the paired collision event with all required entries present. Its
binding bound therefore uses q+4 and requires no freshness or prior-query premise.

SourceSeedVerification proves that returned pairs concatenate to CommitSeed,
and that the success event is exactly distinct source seeds with equal
commitments at the selected common salt/index. It discharges the structural
companion and capacity premises for full outputs and padded/truncated Category
III. Both operational experiments are proved equal to direct source collision
experiments containing no completion, coverage or freshness guard. Their bound
is choose(q+4,2)*C/(M-(q+4))*C/(M-(q+6)); q+6<M gives the useful finite form.
The source's Category-III routine-scope correspondence remains documented.

A shared generic sampling definition avoids comparing concrete enumerations
of the enormous permutation spaces during elaboration. No recursion/heartbeat
limits or trust settings were changed to obtain these proofs. The source and
assumption definitions retain their meaning; only the old Assumptions comment
about unfinished seed probabilities was updated. Final remains unchanged.

The thirty-sixth full validation passed: 3374 build jobs and 12717 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked 279 indexed Lean path references (201 distinct), all seven new imports,
standalone specification imports and three final statements. No proof placeholder,
cryptographic axiom or unchecked shortcut was introduced. Full joint hash/cipher,
seed-tree/reconstruction, BLC/signature and replay cost composition remain open,
as do usable challenge separation, RSD extraction and signing simulation. The
persistent goal remains active.

## Continuation 37 — shared hash/cipher collision reduction

Classified continuation 36 as progress and revalidated its full audit: 3374 jobs,
12717 declarations. Continued the recorded joint-game composition gap rather
than treating the separate hash and seed bounds as a bound for one adversary.

Added nine imported/indexed modules. Spec/HashCipher executes adaptive hash and
forward/inverse cipher requests using one lazy table and one sampled family.
Proofs/HashCipher proves exact joint posterior/fixed-family equivalence and its
standalone ICM model link. HashCipherHash derives hash table/log correspondence,
stored-collision flag coverage, cipher graph consistency and total query length.
The hash birthday bound holds for every fixed family and then its mixture.
HashCipherPair carries the paired-cipher bound through both request branches.
HashCipherSecurity gives choose(q,2)*(1/|Digest|+C/(M-q)*C/(M-q-2)) for the combined
bad event of this same execution, plus an explicit coverage-to-bound transfer
lemma. The probability laws follow the explicitly defined joint model; no extra
conditional-independence or desired-security premise substitutes for a proof.

HashCipherParameters specializes the widths and capacities for full outputs
and Category III. q counts mixed query/action fuel; the bound is conservative
for each service and does not count complete signature services or machine time.
The useful finite cipher denominator requires q+2<M. No concrete SHAKE/AES/
Rijndael security conclusion follows from these ideal-model probability laws.

Spec/Proofs.HashCipherProgram give mixed finite programs, additive budget
composition, completion, and exact operational lifts of the existing hash/cipher
programs. HashCipherSourcePrograms preserves the source seed check's four-call
trace and gives its paired-collision witness, and preserves both complete BAVC
row/outer hash computations with their actual stored-collision coverage. These
source components do not yet comprise full tree expansion/reconstruction or
complete honest signature services; the next step is their sequential execution
after a mixed adversary and full source query accounting.

Targeted builds passed. An initial full validation passed (3383 jobs, 12969
declarations). During review,
the joint sampling choice was also re-exported as Assumptions.sharedOracleModel,
with an explicit note that uniform marginals do not imply this joint law and
no concrete primitive correspondence is asserted. Earlier model definitions
and Final are unchanged.

The final thirty-seventh full validation passed after this boundary addition:
3383 build jobs and 12971 project declarations, with only propext,
Classical.choice and Quot.sound transitively. Checked 289 indexed Lean path
references (211 distinct), all nine new imports, standalone specification
separation and exactly three final statements. No proof placeholder,
cryptographic axiom or unchecked shortcut was introduced.

This is supporting collision analysis, not a completed signature-security
reduction. The existing forgery-to-fork step still uses the honest signing
secret; no RSD solver is extracted from its accepted forks. Extraction, signing
simulation, usable challenge consistency and end-to-end EUF-CMA remain unproved.
Source errors and human boundaries remain explicit. The persistent goal remains
active and incomplete.

## Continuation 38 — mixed verification and actual reconstruction cipher calls

The preceding user-facing status turn updated audit metadata and clarified scope
but made no new proof progress; classified it as no progress toward the security
proof. Revalidated the completed continuation-37 audit (3383 jobs, 12971
declarations), then proceeded with the recorded composition task. No external
blocker or verified wait prevented progress.

Added eight imported/indexed modules. Spec/Proofs.HashCipherPipeline implements
two adaptive phases sharing one family, table and both histories. Stopping or
exhausting the first phase still starts the second. Earlier hash collisions are
retained by OR with the second flag. Exact posterior/fixed-family equivalence,
extension of Assumptions.sharedOracleModel, graph invariants, stored-collision
coverage and total query lengths are proved. HashCipherPipelineSecurity proves
the paired-cipher bound and combined bound with q+k total mixed actions; both
include comparisons against the earlier phase's history.

Spec/Proofs.HashCipherVerification executes the existing source seed and BAVC
two-root checks after an arbitrary mixed adversary. Completion, exact values and
actual collision coverage are derived. HashCipherSourceSeedVerification proves
the exact direct source seed-collision law and bounds for full and Category-III
outputs. The seed bound includes q+4 calls; the root-hash bound includes
q+2*(tau+1). No membership, freshness or completion guard filters the source
collision event. The generic event-transfer coverage premise is discharged for
these component programs, not assumed for complete reconstruction/signatures.

Spec/Proofs.BAVCCipherProgram executes the actual Algorithm-9 cipher operations:
internal-node expansion, revealed-leaf CommitSeed calls and the leaf/row loops.
Full and Category-III Layout values are concrete conversions with exact Enc*
equations, not correctness/security interfaces. Exact returned values equal the
existing staged reconstructionRows, including every error and for any initial
cipher history. The derived bound is 2*(tau*N-1)+2*N*tau. run_shared executes the
program in the mixed interpreter with the exact value and cipher graph while
preserving the hash table/log. The source's literal prefill, separate tree/nodes
bindings, guards and missing-read errors are unchanged.

Rechecked Algorithm 9 in the pinned text (physical page 26, printed page 24).
Line 30 hashes each row before the next row's cipher calls. The new program is
explicitly the cipher projection, not a complete operational reconstruction.
Next insert those hashes in source order and the final outer hash, compose both
selected reconstructions after the mixed adversary, and derive the collision
finder's actual coverage and total cost. Do not silently reorder the row hashes.
Signature/replay costs, usable challenge separation, RSD extraction, secret-free
signing simulation and end-to-end EUF-CMA remain open. Source boundaries are not
repaired, and no further SD-to-RSD detour replaces the signature work.

Targeted builds and the thirty-eighth full validation passed: 3391 build jobs
and 13158 project declarations, with only propext, Classical.choice and Quot.sound
transitively. Checked 297 indexed Lean references (219 distinct paths), all eight
new imports/index entries, standalone specification separation and exactly three
final discrepancy statements. No placeholder, cryptographic axiom, increased
resource/trust setting or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The full goal remains active and incomplete.

## Continuation 39 — ordered reconstruction and derived disagreement probability

Classified continuation 38 as progress and revalidated its completed audit:
3391 jobs and 13158 declarations. Continued the remaining source-order and
reconstruction-coverage obligations, rather than treating the earlier cipher
projection as a complete Algorithm-9 execution.

Added eight imported/indexed modules. Spec/Proofs.HashCipherEvaluation records
each hash lookup in the final table and each actual cipher entry in the final
graph. Evaluation is proved from the shared operational run and a proved bound.
It composes through program bind and lifts, retaining query coverage under
repeated calls and later table/log extension.

Spec/Proofs.BAVCReconstructionProgram executes internal expansion, then each
leaf row followed immediately by its hash, then the outer hash. Its returned
value equals the existing staged reconstructWithNodes, including all errors.
Successful evaluations derive every row/outer lookup; the table fallback is
unused at those inputs. The source's literal prefill, distinct tree/nodes
bindings and undefined-read errors are retained. The derived query bound is
B=2*(tau*N-1)+(2*N+1)*tau+1, not a runtime or signature-query bound.

BAVCReconstructionCoverage proves both actual commitment calls for every
revealed seed from the evaluation certificate. Spec/Proofs.BAVCReconstructionGame
executes both selected reconstructions after a mixed adversary, even when the
first returns an error. Both results remain explicit Except values. For two
successful equal-root outputs with a disagreeing common revealed seed, the
existing computable finder yields an actual stored hash collision or a seed
collision whose cipher coverage is now derived from these executions.

BAVCReconstructionSecurity discharges that coverage for full-output and
Category-III layouts, then proves choose(Q,2)*(1/|Digest|+C/(M-Q)*C/(M-Q-2)) with
Q=q+2*B. Full outputs use C=1,M=2^lambda; Category III uses C=2^64,M=2^256 and
384-bit digests. Width/tweak range premises remain explicit; companion, padding
and capacity facts are proved. Q+2<M gives the useful finite form. No freshness,
prior-membership or completion guard is added to the successful-disagreement
event, and no generic binding contract is assumed. Undefined reconstruction
outcomes are not interpreted as signature rejection or used for vacuous EUF-CMA.

A generic program-boundary event lemma avoids unfolding the concrete Category
III experiment during type comparison. Its coverage premise is discharged by
the source execution proof. No recursion/heartbeat limit, trust setting, oracle
model or theorem conclusion was weakened to finish elaboration.

The next composition is the actual verifier Hashaux/Hashlines chain under the
same oracle, with its query cost and returned-root correspondence. The existing
deterministic chain lemma does not yet provide this execution law. Full BLC
binding is still obstructed by the independent supplied folding seed array,
the Hashlines field mismatch and line-21 boundary. Signature/replay accounting,
usable algebraic challenges, RSD extraction, secret-free signing simulation and
end-to-end EUF-CMA remain open. This turn closes the selected reconstruction
disagreement bound, not signature security or correctness of the literal source.

Targeted builds and the thirty-ninth full validation passed: 3399 build jobs,
13351 project declarations, and only propext, Classical.choice and Quot.sound
transitively. Checked 305 indexed Lean references (227 distinct paths), all eight
new imports/index entries, standalone specification separation and exactly
three final discrepancy statements. No placeholder, cryptographic axiom or
unchecked shortcut was introduced. Assumptions and Final are unchanged. The
persistent goal remains active and incomplete.

## Continuation 40 — verifier hash chain after complete reconstruction

This continuation was started by a different assistant session after the
user asked to read the repository and continue. The previous continuation 39
was classified as progress and its audit (3399 jobs, 13351 declarations) was
taken as the authoritative starting state. The working tree additionally held
two compiling specification modules, Spec/BLCHashChain and
Spec/BLCReconstructionChain, and a proof module Proofs/BLCHashChain that
failed to elaborate at two places: an ambiguous `.ok` constructor and a bind
lemma whose program argument needed `partialSourceMiddle` unfolded. Both were
fixed without changing any statement; none of the three modules was imported
or indexed, so they were not part of the 39th audit.

Added Proofs/BLCReconstructionChain. It proves the opening/verification
budgets 2*(B+p+m+2), evaluation decomposition of a successful chain output
into its reconstruction, intermediate context and two chain lookups, and the
collision reduction: equal line digests give equal roots or a stored collision
on the exact Aux/Lines query pairs, and equal roots with a disagreeing common
revealed seed reduce through the continuation-39 result. Completion after a
mixed adversary and the winning-evaluation extraction follow the existing
pipeline lemmas. full_winning_covered/truncated_winning_covered discharge the
coverage premise, and the full/III bounds are derived with Q=q+2*(B+p+m+2).

The source chain constructor keeps Algorithm 12's three-field Hashlines
payload and exposes the base-matrix computation as a supplied bounded
program, which is the unresolved line-21 boundary. Nothing identifies that
program with the printed subtraction. The intermediate programs and the
corrections encoding are caller inputs without correctness contracts. This
is a BLC root/line binding component on the shared oracle; it is not full
BLC binding, since Algorithm 12's own seed array and share bindings remain
separate, and it is not signature security.

Next: connect this executed chain to the two accepted fresh-message attempts
produced by the forgery-to-fork step, with signature/replay query accounting;
then usable algebraic challenge separation, RSD extraction and secret-free
signing simulation. Source boundaries stay explicit; no assumption, source
repair or success contract was added. Assumptions and Final are unchanged.

The fortieth full validation passed: 3403 build jobs and 13501 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked all four new module imports and index entries, standalone
specification separation and exactly three final discrepancy statements. No
placeholder, cryptographic axiom or unchecked shortcut was introduced.
Assumptions and Final are unchanged. The persistent goal remains active and
the full signature reduction remains incomplete.

## Continuation 41 — seed-vector extraction from two chain executions

Classified continuation 40 as progress and took its audit (3403 jobs, 13501
declarations) as the starting state. Continued the extraction direction of
priority item 1 using the executed chain game.

Added Spec/Proofs.BLCSeedExtraction. The specification defines consistency
of two revealed seed maps at one execution, agreement of a complete vector
with both maps, the pointwise merge, and the game's extraction-failure event.
The proofs derive presence of every non-hidden seed in a successful literal
reconstruction, agreement of the merge under consistency, uniqueness of the
agreeing vector when the hidden indices differ, failure-implies-disagreement
on the game's support, and the resulting full/III failure bounds by
transitivity with the chain bounds.

The hidden indices remain adversary-selected reconstruction inputs. Deriving
them from two distinct accepted digests needs the challenge expansion, whose
literal sampler reads undefined B; that separation is still open. Turning the
seed vector into witness lines needs Algorithm 12's folding with its separate
bindings. Signature/replay accounting, RSD extraction and secret-free signing
simulation remain open. No assumption, source repair or contract was added;
Assumptions and Final are unchanged.

The forty-first full validation passed: 3405 build jobs and 13520 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 42 — extractor bindings for the Algorithm-12 fold

Classified continuation 41 as progress and took its audit (3405 jobs, 13520
declarations) as the starting state. Continued toward witness extraction by
folding an extracted seed vector through Algorithm 12's loop.

Added Spec/Proofs.BLCSeedFold. The specification names the extractor's
bindings for the undeclared seed/rshare/phi_mu, the printed correction read,
the direct fold of the extracted randomness, and the resulting slope,
intercept and affine share. The proofs reuse the existing exact fold sum to
show the share at any hidden index is affine in its Gray row, lift this to
the Q matrix of a reached line-21 boundary, derive the two-index difference
identity, and show the honest Algorithm-10 corrections give the committed
common accumulator as slope. A name clash with Mathlib's `slope` required
qualified names in simp lists; a Fin/Nat vector index needed an explicit
`show`. No statement was weakened.

The transmitted corrections are adversarial in a forgery, so the slope is
the committed accumulator only for honest auxiliary data; this is stated as
such. Next: connect the affine Q to the suffix's witness/randomness lines and
PIOP evaluation at two distinct challenges, and the usable-challenge
separation between two accepted digests. Signature/replay accounting, RSD
extraction and secret-free signing simulation remain open. No assumption,
source repair or contract was added; Assumptions and Final are unchanged.

The forty-second full validation passed: 3407 build jobs and 13550 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 43 — suffix values and a candidate two-challenge consistency reading

Classified continuation 42 as progress and took its audit (3407 jobs, 13550
declarations) as the starting state. Continued toward extraction by carrying
the affine share matrix into the Algorithm-12 suffix and the consistency
columns.

Added Spec/Proofs.BLCSeedLines. The psi decomposition of the affine matrix,
the suffix witness/randomness forms, the constant-slope affine-in-delta
form (using the Gray merge encoding and the nonzero delta from the prefix),
the bilinear form of the consistency columns, and the two-challenge masked-
slope theorem under the explicit candidate reading are proved. Two elaboration
issues were fixed without weakening statements: an auto-included unused
algebra instance needed `omit`, and partially applied matrix definitions
needed explicit function extensionality instead of simp unfolding.

The user offered an agent team mid-turn and then cautioned about an unstable
network connection; the work stays single-stream, with shared ledgers and
one build tree, as agreed. Next: equal plain/base across the fork's two
accepted attempts, the random-matrix argument for non-constant slopes, the
challenge separation between distinct digests, and signature/replay query
accounting. RSD extraction and signing simulation remain open. No assumption,
source repair or contract was added; Assumptions and Final are unchanged.

The forty-third full validation passed: 3409 build jobs and 13569 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 44 — uniform consistency-mask kernel probability

Classified continuation 43 as progress and took its audit (3409 jobs, 13569
declarations) as the starting state. Continued with the probability step
behind the two-challenge masked-slope identity.

Added Spec/Proofs.ConsistencyMatrix. The proofs generalize the existing
kernel/fiber law to any surjective linear map into a finite module, build
M ↦ M·v as a linear map with its surjectivity for nonzero v, and derive the
exact kernel probability, the top-only impossibility, the nonzero-vector
bound, the two-vector equal-mask bound and the binary instantiation. Two
elaboration fixes: `Batching.systematicLeft` needed the `Spec` prefix, and
`Matrix.mulVec` needed an explicit equation before `linear_combination`.

Next: model the mask as the oracle's answer to the auxiliary query after
the slopes are fixed, compose with the two-challenge identity to bound
non-constant slopes, and continue with fork-attempt consistency, challenge
separation and signature/replay accounting. RSD extraction and signing
simulation remain open. No assumption, source repair or contract was added;
Assumptions and Final are unchanged.

The forty-fourth full validation passed: 3411 build jobs and 13596 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 45 — adaptive oracle trap for a fixed function of the query input

Classified continuation 44 as progress and took its audit (3411 jobs, 13596
declarations) as the starting state. Continued with the oracle-ordering
form of the mask kernel bound.

Added Spec/Proofs.RandomOracleTrap. The proofs give a mass identity for
map-true as a sum with indicators, a bind/indicator inequality, the one-query
step with the recorded-table invariant for repeats, the run induction, the
experiment bound budget*epsilon, the table-to-history transfer and the mask
instantiations. Elaboration fixes: the trap predicate is noncomputable
(classical decide), `PMF.map_const` did not match a lambda so a small
map-const mass lemma was proved, and the if-then-else decidability instance
had to be an implicit argument to match the classical instance in goals.

Next: compose the trap with the auxiliary-digest query (hcom, corrections)
and the hcom-to-seeds binding so that distinct slopes across executions are
caught except with budget*2^-(lambda+B) plus the collision terms; then
fork-attempt consistency, challenge separation and signature/replay
accounting. RSD extraction and signing simulation remain open. No
assumption, source repair or contract was added; Assumptions and Final are
unchanged.

The forty-fifth full validation passed: 3413 build jobs and 13622 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 46 — table-dependent trap on the instrumented oracle trace

Classified continuation 45 as progress and took its audit (3413 jobs, 13622
declarations) as the starting state. Analysed the composition with the
auxiliary-digest query: the slope vector is determined by the query input
only through the hash preimage chain hcom -> row hashes -> commitments ->
seeds, which is a property of the oracle table at the time of the mask
query. The fixed-function trap is therefore insufficient; a table-dependent
trap recorded at fresh queries is the right generic shape, and the case
where the chain is completed after the mask query must be charged to a
separate fresh-answer guessing event.

Added Spec/Proofs.RandomOracleTrace accordingly. The bound proof mirrors the
fixed-function one without needing the recorded invariant, since repeats
record nothing; the invariants were restated as a conjunction after a first
attempt made the trace-to-table direction unprovable from table extension
alone. Namespace ambiguity between the collision and trace experiments was
resolved by qualifying the procedure type.

Next: the fresh-answer-hits-earlier-input bound, the model choice for the
mask oracle, and the composition yielding the slope-consistency bound; then
fork-attempt consistency, challenge separation and signature/replay
accounting. RSD extraction and signing simulation remain open. No
assumption, source repair or contract was added; Assumptions and Final are
unchanged.

The forty-sixth full validation passed: 3415 build jobs and 13696 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 47 — fresh answers hitting values mentioned by earlier inputs

Classified continuation 46 as progress and took its audit (3415 jobs, 13696
declarations) as the starting state. Continued with the guessing event
identified in the previous continuation.

Added Spec/Proofs.RandomOracleMention. The trace trap bound was
generalized to predicates on the whole fresh-query prefix with a
position-dependent epsilon, summed over positions; the mention instance
gives choose(budget,2)*m/|Output|. Elaboration notes: `trace[` is reserved
syntax, so an indexed variable was renamed; the uniform membership mass was
proved with an implicit decidability instance and `Finset.sum_ite` to avoid
instance mismatches; `mul_le_mul_left` is the right-factor monotonicity
lemma in this Mathlib.

Next: fix the mask oracle model (a matrix-valued lazy oracle on the
auxiliary digest), compose the table-dependent trap, the mention bound and
the hash collision bound with the hcom-to-seeds chain to bound inconsistent
slopes; then fork-attempt consistency, challenge separation and
signature/replay accounting. RSD extraction and signing simulation remain
open. No assumption, source repair or contract was added; Assumptions and
Final are unchanged.

The forty-seventh full validation passed: 3417 build jobs and 13721 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 48 — product-valued oracle for hash and mask components

Classified continuation 47 as progress and took its audit (3417 jobs, 13721
declarations) as the starting state. Chose the product-valued oracle as the
model for independent hash and mask oracles, since the existing single-
oracle trace lemmas then apply to each component without a new multi-oracle
interpreter.

Added Spec/Proofs.ProductOracle: component marginals from the existing
uniform pair law, the matrix-component mask trap bound, and the digest-
component mention bound. Two small fixes: the constant-map and identity-map
PMF lemmas needed explicit forms.

Next: assemble the standalone slope-consistency theorem: parse the chain
inputs with a mention map, define the table-dependent slope-difference
vector through the chain present at mask time under an explicit injective
commitment hypothesis, and combine the trap, mention and stored-collision
bounds; then fork-attempt consistency, challenge separation and
signature/replay accounting. RSD extraction and signing simulation remain
open. No assumption, source repair or contract was added; Assumptions and
Final are unchanged.

The forty-eighth full validation passed: 3419 build jobs and 13731 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 49 — ordered oracle log and dependency chains

Classified continuation 48 as progress and took its audit (3419 jobs, 13731
declarations) as the starting state. Worked out the ordering argument that
the slope-consistency composition needs: the mask entry's earlier table
either already contains the whole hash chain for its input, or a link was
answered after the mask, in which case that link's fresh digest equals a
value mentioned by the next newer link, an instance of the mention event.

Added Spec/Proofs.OracleChain with the ordering/freshness invariants, the
older-entry lemma, the two-link dichotomy and the chain induction. The
`trace` variable name had to be renamed because `trace[` is reserved
syntax; an index-bound and a drop-index rewrite needed explicit lemmas; the
chain theorem was restated with a separate sink predicate to avoid an
inhabited-digest placeholder.

Next: the concrete BAVC/BLC chain (row inputs, outer input, auxiliary
input, mask input) with its mention parser and distinctness facts, the
table-dependent slope-difference vector, and the assembled bound under an
explicit injective-commitment hypothesis; then fork-attempt consistency,
challenge separation and signature/replay accounting. RSD extraction and
signing simulation remain open. No assumption, source repair or contract
was added; Assumptions and Final are unchanged.

The forty-ninth full validation passed: 3421 build jobs and 13761 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 50 — concrete chain strings and the mention parser

Classified continuation 49 as progress and took its audit (3421 jobs, 13761
declarations) as the starting state. Instantiated the generic chain
dichotomy with the concrete BAVC/BLC strings.

Added Spec/Proofs.BAVCChainInputs. The fixed-width array indexing lemma
was proved by the same head/tail decomposition as the earlier injectivity
proof. The rows of one commitment are siblings rather than a linear chain,
so the dichotomy is applied once per execution to the linear chain
auxiliary-outer-row and the results are combined. A rewrite of the root
inside the auxiliary string was avoided by direct image membership; the
pairwise proof uses explicit constructors; the reconstruction-program
module is imported for the definitional correspondence.

Next: the table-dependent slope-difference vector through the present
chain under an explicit injective-commitment hypothesis, and the assembled
slope-consistency bound combining trap, mention and stored-collision terms;
then fork-attempt consistency, challenge separation and signature/replay
accounting. RSD extraction and signing simulation remain open. No
assumption, source repair or contract was added; Assumptions and Final are
unchanged.

The fiftieth full validation passed: 3423 build jobs and 13824 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 51 — chained claims, uniqueness and digest collisions

Classified continuation 50 as progress and took its audit (3423 jobs, 13824
declarations) as the starting state. Wrote the deterministic uniqueness
step for the slope-consistency composition and the collision event it
needs.

Added Spec/Proofs.SlopeConsistency. A first statement claimed full
equality of the two claims, which is false because the plain check and
witness correction are not part of the chain; the theorem was restated as
equality of the slope-relevant components, with a separate lemma that the
slope depends on the auxiliary data only through its corrections. The
collision total needed its own sum identity, and an unused ordering
hypothesis was dropped.

Next: the table-dependent slope-difference vector through the present
chain, with the assembled bound budget*tau^2*2^-(lambda+B) +
choose(budget,2)*(tau+3)/2^(2*lambda) for the equal-mask event on
inconsistent slopes; then the join to the cipher-model seed binding,
fork-attempt consistency, challenge separation and signature/replay
accounting. RSD extraction and signing simulation remain open. No
assumption, source repair or contract was added; Assumptions and Final are
unchanged.

The fifty-first full validation passed: 3425 build jobs and 13866 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 52 — the standalone slope-consistency bound

Classified continuation 51 as progress and took its audit (3425 jobs, 13866
declarations) as the starting state. Assembled the trap, mention and
collision results into the slope-consistency bound.

Added Spec/Proofs.SlopeConsistencyGame. The trap vector uses classical
choice of a chained claim; the uniqueness theorem turns it into the named
claim's slope difference on a collision-free earlier table. Elaboration
notes: rewriting a vector inside a classical `decide` and applying
`decide_eq_true` both failed on instance re-synthesis, so a small lemma
with a unified (non-instance-implicit) decidability argument was added;
the chain presence was transported to the earlier table through table
extension; the pipeline-security event-mass lemma needed an import.

Next: join the commitment-injectivity hypothesis to the ideal-cipher seed
binding and the chain/seed-extraction games, then fork-attempt consistency,
challenge separation and signature/replay accounting. RSD extraction and
signing simulation remain open. No assumption, source repair or contract
was added; Assumptions and Final are unchanged.

The fifty-second full validation passed: 3427 build jobs and 13904 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 53 — instrumented shared hash/cipher execution

Classified continuation 52 as progress and took its audit (3427 jobs, 13904
declarations) as the starting state. To replace the slope game's injective-
commitment hypothesis by the cipher seed binding, the trap machinery must
live in the shared hash/cipher model, where the cipher is an oracle.

Added Spec/Proofs.HashCipherTrace: the instrumented shared run, exact
projection onto the existing run (the hash branch composes the collision
marking with the forgetful map), the invariant induction with the extra
cipher case, both trap-bound inductions, and the mixture bounds. Three
namespaces each define `Result`, so selective opens were used; one
composition rewrite needed its direction reversed.

Next: instantiate the digest as hash digest times mask, re-state the slope
game here with CommitSeed through the cipher family, and replace the
commitment-injectivity hypothesis by the seed-collision event already
bounded in this model; then fork-attempt consistency, challenge separation
and signature/replay accounting. RSD extraction and signing simulation
remain open. No assumption, source repair or contract was added;
Assumptions and Final are unchanged.

The fifty-third full validation passed: 3429 build jobs and 13963 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 54 — unobserved-key double match

Classified continuation 53 as progress and took its audit (3429 jobs, 13963
declarations) as the starting state. Analysed what replacing the slope
game's injective-commitment hypothesis needs: a seed colliding with a
named seed's commitment is either queried, which the witnessed pair event
covers through the companion structure, or unqueried, which needs a bound
for an unobserved key matching both halves. The existing single-target and
either-fresh comparison bounds give only one half and would lose the union
over 2^lambda keys.

Added Proofs/IdealCipherUnseenMatch with the double-match bound and its
union over a finite key set. The freshness predicate lives in the proofs
namespace of the fresh-answer module, and the right monotonicity lemma for
right multiplication is `mul_le_mul_left` in this Mathlib.

Next: the slope game in the shared model with CommitSeed through the
family, executing the named claim's commitments, and the case split that
replaces injectivity by the witnessed pair event plus this bound; then
fork-attempt consistency, challenge separation and signature/replay
accounting. RSD extraction and signing simulation remain open. No
assumption, source repair or contract was added; Assumptions and Final are
unchanged.

The fifty-fourth full validation passed: 3430 build jobs and 13968 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 55 — slope-consistency game in the shared model

Classified continuation 54 as progress and took its audit (3430 jobs, 13968
declarations) as the starting state. Re-stated the slope game in the
shared model with the source commitment through the cipher family.

Added Spec/Proofs.SharedSlopeGame: local uniqueness, trap vector identity,
chain presence from invariants (a copy of the single-oracle argument with
the invariants as hypotheses), the collision case split, history
consistency through the projection, and the five-way coverage theorem.
Elaboration notes: `Setting` and `Entry` clashed across opened namespaces
and were resolved by selective opens and qualification; `leafOffset` is in
the specification namespace while its bound is in the proofs namespace; a
negated equality from `simp` is `Not`, not `Ne`, so `Ne.symm` was applied
explicitly.

Next: bound the five events on the traced joint experiment (trap and
prefix bounds through the mixture, the witnessed pair bound and the unseen
double match through the projection and the posterior equivalence), then
execute the named commitments to discharge the queried condition; then
fork-attempt consistency, challenge separation and signature/replay
accounting. RSD extraction and signing simulation remain open. No
assumption, source repair or contract was added; Assumptions and Final are
unchanged.

The fifty-fifth full validation passed: 3432 build jobs and 14025 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 56 — probability assembly of the shared-model slope bound

Classified continuation 55 as progress and took its audit (3432 jobs, 14025
declarations) as the starting state. The user asked mid-turn whether the
reduction proof is done and asked to prioritize it; the answer recorded in
the transcript is no, with the proved and missing parts listed, and the
current chain is on that path. The unseen-match event was restated with
the named seed's recorded outputs so that its targets are fixed by the
history.

Added Proofs/SharedSlopeBound. Two heartbeat timeouts were bisected with
temporarily stubbed variants and traced to instance mismatches between
generic cipher lemmas (classical decidability) and concrete statements on
`Bits lambda`; two bridging lemmas, equality of uniform laws across
`Fintype` instances and transfer of mass bounds across decidability
instances, resolve them without any resource or trust setting change.

Next: execute the named claim's commitments to discharge the queried
condition, then connect the fork's two accepted attempts, challenge
separation and signature/replay accounting. RSD extraction and signing
simulation remain open. No assumption, source repair or contract was
added; Assumptions and Final are unchanged.

The fifty-sixth full validation passed: 3433 build jobs and 14051 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 57 — instrumented two-phase shared execution

Classified continuation 56 as progress and took its audit (3433 jobs, 14051
declarations) as the starting state. To discharge the queried-claim
condition by execution, the trap machinery must hold for a two-phase run
whose second phase performs the named commitment calls.

Added Spec/Proofs.HashCipherTracePipeline. The trap bounds for the
two-phase run follow from the single-phase bounds through the bind/indicator
inequality, with the first phase's log as the second phase's starting log
and the fresh-entry count bound shifting the prefix positions. Namespace
ambiguity between the one- and two-phase runs was resolved by a selective
open; the real-number arithmetic step used an associativity rewrite.

Next: the commitment program for the named claim as the second phase, its
coverage of the cipher history, the transfer of the witnessed and unseen
bounds through the two-phase projection and posterior equivalence, and the
re-stated slope game without the queried condition; then fork-attempt
consistency, challenge separation and signature/replay accounting. RSD
extraction and signing simulation remain open. No assumption, source
repair or contract was added; Assumptions and Final are unchanged.

The fifty-seventh full validation passed: 3435 build jobs and 14075 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 58 — executed commitments in the slope game

Classified continuation 57 as progress and took its audit (3435 jobs, 14075
declarations) as the starting state. Discharged the queried-claim
condition by execution.

Added Spec/Proofs.SharedSlopeExec. The claim is carried as the program's
return value so that the second phase's final state determines it; the
existing program-evaluation lemma, applied through the two-phase
projection and decomposition, gives both the claim and the recorded calls.
The coverage argument was restated with the invariants and the claim as
explicit hypotheses and reused for the two-phase experiment. A missing
namespace open was the only build issue.

Next: connect the fork's two accepted attempts to this executed chain,
challenge separation between distinct digests, and signature/replay
accounting; then RSD extraction and signing simulation. No assumption,
source repair or contract was added; Assumptions and Final are unchanged.

The fifty-eighth full validation passed: 3437 build jobs and 14126 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 59 — shared-model scheme skeleton

Classified continuation 58 as progress and took its audit (3437 jobs, 14126
declarations) as the starting state. Began connecting the fork to the
executed chain by instantiating the abstract game's other-state with the
shared world and writing verification as an executed program.

Added Spec/Proofs.SharedScheme. The reconstruction program answers hash
queries with bare digests, so a lift reading the digest component was
added; the chain was inlined so that the middle's values reach the suffix
record; `Digest` was qualified between two namespaces. The typed fork glue
needed no new invariant since equal hash inputs give equal messages.

The composition now needs a declared target for Algorithm 12 lines 9–21
and the index expansion, both undefined in the literal source; this was
recorded as a user decision and the loop continues in the conditional
form. Next: the honest signer as an oracle program, the correspondence of
this verification with the executed-chain games, challenge separation
under a declared expansion, and signature/replay accounting. No
assumption, source repair or contract was added; Assumptions and Final
are unchanged.

The fifty-ninth full validation passed: 3439 build jobs and 14252 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 60 — executed verification and the chain games

Classified continuation 59 as progress and took its audit (3439 jobs, 14252
declarations) as the starting state. Connected the executed verification
to the chain and seed-extraction results.

Added Proofs/SharedSchemeChain with the verification decomposition, equal
roots from equal lines digests, the projected-table view for the existing
reconstruction collision lemma, and the two-verification seed-vector
theorem. One instance mismatch in eliminating a classical `decide` was
resolved with a unification-based eliminator, as before.

Next: relate the middle's value to the fold/slope identities so that the
two accepted attempts of a fork feed the shared-model slope game, write
the honest signer as an oracle program, and handle challenge separation
under a declared expansion; then signature/replay accounting, extraction
and signing simulation. No assumption, source repair or contract was
added; Assumptions and Final are unchanged.

The sixtieth full validation passed: 3440 build jobs and 14259 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 61 — candidate verifier middle

Classified continuation 60 as progress and took its audit (3440 jobs, 14259
declarations) as the starting state. Related the verifier middle to the
fold and slope identities by naming a candidate middle: binding the
reconstruction's revealed seeds, which suffice because the literal loop
skips the hidden index.

Added Spec/Proofs.CandidateVerifier and generalized the middle's
signature. The partial-array fold lemma mirrors the earlier total one;
the evaluation lemma case-splits the program's matches with `split at`
after the hash constructor; the reduced equalities closed trivially.

Next: compose with the two-verification seed vector so that a fork's two
accepted attempts feed the shared-model slope game and the two-challenge
masked-slope identity; then the honest signer program, challenge
separation and signature/replay accounting. RSD extraction and signing
simulation remain open. No assumption, source repair or contract was
added; the candidate is explicitly identified. Assumptions and Final are
unchanged.

The sixty-first full validation passed: 3442 build jobs and 14286 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 62 — fork to slope claim

Classified continuation 61 as progress and took its audit (3442 jobs,
14286 declarations) as the starting state. Composed the candidate middle
with the two-verification seed vector: a fork's two accepted candidate
verifications force the masked slope to equal the plain check at a
differing hidden index, up to a recorded seed collision.

Added Proofs/ForkSlope. The salt is recovered from equal roots through
the recorded outer lookup; each verification's fold is the fold of the
merge completion of its own reconstruction; the two completions agree by
uniqueness; the two base equations are subtracted at a differing Gray bit
and closed by linear_combination. The build passed on the second attempt
after fixing a lemma namespace and adding a seed-table congruence lemma.

Next: the honest signer as an oracle program, challenge separation under
a declared expansion, signature/replay accounting from the fork to the
executed chain games, then RSD extraction and signing simulation. No
assumption, source repair or contract was added; the serialization
injectivity hypotheses are explicit. Assumptions and Final are unchanged.

The sixty-second full validation passed: 3443 build jobs and 14295 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 63 — honest signer commitment program

Classified continuation 62 as progress and took its audit (3443 jobs,
14295 declarations) as the starting state. Wrote the honest signer's
commitment phase as an executed program in the shared model and proved
its evaluation lemma and budget.

Added Spec/SharedSigner and Proofs/SharedSigner. The tree loop, leaf
commitments and row hashes use small generic combinators (an ExpandSeed
call, a per-index collector, a digest-reading hash call) with their own
evaluation and budget lemmas; the main lemma steps through the binds and
the four chain hashes. Build fixes: namespace-qualified lemma names,
explicit continuation arguments for budget metavariables, zero-length
budget rewrite, and projection unfolding by `show`.

Next: attach the PIOP computation, Algorithm 11's retry and the opening
as the abstract game's signing services, then query accounting from the
fork to the executed chain games, challenge separation, extraction and
signing simulation. No assumption, source repair or contract was added;
the Hashlines-tail discrepancy is kept explicit as two named readings.
Assumptions and Final are unchanged.

The sixty-third full validation passed: 3445 build jobs and 14377 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 64 — shared-model signing services

Classified continuation 63 as progress and took its audit (3445 jobs,
14377 declarations) as the starting state. Attached the PIOP, retry and
opening steps as the abstract game's signing services in the shared model
and characterized the supports of signing.

Added Spec/SharedSigning and Proofs/SharedSigning. The run lemma
projects the traced run to the plain run with `runFixed_forget` and uses
the existing `run_evaluates`; the signing lemma unfolds the abstract
scheme's bind chain and the random-oracle storage lemma. Build fixes:
one `open X (names)` per line, a ring instance for the polynomial field,
rewriting the final state before the match, an omitted unused section
instance, and `show` patterns carrying the payload equation.

Next: signature/replay query accounting from the fork into the executed
chain games, challenge separation under declared expansions, then
extraction and signing simulation. No assumption, source repair or
contract was added; the optional body and fixed-instance key generation
are recorded modelling choices. Assumptions and Final are unchanged.

The sixty-fourth full validation passed: 3447 build jobs and 14445 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 65 — fork branches on a common prefix

Classified continuation 64 as progress and took its audit (3447 jobs,
14445 declarations) as the starting state. Reduced the fork's two-branch
situation to the single-table fork-to-slope lemma under an explicit
prefix-visit hypothesis.

Added Proofs/ForkSlopePrefix with the visited-input list, the restriction
and monotonicity lemmas (induction on the evaluation derivation) and the
two-branch corollary. Build fix: a section variable named `Digest`
shadowed the concrete digest type and was renamed in a closed section.

Next: discharge the prefix-visit hypothesis by the chain-mention and
fresh-digest bounds in the signature game, then challenge separation,
extraction and signing simulation. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The sixty-fifth full validation passed: 3448 build jobs and 14464 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 66 — chains across the fork cut

Classified continuation 65 as progress and took its audit (3448 jobs,
14464 declarations) as the starting state. Began discharging the
prefix-visit hypothesis: the verifier's hash chain is in the fork cut
whenever its lines string is, up to the mention event.

Added Proofs/ForkCut, mirroring the mask-sink chain theorem with the
lines string as sink and a cut hypothesis in place of the mask entry. The
build passed on the first attempt.

Next: charge the lines string's fixed-target event and decide the mask
input's treatment across the fork (in the cut, or a per-branch fresh-mask
bound with a counter union), derive the cut property from the forking
construction, then challenge separation, extraction and signing
simulation. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The sixty-sixth full validation passed: 3449 build jobs and 14483 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 67 — fixed-target event along a branch

Classified continuation 66 as progress and took its audit (3449 jobs,
14483 declarations) as the starting state. Charged the lines string's
absence from the fork table by a fixed-target trace event with an explicit
run-level bound, and showed the cut persists along traced runs.

Added Proofs/ForkCutRun. Build fixes: qualified names for the procedure
type, the mark projections and the indicator; instance omissions placed
before doc comments; the multiplication monotonicity lemma's orientation.

Next: derive the cut and pre-cut properties from the forking
construction and compose the per-service runs of a branch, then settle the
mask input's position, challenge separation, extraction and signing
simulation. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The sixty-seventh full validation passed: 3450 build jobs and 14503 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 68 — shared-world invariants along the game

Classified continuation 67 as progress and took its audit (3450 jobs,
14503 declarations) as the starting state. Derived the cut hypothesis of
the fork-cut lemmas from the forking construction of the shared game.

Added Proofs/SharedGameInvariant. Build fixes: explicit preservation
hypotheses (section variables unused in statements are dropped),
qualified `run`, parenthesized `nomatch` lambdas inside anonymous
constructors, a `finalize` terminal lemma, the field restricted to
`Type` for a single program-run hypothesis, and the verifier's body
match handled by `rcases` on the body.

Next: sum the fixed-target and mention events over a branch's service
runs, settle the mask input's position across the fork, then challenge
separation, extraction and signing simulation. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The sixty-eighth full validation passed: 3451 build jobs and 14571 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 69 — visited inputs of the verification

Classified continuation 68 as progress and took its audit (3451 jobs,
14571 declarations) as the starting state. Characterized the hash inputs
read by an accepting executed verification, as needed by the prefix
restriction of the fork-to-slope lemma.

Added Proofs/VisitedInputs, mirroring the reconstruction evaluation
proofs' bind decompositions. Build fixes: qualified `bind` and
`reconstruct`, and reducing the outer match before splitting the inner
one in the candidate middle's visited-input lemma.

Next: compose the cut, chain, fixed-target and visited-input lemmas into
the fork's deterministic outcome with named events, then sum the branch
events over service runs, settle the mask input's position, challenge
separation, extraction and signing simulation. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The sixty-ninth full validation passed: 3452 build jobs and 14623 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 70 — one branch accounted

Classified continuation 69 as progress and took its audit (3452 jobs,
14623 declarations) as the starting state. Composed the cut, chain,
fixed-target and visited-input lemmas into one branch's deterministic
accounting with three named events.

Added Proofs/BranchAccounting and extended VisitedInputs' conclusions.
Build fixes: the observed-lookup lemma's namespace, the row-query
membership arguments, a two-power positivity lemma, and reading the mask
lookup directly from the candidate middle's first hash constructor.

Next: combine both branches into the fork's slope outcome on the
snapshot's table, sum the branch events over the branch's service runs,
address the mask event, then challenge separation, extraction and
signing simulation. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The seventieth full validation passed: 3453 build jobs and 14628 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 71 — deterministic fork outcome

Classified continuation 70 as progress and took its audit (3453 jobs,
14628 declarations) as the starting state. Composed the fork's two
branches into the deterministic slope-or-event outcome on the snapshot's
shared table.

Added Proofs/ForkOutcome. Build fixes: substituted names after case
splits, the `Except.ok` value of the verification run, an explicit `tau`
for the branch event, and the fork pair equation from the map support.

Next: bound the branch events (fixed-target and mention) over the
branch's service runs in the fork experiment, address the mask event,
supply hidden-index separation under a declared expansion, then feed the
slope game, extraction and signing simulation. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The seventy-first full validation passed: 3454 build jobs and 14664 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 72 — game-level event bound

Classified continuation 71 as progress and took its audit (3454 jobs,
14664 declarations) as the starting state. Lifted per-service event
bounds to the attempt of a run and of a fresh branch, generically in the
components and the event.

Added Proofs/GameEventBound. Build fixes: explicit service-bound
hypotheses, the orientations of the additive and multiplicative
monotonicity lemmas, unfolding the scheme by `dsimp` instead of a large
`show`, typed lambdas for the bind-indicator bound, and closing the
arithmetic rearrangements with `ring` and `gcongr`.

Next: instantiate the service constants for the shared services'
fixed-target and mention events, then the mask event, hidden-index
separation, the slope game, extraction and signing simulation. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The seventy-second full validation passed: 3455 build jobs and 14703 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 73 — fixed-target event over the shared game

Classified continuation 72 as progress and took its audit (3455 jobs,
14703 declarations) as the starting state. Instantiated the game-level
event bound for the fixed-target event of the shared services.

Added Proofs/SharedTargetBound. Build fixes: large `show` terms replaced
by unfolding (`dsimp only [components]`, `unfold`, `simp only
[publicOracle]`) to avoid heartbeat timeouts, `split at` for the
prepared-state match, and qualified indicator lemmas.

Next: charge the mention event, whose per-query mass grows with the log
length, then the mask event, hidden-index separation, the slope game,
extraction and signing simulation. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The seventy-third full validation passed: 3456 build jobs and 14739 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 74 — size-dependent game-level bound

Classified continuation 73 as progress and took its audit (3456 jobs,
14739 declarations) as the starting state. Generalized the game-level
event bound to size-dependent per-service bounds, as the mention event
needs, and proved the log-length growth of traced runs.

Added Proofs/GameEventBoundLen, following GameEventBound with the
invariant carried through the induction. Build fix: a qualified
mark-trace lemma.

Next: instantiate the mention event's service bound for the shared
services, then the mask event, hidden-index separation, the slope game,
extraction and signing simulation. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The seventy-fourth full validation passed: 3457 build jobs and 14785 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 75 — mention event over the shared game

Classified continuation 74 as progress and took its audit (3457 jobs,
14785 declarations) as the starting state. Instantiated the
size-dependent game-level bound for the mention event of the shared
services.

Added Proofs/SharedMentionBound, mirroring SharedTargetBound with the
log length as the size. Build fix: a rewrite on a match term replaced by
a case split.

Next: charge the prefix's mention event in the cut experiment, then the
mask event, hidden-index separation, the slope game, extraction and
signing simulation. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The seventy-fifth full validation passed: 3458 build jobs and 14820 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 76 — event bound along the cut

Classified continuation 75 as progress and took its audit (3458 jobs,
14820 declarations) as the starting state. Carried the size-dependent
event bound along the cut and proved the snapshot's level premise.

Added Proofs/CutEventBound, following the run bound with the saved-
snapshot case. The build passed on the first attempt.

Next: assemble, from key generation, the prefix and branch bounds for
the mention event and for the digest-collision event (a collision
service bound of the same shape with mention count one), then the mask
event, hidden-index separation, the slope game, extraction and signing
simulation. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The seventy-sixth full validation passed: 3459 build jobs and 14850 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 77 — collision event and prefix bounds

Classified continuation 76 as progress and took its audit (3459 jobs,
14850 declarations) as the starting state. Charged the digest-collision
event and assembled the prefix bounds of the cut experiment from key
generation.

Added Proofs/SharedCollisionBound. Build fixes: the initial world passed
explicitly to the cut bounds so the level premise can be shown, and
omitted instances on the empty-log lemmas.

Next: the fork experiment's union bound over both branches' events with
the prefix events, then the mask event, hidden-index separation, the
slope game, extraction and signing simulation. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The seventy-seventh full validation passed: 3460 build jobs and 14887 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 78 — charged events of the fork experiment

Classified continuation 77 as progress and took its audit (3460 jobs,
14887 declarations) as the starting state. United the charged events of
the fork experiment and bounded them by the prefix and branch bounds.

Added Proofs/ForkEventUnion. Build fixes: generic type variables
renamed to avoid shadowing opened type names, an explicit `tau` for the
branch event, the branch type spelled out in a function equation, the
fork case kept in bind-then-map shape, and the branch distribution
passed explicitly so the lambda's type is known.

Next: combine the charged-event bound with the deterministic fork
outcome into a statement that the slope outcome fails only with the
charged probability or the mask event, then hidden-index separation,
the slope game, extraction and signing simulation. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The seventy-eighth full validation passed: 3461 build jobs and 14923 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 79 — fork experiment split by charged events

Classified continuation 78 as progress and took its audit (3461 jobs,
14923 declarations) as the starting state. Combined the charged-event
bound with the deterministic fork outcome into the probabilistic split
of the fork experiment.

Added Proofs/ForkGoodOutcome. The build passed on the first attempt.

Next: charge the seed-collision member of the slope outcome, settle the
mask input's position, supply hidden-index separation under a declared
expansion, then feed the slope game, extraction and signing simulation.
No assumption, source repair or contract was added. Assumptions and
Final are unchanged.

The seventy-ninth full validation passed: 3462 build jobs and 14936 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 80 — uniform fork-to-slope data

Classified continuation 79 as progress and took its audit (3462 jobs,
14936 declarations) as the starting state. Made the mask and seed
completion of the fork-to-slope lemma uniform across executions and
recorded the two decisions the reduction's next steps depend on; the
user was notified.

Added Proofs/ForkSlopeUniform by moving the per-execution case split of
the original proof under the quantifier. The build passed on the first
attempt.

Next: continue with work independent of the decisions (the seed-
collision charge, the slope game's deterministic link from uniform
identities to equal masked images), and follow the user's choices on the
mask event and the fork multiplicity when given. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The eightieth full validation passed: 3463 build jobs and 14937 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 81 — candidate verifier against the honest signer

Classified continuation 80 as progress and took its audit (3463 jobs,
14937 declarations) as the starting state. While the two recorded
decisions are pending, proved the decision-independent algebraic
completeness of the candidate reading against the honest signer.

Added Proofs/HonestCandidate. Build fix: exposing the auxiliary record's
plain field by `set`/`show` so the candidate base identity rewrites.

Next: continue decision-independent work (executed completeness of the
honest shared signature under a declared nodes binding, the seed-
collision charge), and follow the user's choices when given. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The eighty-first full validation passed: 3464 build jobs and 14946 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 82 — fork outcomes with uniform data

Classified continuation 81 as progress and took its audit (3464 jobs,
14946 declarations) as the starting state. Restated the fork outcomes
through the uniform fork-to-slope lemma so downstream consumers receive
the shared mask and seed completion.

Added Proofs/ForkOutcomeUniform. The build passed on the first attempt.

Next: executed completeness of the honest shared signature would need
Algorithm 9's reconstruction of an honest opening under a declared nodes
binding, a tree-path correctness proof not yet in the repository; the
seed-collision charge needs a cipher-side game-level bound; both are
decision-independent but substantial, and the two recorded decisions
remain pending. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The eighty-second full validation passed: 3465 build jobs and 14952 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 83 — from uniform fork data to slope consistency

Classified continuation 82 as progress and took its audit (3465 jobs,
14952 declarations) as the starting state. Took the uniform fork data,
under the explicit separation hypothesis, to equal masked images, the
slope dichotomy and the extracted witness line's constant term.

Added Proofs/SlopeConsistencyLink. Build fix: a qualified psi lemma.

Next: the honest-opening reconstruction of the literal Algorithms 8–9
cannot succeed (recorded defect: padded openings prefill an empty tree),
so executed completeness needs a corrected target, another decision; the
seed-collision and slope-game steps need a reduction to the shared
traced experiment. The loop continues on small decision-independent
items and awaits the recorded decisions. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The eighty-third full validation passed: 3466 build jobs and 14956 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 84 — witness line recovery

Classified continuation 83 as progress and took its audit (3466 jobs,
14956 declarations) as the starting state. Closed the decision-
independent algebraic chain with the recovery of the extracted witness
coordinate from the two branches, and recorded the complete list of
decisions the remaining steps depend on.

Added Proofs/WitnessLineRecovery. The build passed on the first attempt.

Next: the loop stops pending the user's decisions; on restart, follow
the chosen targets through executed completeness, the cipher-side
bounds, the PIOP extraction step and the signing simulation. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The eighty-fourth full validation passed: 3467 build jobs and 14959 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 85 — candidate BAVC target

The user decided on 2026-10-09 to take the simplest option for every
recorded decision and to state corrected algorithms as named candidate
targets; the loop restarted. Took the audit of continuation 84 (3467
jobs, 14959 declarations) as the starting state and built the candidate
Algorithm 8–9 target with its executed reconstruction.

Added Spec/CandidateBAVC and Proofs/CandidateBAVC, reusing the signer's
collector and call lemmas. Build fixes: qualified names, a reversed
stored-digest equation and the budget arithmetic.

Next: the candidate verifier program and signing components, then the
fork chain for them. No assumption, source repair or contract was
added; the candidate is a named target. Assumptions and Final are
unchanged.

The eighty-fifth full validation passed: 3469 build jobs and 14997 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 86 — candidate scheme

Classified continuation 85 as progress and took its audit (3469 jobs,
14997 declarations) as the starting state. Built the shared-model scheme
over the candidate target and its verification lemmas.

Added Spec/CandidateScheme and Proofs/CandidateSchemeChain, reusing the
signing setting, state and commitment phase. Build fix: splitting a
match inside a hypothesis instead of casing on a let-bound term.

Next: the two-verification seed lemma, branch accounting and fork
outcomes for the candidate scheme. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The eighty-sixth full validation passed: 3471 build jobs and 15039 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked both new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 87 — candidate fork-to-slope lemma

Classified continuation 86 as progress and took its audit (3471 jobs,
15039 declarations) as the starting state. Re-proved the uniform
fork-to-slope lemma for the candidate scheme, with the seed-vector
extraction simplified to the completion of each opening by the other.

Added Proofs/CandidateForkSlope. Build fix: unfolding the let-bound
completions by `show` before rewriting.

Next: branch accounting, the prefix restriction and the fork outcomes
for the candidate scheme, then its game invariants and event bounds. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The eighty-seventh full validation passed: 3472 build jobs and 15044 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 88 — candidate branch accounting

Classified continuation 87 as progress and took its audit (3472 jobs,
15044 declarations) as the starting state. Carried branch accounting and
the prefix restriction to the candidate scheme.

Added Proofs/CandidateBranch. The build passed on the first attempt.

Next: the game invariants, event bounds and fork outcomes for the
candidate components (the preservation and service-bound records, the
attempt provenance and the fork outcome), then executed completeness.
No assumption, source repair or contract was added. Assumptions and
Final are unchanged.

The eighty-eighth full validation passed: 3473 build jobs and 15050 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 89 — candidate game bounds

Classified continuation 88 as progress and took its audit (3473 jobs,
15050 declarations) as the starting state. Carried the game invariants
and event bounds to the candidate components through a generic
size-dependent service bound.

Added Proofs/CandidateGameBounds. Build fixes: the budget hypotheses made
explicit theorem parameters (section hypotheses are not auto-included),
explicit size and event arguments to the cut-size lemma, and an unused
binder renamed.

Next: attempt provenance, the deterministic and probabilistic fork
outcomes for the candidate components, then executed completeness. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The eighty-ninth full validation passed: 3474 build jobs and 15093 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 90 — candidate fork outcomes

Classified continuation 89 as progress and took its audit (3474 jobs,
15093 declarations) as the starting state. Completed the fork chain for
the candidate scheme up to the uniform slope data.

Added Proofs/CandidateForkOutcome. Build fixes: budget hypotheses as
explicit parameters, and the remaining-fuel fact derived in a separate
step instead of an inline tactic argument.

Next: executed completeness of honest candidate signatures (the honest
signer's opening reconstructs to its own commitments and lines), then
the signing simulator, the PIOP extraction step and the composed final
theorem. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The ninetieth full validation passed: 3475 build jobs and 15123 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 91 — candidate executed completeness

Classified continuation 90 as progress and took its audit (3475 jobs,
15123 declarations) as the starting state. Proved executed completeness
of the candidate target against the honest shared signer.

Added Proofs/CandidateCompleteness. Build fixes: an explicit witness for
the middle's value, simplification of membership conditions instead of
rewriting lambdas, the row-hash function derived from the stored
lookups, the corrections rewritten through the auxiliary record, and a
beta-reduced goal before a rewrite.

Next: the signing simulator without the witness, then the PIOP
extraction step and the composed final theorem. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The ninety-first full validation passed: 3476 build jobs and 15158 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 92 — PIOP extraction step

Classified continuation 91 as progress and took its audit (3476 jobs,
15158 declarations) as the starting state. Resolved decision 4 by naming
the composed verifier as the candidate PIOP target and proved the
deterministic PIOP step of the extraction.

Added Proofs/PIOPExtraction. Build fixes: omitted instances placed
before doc comments, explicit evaluation simp sets closed by `ring`, and
a redundant tail of tactics removed.

Next: the signing simulator interface and the final composed theorem
with the remaining probabilistic steps as named hypotheses, then their
discharge. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The ninety-second full validation passed: 3477 build jobs and 15172 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 93 — deterministic fork extraction

Classified continuation 92 as progress and took its audit (3477 jobs,
15172 declarations) as the starting state. Strengthened the candidate
fork-slope statement and the uniform slope data with the agreement of
the two branches' completions, extended the candidate fork outcomes with
the accepted coefficient tuple, and proved the deterministic end-to-end
extraction from a good candidate fork with the remaining probabilistic
events as named alternatives.

Added Proofs/ForkExtraction. Build fixes: unused recomputation witnesses
dropped from the statement (their types were uninferable), and the
common-slope rewrite stated on the let-bound slopes before use.

Next: the final composed theorem with the Schwartz–Zippel, batching and
simulator steps as named hypotheses, then their discharge. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The ninety-third full validation passed: 3478 build jobs and 15174 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 94 — event-union skeleton of the composed reduction

Classified continuation 93 as progress and took its audit (3478 jobs,
15174 declarations) as the starting state. Defined the named events and
the extraction event of a candidate fork result as Boolean events,
proved that a winning fork without the charged events is one of them,
and bounded the good-fork and fork experiments by the events' sum and
the charged-event bound. Proved that extraction forces the extracted
lines' prover polynomial to be the hashed coefficient polynomial with a
zero constant term.

Added Proofs/CandidateReduction. Build fixes: type abbreviations given
explicit parameters, additive monotonicity lemma orientation, support-
restricted map monotonicity, an unused instance omitted.

Next: bounds of the named events and the batching step, then the
simulator and the composed final theorem. No assumption, source repair
or contract was added. Assumptions and Final are unchanged.

The ninety-fourth full validation passed: 3479 build jobs and 15228 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 95 — composed forgery bound skeleton

Classified continuation 94 as progress and took its audit (3479 jobs,
15228 declarations) as the starting state. Composed the event-union
bound with the random-index fork experiment and the forgery-to-fork
inequality: the forgery advantage against the candidate scheme is
bounded by the random-index named events, the extraction probability,
the charged-event bound and the guessing term.

Added Proofs/ForgeryReduction. Build fix: additive monotonicity lemma
orientation.

Next: bounds of the named events (zero challenge, Schwartz–Zippel over
the counter, seed collision, slope game, mask after fork, separation),
the batching step, the simulator and the RSD statement. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The ninety-fifth full validation passed: 3480 build jobs and 15240 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 96 — extraction split into batching and solution events

Classified continuation 95 as progress and took its audit (3480 jobs,
15240 declarations) as the starting state. Split the extraction event
into the batching event and the solution event using the exact
constant-term identity and the extracted lines' constant terms, and
restated the forgery bound with the two events.

Added Proofs/ExtractionSplit. No build fixes were needed.

Next: bounds of the named events and the batching event, then the
signing simulator and the witness-free solver. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The ninety-sixth full validation passed: 3481 build jobs and 15259 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 97 — solver and simulated statement

Classified continuation 96 as progress and took its audit (3481 jobs,
15259 declarations) as the starting state. Defined the solver on a
scheme's fork experiment with the extracted witness as output, proved
that the solution event is at most the solver's success, and
transferred the forgery bound to an arbitrary scheme of the same types
under a uniform per-event simulation gap.

Added Proofs/SimulatedSolver. Build fixes: explicit arguments of the
scheme event experiment (it does not mention the settings), the
explicit solver output in the existential, an unused instance omitted.

Next: the named witness-free simulator and its gap, then the named
events' probabilities and the batching event's bound. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The ninety-seventh full validation passed: 3482 build jobs and 15280 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 98 — named witness-free simulator

Classified continuation 97 as progress and took its audit (3482 jobs,
15280 declarations) as the starting state. Named the witness-free
signing simulator as a direct scheme that programs the hash table,
proved that its signing never reads the witness and that its other
components are the candidate scheme's, and instantiated the forgery
bound at it.

Added Spec/CandidateSimulator and Proofs/CandidateSimulator. No build
fixes were needed.

Next: the simulation gap in pieces (programming freshness, hidden-share
independence, PIOP honest-verifier zero knowledge), then the named
events' probabilities and the batching event's bound. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The ninety-eighth full validation passed: 3484 build jobs and 15297 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module imports and index entries, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 99 — simulated transcript completeness

Classified continuation 98 as progress and took its audit (3484 jobs,
15297 declarations) as the starting state. Characterized the values of
the candidate verification of an executed commitment (composing the
executed completeness with the verification chain, the candidate
reconstruction and the candidate middle on the committed seeds), and
concluded that the recomputed verification input is the committed lines
digest with the simulator's coefficient tuple.

Added Proofs/SimulatedCompleteness. Build fixes: a qualified digest
type, an unused decidability instance dropped.

Next: the simulator's programming step in the game and its failure
event, then hidden-share independence and PIOP honest-verifier zero
knowledge, then the named events' probabilities and the batching event's
bound. No assumption, source repair or contract was added. Assumptions
and Final are unchanged.

The ninety-ninth full validation passed: 3485 build jobs and 15299 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 100 — provenance of simulated signatures

Classified continuation 99 as progress and took its audit (3485 jobs,
15299 declarations) as the starting state. Proved the provenance of
simulated signatures, mirroring the honest signing provenance.

Added Proofs/SimulatedSign. Build fix: the constructor matches of the
simulated signing reduced before closing the evaluation and family
goals.

Next: the simulator's failure event and the gap pieces, then the named
events' probabilities and the batching event's bound. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

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

Classified continuation 101 as documentation and continuation 100's audit
(3486 jobs, 15308 declarations) as the starting state. Proved the
algebraic split of the prover polynomial into its mask part and its
witness part.

Added Proofs/PIOPMaskSplit. No build fixes were needed.

Next: the coefficients of the mask times X as packed layer constants,
their uniformity from the hidden share, and the one-time-pad step of the
simulation gap. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-second full validation passed: 3487 build jobs and 15316 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 103 — mask coefficients

Classified continuation 102 as progress and took its audit (3487 jobs,
15316 declarations) as the starting state. Proved the coefficient
formulas of the formatted mask and the padding of the hashed prover
coefficients.

Added Proofs/PIOPMaskCoeff. Build fix: the batching namespace opened for
the block count.

Next: the packed constants' uniformity (the submitted power basis makes
packing a bijection of the layer's bits) and the one-time-pad step. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-third full validation passed: 3488 build jobs and 15333 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 104 — packing uniformity and one-time pad

Classified continuation 103 as progress and took its audit (3488 jobs,
15333 declarations) as the starting state. Proved the packing bijection
from the submitted power basis and the quotient ring's cardinality, and
the one-time-pad lemmas.

Added Proofs/PackingUniform. Build fix: a redundant split of the
bijectivity goal removed.

Next: the honest randomness lines' constants as packed hidden-share
bits, then the one-time-pad step on the hashed coefficients. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-fourth full validation passed: 3489 build jobs and 15339 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 105 — hidden-share translation

Classified continuation 104 as progress and took its audit (3489 jobs,
15339 declarations) as the starting state. Proved the translation
structure of the committed arithmetic in one party's random vector, and
recorded that the random table's PRG is a deterministic parameter, so
the hidden-share independence needs an explicit PRG hypothesis.

Added Proofs/HiddenShareTranslation. Build fix: the fold lemma's
namespace qualified.

Next: the revealed triple (witness correction, randomness constants,
plain check) as an affine bijection of the hidden vector, so its image
of a uniform vector is uniform regardless of the witness. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-fifth full validation passed: 3490 build jobs and 15348 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 106 — revealed triple bijection

Classified continuation 105 as progress and took its audit (3490 jobs,
15348 declarations) as the starting state. Proved that the revealed
triple is an affine bijection of the hidden party's vector and that its
image of a uniform vector is uniform regardless of the witness.

Added Proofs/RevealedBijection. No build fixes were needed.

Next: the honest transcript's triple as the revealed map of the hidden
vector with the other parties' constants, then the PRG hypothesis and
the hashed-coefficient pads. No assumption, source repair or contract
was added. Assumptions and Final are unchanged.

The hundred-and-sixth full validation passed: 3491 build jobs and 15362 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 107 — honest transcript as the revealed map

Classified continuation 106 as progress and took its audit (3491 jobs,
15362 declarations) as the starting state. Composed the translation
lemmas with the revealed bijection: the honest triple is the revealed
map of the hidden vector, and a uniform hidden vector makes it uniform
and witness-independent.

Added Proofs/TranscriptRevealed. Build fixes: an ill-typed auxiliary
definition removed, projections reduced before rewriting, unused simp
arguments and a redundant closing tactic removed.

Next: the hashed-coefficient pads (packed layer constants of the
randomness coordinates) and the PRG hypothesis. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The hundred-and-seventh full validation passed: 3492 build jobs and 15368 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 108 — pads on the hashed coefficients

Classified continuation 107 as progress and took its audit (3492 jobs,
15368 declarations) as the starting state. Proved the padding of the
hashed coefficients by packed layer constants and their uniformity in
the submitted field.

Added Proofs/HashedPads. Build fixes: the field-instance section split
from the ring section (the hashed tuple needs a field), and a function
rewrite replaced by a calc step.

Next: the per-execution corrections as translations by each execution's
hidden vector, then the joint pad statement. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The hundred-and-eighth full validation passed: 3493 build jobs and 15374 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 109 — corrections as translations

Classified continuation 108 as progress and took its audit (3493 jobs,
15374 declarations) as the starting state. Proved the per-execution
corrections' translation structure in each execution's hidden vector.

Added Proofs/CorrectionTranslation. Build fixes: the commit module
imported for the transmitted corrections, and that lemma specialized to
the binary field as the transmitted corrections are.

Next: the joint pad statement across executions and the top coefficient's
witness independence. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-ninth full validation passed: 3494 build jobs and 15379 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 110 — top coefficient from slopes

Classified continuation 109 as progress and took its audit (3494 jobs,
15379 declarations) as the starting state. Proved that the top
coefficient of the prover arithmetic depends only on the selector slopes
and the mask's top coefficient, for at least three mux layers.

Added Proofs/TopCoefficient. Build fixes: dependent rewrites of the
coefficient index avoided (an explicit index equation and a rewrite in a
hypothesis instead), summands beta-reduced before rewriting, and the
Mathlib product-coefficient lemma under degree bounds used.

Next: the assembled zero-knowledge statement (joint pads under an
explicit PRG hypothesis). No assumption, source repair or contract was
added. Assumptions and Final are unchanged.

The hundred-and-tenth full validation passed: 3495 build jobs and 15406 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 111 — the revealed view as a bijection

Classified continuation 110 as progress and took its audit (3495 jobs,
15406 declarations) as the starting state. Assembled the revealed view
(witness correction, packed layer constants, plain check) as an affine
bijection of execution zero's hidden vector over the submitted field.

Added Proofs/ViewBijection. Build fix: the explicit-form proof written
with definitional unfolding steps instead of simp lemmas on the
equivalence combinators.

Next: the honest signer's hashed tuple and auxiliary data as functions
of the view, the PRG hypothesis and the assembled gap. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-eleventh full validation passed: 3496 build jobs and 15416 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 112 — hashed coefficients from the view

Classified continuation 111 as progress and took its audit (3496 jobs,
15416 declarations) as the starting state. Proved the single-layer form
of the mask coefficients below the top for the honest randomness lines
and the split of each layer into the hidden party's and the others'.

Added Proofs/HashedView. Build fixes: a dependent if for the slope term
(its layer index needs the positivity of k), and the single-layer
collapse proved inline with the goal's own decidability instances rather
than through a classical lemma.

Next: the assembled honest-view statement and the PRG hypothesis. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-twelfth full validation passed: 3497 build jobs and 15427 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 113 — the honest view

Classified continuation 112 as progress and took its audit (3497 jobs,
15427 declarations) as the starting state. Assembled the honest signer's
hashed coefficients below the top and auxiliary components in terms of
execution zero's hidden vector.

Added Proofs/HonestView. Build fix: the final associativity closed by
ring.

Next: the assembled gap statement under an explicit PRG hypothesis. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-thirteenth full validation passed: 3498 build jobs and 15431 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 114 — honest data uniform under a uniform hidden vector

Classified continuation 113 as progress and took its audit (3498 jobs,
15431 declarations) as the starting state. Proved that the honest
revealed data is a bijective image of the view and hence uniform and
witness-independent under a uniform hidden vector.

Added Proofs/HonestViewUniform. No build fixes were needed.

Next: the PRG hypothesis as an explicit statement on the random table's
row of a uniform seed, then the assembled gap. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The hundred-and-fourteenth full validation passed: 3499 build jobs and 15442 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 115 — the PRG hypothesis

Classified continuation 114 as progress and took its audit (3499 jobs,
15442 declarations) as the starting state. Stated the PRG hypothesis as
a named predicate on the random table's row of a uniform seed and
derived the honest data's uniformity over the hidden seed under it.

Added Proofs/PRGHypothesis. No build fixes were needed.

Next: the committed signature data as the honest data of the hidden
seed, then the simulated transcript's distribution and the gap. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-fifteenth full validation passed: 3500 build jobs and 15450 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 116 — committed signature data as the honest data

Classified continuation 115 as progress and took its audit (3500 jobs,
15450 declarations) as the starting state. Linked the committed
arithmetic's hashed coefficients below the top and auxiliary components
to the honest data map.

Added Proofs/SignatureData. Build fixes: unused implicit section
parameters supplied at use sites, the dependent if split by cases, and
the layer bits unfolded before the ring normalization.

Next: lifting to the executed commitment and the prepared state, then
the simulated transcript and the gap. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The hundred-and-sixteenth full validation passed: 3501 build jobs and 15467 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 117 — the prepared state's data

Classified continuation 116 as progress and took its audit (3501 jobs,
15467 declarations) as the starting state. Lifted the arithmetic link to
the executed commitment and the prepared signing state.

Added Proofs/PreparedData. Build fixes: the shared signing proofs
imported (the signing state lives there), an unused hypothesis dropped.

Next: compose with the honest data map over the hidden seed, then the
simulated transcript and the gap. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The hundred-and-seventeenth full validation passed: 3502 build jobs and 15469 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 118 — the prepared state's data as honest data

Classified continuation 117 as progress and took its audit (3502 jobs,
15469 declarations) as the starting state. Composed the prepared state's
data with the arithmetic link to the honest data map of the hidden
seed's PRG vector.

Added Proofs/PreparedHonestData. Build fix: the degree relation
supplied to the hashed index bound.

Next: the simulated transcript's data in the same form and the gap over
the signing game. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-eighteenth full validation passed: 3503 build jobs and 15471 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 119 — data-level simulation step

Classified continuation 118 as progress and took its audit (3503 jobs,
15471 declarations) as the starting state. Stated and proved the
simulation step at the data level: the real and fake signers' revealed
data coincide in distribution under a uniform hidden vector, and over a
uniform hidden seed under the PRG hypothesis.

Added Proofs/DataSimulation. No build fixes were needed.

Next: the hidden leaf seed's uniformity as a named hypothesis or an
ideal-cipher lemma, then the lifting to the signing game. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-nineteenth full validation passed: 3504 build jobs and 15475 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 120 — fresh-key encryption uniform

Classified continuation 119 as progress and took its audit (3504 jobs,
15475 declarations) as the starting state. Proved that encryption under a
key never used in the ideal cipher's history is uniform over all blocks,
from the existing fresh-input uniformity over unused outputs.

Added Proofs/FreshKeyUniform. Build fix: the finiteness and decidability
instances scoped to the theorems that need them.

Next: the hidden leaf seed as a fresh-key encryption of its parent, the
accounting of the unused-key event, and the lifting of the data-level
simulation to the signing game. No assumption, source repair or contract
was added. Assumptions and Final are unchanged.

The hundred-and-twentieth full validation passed: 3505 build jobs and 15480 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 121 — leaf seed uniform through the layout

Classified continuation 120 as progress and took its audit (3505 jobs,
15480 declarations) as the starting state. Proved the per-call
uniformity of an expanded seed under a fresh parent key through an
output-uniform layout.

Added Proofs/LeafSeedUniform. No build fixes were needed.

Next: the truncated layout's output uniformity, the fresh-parent-key
event's accounting, and the lifting to the signing game. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-twenty-first full validation passed: 3506 build jobs and 15484 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 122 — the truncated layout is output-uniform

Classified continuation 121 as progress and took its audit (3506 jobs,
15484 declarations) as the starting state. Proved the Category III
layout's output uniformity from the uniform-restriction lemma.

Added Proofs/TruncatedLayoutUniform. Build fix: the embedding's
injectivity proved through an intermediate value equation.

Next: the fresh-parent-key event in the commitment program's trace and
the lifting to the signing game. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The hundred-and-twenty-second full validation passed: 3507 build jobs and 15490 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 123 — corrections as one-time pads

Classified continuation 122 as progress and took its audit (3507 jobs,
15490 declarations) as the starting state. Proved that each positive
execution's correction is a uniform pad of its hidden vector.

Added Proofs/CorrectionUniform. Build fix: unused finiteness instances
omitted from the deterministic equation.

Next: the joint pad statement across executions and the lifting to the
signing game. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-twenty-third full validation passed: 3508 build jobs and 15494 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 124 — joint pads over all executions

Classified continuation 123 as progress and took its audit (3508 jobs,
15494 declarations) as the starting state. Assembled the pads of all
executions into one triangular bijection and proved the joint
transcript uniform under independent uniform hidden vectors.

Added Proofs/JointPads. No build fixes were needed.

Next: the game-level lift of the hidden-share step. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-twenty-fourth full validation passed: 3509 build jobs and 15502 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 125 — leaf seed uniform under the posterior family

Classified continuation 124 as progress and took its audit (3509 jobs,
15502 declarations) as the starting state. Restated the fresh-parent leaf
uniformity for the posterior family of the game's fixed-family model.

Added Proofs/PosteriorLeafUniform. Build fix: an unused instance
omitted.

Next: the hidden leaf's expansion in the commitment program's trace and
the fresh-parent-key event. No assumption, source repair or contract was
added. Assumptions and Final are unchanged.

The hundred-and-twenty-fifth full validation passed: 3510 build jobs and 15504 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 126 — the hidden leaf in the seed tree

Classified continuation 125 as progress and took its audit (3510 jobs,
15504 declarations) as the starting state. Proved that a tree node is the
cipher image of its parent and is determined by any family consistent
with a history recording its ancestry; added a simulation-gap status
section to the README.

Added Proofs/HiddenLeafNode. Build fixes: the node's side as a decided
proposition rewritten by its decision, the ancestry heredity through the
power-of-two division identity, and the root case unfolded on each side
separately.

Next: the recorded ancestry from the commitment program's cipher history
and the fresh-parent-key event. No assumption, source repair or contract
was added. Assumptions and Final are unchanged.

The hundred-and-twenty-sixth full validation passed: 3511 build jobs and 15522 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 127 — the tree expansion's recorded entries

Classified continuation 126 as progress and took its audit (3511 jobs,
15522 declarations) as the starting state. Proved that the commitment's
tree expansion records every internal node's expansion entries and hence
every expanded node's ancestry.

Added Proofs/TreeEntries. Build fixes: the seed type qualified, and a
destructuring step re-indented.

Next: the fresh-parent-key event and its accounting. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-twenty-seventh full validation passed: 3512 build jobs and 15529 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 128 — the hidden-share step under the posterior family

Classified continuation 127 as progress and took its audit (3512 jobs,
15529 declarations) as the starting state. Assembled the per-signature
hidden-share step as a conditional theorem under the posterior family,
with the fresh-parent-key event and the PRG hypothesis explicit.

Added Proofs/HiddenShareStep. No build fixes were needed.

Next: the fresh-parent-key event's probability for a uniform parent and
the history prefix at the expansion call. No assumption, source repair
or contract was added. Assumptions and Final are unchanged.

The hundred-and-twenty-eighth full validation passed: 3513 build jobs and 15531 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 129 — the fresh-parent-key probability

Classified continuation 128 as progress and took its audit (3513 jobs,
15531 declarations) as the starting state. Bounded the fresh-parent-key
event's probability for a uniform parent by the history's length over
the number of seeds.

Added Proofs/FreshKeyProbability. Build fixes: a finiteness instance on
keys for the subtype cardinality, and the mapped length closed by simp.

Next: the history prefix at the expansion call and the path recursion
from the root. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-twenty-ninth full validation passed: 3514 build jobs and 15533 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 130 — injective layout keys

Classified continuation 129 as progress and took its audit (3514 jobs,
15533 declarations) as the starting state. Discharged the layout
hypotheses of the hidden-share step for both submitted layouts and
updated the simulation-gap status.

Added Proofs/LayoutKeyInjective. No build fixes were needed.

Next: the path recursion from the root or the signing procedures'
coupling. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-thirtieth full validation passed: 3515 build jobs and 15539 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 131 — fresh hash answers uniform

Classified continuation 130 as progress and took its audit (3515 jobs,
15539 declarations) as the starting state. Proved the random-oracle
facts needed by the signing procedures' coupling.

Added Proofs/FreshHashUniform. Build fix: the stored-answer case closed
by the pure-map lemma.

Next: the signing procedures' coupling. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The hundred-and-thirty-first full validation passed: 3516 build jobs and 15543 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 132 — the public hash answer at a fresh input

Classified continuation 131 as progress and took its audit (3516 jobs,
15543 declarations) as the starting state. Proved the shared world's
public hash answer uniform at a fresh input through the one-step run.

Added Proofs/PublicHashFresh. Build fixes: the domain-separation
namespace opened for the bit type, the one-step run's bind congruence
made explicit with the oracle's decidability instances identified by
subsingleton elimination, and the terminal pure maps reduced.

Next: the signing procedures' coupling, pending the user's direction on
continuing the trace-level argument versus accepting the explicit
hypotheses. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-thirty-second full validation passed: 3517 build jobs and 15559 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 133 — the public mask answer at a fresh input

Classified continuation 132 as progress and took its audit (3517 jobs,
15559 declarations) as the starting state. Proved the mask case of the
public oracle's fresh-answer uniformity.

Added Proofs/PublicMaskFresh. No build fixes were needed.

Next: the signing procedures' coupling, pending the user's direction. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-thirty-third full validation passed: 3518 build jobs and 15562 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 134 — single-step runs

Classified continuation 133 as progress and took its audit (3518 jobs,
15562 declarations) as the starting state. Proved the elementary run
facts of the shared world.

Added Proofs/SingleStepRuns. Build fix: the pure maps reduced (which
also closes the world's structure equality).

Next: the signing procedures' coupling, pending the user's direction.
No assumption, source repair or contract was added. Assumptions and
Final are unchanged.

The hundred-and-thirty-fourth full validation passed: 3519 build jobs and 15572 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 135 — fuel monotonicity of the traced run

Classified continuation 134 as progress and took its audit (3519 jobs,
15572 declarations) as the starting state. Recorded the signing-coupling
checklist in the plan and proved the fuel monotonicity of the traced run
for bounded programs.

Added Proofs/RunFuel. Build fixes: the trace log's entry type named
from the random-oracle trace module, the stepping procedure kept folded
through a reflexive step equation so the induction hypothesis matches,
and an unused decidability instance dropped.

Next: the run-splitting lemma over a program bind. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The hundred-and-thirty-fifth full validation passed: 3520 build jobs and 15597 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 136 — the run-splitting lemma

Classified continuation 135 as progress and took its audit (3520 jobs,
15597 declarations) as the starting state. Proved the run-splitting
lemma for the traced run of a program bind.

Added Proofs/RunBind. Build fixes: the program bind qualified against
the monad bind, the bind reductions and fuel equations rewritten
explicitly, and the stepping procedure kept folded.

Next: the commitment program's prefix/tail decomposition. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-thirty-sixth full validation passed: 3521 build jobs and 15609 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 137 — the commitment program's decomposition

Classified continuation 136 as progress and took its audit (3521 jobs,
15609 declarations) as the starting state. Decomposed the commitment
program into a witness-free prefix and a witness-dependent tail.

Added Proofs/CommitDecomposition. Build fixes: generic bind variables
renamed to avoid shadowing the digest type, the chain-inputs namespace
opened for the outer string and mask input, and two redundant closing
steps removed (the congruence step closes the remaining goals).

Next: the split runs of the honest and simulated commitments and the
lines-query freshness. No assumption, source repair or contract was
added. Assumptions and Final are unchanged.

The hundred-and-thirty-seventh full validation passed (after a proof fix and
relaunch): 3522 build jobs and 15614 project declarations, with only propext,
Classical.choice and Quot.sound transitively. Checked the new module import
and index entry, standalone specification separation and exactly three
final discrepancy statements. No placeholder, cryptographic axiom or
unchecked shortcut was introduced. Assumptions and Final are unchanged. The
persistent goal remains active and the full signature reduction remains
incomplete.

## Continuation 138 — the commitment's split run

Classified continuation 137 as progress and took its audit (3522 jobs,
15614 declarations) as the starting state. Bounded the prefix and tail
and split the commitment's run.

Added Proofs/CommitSplitRun. No build fixes were needed.

Next: the tail's lines query as a fresh hash answer and the equal
distribution of the two signers' tails given the prefix. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-thirty-eighth full validation passed: 3523 build jobs and 15622 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 139 — the tail's lines digest

Classified continuation 138 as progress and took its audit (3523 jobs,
15622 declarations) as the starting state. Proved that the tail's lines
digest is uniform at a fresh lines input, whatever the witness.

Added Proofs/TailLinesDigest. Build fixes: the oracle's decidability
instances identified by subsingleton elimination after the bind
congruence, and an unused simp argument dropped.

Next: the lines-input freshness event and the full tail data. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-thirty-ninth full validation passed: 3524 build jobs and 15639 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 140 — the lines query's mentions

Classified continuation 139 as progress and took its audit (3524 jobs,
15639 declarations) as the starting state. Proved that the lines query
mentions its auxiliary digest and differs from the mask input.

Added Proofs/LinesMention. No build fixes were needed.

Next: a stored lines input as a mention event through the trace
invariants. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-fortieth full validation passed: 3525 build jobs and 15643 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 141 — byte-prefix separation of the chain queries

Classified continuation 140 as progress and took its audit (3525 jobs,
15643 declarations) as the starting state. Proved the byte-prefix
separation of the lines query from the prefix's hash queries.

Added Proofs/QueryPrefixes. Build fixes: the byte injectivity proved
through the injectivity of the list-of-function construction and an
explicit power bound, and the commitments type qualified.

Next: the prefix run's trace shape and the stored-lines-input mention
argument. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-forty-first full validation passed: 3526 build jobs and 15649 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 142 — a fresh hash step at the support level

Classified continuation 141 as progress and took its audit (3526 jobs,
15649 declarations) as the starting state. Proved the support-level form
of a fresh hash step of the traced run.

Added Proofs/ThreeHashRun. Build fix: unused finiteness instances
omitted from the mark lemma.

Next: the three-step iteration and the stored-lines-input mention
argument. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-forty-second full validation passed: 3527 build jobs and 15658 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 143 — three fresh hash queries' trace shape

Classified continuation 142 as progress and took its audit (3527 jobs,
15658 declarations) as the starting state. Iterated the fresh hash step
to the trace shape of three consecutive fresh queries.

Added Proofs/ThreeHashShape. No build fixes were needed.

Next: the prefix's final queries in this shape and the stored-lines-input
mention argument. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-forty-third full validation passed: 3528 build jobs and 15661 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 144 — a stored lines input is a mention event

Classified continuation 143 as progress and took its audit (3528 jobs,
15661 declarations) as the starting state. Proved that a stored lines
input, under the prefix's trace shape, raises the charged mention event.

Added Proofs/StoredLinesMention. No build fixes were needed.

Next: the application to the commitment prefix's run. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-forty-fourth full validation passed: 3529 build jobs and 15663 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 145 — the lines input after the prefix

Classified continuation 144 as progress and took its audit (3529 jobs,
15663 declarations) as the starting state. Applied the three-query shape
and the stored-input mention argument to the commitment prefix's last
three queries.

Added Proofs/PrefixLinesFresh. Build fixes: the oracle-chain namespace
opened for the ordering predicates, and the freshness hypotheses stated
with the classical decidability instance used by the shape lemma.

Next: the three queries' freshness as charged events and the prefix's
head split. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-forty-fifth full validation passed: 3530 build jobs and 15667 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 146 — the prefix's head split

Classified continuation 145 as progress and took its audit (3530 jobs,
15667 declarations) as the starting state. Split the prefix into its
head and its last three queries and split its run accordingly.

Added Proofs/PrefixHeadSplit. Build fix: the head-split equation closed
by reflexivity after the associativity rewrites.

Next: the three queries' freshness as charged events. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-forty-sixth full validation passed: 3531 build jobs and 15676 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 147 — the lines input after a whole prefix run

Classified continuation 146 as progress and took its audit (3531 jobs,
15676 declarations) as the starting state. Composed the head split with
the three-query mention argument through the continuation's support.

Added Proofs/PrefixLinesFreshRun. No build fixes were needed.

Next: the three queries' freshness as charged events and the head's run
invariants from the starting world. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The hundred-and-forty-seventh full validation passed: 3532 build jobs and 15678 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 148 — the auxiliary and mask inputs' freshness

Classified continuation 147 as progress and took its audit (3532 jobs,
15678 declarations) as the starting state. Reduced the auxiliary and
mask inputs' freshness to the charged mention event.

Added Proofs/ChainFresh. No build fixes were needed.

Next: the outer input's freshness through the head's trace shape, then
the assembly of the per-signature lines-input freshness. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-forty-eighth full validation passed: 3533 build jobs and 15684 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 149 — splitting a collection at its last call

Classified continuation 148 as progress and took its audit (3533 jobs,
15684 declarations) as the starting state. Proved the collector's split
at its last call.

Added Proofs/CollectLast. No build fixes were needed.

Next: the head's split at the last row query and the outer input's
mention argument. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-forty-ninth full validation passed: 3534 build jobs and 15688 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 150 — the outer input's freshness

Classified continuation 149 as progress and took its audit (3534 jobs,
15688 declarations) as the starting state. Reduced the outer input's
freshness to the mention event and split the row hashes' collection at
its last execution.

Added Proofs/OuterFresh. Build fixes: the last-query split restated
without a let binding so the nonemptiness side condition elaborates, and
the last execution index named explicitly instead of a placeholder.

Next: the head's run split at the last row query and the assembly of the
per-signature freshness statement. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The hundred-and-fiftieth full validation passed: 3535 build jobs and 15695 project
declarations, with only propext, Classical.choice and Quot.sound transitively.
Checked the new module import and index entry, standalone specification
separation and exactly three final discrepancy statements. No placeholder,
cryptographic axiom or unchecked shortcut was introduced. Assumptions and
Final are unchanged. The persistent goal remains active and the full
signature reduction remains incomplete.

## Continuation 151 — the head split at its last row query

Classified continuation 150 as progress and took its audit (3535 jobs,
15695 declarations) as the starting state. Split the head at its last
row query.

Added Proofs/HeadLastSplit. Build fixes: a binder renamed away from a
keyword, the split equation closed through two further associativity
rewrites, and the redundant tactics after the closing congruence
removed.

Next: the initial part's bound and the last row query's fresh-run shape
with the outer string's mention argument. No assumption, source repair
or contract was added. Assumptions and Final are unchanged.

The hundred-and-fifty-first full validation passed: 3536 build jobs and 15698 project declarations audited, every transitive axiom allowlisted.

## Continuation 152 — the head's run split at its last row query

Classified continuation 151 as progress and took its audit (3536 jobs,
15698 declarations) as the starting state. Ran the head split: bounds,
run split, fresh last-row shape and the outer string's mention event
after the head.

Added Proofs/HeadLastRun. Build fix: the hash-table conjunct of the
fresh-run shape needed the classical and list decidable-equality
instances identified by extensionality and subsingleton elimination.

Next: assemble the per-signature freshness statement (every chain query
and the lines query fresh when asked, under the negation of the charged
mention event) from the head, prefix-tail and tail splits. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-fifty-second full validation passed: 3537 build jobs and 15707 project declarations audited, every transitive axiom allowlisted.

## Continuation 153 — the mention event persists along a run

Classified continuation 152 as progress and took its audit (3537 jobs,
15707 declarations) as the starting state. Proved that a run's trace
extends its starting log and that prefix events persist along runs and
continuations.

Added Proofs/TraceSuffix. Build fix: two omit clauses removed, since the
traced run needs the digest's finiteness and inhabitation instances. The
registration step first merged the new import and index lines with their
neighbours; the validation was stopped, both files repaired to one entry
per line, and the validation relaunched.

Next: the per-signature freshness assembly as a disjunction (mention event
on the final trace, or every chain query and the lines query fresh when
asked), stepping through the outer, auxiliary and mask queries with the
stored-mention lemmas and lifting each event by the suffix lemmas. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-fifty-third full validation passed: 3538 build jobs and 15717 project declarations audited, every transitive axiom allowlisted.

## Continuation 154 — the prefix's last three queries: event or fresh shape

Classified continuation 153 as progress and took its audit (3538 jobs,
15717 declarations) as the starting state. Proved the event-or-shape
disjunction for the prefix's last three queries.

Added Proofs/PrefixTailOrMention. It built without fixes. The first
validation launch preceded a failed registration step; it was stopped,
the import and index entries added, and the validation relaunched.

Next: supply the outer string's stored case from the head's run (the
last-row shape) and assemble the head and prefix-tail runs into one
per-signature statement, then the tail's lines query. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-fifty-fourth full validation passed: 3539 build jobs and 15722 project declarations audited, every transitive axiom allowlisted.

## Continuation 155 — the prefix run: mention event or fresh lines input

Classified continuation 154 as progress and took its audit (3539 jobs,
15722 declarations) as the starting state. Assembled the prefix run's
event-or-fresh statement from the head and prefix-tail splits.

Added Proofs/PrefixOrMention. Build fix: the commit-split namespace
opened for the prefix budget.

The last row query's freshness at the head's initial result is taken as
an explicit hypothesis; it is the named candidate term for the leaf
commitments' freshness and is recorded for a later bound. Next: the
tail's lines query under the disjunction (fresh lines digest uniform
unless the event), then the composition over the signing game. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-fifty-fifth full validation passed: 3540 build jobs and 15730 project declarations audited, every transitive axiom allowlisted.

## Continuation 156 — the commitment run's lines digest up to the event

Classified continuation 155 as progress and took its audit (3540 jobs,
15730 declarations) as the starting state. Carried the prefix's
event-or-fresh statement into the tail's lines digest.

Added Proofs/CommitLinesEvent. Build fix: a deprecated multiplication
monotonicity lemma replaced by its current name.

Next: bound the prefix's mention-event probability by the mention trap
bound (prefix budget and mention-set size), and the last row query's
stored case. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-fifty-sixth full validation passed: 3541 build jobs and 15733 project declarations audited, every transitive axiom allowlisted.

## Continuation 157 — the prefix's mention-event probability

Classified continuation 156 as progress and took its audit (3541 jobs,
15733 declarations) as the starting state. Bounded the prefix's
mention-event probability and combined it with the lines-digest
comparison.

Added Proofs/PrefixMentionBound. Build fix: the addition monotonicity
lemma on the correct side.

Next: the last row query's stored case, or the composition over the
signing game with that condition as an explicit term. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-fifty-seventh full validation passed: 3542 build jobs and 15736 project declarations audited, every transitive axiom allowlisted.

## Continuation 158 — the prefix statement from the head's initial result

Classified continuation 157 as progress and took its audit (3542 jobs,
15736 declarations) as the starting state. Restated the prefix's
event-or-fresh statement from the head's initial result and proved the
bind bound with pointwise costs.

Added Proofs/PrefixFromHead. It built without fixes.

Next: name the row-stored event on the head's initial result and prove
the three-term lines-digest comparison (mention event, row-stored
event). No assumption, source repair or contract was added. Assumptions
and Final are unchanged.

The hundred-and-fifty-eighth full validation passed: 3543 build jobs and 15739 project declarations audited, every transitive axiom allowlisted.

## Continuation 159 — the commitment run's lines digest up to two events

Classified continuation 158 as progress and took its audit (3543 jobs,
15739 declarations) as the starting state. Named the row-stored and
mention events and proved the unconditional three-term lines-digest
comparison.

Added Proofs/CommitLinesEvents. Build fixes: the split equation needed
re-association under the binder; the bind bound's continuations had to
be given explicitly for the transitivity step; the pointwise and algebra
goals needed beta reduction before the case split and rewrites.

Next: the row-stored event's bound, or the composition over the signing
game with both events as explicit terms. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The hundred-and-fifty-ninth full validation passed: 3544 build jobs and 15748 project declarations audited, every transitive axiom allowlisted.

## Continuation 160 — status ledgers for the signing procedures' coupling

Classified continuation 159 as progress and took its audit (3544 jobs,
15748 declarations) as the starting state. Brought the README's
simulation-gap status up to the coupling results and recorded the named
row-stored event in the human-review ledger.

No module added. Next: the per-signature sign step (the honest scheme's
signing unfolded as the commitment run, the PIOP hash query and the
opening, against the simulated signing), to set up the composition over
the signing game. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-sixtieth full validation passed: 3544 build jobs and 15748 project declarations audited, every transitive axiom allowlisted.

## Continuation 161 — the per-signature sign step

Classified continuation 160 as progress and took its audit (3544 jobs,
15748 declarations) as the starting state. Unfolded the honest scheme's
signing and proved the fresh and stored query binding equations.

Added Proofs/SignStep. Build fixes: the preparation equation needed case
analysis on the run state (two match expressions over the same
discriminant), the game world's namespace and the hash input's type
annotation, the candidate opening disambiguated from the shared one, and
the final components projection closed by reflexivity.

Next: the honest and simulated signing compared at a fixed world,
with the input-present event named and the commitment run's witness
swap charged by the two coupling events. No assumption, source repair
or contract was added. Assumptions and Final are unchanged.

The hundred-and-sixty-first full validation passed: 3545 build jobs and 15755 project declarations audited, every transitive axiom allowlisted.

## Continuation 162 — the honest signing against its digest-first form

Classified continuation 161 as progress and took its audit (3545 jobs,
15755 declarations) as the starting state. Named the input-present event
and proved the honest signing within its probability of the digest-first
form.

Added Proofs/SignCompare. It built without fixes.

Next: the simulated signing as the digest-first form with a fake witness
and the recomputed coefficients, and the comparison of the two
digest-first forms. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-sixty-second full validation passed: 3546 build jobs and 15761 project declarations audited, every transitive axiom allowlisted.

## Continuation 163 — the simulated signing at a fixed witness

Classified continuation 162 as progress and took its audit (3546 jobs,
15761 declarations) as the starting state. Fixed the simulated signing's
witness and named the payload-consistency hypothesis.

Added Proofs/SimulatedWith. Build fix: the mixture equation closed at
the first congruence after the two commutations, so the later tactics
were removed.

Next: the digest-first honest signing against the fixed-witness
simulated signing, with the retry-failure event named and payload
consistency assumed. No assumption, source repair or contract was
added; the payload-consistency hypothesis is an explicit theorem
hypothesis. Assumptions and Final are unchanged.

The hundred-and-sixty-third full validation passed: 3547 build jobs and 15772 project declarations audited, every transitive axiom allowlisted.

## Continuation 164 — the bodies at a returned retry

Classified continuation 163 as progress and took its audit (3547 jobs,
15772 declarations) as the starting state. Proved the retry-return
certificates and the hash-input coincidence under payload consistency;
named the retry-failure event.

Added Proofs/DigestFirstBody. Build fixes: the candidate attempt needs
the field instance, the retry constructors written with their type
names, the attempt's field made explicit for instance resolution, and
unused instances omitted on the last lemma.

Next: the digest-first honest signing against the fixed-witness
simulated signing, pointwise over salt, root, run result and digest. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-sixty-fourth full validation passed: 3548 build jobs and 15778 project declarations audited, every transitive axiom allowlisted.

## Continuation 165 — the digest-first honest signing against the simulated one

Classified continuation 164 as progress and took its audit (3548 jobs,
15778 declarations) as the starting state. Proved the digest-first honest
signing within the retry-failure event of the fixed-witness simulated
signing.

Added Proofs/DigestFirstVsSimulated. Build fixes: the preparation
equation rewrites every occurrence at once, so a single rewrite; the
case split on the table lookup leaves the other side's match to reduce
with the split hypothesis.

Next: chain the honest signing to the simulated signing at the honest
witness, then the witness swap as an explicit term over the uniform fake
witness. No assumption, source repair or contract was added. Assumptions
and Final are unchanged.

The hundred-and-sixty-fifth full validation passed: 3549 build jobs and 15802 project declarations audited, every transitive axiom allowlisted.

## Continuation 166 — the honest signing against the simulated scheme's signing

Classified continuation 165 as progress and took its audit (3549 jobs,
15802 declarations) as the starting state. Chained the per-signature
steps into one statement with the witness swap as an explicit term.

Added Proofs/HonestToSimulated. Build fix: the addition monotonicity
lemma applied on the correct side in two steps.

Next: the composition over the signing game (the simulation gap of the
composed bound from the per-signature statement), or the witness swap's
bound. No assumption, source repair or contract was added; the swap term
is an explicit theorem hypothesis. Assumptions and Final are unchanged.

The hundred-and-sixty-sixth full validation passed: 3550 build jobs and 15805 project declarations audited, every transitive axiom allowlisted.

## Continuation 167 — the per-signature comparison under any continuation

Classified continuation 166 as progress and took its audit (3550 jobs,
15805 declarations) as the starting state. Restated the per-signature
bounds under any continuation, the form the game composition needs.

Added Proofs/SignComparePost. Build fix: a section variable included in
a lemma's argument list.

Next: the hybrid over signing calls of the game's run (two schemes
differing only in signing, with a per-call bound under continuations,
give a run bound linear in the fuel). No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The hundred-and-sixty-seventh full validation passed: 3551 build jobs and 15843 project declarations audited, every transitive axiom allowlisted.

## Continuation 168 — the hybrid over signing calls of the game's run

Classified continuation 167 as progress and took its audit (3551 jobs,
15843 declarations) as the starting state. Proved the run hybrid for
schemes agreeing off signing.

Added Proofs/RunHybrid. Build fixes: the continuation had to be pushed
through the binds inside each action branch after the case split, and
the addition monotonicity lemmas applied on the correct sides.

Next: the cut run, continuation, fresh branch and fork hybrids, then the
simulation gap. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-sixty-eighth full validation passed: 3552 build jobs and 15867 project declarations audited, every transitive axiom allowlisted.

## Continuation 169 — the hybrid over the replay experiments

Classified continuation 168 as progress and took its audit (3552 jobs,
15867 declarations) as the starting state. Extended the run hybrid to
the cut run, continuation, fresh branch, fork and cut experiment.

Added Proofs/CutHybrid. It built without fixes.

Next: the event experiments' hybrid, giving the simulation gap of the
composed bound from a uniform per-call bound. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The hundred-and-sixty-ninth full validation passed: 3553 build jobs and 15887 project declarations audited, every transitive axiom allowlisted.

## Continuation 170 — the hybrid over the event experiment

Classified continuation 169 as progress and took its audit (3553 jobs,
15887 declarations) as the starting state. Proved the event-experiment
hybrid with the snapshot's secret key and remaining fuel.

Added Proofs/EventHybrid. It built without fixes.

Next: the simulation gap of the composed bound from the per-signature
comparison under uniform event bounds. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The hundred-and-seventieth full validation passed: 3554 build jobs and 15904 project declarations audited, every transitive axiom allowlisted.

## Continuation 171 — the simulation gap of the composed bound

Classified continuation 170 as progress and took its audit (3554 jobs,
15904 declarations) as the starting state. Discharged the simulation-gap
hypothesis from explicit uniform per-call terms.

Added Proofs/SimulationGap. Build fixes: the honest and simulated event
experiments are equal to the generic one only up to their match
expressions, so the equalities were proved by case analysis rather than
by a change of goal; the closing alternatives were ordered so that an
unfolding that already closes the goal is not followed by a redundant
reflexivity, and the strict ring closer used.

Next: a corollary of the composed forgery bound with the simulation gap
in this explicit form, then the uniform bounds of the three terms. No
assumption, source repair or contract was added; the three uniform
bounds and payload consistency are explicit theorem hypotheses.
Assumptions and Final are unchanged.

The hundred-and-seventy-first full validation passed: 3555 build jobs and 15908 project declarations audited, every transitive axiom allowlisted.

## Continuation 172 — the composed forgery bound with the gap explicit

Classified continuation 171 as progress and took its audit (3555 jobs,
15908 declarations) as the starting state. Stated the composed forgery
bound with the simulation gap discharged from the three uniform terms.

Added Proofs/ForgeryBoundExplicit (its statement generated from the
composed bound's statement with the gap substituted). It built without
fixes.

Next: the uniform bounds, starting with the input-present event (a
hash-table support bound along the game and the lines digest's
freshness). No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-seventy-second full validation passed: 3556 build jobs and 15909 project declarations audited, every transitive axiom allowlisted.

## Continuation 173 — hash tables supported by at most n inputs

Classified continuation 172 as progress and took its audit (3556 jobs,
15909 declarations) as the starting state. Introduced the table-support
invariant and its preservation by queries and both signings.

Added Proofs/TableSupport. Build fix: the update rewrite with the local
decidable-equality instance found by resolution rather than passed
explicitly.

Next: the hybrids refined to an invariant on worlds (the table support
with a global budget), so the per-call bound may assume the invariant.
No assumption, source repair or contract was added. Assumptions and
Final are unchanged.

The hundred-and-seventy-third full validation passed: 3557 build jobs and 15919 project declarations audited, every transitive axiom allowlisted.

## Continuation 174 — the run hybrid under the table-support invariant

Classified continuation 173 as progress and took its audit (3557 jobs,
15919 declarations) as the starting state. Refined the run hybrid to the
table-support invariant.

Added Proofs/RunHybridInv. It built without fixes.

Next: the cut and fork hybrids under the invariant with the saved
snapshot's support bound. No assumption, source repair or contract was
added. Assumptions and Final are unchanged.

The hundred-and-seventy-fourth full validation passed: 3558 build jobs and 15932 project declarations audited, every transitive axiom allowlisted.

## Continuation 175 — the replay hybrids under the table-support invariant

Classified continuation 174 as progress and took its audit (3558 jobs,
15932 declarations) as the starting state. Carried the invariant through
the cut, continuation, branch, fork and cut experiment.

Added Proofs/CutHybridInv. It built without fixes.

Next: the event-experiment hybrid under the invariant and the simulation
gap with the per-call terms at supported worlds only. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-seventy-fifth full validation passed: 3559 build jobs and 15958 project declarations audited, every transitive axiom allowlisted.

## Continuation 176 — the simulation gap at supported worlds

Classified continuation 175 as progress and took its audit (3559 jobs,
15958 declarations) as the starting state. Restated the simulation gap
with the per-call terms at supported worlds only.

Added Proofs/SimulationGapInv. A placeholder written in the first draft
(for the honest signing's support growth at keys that are not good) was
replaced, before any build, by the general unfolding of the honest
signing at any public-key component; build fix: the shared signer's
namespace opened for the commitment program.

Next: the input-present bound at supported worlds from the lines
digest's freshness. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-seventy-sixth full validation passed: 3560 build jobs and 15966 project declarations audited, every transitive axiom allowlisted.

## Continuation 177 — the hybrids under an abstract counted invariant

Classified continuation 176 as progress and took its audit (3560 jobs,
15966 declarations) as the starting state. Generalized the invariant
hybrids to an abstract counted invariant, generated from the
table-support versions.

Added Proofs/RunHybridGen and Proofs/CutHybridGen. They built without
fixes.

Next: the simulation gap under the combined invariant of table support
and the shared world's well-formedness, so the input-present bound can
use the lines digest's freshness. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The hundred-and-seventy-seventh full validation passed: 3562 build jobs and 16005 project declarations audited, every transitive axiom allowlisted.

## Continuation 178 — the simulation gap under the combined invariant

Classified continuation 177 as progress and took its audit (3562 jobs,
16005 declarations) as the starting state. Instantiated the abstract
invariant with table support and shared-world well-formedness.

Added Proofs/SimulationGapGen. Build fixes: the preservation of
well-formedness proved directly for the candidate components (the shared
proof covers the shared components, which differ in the opening and the
verification), and unused field instances omitted on the pure invariant
lemmas.

Next: the input-present bound at worlds satisfying the combined
invariant. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-seventy-eighth full validation passed: 3563 build jobs and 16036 project declarations audited, every transitive axiom allowlisted.

## Continuation 179 — hitting a supported table and the tail's output

Classified continuation 178 as progress and took its audit (3563 jobs,
16036 declarations) as the starting state. Proved the counting lemma and
the tail's output distribution at a fresh lines input.

Added Proofs/HitCount. Build fixes: the cast inequality's target type
annotated, and the two-sided multiplication monotonicity lemma used.

Next: the input-present bound's assembly. No assumption, source repair
or contract was added. Assumptions and Final are unchanged.

The hundred-and-seventy-ninth full validation passed: 3564 build jobs and 16046 project declarations audited, every transitive axiom allowlisted.

## Continuation 180 — the input-present event over the tail

Classified continuation 179 as progress and took its audit (3564 jobs,
16046 declarations) as the starting state. Bounded the input-present
event over the tail at a fresh lines input.

Added Proofs/InputPresentTail. Build fixes: the pointwise goals of the
generic lemma beta-reduced before the case split, and an unused
decidable-equality instance dropped from the file's variables.

Next: the assembly over the prefix run. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The hundred-and-eightieth full validation passed: 3565 build jobs and 16062 project declarations audited, every transitive axiom allowlisted.

## Continuation 181 — the input-present bound

Classified continuation 180 as progress and took its audit (3565 jobs,
16062 declarations) as the starting state. Assembled the input-present
bound over the prefix run.

Added Proofs/InputPresentBound. Build fix: the last-index definition's
namespace opened.

Finding: the mention term is the prefix's cumulative mention event,
which includes mention events already present in the starting trace,
so the prefix trap bound gives it only up to that trace's event
indicator; a uniform per-call bound needs the mention event relative to
the starting log (the new entries' mentions), which the chain's
stored-mention lemmas do establish (the mentioning entry is one of the
signing's own fresh entries) but currently export only as the cumulative
event. Next: the relative mention event, its trap bound and the chain
restated with it. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-eighty-first full validation passed: 3566 build jobs and 16070 project declarations audited, every transitive axiom allowlisted.

## Continuation 182 — the mention event relative to a base log

Classified continuation 181 as progress and took its audit (3566 jobs,
16070 declarations) as the starting state. Defined the relative mention
event and proved its trap bound without the base's indicator.

Added Proofs/NewMention. Build fixes: a duplicate length rewrite
removed, the fresh-query lemma's namespace opened, a nonexistent map
congruence replaced by a support-wise bound on the mass at true, and
the event hypothesis beta-reduced before rewriting.

Next: the chain restated with the relative event. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The hundred-and-eighty-second full validation passed: 3567 build jobs and 16105 project declarations audited, every transitive axiom allowlisted.

## Continuation 183 — the chain's mention events relative to a base log

Classified continuation 182 as progress and took its audit (3567 jobs,
16105 declarations) as the starting state. Restated the chain's
stored-mention lemmas and the three-query statement with the relative
event.

Added Proofs/NewMentionChain. Build fix: the chain-inputs namespace
opened for the mention-membership lemmas.

Next: the head and prefix assembly with the relative event. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-eighty-third full validation passed: 3568 build jobs and 16120 project declarations audited, every transitive axiom allowlisted.

## Continuation 184 — the head and prefix statements with the relative event

Classified continuation 183 as progress and took its audit (3568 jobs,
16120 declarations) as the starting state. Carried the relative event
through the head and the prefix from a head-initial result.

Added Proofs/NewMentionPrefix. It built without fixes.

Next: the input-present bound with the relative mention term and the
term's indicator-free bound. No assumption, source repair or contract
was added. Assumptions and Final are unchanged.

The hundred-and-eighty-fourth full validation passed: 3569 build jobs and 16125 project declarations audited, every transitive axiom allowlisted.

## Continuation 185 — the input-present bound with the relative mention term

Classified continuation 184 as progress and took its audit (3569 jobs,
16125 declarations) as the starting state. Restated the input-present
bound with the relative mention term and bounded that term without the
indicator.

Added Proofs/InputPresentUniform (generated from the cumulative version
with the relative statements substituted). It built without fixes.

Next: the shared trace's length bound along runs and the uniform form of
the input-present bound in terms of a trace-length budget. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-eighty-fifth full validation passed: 3570 build jobs and 16131 project declarations audited, every transitive axiom allowlisted.

## Continuation 186 — trace growth and the uniform input-present bound

Classified continuation 185 as progress and took its audit (3570 jobs,
16131 declarations) as the starting state. Bounded a run's trace growth
and stated the input-present bound with a trace-length budget.

Added Proofs/TraceLength. Build fixes: two namespaces opened and the
addition monotonicity lemma on the correct side.

Next: the trace-length budget as an invariant component, which needs
the public oracle to advance the count in the generic hybrids. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-eighty-sixth full validation passed: 3571 build jobs and 16142 project declarations audited, every transitive axiom allowlisted.

## Continuation 187 — trace growth along the game's services

Classified continuation 186 as progress and took its audit (3571 jobs,
16142 declarations) as the starting state. Bounded the services' trace
growth and let the public oracle advance the generic hybrids' count.

Added Proofs/TraceGrowth; edited the three generic hybrid modules (the
public-oracle hypothesis advances the count, the query branches use the
advanced count). Build fixes: the honest unfolding's namespace opened
and an unused instance omitted before the doc comment.

Next: the combined invariant with the trace-length budget and the
simulation gap with the input-present term discharged uniformly. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-eighty-seventh full validation passed: 3572 build jobs and 16161 project declarations audited, every transitive axiom allowlisted.

## Continuation 188 — the simulation gap with the input-present term discharged

Classified continuation 187 as progress and took its audit (3572 jobs,
16161 declarations) as the starting state. Added the trace-length budget
to the counted invariant and discharged the input-present term of the
simulation gap uniformly.

Added Proofs/SimulationGapTrace (generated from the combined-invariant
gap theorem). Build fixes: the invariant's execution parameters made
explicit, an unused instance omitted on the pure lemmas, and the
input-present term's implicit parameters passed.

Next: the retry-failure bound or the row-stored bound, both tied to
pending decisions, or the witness-swap term's coupling. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-eighty-eighth full validation passed: 3573 build jobs and 16174 project declarations audited, every transitive axiom allowlisted.

## Continuation 189 — the bridge to the verifier's share matrix

Classified continuation 188 as progress and took its audit (3573 jobs,
16174 declarations) as the starting state. Proved the bridge between the
honest arithmetic and the verifier's share matrix for the
payload-consistency proof.

Added Proofs/PayloadBridge. Build fixes: the bits type's namespace opened
and the slope qualified against a root-level name.

Next: the prover polynomial's constant term vanishes for a solution
witness (the unitary check vanishes on binary at-most-one selectors),
then the assembly of payload consistency. No assumption, source repair
or contract was added. Assumptions and Final are unchanged.

The hundred-and-eighty-ninth full validation passed: 3574 build jobs and 16182 project declarations audited, every transitive axiom allowlisted.

## Continuation 190 — the constant term vanishes for a solution

Classified continuation 189 as progress and took its audit (3574 jobs,
16182 declarations) as the starting state. Proved the constant term's
vanishing for a solution witness.

Added Proofs/ConstantTermZero. It built without fixes.

Next: the assembly of payload consistency from the bridge, the degree
bound, the restored-equals-hashed criterion and the constant term. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-ninetieth full validation passed: 3575 build jobs and 16189 project declarations audited, every transitive axiom allowlisted.

## Continuation 191 — payload consistency

Classified continuation 190 as progress and took its audit (3575 jobs,
16189 declarations) as the starting state. Proved the payload-consistency
hypothesis from the bridge, the degree bound, the constant term and the
restored-equals-hashed criterion.

Added Proofs/PayloadConsistent. Build fixes: the witness-at-zero lemma's
namespace qualified and an unused instance dropped.

Next: the composed forgery bound with payload consistency discharged
(the candidate encoding and the higher-coefficient count as hypotheses),
then the remaining three terms. No assumption, source repair or contract
was added. Assumptions and Final are unchanged.

The hundred-and-ninety-first full validation passed: 3576 build jobs and 16194 project declarations audited, every transitive axiom allowlisted.

## Continuation 336 — the candidate encoding and the distributional bound

Classified continuation 335 as progress and took its audit (3753 jobs,
19149 declarations) as the starting state; verified this continuation's
registration (import lines, index entries). The user asked which
decisions to take and then said to continue; the defaults were: idealize
the challenge and batching expansions, state hardness over the key
generation's distribution, and fix a candidate serialization.

Examined the first. With the expansion a deterministic parameter of the
settings, the forger evaluates it at every counter without a query, so
the non-separation, zero-challenge and Schwartz–Zippel events are unions
over all counters: a balancedness hypothesis on the expansion would give
bounds carrying the counter range as a factor, and the retry bound needs
a joint statement over counters that per-counter balancedness does not
give. Discharging these terms therefore needs the expansion modelled as
a counted oracle of the digest and counter, which is a refactor of
`SigningSetting` and `VerifierSetting` across the reduction, not a local
proof. Recorded as the blocker in PLAN.md; the constants stay named.

Added Proofs/CandidateSerialization: a bit-per-coordinate encoding and
the two injectivity facts the final statement hypothesizes, and the
full-layout bound restated with the candidate encoding. Added
Proofs/DistributionalFinal: the bound averaged over an arbitrary
distribution of (setting, public key, witness sampler) under a
distributional hardness assumption, in mean-square form by linearity and,
for a finite index type, on the averaged advantage by the weighted
power-mean inequality. Algorithm 2's own law is not formed, because the
literal routine reads the undefined `B` and `x_A`; the distribution is a
parameter.

The three-hundred-and-thirty-sixth full validation passed: 3755 build jobs and 19173 project declarations audited, every transitive axiom allowlisted.

## Continuation 335 — the final statement at the full layout

Classified continuation 334 as progress and took its audit (3752 jobs,
19143 declarations) as the starting state; verified this continuation's
registration (import line, index entry). The layout facts are proved for
a layout variable equal to the full layout (so `subst` applies), and the
fiber bounds go through the subsingleton form, which is independent of
the subtype's decidability instance. Generation by substitution needed
word boundaries on the constant names (a bare replacement of `cKey` had
hit `publicKey`).

Added Proofs/FullLayoutFinal. The seven layout hypotheses of the generic
statement are discharged at the submitted full layout (Categories I and
V). Found while writing the review note that the settings' layout type
fixes the key and block width to λ, so the Category-III truncated layout
is outside the reduction's settings; recorded as a scope item.

The three-hundred-and-thirty-fifth full validation passed: 3753 build jobs and 19149 project declarations audited, every transitive axiom allowlisted.

## Continuation 334 — the simulator's seed-collision term discharged

Classified continuation 333 as progress and took its audit (3751 jobs,
19134 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Found on review that the
simulated seed-collision term of the final statement was never needed:
the real-experiment seed-collision bound (`seedCollision_le`) was already
used to discharge that event's gap hypothesis, with the simulated term
kept only as slack. Regenerated the chain from the per-event gaps with
the seed summand free, then instantiated it with the pair cost; the
generation is by substitution from the existing modules, and the proofs
are unchanged apart from the dropped gap argument.

Added Proofs/SeedTermDischarge. The named simulator constants are now
five (mask-after-fork, non-separation, zero-challenge, Schwartz–Zippel,
batching); the seed collision is a proved term.

The three-hundred-and-thirty-fourth full validation passed: 3752 build jobs and 19143 project declarations audited, every transitive axiom allowlisted.

## Continuation 333 — the hardness assumption on the instance

Classified continuation 332 as progress and took its audit (3750 jobs,
19132 declarations) as the starting state; verified this continuation's
registration (import line, index entry). The assumption is quantified
over every adversary at a fixed universe, so the module fixes the
adversary state's universe explicitly and the final statement instantiates
it. The proof is the previous final statement and monotonicity of the sum.

Added Proofs/InstanceHardness. Track A's right-hand side is now entirely
named constants and proved slacks. The remaining Track A items are the
hardness-distribution correspondence (a decision) and the
candidate-to-submission correspondence (blocked on Track B).

The three-hundred-and-thirty-third full validation passed: 3751 build jobs and 19134 project declarations audited, every transitive axiom allowlisted.

## Continuation 332 — review pass

Classified continuation 331 as progress and took its audit (3750 jobs,
19132 declarations) as the starting state. Checked the final statement's
hypothesis list against the theorem signature, the locations of the
named definitions (`OffHitAssembly.DataClose`, `LeafTermBound.LeafHide`,
`NamedSimulatorTerms.SimulatorTermBounds`, `ForgeryRSD.rsdSuccess`),
and the assumption interface (no axiom declared, `SDHardness` not
consumed). Rewrote the README status bullets (they described the state
at continuation 218), annotated the plan's open lines and the review
ledger's continuation-292 record, and extended the assumption
interface's docstring with the current state.

The user's milestone (slope term in-model, expansion-dependent terms
named, hardness term as syndrome decoding, review pass) is complete.
What remains open are the named hypotheses themselves and the human
correspondence obligations.

The three-hundred-and-thirty-second full validation passed: 3750 build jobs and 19132 project declarations audited, every transitive axiom allowlisted.

## Continuation 331 — the expansion-dependent simulator terms named

Classified continuation 330 as progress and took its audit (3749 jobs,
19130 declarations) as the starting state; verified this continuation's
registration (import line, index entry). The statement is generated
from the previous final statement by substituting the named constants
for the six simulator terms; the proof is the previous statement
followed by monotonicity of the sum.

Added Proofs/NamedSimulatorTerms. The user's milestone items (1)–(3)
are complete; next: the review pass.

The three-hundred-and-thirty-first full validation passed: 3750 build jobs and 19132 project declarations audited, every transitive axiom allowlisted.

## Continuation 330 — the hardness term as syndrome decoding

Classified continuation 329 as progress and took its audit (3746 jobs,
19070 declarations) as the starting state; verified this continuation's
registration (three import lines, three index entries). The mux tree's
reading with unitary selectors is proved layer by layer; the solution
vector is defined through the flattened-index equivalence so that the
systematic instance applied to it is the chunk sum of the selected
columns, which the zero residual identifies with the syndrome; its
weight is the number of chunks by the image of the selected addresses.

Added Proofs/MuxSelect, Proofs/SolutionRegular, Proofs/ForgeryRSD. The
hardness-term milestone is complete. Next: the expansion-dependent
simulator terms documented as named assumptions, then the review pass.

The three-hundred-and-thirtieth full validation passed: 3749 build jobs and 19130 project declarations audited, every transitive axiom allowlisted.

## Continuation 329 — the final statements with the slope term explicit

Classified continuation 328 as progress and took its audit (3745 jobs,
19066 declarations) as the starting state; verified this continuation's
registration (import line, index entry). The four final statements were
generated from the existing ones by substitution (the identity-layout
hypothesis after the security-parameter bound, the slope summand replaced
by the three constants), with the swap-closeness level proved from the
regenerated per-event gaps and the three real-experiment bounds.

Added Proofs/ForgerySlope. The slope-game milestone is complete. Next:
the hardness term (the extracted solution as a regular syndrome-decoding
solution of the systematic public instance), then the review pass.

The three-hundred-and-twenty-ninth full validation passed: 3746 build jobs and 19070 project declarations audited, every transitive axiom allowlisted.

## Continuation 328 — the composed bound's skeleton with the three events

Classified continuation 327 as progress and took its audit (3744 jobs,
19059 declarations) as the starting state; verified this continuation's
registration (import line, index entry). The live chain to the final
statement was traced (the fork-to-union step, the random-index step, the
skeleton, the split, the per-event gaps, the swap-closeness, data-level,
leaf-hiding and seed-collision final statements); the earlier composed
bounds are off that path. The regenerated theorems mirror the originals
with the identity-layout hypothesis and the three events; the union's
split keeps the nested shape and closes by ring.

Added Proofs/SlopeChainReduction. Next: the four final statements with
the slope term explicit, generated from the existing ones.

The three-hundred-and-twenty-eighth full validation passed: 3745 build jobs and 19066 project declarations audited, every transitive axiom allowlisted.

## Continuation 327 — the unseen match's bound in the real experiment

Classified continuation 326 as progress and took its audit (3743 jobs,
19004 declarations) as the starting state; verified this continuation's
registration (import line, index entry). The unseen event was extended
with the named seed's recorded halves (which the coverage already
provides through the queried seeds) so that it matches the shared game's
unseen event at the final world. Build fixes: the case analysis on the
claim, the attempt-history rewrite, the setting included in a lemma, a
shadowed name, and a finiteness-instance mismatch transported by a lemma.

Added Proofs/ForkUnseenBound. Next: the composed bound's regeneration
(the union event with the three events, the forgery skeleton, the split
and the per-event gaps, then the final statements).

The three-hundred-and-twenty-seventh full validation passed: 3744 build jobs and 19059 project declarations audited, every transitive axiom allowlisted.

## Continuation 326 — the witnessed pair's bound in the real experiment

Classified continuation 325 as progress and took its audit (3742 jobs,
18962 declarations) as the starting state; verified this continuation's
registration (import line, index entry). The proof was split into small
lemmas after a heartbeat timeout in the single calc (no heartbeat
setting was changed): the pointwise end-resampled bound, the union's
containment in the final history and the restored chain's pair mass.
Build fixes: the history-growth lemma's implicit world, the attempt's
world equation, the set-invariance of the witnessed predicate, the
match reductions in the event lemmas and the fiber bound's instance.

Added Proofs/ForkWitnessedBound. Next: the unseen match's bound (the
recorded entries added to the event), then the composed bound's
regeneration.

The three-hundred-and-twenty-sixth full validation passed: 3743 build jobs and 19004 project declarations audited, every transitive axiom allowlisted.

## Continuation 325 — the fork bound for family-dependent events

Classified continuation 324 as progress and took its audit (3741 jobs,
18954 declarations) as the starting state; verified this continuation's
registration (import line, index entry). The bound generalizes the
pair-mass fork bound: the event's family is the one resampled after the
first branch, which the second branch runs with; the checked first branch
is swapped out of that resampling (its embedded family is immaterial to
the event), the second branch is shifted from the empty-history base,
and the family is resampled once more at the end of the restored second
branch. Build fixes: a binder's type, the attempt-history equation and a
beta reduction.

Added Proofs/PairForkFamily. Next: the witnessed pair's bound through
it (the pair mass of the second branch's final history), then the
unseen match's bound (the unobserved-key bound at the final world).

The three-hundred-and-twenty-fifth full validation passed: 3742 build jobs and 18962 project declarations audited, every transitive axiom allowlisted.

## Continuation 324 — the mask trap's bound in the real experiment

Classified continuation 323 as progress and took its audit (3740 jobs,
18944 declarations) as the starting state; verified this continuation's
registration (import line, index entry). The per-run bound is the union
over execution pairs of the traced-run bound with the uniform mask trap's
per-query bound, with the trivial case when the trap already holds;
the service and prefix bounds follow the digest-collision pattern.
Build fixes: missing imports for the mean lemmas, the indicator lemmas'
namespace, the traced-run lemma's namespace and a cast in the
statement.

Added Proofs/SlopeTrapBound. Next: the family-dependent fork bound
(the plain fork's event at most the restored chain's mean of a predicate
under the family resampled at the end of the second branch), then the
witnessed pair and the unseen match through it.

The three-hundred-and-twenty-fourth full validation passed: 3741 build jobs and 18954 project declarations audited, every transitive axiom allowlisted.

## Continuation 323 — the fork-level coverage of the slope event

Classified continuation 322 as progress and took its audit (3739 jobs,
18923 declarations) as the starting state; verified this continuation's
registration (import line, index entry). The coverage mirrors the shared
slope game's `wins_covered` on the snapshot's trace: with the claim's
chain present before the stored mask's query (else a digest mention),
the mask's answer kills the nonzero slope difference (the trap); without
local collision-freeness the queried seeds give a witnessed pair or an
unseen match. Build fix: the rewrites of the claim's fields split by
hypothesis.

Added Proofs/SlopeCoverFork. Next: the trap's bound in the real
experiment through the service-bound framework, then the witnessed pair
and the unseen match through the end-resampled family.

The three-hundred-and-twenty-third full validation passed: 3740 build jobs and 18944 project declarations audited, every transitive axiom allowlisted.

## Continuation 322 — the stored-mask slope event from the good fork

Classified continuation 321 as progress and took its audit (3738 jobs,
18922 declarations) as the starting state; verified this continuation's
registration (import line, index entry). The existing extraction lemma
abstracted the mask existentially, so the fork-slope lemma, the
uniform-slope predicate and the extraction lemma were extended in place
to expose the stored mask, the auxiliary query, the equal commitments
and the salt equality (the previous versions are kept in the session
scratchpad; every downstream module rebuilt unchanged). Build fixes:
the completion lemmas' namespace, and the chain moved to the snapshot's
table where the reconstruction facts live.

Added Proofs/SlopeChainFork. Next: the fork-level coverage of the
stored-mask event by the mask trap on the snapshot's trace, the
witnessed pair and the unseen match, then their real-experiment bounds.

The three-hundred-and-twenty-second full validation passed: 3739 build jobs and 18923 project declarations audited, every transitive axiom allowlisted.

## Continuation 321 — the stored-mask slope event

Restarted the loop on the user's decision (the data-level closeness, the
leaf hiding and the retry bound stay as the named cryptographic
assumptions) toward the milestone: bound the slope-game simulator term
in-model, state the expansion-dependent events consistently as named
assumptions, tie the solver term to syndrome decoding, then review.
Classified continuation 320 as progress and took its audit (3737 jobs,
18905 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Surveyed the slope-game event:
its existential mask cannot be bounded, the stored mask is what the
extraction provides, and the shared slope game is formalized without a
layout, so the identity layout is taken as a hypothesis. Build fixes:
namespaces, the match reductions in the case analysis, rewriting the
body equations only in the hypothesis, and an unused universe variable.

Added Proofs/SlopeEventSetting. Next: expose the stored mask, the
chain's auxiliary query and the equal commitments in the fork-slope
lemma, the uniform-slope predicate and the extraction lemma, and derive
the stored-mask event from the good fork.

The three-hundred-and-twenty-first full validation passed: 3738 build jobs and 18922 project declarations audited, every transitive axiom allowlisted.

## Continuation 320 — the seed-collision bound and the final statement with its explicit slack

Classified continuation 319 as progress and took its audit (3734 jobs,
18869 declarations) as the starting state; verified this continuation's
registration (import lines, index entries). Drafted the witness and the
assembly during validation 319's window and compiled them after; the
final-statement module was generated from the previous one by
substitution. Build fixes: the involution unfolded at the inner
argument, the companion lemmas' namespace, the event's case analysis
with the hypotheses reverted and reintroduced in order, the
forgery-reduction namespace, the list-length lemma's name, the bind
split in the mean before the chain, and the adversary state's universe.

Added Proofs/SeedCollisionWitness, Proofs/SeedCollisionBound and
Proofs/ForgeryColl. The seed-collision bound is discharged; the final
statement's named hypotheses are the data-level closeness, the leaf
hiding, the retry bound and the layout, size and structural conditions.
Next: the leaf hiding and the data-level closeness. The tail's data
depends on a hidden leaf's block through the deterministic PRG parameter
(the random table of the commitment's arithmetic), so both are
statements about that parameter; the next step reads the named PRG
uniformity already in the data-level modules to see whether they reduce
to it by counting, with the continuation's recorded keys bounded.

The three-hundred-and-twentieth full validation passed: 3737 build jobs and 18905 project declarations audited, every transitive axiom allowlisted.

## Continuation 319 — the pair mass through the fork

Classified continuation 318 as progress and took its audit (3733 jobs,
18834 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted the fork module during
validation 318's window and compiled it after. Build fixes: the
attempt's world equation flipped, the shift lemmas instantiated at the
base snapshot and simplified before rewriting, the resampling membership
stated at the updated world, and the restore lemma's function given
explicitly.

Added Proofs/PairFork. Next: the seed-collision event as a witnessed pair
of the union history (the layout's transport of the seed-pairing
companion), the assembled bound over the random event experiment, and the
final statement with the explicit seed-collision slack.

The three-hundred-and-nineteenth full validation passed: 3734 build jobs and 18869 project declarations audited, every transitive axiom allowlisted.

## Continuation 318 — the pair mass through the oracles and the run

Classified continuation 317 as progress and took its audit (3731 jobs,
18783 declarations) as the starting state; verified this continuation's
registration (import lines, index entries). Drafted the oracle module
during validation 317's window and compiled both modules after it ended.
Build fixes: constant means under a dependent binder by `show`, the
budget lemma's namespace, the action match reduced before the mean
lemmas in every case, and the cut's finish case closed by simp.

Added Proofs/PairOracles and Proofs/PairRun. Next: the fork (the plain
fork's event through the common form and the shift law to the restored
second branch's final world), then the seed-collision event as a
witnessed pair of the union history and the assembled bound.

The three-hundred-and-eighteenth full validation passed: 3733 build jobs and 18834 project declarations audited, every transitive axiom allowlisted.

## Continuation 317 — the posterior pair mass

Classified continuation 316 as progress and took its audit (3730 jobs,
18772 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Surveyed the remaining named
hypotheses and chose the seed-collision bound as the next discharge: it
is a statement about the ideal cipher alone, with the single-run
paired-cipher bound and the resampling law already proved. Developed
against the compiler from the scratchpad. Build fixes: the mean-bind
and indicator lemmas' namespaces, the posterior-run rewriting with the
trace log fixed, and a decidable-instance mismatch in the fiber bound.

Added Proofs/PairMass. Next: the pair mass through the candidate
scheme's oracles, the game run, the cut and the fork, then the
seed-collision event as a witnessed pair of the union history.

The three-hundred-and-seventeenth full validation passed: 3731 build jobs and 18783 project declarations audited, every transitive axiom allowlisted.

## Continuation 316 — the leaf hiding and the leaf term

Classified continuation 315 as progress and took its audit (3727 jobs,
18734 declarations) as the starting state; verified this continuation's
registration (import lines, index entries). Developed against the
compiler from the scratchpad after validation 315 ended. Build fixes:
namespaces for the all-paths and own views, the leaf bound rewritten for
omega, the composed map reduced before the pointwise step, the sum of
means pushed inside by simp, the division step's form, and an unused
variable.

Added Proofs/LeafSliced, Proofs/LeafTermBound and Proofs/ForgeryHide.
The leaf-term bounds are discharged; the final statement's named
hypotheses are the data-level closeness, the leaf hiding, the retry bound,
the seed-collision bound and the layout, size and structural conditions.
Next: the content of the two data-level hypotheses (the PRG hypothesis
and the hidden share's uniformity), or the seed-collision bound.

The three-hundred-and-sixteenth full validation passed: 3730 build jobs and 18772 project declarations audited, every transitive axiom allowlisted.

## Continuation 315 — the off-hit closeness and the final statement under the data-level closeness

Classified continuation 314 as progress and took its audit (3725 jobs,
18721 declarations) as the starting state; verified this continuation's
registration (import lines, index entries). Developed against the
compiler from the scratchpad after validation 314 ended; the arithmetic
compiled after two cast fixes, the closeness on the first attempt, and
the final statement was generated from the previous final statement's
text with the closeness hypothesis replaced.

Added Proofs/OffHitClose and Proofs/ForgeryData. The pruned closeness is
discharged; the final statement's named hypotheses are the data-level
closeness, the leaf-term bounds, the retry bound, the seed-collision
bound and the layout, size and structural conditions. Next: the leaf-term
bounds (the continuation's queries against the hidden leaves' keys, from
the joint uniformity), then the data-level closeness's content.

The three-hundred-and-fifteenth full validation passed: 3727 build jobs and 18734 project declarations audited, every transitive axiom allowlisted.

## Continuation 314 — the off-hit chain assembled at fixed draws

Classified continuation 313 as progress and took its audit (3724 jobs,
18712 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 313,
compiled from the scratchpad after it ended. Build fixes: a type
annotation on the post-processing's output, and the unused instances
omitted.

Added Proofs/OffHitAssembly. Next: the arithmetic closing the off-hit
closeness (cancellation, division by the scaling, the uniform bound of
the scaling through the counted invariant, the distinct-tree term and
the averaging over the draws), giving `PrunedCloseOff` for the pre-call
hit with an explicit slack.

The three-hundred-and-fourteenth full validation passed: 3725 build jobs and 18721 project declarations audited, every transitive axiom allowlisted.

## Continuation 313 — the hidden tuple of the digest

Classified continuation 312 as progress and took its audit (3723 jobs,
18677 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Written after validation 312
ended. Build fixes: the attempt unfolded with its let-binding reduced
before the decision's rewrite, the case analysis carrying the
observation's equation, and an unused instance omitted.

Finding (recorded in the review ledger): the tuple sum's slack would
scale with the number of tuples; resolved since the hidden tuple is
determined by the digest. Added Proofs/TupleOfDigest. Next: the
composition into the off-hit closeness over the two tuples with the
plain mixture lower bound, the distinct-tree term and the data-level
closeness hypothesis.

The three-hundred-and-thirteenth full validation passed: 3724 build jobs and 18712 project declarations audited, every transitive axiom allowlisted.

## Continuation 312 — the off-hit chain's two sides

Classified continuation 311 as progress and took its audit (3722 jobs,
18665 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 311,
compiled from the scratchpad on the first attempt after it ended.

Added Proofs/OffHitChain. Next: the data-level closeness hypothesis as a
named definition on the mixing families, the arithmetic assembly of the
chain with the distinct-tree and hit terms, and the off-hit closeness
with its explicit slack.

The three-hundred-and-twelfth full validation passed: 3723 build jobs and 18677 project declarations audited, every transitive axiom allowlisted.

## Continuation 311 — the relative mixture bound and the off-hit setup

Classified continuation 310 as progress and took its audit (3720 jobs,
18643 declarations) as the starting state; verified this continuation's
registration (import lines, index entries). Written after validation 310
ended. Build fix: the inner mean's name qualified against the inner
product's, and unused instances omitted.

Finding on the way: the plain mixture lower bound, summed over the
tuples, multiplies its slack by the number of tuples; the bound relative
to the tuple probability avoids this. Added Proofs/LeafMixtureGen and
Proofs/OffHitSetup. Next: the composition into the off-hit closeness
with the data-level closeness hypothesis and the explicit slack.

The three-hundred-and-eleventh full validation passed: 3722 build jobs and 18665 project declarations audited, every transitive axiom allowlisted.

## Continuation 310 — the sliced data under the leaf exchange

Classified continuation 309 as progress and took its audit (3719 jobs,
18620 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 309
and developed against the compiler from the scratchpad after it ended.
Build fixes: the tree expansion's namespace, the leaf-count hypothesis
for the leaf's address bound, the expansion's leaf lemma applied up to
the leaf address's definition, and the record world closed by
reflexivity.

Added Proofs/SlicedInvariance. Next: the composition — the off-hit
pruned mean over the uniform draws as the posterior mean of the tuple
sum, the mixture bounds applied per tuple with the sliced data, the
data-level closeness hypothesis stated on the tuple-summed data at a
uniform block tuple, and the off-hit closeness with its explicit slack.

The three-hundred-and-tenth full validation passed: 3720 build jobs and 18643 project declarations audited, every transitive axiom allowlisted.

## Continuation 309 — the signing-data identity

Classified continuation 308 as progress and took its audit (3718 jobs,
18593 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 308
and developed against the compiler from the scratchpad after it ended.
Build fixes: the selection lemma takes the decidable-equality instance
from the call site, the constants are kept outside the means by a
dedicated lemma, and the final congruence closes the resampling of
worlds differing only in the family by reflexivity.

Added Proofs/SigningData. Next: the invariance of the sliced data under
the leaf exchange (the view by the phase-view exchange, the hit factor
and the pruned keys by the hidden-keys exchange, the tree with the
tuple's leaves replaced), then the data-level closeness hypothesis and
the composition into the off-hit closeness.

The three-hundred-and-ninth full validation passed: 3719 build jobs and 18620 project declarations audited, every transitive axiom allowlisted.

## Continuation 308 — the tail's run

Classified continuation 307 as progress and took its audit (3717 jobs,
18580 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 307,
built after it ended. Build fix: the generic section scoped so that its
digest type variable does not shadow the digest type.

Added Proofs/TailRun. Next: the signing's data function per hidden
tuple (the tail and the post-processing from the phase view and the tree
with the hidden leaves replaced), the identity of the off-hit pruned
mean with the tuple-summed data functions at the own blocks, and the
invariance of each under the leaf exchange.

The three-hundred-and-eighth full validation passed: 3718 build jobs and 18593 project declarations audited, every transitive axiom allowlisted.

## Continuation 307 — the uniform-mixture comparison

Classified continuation 306 as progress and took its audit (3716 jobs,
18569 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 306,
built after it ended. Build fixes: the sum over the tuple selected with
the indicator unfolded, and the complement's invariance by simp.

Added Proofs/LeafMixture, with the lower bound in additive form to avoid
truncated subtraction. Next: the signing's data as a function of the
phase view, the non-hidden tree and the hidden blocks (the tail and the
post-processing), so that the mixture comparison applies with the
data-level closeness hypothesis; then the composition into the off-hit
closeness.

The three-hundred-and-seventh full validation passed: 3717 build jobs and 18580 project declarations audited, every transitive axiom allowlisted.

## Continuation 306 — the joint block bound

Classified continuation 305 as progress and took its audit (3715 jobs,
18550 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 305,
built after it ended. Build fix: the label lemma proved by cases on the
distinctness and the fiber rather than by congruence.

Finding on the way: the joint bound of continuation 305 fixes the parent
seeds too, so summing it over the parents loses a factor of the number
of seeds per execution; the block bound keeps the parent only inside
each step. Added Proofs/LeafBlockBound. Next: the uniform-mixture
comparison (upper and lower bounds of a bounded function of the view and
the hidden blocks against its uniform mixture over the blocks), then the
tail's data and the composition.

The three-hundred-and-sixth full validation passed: 3716 build jobs and 18569 project declarations audited, every transitive axiom allowlisted.

## Continuation 305 — the joint uniformity of the hidden leaves

Classified continuation 304 as progress and took its audit (3714 jobs,
18526 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 304,
built after it ended. Build fixes: the signer setting's namespace, the
product bound's nonnegativity argument, the label characterisation
applied by simp under the decision, the leaf-count hypothesis included,
and the power step's association.

Added Proofs/LeafJointBound. Next: the two-sided form (summing the
one-sided bound over the targets) and the instantiation of the invariant
function with the all-executions phase view; then the tail's data.

The three-hundred-and-fifth full validation passed: 3715 build jobs and 18550 project declarations audited, every transitive axiom allowlisted.

## Continuation 304 — distinctness and the other leaves under the exchange

Classified continuation 303 as progress and took its audit (3713 jobs,
18508 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Written and built after
validation 303 ended. Build fixes: the parent key folded before the
transposition lemma, and the transposition's non-fixed-point lemma
applied with the classical decidability instance explicitly, since the
bit-vector type also has the finite-type instance.

Added Proofs/LeafExchangeDistinct. Next: the joint one-sided uniformity
of the hidden leaves' blocks by induction over the executions, with the
weight fixing the other executions' fibers.

The three-hundred-and-fourth full validation passed: 3714 build jobs and 18526 project declarations audited, every transitive axiom allowlisted.

## Continuation 303 — the all-executions phase view and the generic leaf bound

Classified continuation 302 as progress and took its audit (3712 jobs,
18490 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 302,
built after it ended. Build fixes: the leaf address's namespace, two
unused instances omitted, and the record world closed by reflexivity.

Added Proofs/PhaseViewLeafAll. Next: the joint one-sided uniformity of
the hidden leaves' blocks given the all-executions phase view (iterating
the generic bound over the executions with the other leaves' blocks fixed
in the weight), then the two-sided form and the tail's data.

The three-hundred-and-third full validation passed: 3713 build jobs and 18508 project declarations audited, every transitive axiom allowlisted.

## Continuation 302 — the posterior bound at the leaf

Classified continuation 301 as progress and took its audit (3711 jobs,
18480 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 301,
built after it ended. Build fixes: the phase view's world with the family
set rewritten to the world (a reflexivity lemma) and the final step closed
by definitional reflexivity.

Added Proofs/HonestLeafBound, mirroring the internal-node bound with the
phase view. Next: the two-sided form (summing the one-sided bound over
the blocks), the tail's data as a function of the phase view and the
seeds, and the data-level closeness hypothesis, composing into the
off-bad closeness.

The three-hundred-and-second full validation passed: 3712 build jobs and 18490 project declarations audited, every transitive axiom allowlisted.

## Continuation 301 — the phase view's leaf exchange

Classified continuation 300 as progress and took its audit (3710 jobs,
18457 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 300,
built after it ended. Build fixes: the shared scheme's namespace opened
for the world type, the map congruence closed through the pure
composition, an argument order, and the unused instances omitted.

Added Proofs/PhaseViewLeaf. Next: the posterior bound at the leaf
(`HonestNodeBound` mirrored with the phase view and the leaf's bound in
place of the internal-node bound and the post-processing invariance),
then the tail's data as a function of the phase view and the seeds.

The three-hundred-and-first full validation passed: 3711 build jobs and 18480 project declarations audited, every transitive axiom allowlisted.

## Continuation 300 — the commitment run's leaf exchange

Classified continuation 299 as progress and took its audit (3709 jobs,
18444 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 299,
built after it ended. Build fixes: the subset-prune case closed with the
derived non-membership, and the unused instances omitted.

Added Proofs/CommitRunLeaf. Next: the exchange as a bijection on the
candidate families of the pre-call history (`posterior_swapNode` in
`NodeExchange`), giving the hidden leaf's conditional law given the view
before the tail; then the tail's data as a function of the seeds with
the leaf set, and the data-level closeness hypothesis.

The three-hundredth full validation passed: 3710 build jobs and 18457 project declarations audited, every transitive axiom allowlisted.

## Continuation 299 — the commitment phase's leaf exchange

Classified continuation 298 as progress and took its audit (3708 jobs,
18427 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 298,
built after it ended. Build fixes: the leaf address rewritten to its
numeral form before the swap lemmas, the bound hypotheses included, and
the unused hypotheses and instances omitted.

Added Proofs/CommitPhaseLeaf. Next: the view under the leaf exchange
(the tree phase's pruned history from `treeHistory_exchanged`, the phase's
relabelled history pruned by `pruneAt_map`, the tail at the seeds with
the leaf set), then the exchange as a bijection on the candidate
families.

The two-hundred-and-ninety-ninth full validation passed: 3709 build jobs and 18444 project declarations audited, every transitive axiom allowlisted.

## Continuation 298 — programs under a key relabelling

Classified continuation 297 as progress and took its audit (3707 jobs,
18401 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 297,
built after it ended. Build fix: the pruned-history case where the key
is pruned, closed by the decided predicates rather than simp.

Added Proofs/ProgramRelabel, the generic tool for the leaf exchange: the
commitment phase at the exchanged leaf queries the new value's key, so it
is the original phase with one key relabelled, and the exchanged family
agrees through that relabelling at the leaves' keys. Next: the
commitment phase at a leaf under the exchange (`commitRest` as the leaf
commitments followed by the tail, the relabelled phase, the pruned
histories).

The two-hundred-and-ninety-eighth full validation passed: 3708 build jobs and 18427 project declarations audited, every transitive axiom allowlisted.

## Continuation 297 — the off-bad closeness

Classified continuation 296 as progress and took its audit (3707 jobs,
18397 declarations) as the starting state. Built on the first build.

Finding (recorded in the review ledger): the off-hit equality is not
exact, since the hidden seed is the output of a block distinct from its
sibling's and the output map need not be a bijection; the off-hit target
is a closeness. Studied the exchange machinery: it covers internal nodes
(the commitment rest reads internal nodes only in its final value), so
the hidden leaf needs its own exchange, under which the commitment
entries are relabelled to the new key (pruned in the view) and the PRG
share moves. Next: the leaf exchange of the tree (`TreeExchange` at a
leaf address), then of the commitment run and the own view.

The two-hundred-and-ninety-seventh full validation passed: 3707 build jobs and 18401 project declarations audited, every transitive axiom allowlisted.

## Continuation 296 — the hit term

Classified continuation 295 as progress and took its audit (3706 jobs,
18381 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 295,
built after it ended. Build fixes: three namespace references (the
grinding variant, the tree node, the program's family lemma) and the
unused-instance omissions on two lemmas.

Added Proofs/HitTerm: the pre-call hit term is bounded by the tree's
distinctness failure probability, reusing `bad_tree_le`. Next: the
off-hit pruned equality, from the commitment run's witness-free prefix
and witness-dependent tail with the PRG hypothesis; first the statement
of what the two signings share off the hit (the prefix's law) and where
the witness enters (the tail's lines query and result).

The two-hundred-and-ninety-sixth full validation passed: 3707 build jobs and 18397 project declarations audited, every transitive axiom allowlisted.

## Continuation 295 — the closeness over the uniform draws

Classified continuation 294 as progress and took its audit (3706 jobs,
18374 declarations) as the starting state. Drafted during validation 294,
built after it ended, on the first build.

Finding: the closeness at a fixed salt, root and digest is unsatisfiable
with a small slack (a recorded root key is hit with certainty); restated
over the uniform draws, with the swap's core averaging its three steps.
The split's bad event is now a parameter so that it can be enlarged.
Next: the bad term for the pre-call hit (the root's key against the
recorded keys, then the fresh-parent chain), reusing the touching total's
distinctness term, and the off-bad equality.

The two-hundred-and-ninety-fifth full validation passed: 3706 build jobs and 18381 project declarations audited, every transitive axiom allowlisted.

## Continuation 294 — the closeness slack split

Classified continuation 293 as progress and took its audit (3705 jobs,
18365 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 293,
built after it ended, on the first build.

Added Proofs/SwapCloseSplit: the closeness slack is the probability of
the pre-call hit, provided the two signings agree exactly on the calls
without a hit. Both parts are named targets. Next: the hit term, in the
shape of the leaf bounds (the hidden path's keys against the pre-call
history under the counted invariant), and the off-hit equality from the
commitment run's witness-free prefix and witness-dependent tail with the
PRG hypothesis.

The two-hundred-and-ninety-fourth full validation passed: 3706 build jobs and 18374 project declarations audited, every transitive axiom allowlisted.

## Continuation 293 — the pruned closeness

Classified continuation 292 as progress and took its audit (3704 jobs,
18347 declarations) as the starting state; verified this continuation's
registration (import line, index entry). Drafted during validation 292,
built after it ended.

Finding: the pruned equality cannot hold exactly, since the pre-call
cipher history may record a key of the hidden path and a functional
knowing that entry distinguishes the honest signing on the hit event
(recorded in the review ledger). Added Proofs/SwapClose, generated from
the swap, gap and final theorems with the equality replaced by the
closeness and the slack carried through. Build fixes: the module renamed
from the definition's name (duplicated-namespace lint), the last step of
the swap's core closed by the constant mean rather than the added
constant. Next: the content of the closeness slack, that is the hit term
for the hidden path's keys in the pre-call history, in the shape of the
leaf bounds.

The two-hundred-and-ninety-third full validation passed: 3705 build jobs and 18365 project declarations audited, every transitive axiom allowlisted.

## Continuation 292 — the named hypotheses recorded

Classified continuation 291 as progress and took its audit (3704 jobs,
18347 declarations) as the starting state. Documentation only: the
review ledger's new section on the final composed bound and its named
hypotheses, the plan's status lines (the reduction is composed end to
end with named unproved hypotheses), and the README header. Surveyed the
remaining hypotheses for the next module: the retry bound needs the
challenge expansion's model (decision kept in the simplest form, an
explicit bound); the seed-collision event spans both fork branches, so
the single-run paired-cipher bound does not apply directly; the pruned
equality and the leaf bounds are proof work on the pruned world's
posterior. Next: the pruned equality (`PrunedEqual`), starting from the
commitment run's decomposition at the hidden leaf.

The two-hundred-and-ninety-second full validation passed: 3704 build jobs and 18347 project declarations audited, every transitive axiom allowlisted.

## Continuation 291 — the events' requirements

Classified continuation 290 as progress and took its audit (3703 jobs,
18334 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3704). Drafted during
validation 290, built after it ended.

Finding: the seed-collision event reads the snapshot world's family and
the branches' cipher histories, so the events' requirements cannot hold
for it; its probability enters the composition directly as a named bound
instead. Added Proofs/EventRequirements (`pruneCompat_const`,
`rightEval_eq`, `eventOKP_of`, seven `eventOKP_*` instances by case
analysis and reflexivity, `hgap_final`, `forgery_le_final'`). Build
fixes: unused instances omitted per lemma, the final bound split into the
per-event gap and the composition against the heartbeat budget, the
per-event slack parenthesised. Next: the seed-collision bound, the retry
term, and the statement of the named hypotheses' content in the review
ledger.

The two-hundred-and-ninety-first full validation passed: 3704 build jobs and 18347 project declarations audited, every transitive axiom allowlisted.

## Continuation 290 — the final composed bound

Classified continuation 289 as progress and took its audit (3702 jobs,
18326 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3703). Drafted during
validation 289, built after it ended.

Found that the events' insensitivity to an arbitrary replacement of an
attempt's embedded world is too strong for the mask event, which reads
that world's inner hash table; weakened it to replacements of the family
and the cipher history (`adjust`), which is what the chain's resampling,
pruning, family setting and history shifting produce, re-deriving the
finalized terminal from the finalization's support (`finalize_terminal`).
Added Proofs/ForgeryFinal (`εTouch_mono`, `touchR_mono`,
`forgery_le_final`). Build fixes: namespaces opened. Remaining
hypotheses of the final bound: the pruned equality, the leaf-term bounds,
the retry bound, the layout's fiber bounds and size conditions, and the
events' requirements. Next: the events' requirements for the named
events.

The two-hundred-and-ninetieth full validation passed: 3703 build jobs and 18334 project declarations audited, every transitive axiom allowlisted.

## Continuation 289 — the touching bounds

Classified continuation 288 as progress and took its audit (3701 jobs,
18286 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3702). The module and
the refactor were drafted during validation 288 and built after it ended.

Found that the per-call hypotheses, stated at the budget, could not let
the touching bound reach the end budget, since the run after the call adds
its fuel to the count; restated `SignRunWMeanP`, `SignCutWMeanP`, `TouchR`
and `TouchC` with the world's count and the fuel within the budget, and
the discharges accordingly; the monotonicity variable became unused in the
two hybrids and was dropped from their argument lists. Added
Proofs/TouchBound (`εTouch`, `card_keysOf_le`, `mem_rootDraw`,
`touchMean_le`, `cutW_inv_sim`, `LeafR`, `LeafC`, `touchR_of`,
`touchC_of`). Build fixes: a parenthesis, the scheme variables included.
The composed forgery bound's remaining hypotheses: the pruned equality,
the leaf-term bounds, the retry bound and the eight events' requirements.
Next: assemble the composed bound with the touching bounds instantiated;
then the events' requirements.

The two-hundred-and-eighty-ninth full validation passed: 3702 build jobs and 18326 project declarations audited, every transitive axiom allowlisted.

## Continuation 288 — the touching term as the touching total

Classified continuation 287 as progress and took its audit (3700 jobs,
18273 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3701). The module was
drafted during validation 287 and built after it ended.

Added Proofs/TouchIdentity (`postT`, `hiddenT`, `contT`, `newT`,
`touchInner_eq_touchAll`, `invC_setFamily`, `expLen_le`). The identity
unfolds both sides to the joint draw, rewrites the commitment run's
family on its support and closes by reflexivity; the length bound follows
the invariant through the call, the pruning, the resampling and the
process. Build fixes: the program type's namespace, unused instances
omitted, the lemmas' argument lists. Next: the touching total applied with
the post-processing invariance, made uniform in the history's key count
through the budget, with the leaf term as a named hypothesis, giving the
two touching bounds.

The two-hundred-and-eighty-eighth full validation passed: 3701 build jobs and 18286 project declarations audited, every transitive axiom allowlisted.

## Continuation 287 — preparations for the touching bound

Classified continuation 286 as progress and took its audit (3699 jobs,
18258 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3700).

Correction of continuation 286's finding: the candidate opening
(`Spec.CandidateBAVC.openKey`) reads the key's tree only at the leaves
other than the hidden ones, together with the commitments, so setting an
internal node leaves the simulated post-processing unchanged; the
assembled touching bound's blanket invariance hypothesis is therefore
satisfiable, and the constant-tuple restatement of continuation 286 is a
valid generalisation that is not needed. Added Proofs/TouchPrep
(`leafCount_le_leafAddress`, `openKey_setTree`, `simPost_setTree`,
`invC_pruneW`, `invC_commitOracle`). Build fixes: the opening's full
namespace, the committed value's namespace, unused instances omitted, the
section variables of the simulated scheme included, the oracle's
membership unfolded before matching the simulated signing's support.
Next: the identification of the swap's touching term with the touching
total's probability (the signing-shaped oracle on the resampled world as
the joint root and family draw, the pruned resampled world as the view
with the family resampled), the expected-length bound from the invariant,
and the uniform bound.

The two-hundred-and-eighty-seventh full validation passed: 3700 build jobs and 18273 project declarations audited, every transitive axiom allowlisted.

## Continuation 286 — the touching bound for a constant hidden tuple

Classified continuation 285 as progress and took its audit (3698 jobs,
18240 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3699).

Finding: the touching total's hypothesis that the post-processing is
invariant under setting any internal node of the committed tree is false
for the simulated post-processing, since `setTree` edits the key's tree
and the opening read by the retry's attempt reveals the co-path of the
hidden tuple; the invariance holds only on the output's own hidden paths.
The retry accepts a counter on the hidden tuple and grinding alone (the
opening's bound error depends on the hidden tuple), so when the opening is
defined the hidden tuple is a function of the digest. Added
Proofs/TouchConst (`hitVR_const_ne`, `hitV_const_ne`, `root_term_const`,
`node_term_const`, `touch_assembly_const`, `touch_total_const`),
generated from the assembly and total modules for a constant hidden tuple.
Build fixes: the copied header reduced to the variable declarations, the
namespaces of the assembly and total modules opened, argument orders of
the constant terms, the tuple rewritten rather than substituted. Next: the
hidden tuple as a function of the digest and the instantiation of the
touching bounds, with the post-processing's path invariance as a named
hypothesis.

The two-hundred-and-eighty-sixth full validation passed: 3699 build jobs and 18258 project declarations audited, every transitive axiom allowlisted.

## Continuation 285 — the composed bound with the swaps discharged

Classified continuation 284 as progress and took its audit (3697 jobs,
18214 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3698). The module was
drafted during validation 284 and built after it ended.

Added Proofs/SimulationGapCompat (`EventOKP`, `eventOK_left`,
`eventOK_right`, `eventOK_shift`, `TouchR`, `TouchC`, `PrunedEqual`,
`hgap_meanP`, `εSimP`, `forgery_le_meanP`), generated from the mean-form
composition with the per-call hypotheses replaced by their discharges.
Build fix: unused instances omitted on the derived event lemmas. The
remaining hypotheses of the composed bound: the pruned equality (named,
seed hiding), the touching bounds (to be instantiated from the touching
total), the retry bound, and the eight events' requirements. Next: the
touching bounds' instantiation.

The two-hundred-and-eighty-fifth full validation passed: 3698 build jobs and 18240 project declarations audited, every transitive axiom allowlisted.

## Continuation 284 — the per-call swaps discharged

Classified continuation 283 as progress and took its audit (3696 jobs,
18175 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3697).

Added Proofs/SwapDischarge (`prepareVerification_keeps`, `sigHidden`,
`simulatedSignWith_eq`, `prunedMean`, `touchInner`, `touchMean`,
`swap_core`, `signRunW_meanP`, `signCutW_meanP`). The pruned equality
(the law of the signature together with the resampled world pruned at the
output's hidden keys is the same for the honest and a fake witness) is the
named hypothesis carrying the seed-hiding content; the touching bound is a
hypothesis to be instantiated from the touching total. Build fixes: the
consistency predicate disambiguated, namespaces of the row term and retry
event opened. Next: the composed simulation gap and forgery bound with the
discharged per-call hypotheses, then the touching bound's instantiation.

The two-hundred-and-eighty-fourth full validation passed: 3697 build jobs and 18214 project declarations audited, every transitive axiom allowlisted.

## Continuation 283 — the event experiment for compatible continuations

Classified continuation 282 as progress and took its audit (3695 jobs,
18136 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3696). The module was
drafted during validation 282 and built after it ended.

Found that the cut's per-call hypothesis must restrict the process's
invariant keeping to reachable cuts, since a saved snapshot's remaining
fuel is bounded only along the cut; restated `SignCutWMeanP` with the
cut's fuel within the budget and `ReachC`. Added Proofs/EventCutCompat
(`cutProc`, `branchEval`, `fork_pruneCompat`, `innerEval_hist`,
`forkProc_hist`, `forkProc_touches`, `cutProc_touches`,
`eventBranch_pruneCompatC`, `cutProc_inv`, `eventExpE_le_meanP`). Build
fixes: the start worlds of the touching lemmas named explicitly; a
snapshot projection shown before `omega`; the idempotence lemma's
namespace. Next: the discharge of the two per-call hypotheses from the
generalised agreement, the per-call bridge and a named pruned-equality
hypothesis, then the touching bound's instantiation.

The two-hundred-and-eighty-third full validation passed: 3696 build jobs and 18175 project declarations audited, every transitive axiom allowlisted.

## Continuation 282 — the cut with its final world

Classified continuation 281 as progress and took its audit (3693 jobs,
18062 declarations) as the starting state; verified this continuation's
registration (import lines, index entries, job count 3695). Both modules
were drafted during validation 281 and built after it ended.

Finding: the replay's cut returns no world on its exhausted, aborted and
rejected outcomes, so a touching functional of the cut alone cannot be at
least one whenever the start touched the keys, which the agreement's sign
and query cases need. Added Proofs/CutWorld (`cutW`, `cutW_fst`,
`withWorldC`, `touchesG_cutW`, `PruneCompatC`, `pruneCompatC_compl`,
`cutW_le_prune_gen`, `prune_le_cutW_gen`; generated from the run
versions, with the saved case using the compatibility directly) and
Proofs/MeanCutCompat (`SignCutWMeanP`, `cutW_le_cutW_mean_contP`;
generated from the cut hybrid). Build fix: the cut's world replacement
needed its type ascribed in the finish case. Next: the compatibility of
the event branch after the cut (through the end-resampled fork's mean
form) and the event experiment's hybrid for compatible continuations
over the cut with its world.

The two-hundred-and-eighty-second full validation passed: 3695 build jobs and 18136 project declarations audited, every transitive axiom allowlisted.

## Continuation 281 — the hybrid chain for compatible continuations

Classified continuation 280 as progress and took its audit (3692 jobs,
18025 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3693). The module was
drafted during validation 280 and built only after it ended.

Added Proofs/MeanHybridCompat, generated from the mean-form hybrid proofs
with the per-call hypothesis restricted to compatible continuations. The
fork hybrid exceeded the heartbeat budget as one declaration: its two steps
and the per-call applications were split into separate lemmas
(`stepA_core`, `stepA`, `stepB`) through a module-level inner evaluation,
the fork's process and its compatibility were stated as lemmas, and the
right continuation's compatibility was stated in the applied form the
hybrid expects, so that no unification unfolds the oracles. Next: the
world-carrying cut and its generalised agreement (the cut forgets the
final world on its ended outcomes, so the touching functional must be
read from a world-carrying variant), then the event experiment's hybrid
for compatible continuations and the swap's discharge.

The two-hundred-and-eighty-first full validation passed: 3693 build jobs and 18062 project declarations audited, every transitive axiom allowlisted.

## Continuation 280 — the fork continuation's compatibility

Classified continuation 279 as progress and took its audit (3691 jobs,
18015 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3692).

Added Proofs/ForkPruneCompat (`pruneCompat_congr`, `rightEval`,
`leftEval`, `forkCont`, `leftTouch`, `forkTouch`,
`forkCont_pruneCompat`), composing the closure steps: finalization then
the event for the second branch's run, the game run's compatibility, the
hash update and restoration, the uniform answer, the first branch's
finalization and the resampling. Build fix: the abbreviated trace had to
be unfolded in the congruence steps. Next: the per-call hypotheses
restricted to compatible continuations (with the touching functional given
by a process keeping the invariant within an end budget) and the mean-form
chain's variants for them; the cut analogue of the generalised agreement.

The two-hundred-and-eightieth full validation passed: 3692 build jobs and 18025 project declarations audited, every transitive axiom allowlisted.

## Continuation 279 — closure of prune compatibility

Classified continuation 278 as progress and took its audit (3690 jobs,
18001 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3691).

Added Proofs/PruneCompatClosure (`mean_resampleW_resampleW`,
`pruneCompat_free`, `pruneCompat_resample`, `pruneCompat_sample`,
`pruneCompat_restore`, `pruneCompat_update`, `finalize_withWorld_table`,
`pruneCompat_finalize`). Build fixes: the compatibility's implicit types
must be named when the evaluation reads only the world; pair projections
reduced before rewriting; a beta-redex closed by `simp only`.
Note: single-module builds of the next, unregistered modules
(Proofs/PruneCompatClosure during validation 278, Proofs/ForkPruneCompat
during validation 279) ran while the validations were in progress, against
the loop's rule of not building during a validation; both validations
report the expected job counts of the registered library (3690 and 3691),
and the registered modules were not rebuilt by those single-module builds.
From continuation 280 on, modules are only drafted during a validation and
built after it ends. Next: the
fork continuation's compatibility assembled from these steps, with the
end-resampled event's compatibility as a per-event hypothesis.

The two-hundred-and-seventy-ninth full validation passed: 3691 build jobs and 18015 project declarations audited, every transitive axiom allowlisted.

## Continuation 278 — prune-compatible evaluations

Classified continuation 277 as progress and took its audit (3689 jobs,
17975 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3690).

Finding: the shaped swap hypotheses cannot be discharged through the
existing pruned-run agreement, whose evaluation is family-free and read at
the pruned result, because the hybrid's continuation after a signing call
reads the final history (the fork resamples it, finalizes, restores it
into the snapshot and runs the second branch from it). Added
Proofs/GamePruneGen (`PruneCompat`, `one_sub_le_iff`,
`pruneCompat_compl`, `runW_le_prune_gen`, `prune_le_runW_gen`,
`runW_pruneCompat`): the agreement for prune-compatible evaluations with a
touching functional, in both directions, read at the actual result; the
finish case re-resamples after the verification preparation (its
resampling law and consistency keeping) and the leaf cases use the
compatibility directly. Build fix: an unused-instance lint on the
complement lemma. Next: compatibility of the fork continuation
(resampling, finalization, restoration, second branch, end-resampled
event) and the per-call hypotheses restricted to compatible continuations.

The two-hundred-and-seventy-eighth full validation passed: 3690 build jobs and 18001 project declarations audited, every transitive axiom allowlisted.

## Continuation 277 — the composed bound in mean form

Classified continuation 276 as progress and took its audit (3687 jobs,
17959 declarations) as the starting state; verified this continuation's
registration (import lines, index entries, job count 3689), moving the
index entries once after a first insertion landed after the wrong key.

Added Proofs/ForgeryEvents (`forgery_le_simulated_events`, the forgery
reduction with eight per-event gap hypotheses) and
Proofs/SimulationGapMean2 (`εCall`, `EventOK`,
`simulated_keygen_resampled`, `call_mean`, `signRunW_mean`,
`signCut_mean`, `hgap_mean`, `εSim`, `forgery_le_mean`). The composition
takes the event experiment to its end-resampled restored form for both
schemes, applies the mean-form hybrid under the extended counted
invariant with the candidate and simulated instantiations, and returns to
the simulator's experiment. Build fixes: a section closed in the wrong
order in the generated header; the mean lemmas' namespace; an unreachable
`first` alternative; event implicits fixed on `EventOK` rather than on
the events.

The two-hundred-and-seventy-seventh full validation passed: 3689 build jobs and 17975 project declarations audited, every transitive axiom allowlisted.

## Continuation 276 — the event experiment's mean-form hybrid

Classified continuation 275 as progress and took its audit (3683 jobs,
17931 declarations) as the starting state; verified this continuation's
registration (import lines, index entries, job count 3687) after a first
attempt whose shell chain broke on a zero count.

Added Proofs/MeanForkCont2 (`forkEventE_mean`, `forkEventE_le_mean`),
Proofs/MeanEventCont (`eventBranch`, `eventExpE_eq_branch`,
`eventExpE_le_mean`), Proofs/CandidateKeepsFamily (`honest_keepsFamily`,
`simulated_keepsFamily`, `publicOracle_keepsFamily`,
`prepareVerification_keepsFamily`) and Proofs/InvCExtra (`invC_restore`,
`invC_prep`). Build fixes: an unreduced snapshot projection in a fuel
bound, the fork evaluation named to avoid restating a match, a lemma's
namespace.

Next: the composition into the simulation gap and the forgery bound with
the per-call swap hypotheses in mean form for the game's continuations,
then their discharge. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-seventy-sixth full validation passed: 3687 build jobs and 17959 project declarations audited, every transitive axiom allowlisted.

## Continuation 275 — the branch hybrid in mean form

Classified continuation 274 as progress and took its audit (3682 jobs,
17914 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3683).

Added Proofs/MeanForkCont (`runW_inv`, `freshBranchW_le_mean`), built at
the first attempt. The verification preparation's preservation of the
counted invariant is a hypothesis of the run's invariant, since the
restored fork's second branch starts from the first branch's final world,
which may come from a verification.

Next: the restored event fork's hybrid (second branch then first branch),
the event experiment's hybrid, the composition and the discharge of the
shaped swap. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-seventy-fifth full validation passed: 3683 build jobs and 17931 project declarations audited, every transitive axiom allowlisted.

## Continuation 274 — the end-resampled event experiment

Classified continuation 273 as progress and took its audit (3680 jobs,
17867 declarations) as the starting state; verified this continuation's
registration (import lines, index entries, job count 3682).

Added Proofs/ForkRestoreEnd (`setFamilyT`, `setFamilyBranch`,
`withWorld_setFamily`, `finalize_setFamilyT`, `runW_attempt`,
`freshBranchW_family`, `mean_freshBranch_eq_W`, `mean_resampleW_update'`,
`mean_resampleW_restore`, `right_end_resample`, `forkEventE`,
`forkEventR_eq_E`) and Proofs/EventRestore (`pmf_bool_ext`, `eventExpE`,
`eventExp_eq_E`). Build fixes: a family lemma's world argument, the
table-update rewrite from the world's own table (a one-sided rewrite with
explicit congruence functions and a beta reduction), an instance
omission, and the event-experiment proof redone at the distribution level
with the boolean extensionality.

Hypotheses on the event recorded for later discharge per named event:
insensitivity to the second branch's history suffix and to the attempts'
embedded families.

Next: the mean-form hybrid of the end-resampled event fork and of the
event experiment, then the composition and the discharge of the shaped
swap. No assumption, source repair or contract was added. Assumptions and
Final are unchanged.

The two-hundred-and-seventy-fourth full validation passed: 3682 build jobs and 17914 project declarations audited, every transitive axiom allowlisted.

## Continuation 273 — the fork restoration and the run-with-world hybrid

Classified continuation 272 as progress and took its audit (3678 jobs,
17846 declarations) as the starting state; verified this continuation's
registration (import lines, index entries, job count 3680).

Added Proofs/ForkRestoreEq (`forkEventR`, `map_true`, `common`,
`shared_eq_common`, `restored_eq_common`, `fork_restore_eq`) and
Proofs/MeanHybridContW (`SignRunWMean`, `runW_le_runW_mean_cont`). Build
fix: a missing import.

Noted for the composition: the seed-collision event reads the snapshot
world's family, so the event must be evaluated at a family resampled at
the end of the fork (the resampling law of the second branch moves the
family's resampling to its end, and the event's probability is unchanged);
events must be insensitive to the attempt worlds' families and to the
second branch's history suffix, hypotheses to be checked per named event.

Next: the end-resampled event fork and its equality with the restored
one, then the mean-form branch, fork and event hybrids. No assumption,
source repair or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-seventy-third full validation passed: 3680 build jobs and 17867 project declarations audited, every transitive axiom allowlisted.

## Continuation 272 — the fork restoration's supporting facts

Classified continuation 271 as progress and took its audit (3676 jobs,
17817 declarations) as the starting state; verified this continuation's
registration (import lines, index entries, job count 3678).

Added Proofs/ForkRestoreLemmas (`runW_history`,
`eq_setFamily_of_mem_resampleW`, `shiftBranch`, `finalize_shiftT`) and
Proofs/ForkRestoreShift (`runW_postLaw_mean`, `freshBranch_eq`,
`freshBranch_shift`, `setFamily_eq_shiftG`, `restore_eq_shiftG`). Build
fixes: a wrongly omitted instance (finalization queries the oracle), the
idempotence lemma's namespace, and the shifted-terminal lemma restated
with the checked terminal shifted (so the branch shift is a composition).

Next: the equality in law of the shared and restored event forks from a
resampled snapshot world, for events insensitive to the second branch's
history suffix. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-seventy-second full validation passed: 3678 build jobs and 17846 project declarations audited, every transitive axiom allowlisted.

## Continuation 271 — the shift laws and the restored fork

Classified continuation 270 as progress and took its audit (3674 jobs,
17786 declarations) as the starting state; verified this continuation's
registration (import lines, index entries, job count 3676).

Added Proofs/CandidateShift (`honest_shiftLaw`, `simulated_shiftLaw`,
`publicOracle_shiftLaw`, `prepareVerification_shiftLaw`,
`candidate_runW_shift`, `simulated_runW_shift`) and Proofs/ForkRestore
(`KeepsFamily`, `keepsFamily_run`, `keepsFamily_sample`,
`keepsFamily_pure`, `runW_family`, `freshBranchW`, `freshBranchW_fst`,
`restore`, `forkAtR`). Both built at the first attempt.

Next: the equality in law of the shared and restored forks from a
resampled snapshot world, for events insensitive to the second branch's
history suffix; then the mean-form branch, fork and event hybrids over the
restored fork. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-seventy-first full validation passed: 3676 build jobs and 17817 project declarations audited, every transitive axiom allowlisted.

## Continuation 270 — the history as a log for the game run

Classified continuation 269 as progress and took its audit (3673 jobs,
17767 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3674).

Added Proofs/HistoryShiftGame (`shiftG`, `ShiftLaw`, `shiftLaw_run`,
`shiftLaw_sample`, `shiftLaw_pure`, `shiftT`, `runW_shift`). Build fixes:
the history-shift lemma's procedure argument and unused simp lemmas.

Next: the candidate and simulated oracles' shift laws, the restored fork
and its equality in law with the shared fork, the mean-form branch, fork
and event hybrids, the composition, and the discharge of the mean-form
shaped swap. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-seventieth full validation passed: 3674 build jobs and 17786 project declarations audited, every transitive axiom allowlisted.

## Continuation 269 — the reverse instantiations and the mean-form hybrids

Classified continuation 268 as progress and took its audit (3671 jobs,
17736 declarations) as the starting state; verified this continuation's
registration (import lines, index entries, job count 3673).

Added Proofs/CandidateGamePruneReverse (`candidate_prune_le_runW`,
`simulated_prune_le_runW`) and Proofs/MeanHybridCont (`SignRunMean`,
`SignCutMean`, `run_le_run_mean_cont`, `cut_le_cut_mean_cont`). The
fixed-world charge chain cannot carry the swap: any charge valid at every
world dominates the pointwise gap, whose mean is not bounded by the mean
gap; so the chain is redone in mean form for the game's continuations,
following the mean-form run hybrid.

Analysis recorded for the fork: the two branches share the world's
family, so a branch's continuation is not a fixed function of the signing
output; the route is the restored fork (the right branch from the left
branch's final world with the snapshot's table and trace, the history
being only a log), with the event insensitive to the right branch's
history prefix as a hypothesis, after which every continuation is a run.

Next: the restored fork and its equality in law with the shared fork, the
mean-form branch, fork and event hybrids, then the composition and the
discharge of the mean-form shaped swap. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The two-hundred-and-sixty-ninth full validation passed: 3673 build jobs and 17767 project declarations audited, every transitive axiom allowlisted.

## Continuation 268 — the reverse pruned-run agreement

Classified continuation 267 as progress and took its audit (3670 jobs,
17734 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3671).

Added Proofs/GamePruneReverse (`mean_one_sub`, `prune_le_runW`): instead of
a second induction with per-oracle reverse laws (whose touching charges
would double at every call), the forward agreement is applied to the
complement of the evaluation, which is again family-free and bounded, and
the two means are rearranged. Build fix: the two-sided addition lemma in
place of a one-sided one whose side differs from its name.

Next: the candidate and simulated instantiations of the reverse
agreement, the touching term connected to the total touching bound, and
the discharge of the shaped swap hypotheses with the pruned equality of
the two signings as the named remaining hypothesis. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-sixty-eighth full validation passed: 3671 build jobs and 17736 project declarations audited, every transitive axiom allowlisted.

## Continuation 267 — the hybrid chain for the game's continuations

Classified continuation 266 as progress and took its audit (3667 jobs,
17678 declarations) as the starting state; verified this continuation's
registration (import lines, index entries, job count 3670).

Added Proofs/ChargeRunCont (`run_le_run_add_charge_cont`),
Proofs/ChargeCutCont (`SignRun`, `SignCut`, `cut_le_cut_add_charge`,
`continueWith_le_charge`, `freshBranch_le_charge`, `forkAt_le_charge`,
`cutExperiment_le_charge`, `eventExp_le_charge`) and
Proofs/SimulationGapCont (`hgap_of_cipher_cont`,
`forgery_le_cipher_cont`): the hybrid chain's proofs apply the per-call
bound only to the second scheme's run or cut continuation from the
signing output, so the bound is now hypothesised in exactly that shape
(`hswapRun`, `hswapCut`), the shape the identical-until-bad route can
discharge; the composed statements are otherwise unchanged. Build fix:
rewriting the key equation instead of substituting (the substitution
removed the public key's name).

Next: discharging the shaped swap hypotheses for the simulated signing
with the witness against the fake: the bridge to the pruned run, the
pruned equality of the two signings (the hidden-share step), the reverse
bridge, and the touching term through the total touching bound. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The two-hundred-and-sixty-seventh full validation passed: 3670 build jobs and 17734 project declarations audited, every transitive axiom allowlisted.

## Continuation 266 — the per-call bridge to the pruned run

Classified continuation 265 as progress and took its audit (3666 jobs,
17668 declarations) as the starting state; verified this continuation's
registration (import line, index entry, job count 3667).

Added Proofs/SignBridge (`commitOracle`, `outKeys`,
`commitOracle_postLaw`, `commitOracle_consistent`,
`history_of_mem_resampleW`, `pruneW_congr_mem`, `outKeys_congr`,
`sign_bridge`). The bridge takes the game's pruned-run agreement at a
fixed key list as a hypothesis (the candidate and simulated schemes have
it) and applies it at the output's keys after the resampling law moves
the family's resampling past the call. Build fix: a missing import.

Next: the hybrid chain with the per-call hypothesis stated for the game's
continuations, the pruned equality of the witness and fake signings, the
touching term through the total touching bound, and the composition. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The two-hundred-and-sixty-sixth full validation passed: 3667 build jobs and 17678 project declarations audited, every transitive axiom allowlisted.

## Continuation 265 — the commitment run's recorded expansion

Classified continuation 264 as progress and took its audit as the
starting state, then found that its audit, like those of continuations
262 and 263, did not cover the continuation's module: the import lines of
Proofs/TouchAssembly, Proofs/TouchTotal and Proofs/TreeOfMatches were
missing from the library root (the registration step keyed on a trailing
newline that the root file lacked, and did not check its own effect), so
the three validations audited the previous state (3662 jobs, 17592
declarations each). The three modules had each been built on their own.
Added the import lines and the index entries, and this continuation's
full build (3666 jobs) and validation cover them.

Added Proofs/CommitHistoryContains (`commitRun_contains`,
`commit_contains`, `mem_hiddenKeysAll_commit`). Build fix: a membership
split.

Next: the per-call bridge from the signing call to the game's pruned run.
No assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The two-hundred-and-sixty-fifth full validation passed: 3666 build jobs and 17668 project declarations audited, every transitive axiom allowlisted.

## Continuation 264 — the tree of any matching family

Classified continuation 263 as progress and took its audit (3662 jobs,
17592 declarations) as the starting state. Started the bridge from the
signing call to the game: the resampling law replaces the output world's
family by a fresh one consistent with the history, so the pruning keys
must be shown independent of the family.

Added Proofs/TreeOfMatches (`node_of_le`, `childEntry`,
`childEntry_even_mem`, `childEntry_odd_mem`, `node_eq_of_matches`,
`mem_hiddenKeysAll_of_matches`). Build fixes: a seed namespace and the
one-step unfolding of the node recursion on both sides.

Next: the commitment run's final history contains the expansion's
entries; the per-call bridge (the signing call followed by the game run
is below the call followed by the resampled pruned run plus the touching
probability, via the game's pruned-run agreement); the pruned equality of
the witness and fake signings; the hybrid chain with the per-call
hypotheses stated for the game's continuations. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-sixty-fourth full validation passed: 3662 build jobs and 17592 project declarations audited, every transitive axiom allowlisted.

## Continuation 263 — the total touching bound

Classified continuation 262 as progress and took its audit (3662 jobs,
17592 declarations) as the starting state. Closed the touching bound over
all pairs of the joint draw.

Added Proofs/TouchTotal (`pathAddresses_length_le`, `innerPath_card_le`,
`map_decide_eq_mean`, `bad_tree_le`, `touchAll_le_one`, `touch_total`):
the depth parameter of the assembled bound is the binary logarithm of the
leaf count, the pairs whose tree keys are not fresh and distinct are
charged by the distinctness bound and the uniform root's key hit, and the
touching probability under the joint draw is at most that failure plus
the assembled bound plus the leaf term. Build fixes: the decide lemma
generalized over the decidability instance, a wrongly omitted instance,
a missing namespace.

Next: the game bridge (the signing call's commitment view with the game's
continuation as the pruned run, the leaf term as the explicit seed-hiding
hypothesis, the equal law of the witness and fake signings in the pruned
world, the events' insensitivity hypothesis, composition into the
forgery bound). No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-sixty-third full validation passed: 3662 build jobs and 17592 project declarations audited, every transitive axiom allowlisted.

## Continuation 262 — the assembled touching bound

Classified continuation 261 as progress and took its audit (3662 jobs,
17592 declarations) as the starting state. Assembled the touching bound
for the view pruned at the signature's hidden keys against the joint draw
of a uniform root and the posterior family.

Added Proofs/TouchAssembly (`mean_rootDraw`, `GoodTree`,
`goodAllR_of_distinct`, `leafTerm`, `sum_expected`, `root_term`,
`node_term`, `touch_assembly`): on the good pairs the touching probability
is at most the executions times (the key fiber bound over the seeds less
the root's bad targets, plus the internal path depth times the output
fiber bound over the seeds less a node's bad targets) times the expected
recorded length, plus the leaf term. The internal path depth is a
parameter with its bound as a hypothesis (`hD`); the leaf term is kept
explicit. Build fix: the division rewrite in `ℝ≥0∞` (`div_eq_mul_inv`,
`mul_right_comm`).

Next: the internal path depth bound as a proved lemma, the distinctness
failure term, the leaf term as an explicit seed-hiding hypothesis, and the
bridge from the game's signing call to the pruned run. No assumption,
source repair or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-sixty-second full validation passed: 3662 build jobs and 17592 project declarations audited, every transitive axiom allowlisted.

## Continuation 261 — the instantiated bounds and the touching split

Classified continuation 260 as progress and took its audit (3660 jobs,
17562 declarations) as the starting state. Instantiated the abstract
bounds with the view pruned at all executions' hidden keys and split the
touching probability of the view-dependent pruning.

Added Proofs/AllViewBounds (`viewAll`, `viewAll_exchanged`,
`viewAll_root_exchanged`, `node_touch_bound_all`, `root_touch_bound_all`)
and Proofs/TouchSplit (`mean_le_triple_sum`, `innerPath`,
`sum_pathSet_split`, `innerPath_bounds`, `innerPath_subset`, `viewAct`,
`touchAll`, `expLen`, `leafHit`, `touchAll_le`). Build fix: a
decidable-instance mismatch between the generic slicing lemma and the
concrete tuple type, bridged by `convert` and `decide_eq_decide`.

Next: the assembled touching bound against the joint draw (the
distinctness indicator, the node and root bounds per tuple and execution,
the sums of the sliced expected lengths back to the expected length, the
leaf term kept explicit), then the game bridge. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-sixty-first full validation passed: 3662 build jobs and 17592 project declarations audited, every transitive axiom allowlisted.

## Continuation 260 — the node and root bounds for an abstract view

Classified continuation 259 as progress and took its audit (3658 jobs,
17527 declarations) as the starting state. Restated the node and root
bounds for an abstract view with the exchange invariance as a hypothesis,
so that they apply to the view pruned at the hidden keys of all
executions.

Added Proofs/ViewNodeBound (`weightV`, `weightV_le_one`,
`weightV_exchanged`, `honest_node_boundV`, `HitV`, `expectedNewV`,
`goodHitV_le_sum`, `pairV_bound`, `node_touch_boundV`) and
Proofs/ViewRootBound (`weightVR`, `weightVR_le_one`, `weightVR_exchanged`,
`honest_root_boundVR`, `HitVR`, `expectedNewVR`, `goodHitVR_le_sum`,
`seedVR_bound`, `root_touch_boundVR`). Build fixes: argument lists of the
definitions (the view-only definitions take fewer parameters) and omitted
unused section instances.

Next: the instantiation with the view pruned at all executions' hidden
keys (drafted), then the assembled touching bound for the view-dependent
pruning and the game bridge. No assumption, source repair or contract was
added. Assumptions and Final are unchanged.

The two-hundred-and-sixtieth full validation passed: 3660 build jobs and 17562 project declarations audited, every transitive axiom allowlisted.

## Continuation 259 — the own-view exchange for all executions' keys

Classified continuation 258 as progress and took its audit (3655 jobs,
17500 declarations) as the starting state. The touching bounds were
proved for the view pruned at one leaf's hidden keys, while the game
prunes at the hidden keys of all executions; so the own-view exchange was
abstracted over the key list and instantiated for all executions.

Added Proofs/OwnViewExchangeGen (`ownView_exchanged_of_mem`,
`ownView_root_exchanged_of_mem`: the proofs of the hidden keys' own-view
exchanges with the three membership facts as hypotheses),
Proofs/HiddenKeysAllExchange (`lt_of_mem_path`, `key_mem_hiddenKeysAll`,
`mem_hiddenKeysAll_exchanged`, `mem_hiddenKeysAll_root_exchanged`) and
Proofs/OwnViewExchangeAll (`ownView_exchanged_all`,
`ownView_root_exchanged_all`). Build fix: a missing namespace.

Next: the node and root bounds for an abstract view function (the
weight's exchange invariance as a hypothesis), instantiated with the view
pruned at all executions' hidden keys; then the assembled touching bound
for the view-dependent pruning and the game bridge. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-fifty-ninth full validation passed: 3658 build jobs and 17527 project declarations audited, every transitive axiom allowlisted.

## Continuation 258 — the hidden tuples and the sliced view

Classified continuation 257 as progress and took its audit (3653 jobs,
17478 declarations) as the starting state. Prepared the sum over the
hidden leaves: the hidden keys are chosen from the signature (one leaf
per execution) and the family, so the view pruned at them is sliced over
the possible choices.

Added Proofs/HiddenTuple (`hiddenKeysAll`, `mem_hiddenKeysAll`,
`touchAll_le_sum`) and Proofs/HiddenSlice (`viewPruned`,
`mean_congr_support`, `mean_viewPruned_eq_sum`, `sliceCont`, `sliceNew`,
`mean_sliceCont`, `hitWeight_slice`, `hitWeightR_slice`,
`length_slice`). Build fix: an unused simp lemma.

Next: the assembled touching bound for the view-dependent pruning (sum
over executions, path nodes and hidden tuples of the node and root
touching bounds with the sliced continuation, plus the distinctness
failure and the leaf term as an explicit hypothesis), then the bridge
from the game's signing call to the pruned run. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-fifty-eighth full validation passed: 3655 build jobs and 17500 project declarations audited, every transitive axiom allowlisted.

## Continuation 257 — the root's posterior and touching bounds

Classified continuation 256 as progress and took its audit (3650 jobs,
17423 declarations) as the starting state. Proved the root's analogues
of the node posterior bound, the honest view bound and the touching
bound, against the joint draw of a uniform root and the posterior family.

Added Proofs/RootPosteriorBound (`rootDraw`, `GoodR`, `BadR`,
`exchangeR`, `exchangeR_eq`, `labelR`, `labelR_eq_iff`, `node_exchangeR`,
`labelR_exchangeR`, `count_root_hits`, `badR_card_le`,
`rootDraw_map_exchangeR`, `BadTR`, `posterior_root_bound`),
Proofs/RootHonestBound (`FreshR`, `weightR`, `weightR_le_one`,
`weightR_exchanged`, `honest_root_bound`) and Proofs/RootTouchBound
(`hitWeightR`, `GoodAllR`, `HitR`, `expectedNewR`, `hitWeightR_le_one`,
`sum_root_hit_le`, `goodHitR_le_sum`, `seed_bound`, `root_touch_bound`).
The bad targets are counted by a fiber bound on the layout's key alone
(`hfiberR`), stated as an explicit hypothesis since the existing bound is
on the key of an output. Build fixes: a decidable-instance mismatch in
the swap (closed by a deeper `convert`) and a range-card step.

Next: the generalized hit weight with a view factor and the sum over the
hidden leaves, the leaf's explicit seed-hiding hypothesis, the bridge from
the commitment view with a continuation to the game's pruned run. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The two-hundred-and-fifty-seventh full validation passed: 3653 build jobs and 17478 project declarations audited, every transitive axiom allowlisted.

## Continuation 256 — the root's exchange through the own view

Classified continuation 255 as progress and took its audit (3646 jobs,
17387 declarations) as the starting state. Simplified the root exchange
to a direct swap of two keys, dropping the dummy key, and carried it
through the commitment run, the commitment view and the own view.

Added Proofs/KeySwap (`swapKeys`, `swapKeys_involutive`,
`matches_swapKeys`, `swapCandidates`, `posterior_swapKeys`),
Proofs/RootCommitRun (`root_exchanged_tree_eq`,
`root_exchanged_leafKeys`, `commitRun_root_exchanged`),
Proofs/RootCommitView (`commit_view_root_exchanged`,
`mem_hiddenKeys_root_exchanged`) and Proofs/RootOwnView
(`ownView_root_exchanged`); restated Proofs/RootExchange and
Proofs/RootHistoryExchange over the key swap (two root keys, no `G1`).
Build fixes: an explicit implicit argument in the involutivity statement
and omitted unused section instances.

Next: the joint posterior bound for the root over the product of the root
draw and the family, the generalized hit weight with a view factor, the
leaf's explicit seed-hiding hypothesis, then the game bridge. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The two-hundred-and-fifty-sixth full validation passed: 3650 build jobs and 17423 project declarations audited, every transitive axiom allowlisted.

## Continuation 255 — the distinctness bridge and the root's exchange

Classified continuation 254 as progress and took its audit (3642 jobs,
17354 declarations) as the starting state. Bridged the distinctness
bound to the family's tree and started the root's exchange chain, keeping
the validation window busy with the next proofs.

Added Proofs/DistinctBridge (`distinct_of_distinctTo`,
`distinct_family_le`), Proofs/RootExchange (`rootExchanged`,
`node_root_exchanged`), Proofs/ProductSwap (`product`,
`product_map_eq`, `uniform_map_swap`) and Proofs/RootHistoryExchange
(`rootKeys`, `run_root_exchanged`, `treeHistory_root_exchanged`). Build
fixes: implicit parameters and an unused hypothesis.

Next: the commitment run and view under the root exchange, the joint
posterior bound for the root, then the game bridge. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-fifty-fifth full validation passed: 3646 build jobs and 17387 project declarations audited, every transitive axiom allowlisted.

## Continuation 254 — the distinct-keys bound

Classified continuation 253 as progress and took its audit (3641 jobs,
17322 declarations) as the starting state. Proved the probability bound
on the tree's keys being fresh and pairwise distinct.

Added Proofs/TreeDistinctBound (`DistinctTo`, `keysTo`,
`keysTo_card_le`, `notDistinct`, `distinct_step`, `treeHistory_key_le`,
`tree_distinct_le`). Build fixes: a cardinal step's orientation, the
case analysis of the step, the tree-expansion namespace, the pure-support
lemma's arguments, the length facts, the continuation's map composition,
and the step range.

Next: the bridge from the run's distinctness to the family's, the root's
exchange, the leaf's hypothesis, and the bridge to the game. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The two-hundred-and-fifty-fourth full validation passed: 3642 build jobs and 17354 project declarations audited, every transitive axiom allowlisted.

## Continuation 253 — the union bound, distinct keys and sibling keys

Classified continuation 252 as progress and took its audit (3638 jobs,
17303 declarations) as the starting state. Found that the goodness
hypotheses quantified over address zero, the tree's unused totalization
cell, which made them unsatisfiable for the root's children; weakened
them to positive addresses throughout the exchange chain and rebuilt it.

Added Proofs/PathUnion (`pathSet`, `touch_le_sum`), Proofs/TreeDistinct
(`Distinct`, `goodAll_of_distinct`) and Proofs/SiblingKeys
(`sibling_keys_le`). Build fixes: the explicit summand of the single-term
bound, a namespace clash, the argument order of the distinctness
hypothesis, instance omissions.

Next: the distinctness bound by the step induction with a growing key
set, the root's exchange, the leaf's hypothesis, and the bridge to the
game. No assumption, source repair or contract was added. Assumptions
and Final are unchanged.

The two-hundred-and-fifty-third full validation passed: 3641 build jobs and 17322 project declarations audited, every transitive axiom allowlisted.

## Continuation 252 — the touching bound at a hidden node

Classified continuation 251 as progress and took its audit (3635 jobs,
17271 declarations) as the starting state. Instantiated the posterior
bound for the commitment view and derived the touching bound at a hidden
node, keeping the validation window busy with the next proofs.

Changed Proofs/PosteriorNodeBound (one-sided `hWex`). Added
Proofs/HonestNodeBound (`Fresh`, `weight`, `weight_le_one`,
`weight_exchanged`, `honest_node_bound`), Proofs/KeyWeightSum
(`card_hits_le`, `sum_hit_weight_le`) and Proofs/NodeTouchBound
(`hitWeight`, `GoodAll`, `Hit`, `expectedNew`, `hitWeight_le_one`,
`sum_mean`, `goodHit_le_sum`, `pair_bound`, `node_touch_bound`). Build
fixes: stuck decidabilities, omitted instances, indicator rewrites by
simp instead of if-rewrites.

Next: the union bound over the hidden path's nodes, the root's exchange,
the goodness event's bound, the leaf's seed-hiding hypothesis, and the
bridge from the commitment view with a continuation to the game's
pruned run. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-fifty-second full validation passed: 3638 build jobs and 17303 project declarations audited, every transitive axiom allowlisted.

## Continuation 251 — the posterior bound on a hidden node's block

Classified continuation 250 as progress and took its audit (3634 jobs,
17238 declarations) as the starting state. Proved the posterior bound on
a hidden node's block for weights invariant under the exchange.

Added Proofs/PosteriorNodeBound (`OnFiber`, `Good`, `Bad`, `exchangeTo`,
`exchangeTo_eq`, `goodness`, `label`, `label_eq_iff`,
`label_exchangeTo`, `sibling_unique`, `bad_card_le`, `sum_mean_mul`,
`sum_bad_mass_on`, `label_mass_le_of_bad_on`, `BadT`,
`posterior_node_bound`). Written in the scratchpad and moved in once it
built; build fixes: argument lists of the fixed exchange, the key-hit
count's instance, the monotonicity lemmas' orientation, the goal order
after convert, and the swap lemma's decidability instance.

Next: the bound instantiated for the honest signing's own-keys view at a
fixed salt and root. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-fifty-first full validation passed: 3635 build jobs and 17271 project declarations audited, every transitive axiom allowlisted.

## Continuation 250 — the own-keys view under the exchange

Classified continuation 249 as progress and took its audit (3633 jobs,
17230 declarations) as the starting state. Proved the own-keys view
invariant under the exchange of a path node.

Added Proofs/OwnViewExchange (`ownView`, `ownView_cons_of_fresh`,
`ownView_congr_mem`, `ownView_exchanged`). The hard theorem was written
in the scratchpad and moved in once it built; build fixes: two imports
and the exchanged-keys membership normalization.

Next: the posterior bound (the counting applied to the posterior family
with the node exchange and the bad targets). No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-fiftieth full validation passed: 3634 build jobs and 17238 project declarations audited, every transitive axiom allowlisted.

## Continuation 249 — the hidden keys under the exchange

Classified continuation 248 as progress and took its audit (3632 jobs,
17223 declarations) as the starting state. Related the hidden keys of the
exchanged family to the family's.

Added Proofs/HiddenKeysExchange (`pruneAt_congr_mem`,
`le_of_mem_pathAddresses`, `mem_hiddenKeys_exchanged`). Built first try.

Next: the commitment view pruned at its own hidden keys under the
exchange, then the posterior bound. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The two-hundred-and-forty-ninth full validation passed: 3633 build jobs and 17230 project declarations audited, every transitive axiom allowlisted.

## Continuation 248 — the keys the commitment run records

Classified continuation 247 as progress and took its audit (3631 jobs,
17211 declarations) as the starting state. Bounded the commitment run's
recorded keys by the tree's keys.

Added Proofs/CommitHistoryKeys (`treeHistory_key`, `commitRun_keys`).
Built first try.

Next: the hidden keys under the exchange and the commitment view pruned
at its own hidden keys, then the posterior bound. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-forty-eighth full validation passed: 3632 build jobs and 17223 project declarations audited, every transitive axiom allowlisted.

## Continuation 247 — the keys a run records

Classified continuation 246 as progress and took its audit (3630 jobs,
17204 declarations) as the starting state. Proved that a run records only
the keys it queries.

Added Proofs/RunKeys (`entry_key`, `runFixed_keys`). Built first try.

Next: the commitment run's recorded keys among the tree's keys, then the
commitment view pruned at its own hidden keys under the exchange. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The two-hundred-and-forty-seventh full validation passed: 3631 build jobs and 17211 project declarations audited, every transitive axiom allowlisted.

## Continuation 246 — the one-sided fiber exchange

Classified continuation 245 as progress and took its audit (3629 jobs,
17202 declarations) as the starting state. Proved the one-sided form of
the fiber exchange, which the node exchange needs since the goodness of
the exchanged tree is only implied one way, and the pruning law at an
unused key.

Added Proofs/FiberCountingSided (`mean_label_le_of_map`,
`pruneAt_cons_of_no_entry`). Built first try.

Next: the keys recorded by a run that queries within a key set, then the
commitment view pruned at its own hidden keys under the exchange, then
the posterior bound. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-forty-sixth full validation passed: 3630 build jobs and 17204 project declarations audited, every transitive axiom allowlisted.

## Continuation 245 — fiber counting with bad targets

Classified continuation 244 as progress and took its audit (3628 jobs,
17198 declarations) as the starting state. Extended the counting to
exchanges with bad targets, as the node exchange needs.

Added Proofs/FiberCountingBad (`indicator_not_add`, `mean_split`,
`sum_bad_mass`, `label_mass_le_of_bad`). Build fix: the truncated
natural-cast subtraction lemma. A draft placeholder was again written and
replaced by full proofs before any build; the rule not to write
placeholders is re-recorded.

Next: the counting applied to the posterior family with the node
exchange. No assumption, source repair or contract was added. Assumptions
and Final are unchanged.

The two-hundred-and-forty-fifth full validation passed: 3629 build jobs and 17202 project declarations audited, every transitive axiom allowlisted.

## Continuation 244 — fiber counting under a measure-preserving exchange

Classified continuation 243 as progress and took its audit (3627 jobs,
17192 declarations) as the starting state. Proved the generic counting
lemmas for the exchange argument.

Added Proofs/FiberCounting (`mean_label_eq`,
`mean_label_eq_of_involutive`, `sum_indicator_le_one`, `sum_mean_label`,
`sum_label_le`, `label_mass_le`). Build fixes: a deprecated monotonicity
lemma and the false indicator reduced. A draft placeholder written during
the previous tick was replaced by full proofs before any build.

Next: the counting applied to the posterior family with the node exchange
(the parent's seed fixed, the node's block as the label, the pruned view's
probability as the weight). No assumption, source repair or contract was
added. Assumptions and Final are unchanged.

The two-hundred-and-forty-fourth full validation passed: 3628 build jobs and 17198 project declarations audited, every transitive axiom allowlisted.

## Continuation 243 — the candidate post-processings under the exchange

Classified continuation 242 as progress and took its audit (3626 jobs,
17181 declarations) as the starting state. Checked that both candidate
post-processings ignore internal nodes.

Added Proofs/HonestViewExchange (`internal_ne_leaf`, `honestPost_setTree`,
`simPost_setTree`). Build fix: a namespace for the hash input type.

Next: the generic fiber-counting lemma (a measure-preserving bijection
carrying one label value to another while fixing the view bounds the
joint probability by the view's probability over the number of values),
then its application to the node's value. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The two-hundred-and-forty-third full validation passed: 3627 build jobs and 17192 project declarations audited, every transitive axiom allowlisted.

## Continuation 242 — the commitment run's view under the exchange

Classified continuation 241 as progress and took its audit (3625 jobs,
17176 declarations) as the starting state. Proved the equal law of the
commitment run's pruned view under the exchange.

Added Proofs/CommitViewExchange (`stripFamily`,
`commit_view_exchanged`). Build fixes: the shared pruning import, the base
tree unfolded on both sides, and the history shift applied to the right
side only.

Next: the honest signing's inner view (the candidate post-processing does
not read an internal node), then the counting argument over the node's
value. No assumption, source repair or contract was added. Assumptions
and Final are unchanged.

The two-hundred-and-forty-second full validation passed: 3626 build jobs and 17181 project declarations audited, every transitive axiom allowlisted.

## Continuation 241 — what the exchange leaves unchanged

Classified continuation 240 as progress and took its audit (3624 jobs,
17158 declarations) as the starting state. Proved the pruned-history
equality for superset key lists and the signature's independence from
internal nodes.

Added Proofs/CommitPruned (`treeHistory_exchanged_subset`,
`openKey_setTree`, `attempt_setTree`, `payloadOf_setTree`,
`bodyOf_setTree`). Build fixes: unused-instance omissions only.

Next: the honest signing's pruned output under the exchange (the
commitment run's base, the finished state, the payload and body unchanged,
the pruned histories equal). No assumption, source repair or contract was
added. Assumptions and Final are unchanged.

The two-hundred-and-forty-first full validation passed: 3625 build jobs and 17176 project declarations audited, every transitive axiom allowlisted.

## Continuation 240 — the commitment run under the exchange

Classified continuation 239 as progress and took its audit (3623 jobs,
17137 declarations) as the starting state. Assembled the commitment run
under the exchange of an internal node.

Added Proofs/CommitRunExchange (`restBudget`, `commitBudget_eq`,
`commitRest_bounded`, `commitRun_eq`, `commitFour_congr`,
`commitTail_congr`, `commitRest_congr`, `baseTree`, `leafCount_pos`,
`exchanged_tree_eq`, `exchanged_leafKeys`, `commitRun_exchanged`). Build
fixes: a leaf rewrite by the node's value, the positivity lemma's
arguments, the leaf-count arithmetic facts supplied to omega, and the
included hypotheses trimmed.

Next: the pruned histories of the two commitment runs coincide (the
expansion histories pruned at any key list containing the exchanged
keys), then the signing output's pruned data under the exchange. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The two-hundred-and-fortieth full validation passed: 3624 build jobs and 17158 project declarations audited, every transitive axiom allowlisted.

## Continuation 239 — a run only appends to its starting history

Classified continuation 238 as progress and took its audit (3622 jobs,
17130 declarations) as the starting state. Proved the history-shift law
of program runs.

Added Proofs/RunHistoryShift (`appendHistory`,
`runFixed_history_shift`). Build fix: the cipher case closed by list
associativity.

Next: the commitment run under the exchange assembled from the
expansion's closed form, the finish map, the run congruence at the
leaves' keys and the history shift. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The two-hundred-and-thirty-ninth full validation passed: 3623 build jobs and 17137 project declarations audited, every transitive axiom allowlisted.

## Continuation 238 — the commitment phase after the expansion

Classified continuation 237 as progress and took its audit (3621 jobs,
17112 declarations) as the starting state. Split the commitment program
and proved the rest's query locality and its finish form under an
internal node's replacement.

Added Proofs/CommitPhaseExchange (`commitFour`, `commitTail`,
`commitRest`, `commitProgram_eq`, `leafKeys`, `queriesIn_collect`,
`queriesIn_hashCall`, `queriesIn_commitCall`, `queriesIn_commitFour`,
`queriesIn_commitTail`, `queriesIn_commitRest`, `setTree`,
`leaves_update`, `commitFour_update`, `commitTail_update`,
`commitRest_update`). Build fixes: qualified spec names, the tree update
as a function equality, the rest's locality by tactic.

Next: the commitment run under the exchange assembled from the expansion's
closed form, the run congruence at the leaves' keys and the finish map.
No assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The two-hundred-and-thirty-eighth full validation passed: 3622 build jobs and 17130 project declarations audited, every transitive axiom allowlisted.

## Continuation 237 — run congruence and the finish map

Classified continuation 236 as progress and took its audit (3620 jobs,
17093 declarations) as the starting state. Proved the two generic run
facts the commitment phase's comparison under the exchange needs.

Added Proofs/RunCongr (`step_done`, `step_hash`, `step_cipher`,
`QueriesIn`, `queriesIn_bind`, `answer_congr`, `runFixed_congr_family`,
`runFixed_bind_done`). Build fix: folded step lemmas instead of unfolding
the procedure, so the induction hypothesis matches.

Next: the commitment phase's queries lie at the leaves' keys and its
program with the exchanged tree is the program with a finish map, hence
the commitment run under the exchange. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The two-hundred-and-thirty-seventh full validation passed: 3621 build jobs and 17112 project declarations audited, every transitive axiom allowlisted.

## Continuation 236 — the expansion's run and entries under the exchange

Classified continuation 235 as progress and took its audit (3619 jobs,
17074 declarations) as the starting state. Carried the exchange through
the tree expansion's run and its recorded entries.

Added Proofs/TreeHistoryExchange (`pruneAt_cons_of_mem'`,
`exchangedKeys`, `run_exchanged`, `treeHistory_exchanged`). Build fixes:
a qualified seed-tree lemma, pruning the recorded calls by key membership
instead of unfolding, and a closing reflexivity removed.

Next: the commitment phase under the exchange (leaf commitments and hash
chain unchanged since leaves are unchanged), then the signing output's
pruned data. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-thirty-sixth full validation passed: 3620 build jobs and 17093 project declarations audited, every transitive axiom allowlisted.

## Continuation 235 — the tree expansion's run in closed form

Classified continuation 234 as progress and took its audit (3618 jobs,
17063 declarations) as the starting state. Proved the closed form of the
tree expansion's run, the first step of the commitment run's invariance
under the exchange.

Added Proofs/TreeRunClosed (`treeHistory`, `tree_run_eq`). Build fixes:
an import and an unused simp argument.

Checked the candidate opening: it reveals leaf seeds and hidden
commitments only, so internal path nodes never appear in the signature;
the exchange argument covers the internal keys and the leaf's key needs
the seed-hiding hypothesis. Next: the seed tree's run and its recorded
entries under the exchange (equal pruned histories, tree equal except at
the node). No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-thirty-fifth full validation passed: 3619 build jobs and 17074 project declarations audited, every transitive axiom allowlisted.

## Continuation 234 — the seed tree under the exchange

Classified continuation 233 as progress and took its audit (3617 jobs,
17049 declarations) as the starting state. Proved that the exchange of a
node's value changes the seed tree only at that node, under the tree's
goodness.

Added Proofs/TreeExchange (`parentKey`, `nodeBlock`,
`node_eq_output_nodeBlock`, `exchanged`, `nodeTweak_ne_of_sibling`,
`node_exchanged`). Build fixes: a qualified lemma name, the root case
through a helper, an unused hypothesis.

Next: the commitment run's recorded entries and commitments under the
exchange (the pruned signing output's invariance), then the goodness
event's bound. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-thirty-fourth full validation passed: 3618 build jobs and 17063 project declarations audited, every transitive axiom allowlisted.

## Continuation 233 — the exchange of a node's value

Classified continuation 232 as progress and took its audit (3616 jobs,
17034 declarations) as the starting state. Defined the exchange of a
node's value and proved it preserves the posterior family.

Added Proofs/NodeExchange (`swapNode`, `swapNode_apply_parent`,
`swapNode_apply_of_ne`, `swapNode_apply_left`, `swapNode_apply_right`,
`swapNode_involutive`, `swapNodeEquiv`, `matches_swapNode`,
`swapCandidates`, `posterior_swapNode`). Built first try.

Next: the tree expansion's run under the exchange (the exchanged family
computes the tree with the node's value exchanged and the same values
elsewhere), then the pruned signing output's invariance. No assumption,
source repair or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-thirty-third full validation passed: 3617 build jobs and 17049 project declarations audited, every transitive axiom allowlisted.

## Continuation 232 — the hidden keys with the leaf

Classified continuation 231 as progress and took its audit (3615 jobs,
17022 declarations) as the starting state. Defined the hidden keys with
the leaf's key, as the touching term's design requires.

Added Proofs/HiddenKeys (`hiddenKeys`, `mem_hiddenKeys`,
`root_key_mem_hiddenKeys`, `leaf_key_mem_hiddenKeys`,
`parent_mem_pathAddresses`, `pathKeys_subset_hiddenKeys`,
`freshKey_hiddenKeys`, `pruneAt_hiddenKeys_pruneAt_pathKeys`). Build
fixes: a membership simp set and a division rewrite.

Next: the exchange bijection on families for one path node (the
internal-key touching bound), and the explicitly named seed-hiding
hypothesis for the leaf's key. No assumption, source repair or contract
was added. Assumptions and Final are unchanged.

The two-hundred-and-thirty-second full validation passed: 3616 build jobs and 17034 project declarations audited, every transitive axiom allowlisted.

## Continuation 231 — the game-level agreement for both schemes

Classified continuation 230 as progress and took its audit (3614 jobs,
17020 declarations) as the starting state. Instantiated the game-level
pruned-run agreement for the candidate and simulated schemes.

Added Proofs/CandidateGamePrune (`candidate_runW_le_prune`,
`simulated_runW_le_prune`). Build fix: namespaces opened.

Also recorded the touching term's design: the hidden keys must include
the leaf's key (its commitment is a cipher call at that key); the PRG is
a pure function, so the leaf-key hit is computational and needs an
explicitly named seed-hiding hypothesis, while the internal path keys
follow from an exchange argument on the family. Next: the hidden keys
with the leaf, then that exchange argument. No assumption, source repair
or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-thirty-first full validation passed: 3615 build jobs and 17022 project declarations audited, every transitive axiom allowlisted.

## Continuation 230 — the candidate oracles' prune laws

Classified continuation 229 as progress and took its audit (3613 jobs,
16964 declarations) as the starting state. Instantiated the generic prune
laws for the candidate and simulated schemes' oracles.

Added Proofs/CandidatePrune (the oracle shape equalities and the prune
law, growth and consistency-keeping theorems of each oracle). Built first
try.

Next: the game-level agreement instantiated for both schemes, then the
touching term's bound from the hidden seeds' uniformity under the pruned
posterior. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-thirtieth full validation passed: 3614 build jobs and 17020 project declarations audited, every transitive axiom allowlisted.

## Continuation 229 — prune laws of program-shaped oracles

Classified continuation 228 as progress and took its audit (3612 jobs,
16931 declarations) as the starting state. Threaded the consistency
invariant through the game-level prune law (the shared lift needs a
possible history) and proved the generic prune laws of program-shaped
oracles.

Changed Proofs/GamePrune (`Possible`, `Consistent`, `Keeps`,
`consistent_of_mem_resampleW`; `PruneLaw` and `runW_le_prune` take the
invariant). Added Proofs/PruneLawRun (`touchesW_pruneShared`,
`runFixed_matches`, `runOracle`, `grows_run`, `keeps_run`,
`pruneLaw_run`, `grows_sample`, `keeps_sample`, `pruneLaw_sample`,
`grows_pure`, `keeps_pure`, `pruneLaw_pure`). Build fixes: the
family-free law unfolded before simp, instance omissions, a final
reflexivity.

Next: the candidate scheme's oracles instantiated (honest and simulated
signing, the public oracle, verification preparation), then the touching
term's bound. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-twenty-ninth full validation passed: 3613 build jobs and 16964 project declarations audited, every transitive axiom allowlisted.

## Continuation 228 — the game run agrees with its pruned run

Classified continuation 227 as progress and took its audit (3611 jobs,
16897 declarations) as the starting state. Proved the game-level
pruned-run agreement from abstract oracle prune laws.

Added Proofs/GamePrune (`setFamily`, `pruneW`, `touchesG`,
`FamilyFreeG`, `FamilyFreeT`, `PruneLaw`, `Grows`, `resampleW_setFamily`,
`mean_resampleW_const`, `touchesG_of_append`, `touchesG_of_mem_resampleW`,
`touchesG_runW`, `withWorld_withWorld`, `mean_hash_step`,
`runW_le_prune`). Build fixes: a hash-step world argument, the match
cases handled by case split instead of a restated matcher, an unused
hypothesis dropped, and a lint on a tactic combinator.

Next: the candidate scheme's oracle prune laws and growth (from the
shared lift and the oracle shapes), then the touching term's bound. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The two-hundred-and-twenty-eighth full validation passed: 3612 build jobs and 16931 project declarations audited, every transitive axiom allowlisted.

## Continuation 227 — the pruned-run agreement for shared program runs

Classified continuation 226 as progress and took its audit (3610 jobs,
16889 declarations) as the starting state. Lifted the pruned-run
agreement to the shared scheme's program runs.

Added Proofs/SharedPrune (`pruneShared`, `touchesW`, `FamilyFree`,
`runProgram_le_prune`, `prune_le_runProgram`). Build fixes: the
family-free law applied by rewriting, and decidability-instance
mismatches of the touching event closed by congruence.

Next: the game-level agreement (the adversary's run from a resampled
world and from its pruned world, each oracle call being a program run),
then the touching term's bound. No assumption, source repair or contract
was added. Assumptions and Final are unchanged.

The two-hundred-and-twenty-seventh full validation passed: 3611 build jobs and 16897 project declarations audited, every transitive axiom allowlisted.

## Continuation 226 — the reverse pruned-run agreement

Classified continuation 225 as progress and took its audit (3609 jobs,
16884 declarations) as the starting state. Proved the reverse direction
of the pruned-run agreement.

Added Proofs/PrunedRunReverse (`prune_le_run`). Built first try.

Next: the touching term's bound from the uniformity of the hidden seeds
under the pruned posterior, and the lift of both directions to the
shared scheme's program runs and the game's run. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-twenty-sixth full validation passed: 3610 build jobs and 16889 project declarations audited, every transitive axiom allowlisted.

## Continuation 225 — the run agrees with its pruned run until a hit

Classified continuation 224 as progress and took its audit (3608 jobs,
16867 declarations) as the starting state. Proved the identical-until-bad
agreement of the shared interpreter's run with its run from the pruned
history, in the direction the real-to-pruned step needs.

Added Proofs/PrunedRun (`posterior_cipher_step`,
`matches_of_mem_posterior`, `entry_key`, `pruneAt_cons_of_not_mem`,
`pruneAt_cons_of_mem`, `pruneResult`, `touches`, `touches_of_mem`,
`mean_fun_answer`, `run_le_prune`). Build fixes: the composition form
before the one-step lemma, a local posterior-support lemma, and
underscored statement binders.

Next: the reverse direction (pruned run below the run plus the touching
term), then the touching term's bound from the uniformity of the hidden
seeds under the pruned posterior. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The two-hundred-and-twenty-fifth full validation passed: 3609 build jobs and 16884 project declarations audited, every transitive axiom allowlisted.

## Continuation 224 — the posterior factorises over keys

Classified continuation 223 as progress and took its audit (3607 jobs,
16843 declarations) as the starting state. Proved the factorisation of
the posterior over keys needed by the pruned-world agreement.

Added Proofs/PosteriorPrune (`uniform_map_apply`, `matches_update`,
`mem_pruneAt_of_key`, `Fiber`, `exchange`, `card_fiber_mul`,
`posterior_coord_eq`, `keyOf`, `posterior_answer_eq_prune`). Build
fixes: substitution instead of dependent rewrites of the entry's key,
instance-generic fiber cardinals, the map-composition direction, and the
fiber membership by simp.

Next: the pruned-world agreement of a fixed-family run under the
posterior until a query hits the pruned keys, in the identical-until-bad
form. No assumption, source repair or contract was added. Assumptions
and Final are unchanged.

The two-hundred-and-twenty-fourth full validation passed: 3608 build jobs and 16867 project declarations audited, every transitive axiom allowlisted.

## Continuation 223 — the hidden path's entries and the pruned history

Classified continuation 222 as a finding and took the latest audit (3606
jobs, 16803 declarations) as the starting state. Defined the named
objects of the identical-until-bad route for the witness swap.

Added Proofs/HiddenEntries (`pathAddresses`, `mem_pathAddresses_iff`,
`pathKeys`, `entriesAt`, `pruneAt`, `matches_iff`, `pruneAt_possible`,
`pruneWorld`, `freshKey_pruneWorld`, `freshKey_pathKeys`,
`hiddenEntries`, `nodeEntry_mem_hiddenEntries`). Build fix: explicit
list arguments to the filter-append lemma.

Next: the posterior's answer law at a key depends only on the entries at
that key (the factorisation over keys), then the pruned-world agreement
of a program run until a query hits the path's keys. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The two-hundred-and-twenty-third full validation passed: 3607 build jobs and 16843 project declarations audited, every transitive axiom allowlisted.

## Continuation 222 — finding: the swap needs oracle-access continuations

Classified continuation 221 as progress and took its audit (3606 jobs,
16803 declarations) as the starting state. Before drafting the fork
identity, checked the recorded correction of the witness-swap term: the
mean-form per-call bound quantified over every continuation is
unsatisfiable below one, because the signing's commitment program records
the hidden path's cipher calls and the hidden leaf's commitment query, and
a continuation reading the output world recovers the witness.

Recorded the finding and the corrected route (audit/HUMAN_REVIEW.md): the
hidden entries and the pruned world as named candidates, the uniformity of
the hidden seeds under the pruned posterior, the identical-until-bad
agreement of the run, cut and fork with the pruned world, the equal law
of the witness and fake signings in the pruned world, and an explicit
insensitivity hypothesis on the events.

Next: Proofs/HiddenEntries (the hidden path's cipher entries and the
leaf commitment's table entry, the pruned world), then the hidden seeds'
uniformity under the pruned posterior. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

## Continuation 221 — the candidate verification law

Classified continuation 220 as progress and took its audit (3605 jobs,
16789 declarations) as the starting state. Proved the candidate scheme's
verification-preparation resampling law, the last oracle law the
run-with-world law needs for the candidate scheme.

Added Proofs/CandidatePrepLaw (`verifyAnswer`,
`prepareVerification_postLaw`). Build fix: qualified names only.

Next: the fork identity with the end-resampled family, then the fork and
event hybrids in mean form. No assumption, source repair or contract was
added. Assumptions and Final are unchanged.

The two-hundred-and-twenty-first full validation passed: 3606 build jobs and 16803 project declarations audited, every transitive axiom allowlisted.

## Continuation 220 — the run with its final world

Classified continuation 219 as progress and took its audit (3604 jobs,
16747 declarations) as the starting state. Threaded the final world
through the run and proved its resampling law, for the fork identity.

Added Proofs/RunWorld (`runW`, `run_eq_runW`, `withWorld`,
`runW_postLaw`). Build fixes: the verification law applied on the left
side, an unused simp argument.

Next: the candidate scheme's verification-preparation law, the fork
identity with the end-resampled family, then the fork and event hybrids
in mean form. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-twentieth full validation passed: 3605 build jobs and 16789 project declarations audited, every transitive axiom allowlisted.

## Continuation 219 — the run hybrid in mean form

Classified continuation 218 as progress and took its audit (3603 jobs,
16733 declarations) as the starting state. Recorded the finding that the
charged per-world swap slack is unsatisfiable below one, and started the
mean-form hybrid that the witness-swap term needs.

Added Proofs/MeanHybrid (`mean_bind_apply`, `mean_add_const`,
`run_le_run_mean`). Build fixes: the resampling laws' continuations
given explicitly, the hash-case helper restructured, the additive sides.

Next: the run with its final world and its resampling law, the fork
identity with the end-resampled family, then the cut, fork and event
hybrids in mean form. No assumption, source repair or contract was
added. Assumptions and Final are unchanged.

The two-hundred-and-nineteenth full validation passed: 3,604 build jobs and 16,747 project declarations audited, every transitive axiom allowlisted.

## Continuation 218 — the composed bound under the extended invariant

Classified continuation 217 as progress and took its audit (3602 jobs,
16729 declarations) as the starting state. Restated the mean-form gap
with the extended invariant and discharged the cipher-history
hypothesis in the composed bound, closing the row-stored term.

Added Proofs/SimulationGapCipher (`hgap_of_cipher`,
`forgery_le_cipher`, generated from the mean-form gap and the explicit
row bound). Built without fixes.

Next: the witness-swap mean, the last cipher-dependent term, through the
data-level hidden-share step. No assumption, source repair or contract
was added. Assumptions and Final are unchanged.

The two-hundred-and-eighteenth full validation passed: 3,603 build jobs and 16,733 project declarations audited, every transitive axiom allowlisted.

## Continuation 217 — the cipher-history invariant

Classified continuation 216 as progress and took its audit (3601 jobs,
16695 declarations) as the starting state. Extended the counted
invariant with cipher-consistency and a cipher-history budget, so the
named cipher-history hypothesis of the explicit row bound is derivable.

Added Proofs/CipherInvariant (`Consistent`, `runProgram_cipher`,
`honest_sign_cipher`, `simulatedSign_cipher`, `publicOracle_cipher`,
`InvC`, `invC_mono`, `invC_query`, `invC_update`, `invC_pub`,
`invC_honest`, `invC_simulated`, `invC_keygen`, `invC_resample`,
`invC_game`). Built without fixes.

Next: the simulation gap and the composed bound restated with the
extended invariant, discharging the cipher-history hypothesis. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The two-hundred-and-seventeenth full validation passed: 3,602 build jobs and 16,729 project declarations audited, every transitive axiom allowlisted.

## Continuation 216 — the row-stored term explicit in the composed bound

Classified continuation 215 as progress and took its audit (3600 jobs,
16690 declarations) as the starting state. Discharged the row-stored
hypothesis of the composed bound with the explicit bound.

Added Proofs/RowBoundExplicit (`rowBound`, `rowTerm_mean_le_explicit`,
`forgery_le_row`, the latter generated from the mean-form statement).
Build fixes: the explicit terms' namespaces, and a separate fiber bound
for the output map.

Next: the cipher-history invariant (the world's family matches its
history, and the history's length is budgeted) to discharge the named
hypothesis, then the witness-swap mean. No assumption, source repair
or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-sixteenth full validation passed: 3,601 build jobs and 16,695 project declarations audited, every transitive axiom allowlisted.

## Continuation 215 — the staleness term's bound

Classified continuation 214 as progress and took its audit (3599 jobs,
16682 declarations) as the starting state. Completed the fresh-parent-
key chain: the staleness term is bounded explicitly, so the row-stored
term of the simulation gap is explicit.

Added Proofs/StaleTermBound (`uniform_event_eq`, `count_key_root`,
`root_key_le`, `staleTerm_le`). Build fixes: the uniform-event lemma
made generic in the decidability instance, the step count written as a
natural-number cast, the additive side, a hypothesis beta-reduced, the
final constant given explicitly.

Next: the explicit row-stored hypothesis for the mean-form gap as a
corollary, then the witness-swap mean and the retry term. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The two-hundred-and-fifteenth full validation passed: 3,600 build jobs and 16,690 project declarations audited, every transitive axiom allowlisted.

## Continuation 214 — a stale last call forces the tree not to be good

Classified continuation 213 as progress and took its audit (3598 jobs,
16659 declarations) as the starting state. Connected the staleness of
the last call to the tree's goodness through the inputs' disjointness.

Added Proofs/StaleNotGood (`commitPhase`, `headBefore_eq`,
`phaseBudget`, `commitPhase_bounded`, `beforeBudget_eq`,
`runFixed_headBefore_split`, `leftEntry`, `commitPhase_support`,
`stale_notGood`, `stale_le_notGood`). Build fixes: an unused binder,
the run split's parts and boundedness given explicitly, the offset
injectivity's arguments and the leaf-address bound's leaf count made
explicit.

Next: the staleness term's bound, combining the tree's goodness
induction with the uniform root. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The two-hundred-and-fourteenth full validation passed: 3,599 build jobs and 16,682 project declarations audited, every transitive axiom allowlisted.

## Continuation 213 — the commitment calls' run

Classified continuation 212 as progress and took its audit (3597 jobs,
16648 declarations) as the starting state. Characterized the entries
recorded by the commitment phase before the last call.

Added Proofs/CommitEntries (`commitOf`, `commitEntry`, `CommitInput`,
`commit_entries`, `allPairs_nodup`, `ne_lastPair_of_mem_dropLast`,
`commit_address_lt`). Build fixes: the run split's boundedness proofs
given explicitly, the recorded entries named and given explicitly in
the witness, an unused simp argument. A validation launched before the
last fix was stopped and relaunched.

Next: a stale last call forces the tree not to be good for the starting
keys, then the staleness term's bound. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The two-hundred-and-thirteenth full validation passed: 3,598 build jobs and 16,659 project declarations audited, every transitive axiom allowlisted.

## Continuation 212 — the tree's goodness along the expansion

Classified continuation 211 as progress and took its audit (3596 jobs,
16625 declarations) as the starting state. Proved the induction over
the expansion steps under the posterior family.

Added Proofs/TreeGoodInduction (`treeOf`, `notGood`,
`expandStep_run_eq`, `tree_good_le`). A first draft briefly held two
placeholders, replaced before any build. Build fixes: the answer
unfolded by reflexivity, the zero case proved by cases on the root's
membership, the step split rewritten under the binder by simp, the
step's history spelled out, the additive-monotonicity side.

Next: the commit phase after the tree (its inputs disjoint from the last
call) and the staleness term's bound. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The two-hundred-and-twelfth full validation passed: 3,597 build jobs and 16,648 project declarations audited, every transitive axiom allowlisted.

## Continuation 211 — one expansion step under the posterior family

Classified continuation 210 as progress and took its audit (3595 jobs,
16610 declarations) as the starting state. Proved the per-step bound of
the fresh-parent-key chain.

Added Proofs/TreeStepFresh (`keysOf`, `keysOf_card_le`, `mem_keysOf`,
`Good`, `count_key_hits`, `posterior_key_le`, `step_inputs_fresh`,
`child_key_le`, `step_le`, `good_step`). Build fix: the cipher-input
injectivity lemma's namespace.

Next: the induction over the expansion steps under the posterior family
(the tree's goodness fails with probability at most the root's key
being in the set plus the steps times the step bound). No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The two-hundred-and-eleventh full validation passed: 3,596 build jobs and 16,625 project declarations audited, every transitive axiom allowlisted.

## Continuation 210 — the tree expansion's run step by step

Classified continuation 209 as progress and took its audit (3594 jobs,
16594 declarations) as the starting state. Started the fresh-parent-key
chain with the tree expansion's step structure.

Added Proofs/TreeRunEntries (`expandStep`, `treeThrough_succ`,
`expandStep_bounded`, `runFixed_tree_succ`, `expand_run_support`,
`TreeInput`, `tree_entries`). Build fixes: unused simp arguments, the
recorded entries given explicitly in the witness, the list appends
rewritten.

Next: the expansion step under the posterior family (a node whose key is
not in the starting history's keys has children whose keys are in it
with small probability), then the induction over the steps. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The two-hundred-and-tenth full validation passed: 3,595 build jobs and 16,610 project declarations audited, every transitive axiom allowlisted.

## Continuation 209 — the row-stored mean bounded by the staleness term

Classified continuation 208 as progress and took its audit (3593 jobs,
16562 declarations) as the starting state. Assembled the row-stored
mean bound at the split: the run before the last call under the
posterior family, the resampling at the split point, and the bound after
the last call unless it is stale.

Added Proofs/RowStoredPosterior (`runFixed_cipher_matches`,
`runFixed_cipher_length_le`, `posterior_support_matches`, `staleOf`,
`after_le`, `staleTerm`, `mean_eq_bind`, `rowTerm_mean_le`). Build
fixes: indicator and run-invariant namespaces, the hash-input
namespace, a no-op simplification, the one-bound lemma's name, the
indicator case split, the map form before the posterior bound, an
unused instance.

Next: the staleness term's bound through the fresh-parent-key chain of
the seed tree under the posterior family. No assumption, source repair
or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-ninth full validation passed: 3,594 build jobs and 16,594 project declarations audited, every transitive axiom allowlisted.

## Continuation 208 — the row-stored event after the last call

Classified continuation 207 as progress and took its audit (3592 jobs,
16551 declarations) as the starting state. Placed the row-stored event
after the last call inside the fixed set.

Added Proofs/RowStoredAfter (`map_true_mono`, `map_const_true`,
`map_true_le_indicator`, `bind_true_le_bind_true`, `stale`, `fixedSet`,
`fixedSet_card_le`, `rowQuery_other`, `rowStored_mem`). Build fixes:
the map-truth lemma's namespace, the two entry types disambiguated, an
unused parameter.

Next: the assembly of the row-stored mean bound at the split with the
staleness term named. No assumption, source repair or contract was
added. Assumptions and Final are unchanged.

The two-hundred-and-eighth full validation passed: 3,593 build jobs and 16,562 project declarations audited, every transitive axiom allowlisted.

## Continuation 207 — counting the last blocks that hit a fixed set

Classified continuation 206 as progress and took its audit (3591 jobs,
16544 declarations) as the starting state. Counted the last blocks
hitting the fixed set and bounded the row query's membership under the
posterior family.

Added Proofs/RowStoredCount (`card_instance_eq`, `count_hits`,
`posterior_row_le`). Build fixes: an explicit cast of the count bound,
and the decidability and finiteness instances of the membership event
bridged explicitly, since the posterior event bound is stated with
classical instances.

Next: the assembly of the row-stored mean bound at the split, with the
trace invariants bounding the inner table's support and the last call's
freshness as a named term. No assumption, source repair or contract was
added. Assumptions and Final are unchanged.

The two-hundred-and-seventh full validation passed: 3,592 build jobs and 16,551 project declarations audited, every transitive axiom allowlisted.

## Continuation 206 — the row-stored event reduced to the last block

Classified continuation 205 as progress and took its audit (3590 jobs,
16529 declarations) as the starting state. Reduced the row-stored event
to the last block's membership in a set fixed before the last call.

Added Proofs/RowStoredReduce (`lastPair_eq`, `lastPair_fst`,
`lastBlock`, `commitsWith`, `lastRowQuery`, `rowStored_reduce`,
`lastRowQuery_injective`). Build fixes: an unused simp argument, the
row-query injectivity lemma's namespace, the evaluation at the last
pair through an explicit pair equation, and the concatenation lemma's
namespace.

Next: the counting of last blocks hitting the fixed set and the
posterior bound of the row-stored term at the split, with the last
call's freshness as a named term. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The two-hundred-and-sixth full validation passed: 3,591 build jobs and 16,544 project declarations audited, every transitive axiom allowlisted.

## Continuation 205 — the rows' table support

Classified continuation 204 as progress and took its audit (3589 jobs,
16517 declarations) as the starting state. Proved the table and state
facts about the partial row hashes.

Added Proofs/RowsSupport (`step_hash`, `step_cipher`, `step_done`,
`hashCall_bind`, `rows_defined`, `runFixed_bind_done`). Build fixes:
the digest name, the cipher-step lemma, the bind reduced at the hash
constructor, the answer's digest component, and the update at another
input closed through the definition rather than an instance-sensitive
rewrite.

Next: the row-stored event reduced to the last block's membership in a
set fixed before the last call, with the row query's injectivity in the
last block. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The two-hundred-and-fifth full validation passed: 3,590 build jobs and 16,529 project declarations audited, every transitive axiom allowlisted.

## Continuation 204 — the head split at the last commitment call

Classified continuation 203 as progress and took its audit (3588 jobs,
16497 declarations) as the starting state. Split the head's initial run
at the last commitment call, the point where the row-stored bound draws
its fresh block.

Added Proofs/HeadCommitSplit (`allPairs_ne_nil`, `lastPair`,
`allPairs_split`, `commit_collect_split`, `lastAddress`, `lastKey`,
`headBefore`, `headAfter`, `headInit_eq_split`, `beforeBudget`,
`headBudget_split`, `headBefore_bounded`, `headAfter_bounded`,
`runFixed_headInit_split`). Build fixes: deprecated lemma names, the
leaf count made explicit at every use, associativity rewritten under
binders with the commit-decomposition lemma, a budget rewrite that
touched types replaced by monotonicity, and a congruence that closes the
split equality.

Next: the rows' table support and the row-stored event's reduction to
membership of the last block in a set fixed before the last call, then
the posterior bound. No assumption, source repair or contract was
added. Assumptions and Final are unchanged.

The two-hundred-and-fourth full validation passed: 3,589 build jobs and 16,517 project declarations audited, every transitive axiom allowlisted.

## Continuation 203 — fresh-input answers under the posterior family

Classified continuation 202 as progress and took its audit (3587 jobs,
16493 declarations) as the starting state. Started the row-stored mean
bound with the per-call facts under the posterior family.

Added Proofs/PosteriorFresh (`posterior_answer`, `posterior_event_le`,
`posterior_target_le`, `posterior_mem_le`). Build fix: the composed
function made explicit before rewriting with the posterior answer.

Next: the fresh-key chain of the per-signature seed tree under the
posterior family, then the last commitment block's uniformity and the
row-stored union bound. No assumption, source repair or contract was
added. Assumptions and Final are unchanged.

The two-hundred-and-third full validation passed: 3,588 build jobs and 16,497 project declarations audited, every transitive axiom allowlisted.

## Continuation 202 — the composed bound with the mean-form gap

Classified continuation 201 as progress and took its audit (3586 jobs,
16492 declarations) as the starting state. Stated the composed forgery
bound with the mean-form gap.

Added Proofs/ForgeryBoundMean (`forgery_le_mean`, derived from the
trace-form statement with the mean-form gap). Built without fixes.

Next: the row-stored mean bound from the leaf commitments' uniformity
under fresh keys over the resampled family. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The two-hundred-and-second full validation passed: 3,587 build jobs and 16,493 project declarations audited, every transitive axiom allowlisted.

## Continuation 201 — the simulation gap in mean form

Classified continuation 200 as progress and took its audit (3585 jobs,
16486 declarations) as the starting state. Composed the charged hybrids,
the expected-charge bounds and the candidate oracles' resampling laws
into the simulation gap with mean-form hypotheses, completing the
correction begun at continuation 193.

Added Proofs/SimulationGapMean (`chargeOf`, `invT_resample`,
`hgap_of_mean`). Build fixes: the additive-monotonicity lemmas' sides,
the resampling-invariant's implicit arguments, the event-hybrid
namespace.

Next: the composed forgery bound with the mean-form gap, then the
row-stored mean bound from the leaf commitments' uniformity under fresh
keys. No assumption, source repair or contract was added. Assumptions
and Final are unchanged.

The two-hundred-and-first full validation passed: 3,586 build jobs and 16,492 project declarations audited, every transitive axiom allowlisted.

## Continuation 200 — the candidate oracles' resampling laws

Classified continuation 199 as progress and took its audit (3584 jobs,
16396 declarations) as the starting state. Instantiated the generic
resampling laws at the candidate scheme's oracles.

Added Proofs/CandidateResample (`payloadOf`, `signedOf`, `bodyOf`,
`honestPost`, `honest_sign_shape`, `honest_postLaw`, `simPost`,
`simulated_sign_shape`, `simulated_postLaw`, `publicOracle_postLaw`,
`uniformOfFintype_congr`, `keygen_resampled`). Build fixes: ambiguous
names, world type annotations, the pattern of the observation cases,
matches from different definitions closed by congruence or by rewriting
the split hypothesis into the other side, and the uniform family's
instance mismatch closed by subsingleton elimination instead of
definitional unfolding, which timed out.

Next: the simulation gap restated with the mean-form hypotheses through
the charged hybrids. No assumption, source repair or contract was
added. Assumptions and Final are unchanged.

The two-hundredth full validation passed: 3,585 build jobs and 16,486 project declarations audited, every transitive axiom allowlisted.

## Continuation 199 — the shared scheme's resampling laws

Classified continuation 198 as progress and took its audit (3583 jobs,
16382 declarations) as the starting state. Proved the generic forms of
the resampling laws that the candidate scheme's oracles instantiate.

Added Proofs/SharedResample (`bind_congr_support`,
`runFixed_cipher_suffix`, `matches_of_append`, `posterior_impossible`,
`runProgram_resample'`, `resample_idem`, `postLaw_sample`,
`postLaw_run`, `posterior_nil`). Build fixes: lint omissions, the
sampling law's rewrite targets, the run law's final bind exchange, and
the empty-history posterior, whose identification with the uniform
family timed out at concrete bit-string types and is stated generically
over opaque key and block types instead.

Next: the candidate scheme's oracles in the program-running shape
(honest and simulated signing, the public oracle) and key generation as
a resampled world; then the simulation gap restated with the mean-form
hypotheses. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-ninety-ninth full validation passed: 3,584 build jobs and 16,396 project declarations audited, every transitive axiom allowlisted.

## Continuation 198 — the expected replay charges

Classified continuation 197 as progress and took its audit (3582 jobs,
16340 declarations) as the starting state. Proved the expected bounds of
the replay charges from a resampled key.

Added Proofs/ChargeCutExpect (`mean_mul_left`,
`mean_resampleW_update`, `resampleCut`, `cut_postLaw`,
`chargeCut_mean_le`, `chargeExperiment_le`, `chargeFork_le`). Build
fixes: match expressions reduced before rewriting, binds reassociated
inside each case, the resampled key generation peeled twice, and a
rewrite that matched through structure eta replaced by a dedicated lemma
with its function passed explicitly.

Next: the candidate scheme's oracle resampling laws (honest and
simulated signing, the public oracle) from the program-run resampling
law, and key generation as a resampled world; then the simulation gap
restated with the mean-form hypotheses. No assumption, source repair or
contract was added. Assumptions and Final are unchanged.

The hundred-and-ninety-eighth full validation passed: 3,583 build jobs and 16,382 project declarations audited, every transitive axiom allowlisted.

## Continuation 197 — the replay hybrids with the charge

Classified continuation 196 as progress and took its audit (3581 jobs,
16289 declarations) as the starting state. Restated the replay hybrids
with the charge.

Added Proofs/ChargeCut (`chargeCut`, `chargeBranch`,
`chargeExperiment`, `chargeFork` and the six hybrids). Build fixes: the
per-call bound's continuation type must be Boolean for the event
experiment, so the bound became an explicit parameter of each theorem,
and the call sites' argument order.

Next: the cut's resampling law and the expected bounds of the cut
experiment's and fork charges, then the candidate scheme's oracle
resampling laws. No assumption, source repair or contract was added.
Assumptions and Final are unchanged.

The hundred-and-ninety-seventh full validation passed: 3,582 build jobs and 16,340 project declarations audited, every transitive axiom allowlisted.

## Continuation 196 — the expected charge from a resampled world

Classified continuation 195 as progress and took its audit (3580 jobs,
16263 declarations) as the starting state. Stated and proved the
expected-charge bound: at every signing query the resampling law moves
the fresh posterior draw to the result world, so the charge at the call
is averaged over the resampled world and bounded by the per-call average
bound, and the remaining charge by the induction hypothesis.

Added Proofs/ChargeExpect (`mean` and its laws, `PostLaw`,
`postLaw_bind`, `postLaw_mean`, `hashTable_of_mem`,
`resampleW_update`, `charge_succ`, `charge_mean_le`). Build fix: a
rewrite that matched the wrong occurrence through structure eta, made
explicit.

Next: the cut and fork charges with their expected bounds, then the
candidate scheme's oracle resampling laws. No assumption, source repair
or contract was added. Assumptions and Final are unchanged.

The hundred-and-ninety-sixth full validation passed: 3,581 build jobs and 16,289 project declarations audited, every transitive axiom allowlisted.

## Continuation 195 — the run hybrid with a world-dependent charge

Classified continuation 194 as progress and took its audit (3579 jobs,
16233 declarations) as the starting state. Examined the fork
experiments under the resampling scheme and found that their laws differ
from the shared-family fork (the branches share the family), so the
transfer of the composed bound to a resampling scheme is not available
through an equality; chose instead to keep the shared-family game and
charge the per-call term at the world of each signing query, to be
averaged afterwards with the resampling law.

Added Proofs/ChargeRun (`charge`, `run_le_run_add_charge`, mirroring
the counted run hybrid with the cost-bind lemma). Build fix: the
additive-monotonicity lemma's side.

Next: the expected charge from a resampled world under the oracle
commutation laws, then the cut and fork charges. No assumption, source
repair or contract was added. Assumptions and Final are unchanged.

The hundred-and-ninety-fifth full validation passed: 3,580 build jobs and 16,263 project declarations audited, every transitive axiom allowlisted.

## Continuation 194 — the game under resampling

Classified continuation 193 as progress and took its audit (3578 jobs,
16212 declarations) as the starting state. Stated the game-level
resampling equality abstractly, with the oracle commutation laws as
hypotheses to be discharged for the candidate scheme from the program-run
resampling law.

Added Proofs/GameResample (`resampleW`, `resampled`, `resampleW_bind`,
`run_resample`, `terminalLaw_resample`, `advantage_resample`). Build
fixes: unreduced match expressions after the case split (a `dsimp only`
and the projection lemmas of the resampling scheme), lint omissions.

Next: the cut, continuation and fork experiments under resampling, then
the candidate scheme's oracle commutation laws and key generation. No
assumption, source repair or contract was added. Assumptions and Final
are unchanged.

The hundred-and-ninety-fourth full validation passed: 3,579 build jobs and 16,233 project declarations audited, every transitive axiom allowlisted.

## Continuation 193 — the cipher resampling law

Classified continuation 192 as progress and took its audit (3577 jobs,
16195 declarations) as the starting state. Consolidated the reduction's
status in the README and the review ledger, then examined the row-stored
bound and found the per-world cipher-dependent hypotheses unsatisfiable
at a fixed family (recorded in the review ledger).

Added Proofs/CipherResample (posterior family, `runFixed_resample` by
induction on the fuel with the ideal cipher's posterior step at cipher
actions, `resample`, `resample_bind_resample`, `runProgram_resample`).
Build fixes: ambiguous `runFixed` under the opened namespaces, a
constant-bind rewrite that closed the goal early, the bit-string type's
namespace.

Next: the game-level resampling equality (the run with the family
resampled before each signing query equals the run), then the restated
simulation-gap hypotheses over the resampled family. No assumption,
source repair or contract was added. Assumptions and Final are
unchanged.

The hundred-and-ninety-third full validation passed: 3,578 build jobs and 16,212 project declarations audited, every transitive axiom allowlisted.

## Continuation 192 — the composed bound with payload consistency discharged

Classified continuation 191 as progress and took its audit (3576 jobs,
16194 declarations) as the starting state. Stated the composed forgery
bound with payload consistency discharged.

Added Proofs/ForgeryBoundTrace (its statement generated from the
composed bound's and the trace-budget gap's). Build fixes: the colon
before the conclusion and the positivity hypothesis converted for the
row-stored term.

Next: the remaining three terms, starting with the row-stored event's
bound. No assumption, source repair or contract was added. Assumptions
and Final are unchanged.

The hundred-and-ninety-second full validation passed: 3,577 build jobs and 16,195 project declarations audited, every transitive axiom allowlisted.
