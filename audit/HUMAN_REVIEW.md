# Human review boundary

This file is not imported into Lean. Items here are not mathematical assumptions
and are not discharged by a successful build. No issue is silently repaired.

## Source correspondence

A human must compare all formal definitions with the pinned PDF, including
indexing, bit and byte order, encodings, and concrete primitive instantiations.
Comments and extracted text are not a certificate of faithful transcription.

## Source issues identified during inspection

1. **§2.1, printed pp. 3–4, equations (1) and (2).** Equation (1) defines
   `Pα(X) = P0(X) X + Σ γj fj(P(X))`. Equation (2) checks
   `Pα(Δ) Δ = v0 Δ + Σ γj fj(v)`. The additional factor on the left does not
   follow from equation (1). The page image confirms that this is in the PDF,
   not an extraction artifact. `Final.literal_piop_not_complete` is a checked
   counterexample over a field of size `2^128`: valid zero witness and constraint,
   `P₀ = X`, `Pα = X²`, and `Δ` different from zero and one. Honest evaluation
   reduces the printed check to `Δ³ = Δ²`, which is false. This concerns the
   generic introductory PIOP, not an execution or attack on an implementation.

   The printed soundness bound is now also refuted in
   `Proofs/PIOPSoundnessDiscrepancy.lean`. Let d=2, f=1, P0=P1=X, and let S be
   the three cube roots of one. Reply to gamma with P_alpha=gamma*X^2+X.
   All openings are consistent, every displayed degree bound and binary
   constant-term condition holds, and the constraint has no witness. The
   literal verifier nevertheless accepts for every gamma and every delta in S.
   The resulting probability one exceeds the printed 1/q+(1-1/q)*2/3 bound.
   The existence and cardinality of S are proved in every submitted Table-2
   field; the printed page-4 formula was visually rechecked. This refutes the
   generic introductory claim, not the detailed BLC challenge-image set or a
   full signature execution. No source equation has been repaired.
2. **§5.1, Theorem 5.1, printed pp. 42–43.** The stated rigorous lower bound
   relies on a step explicitly called heuristic, followed by approximations.
   Neither independence of collision events nor conditioning on arbitrary solver
   success is justified. The printed inequality for `nby` also has the opposite
   direction from the preceding parameter constraint. These steps cannot be
   entered as proved lemmas or disguised as SD hardness.

   The exact support-counting part is now proved. With n=w*m, there are m^w
   regular supports among choose(w*m,w) weight-w supports. A uniform ambient
   permutation sends a fixed support uniformly over those supports; the proof
   constructs equal-fiber bijections instead of assuming this distribution.
   `Proofs/SDReductionProbability.lean` transfers the law to the actual flattened
   field vector and proves a lower bound for existence of some regular solution.
   The latter event is not identical to the fixed-witness event used in counting.
   `Proofs/SDReductionDiscrepancy.lean` checks a binary n=4, w=2, k=1 instance
   with H=0, y=0: every permutation admits a regular solution, so that event has
   probability 1, while a fixed weight-2 witness becomes regular with probability
   4/6. This refutes the pointwise instance-event equality, not by itself the
   claimed final reduction bound or an assertion about seed-generated keys.
   Both printed pages were visually rechecked. The first counting display uses
   n/d rather than n/w; d is not a parameter of Theorem 5.1. The exact result is
   recorded in unambiguous chunk-size variables, not as a repair of that display.

   `Spec/SDReduction.lean` now specifies the displayed randomized algorithm,
   retaining its full-syndrome-only check and inverse permutation. Correctness
   requires the explicit premise that the supplied solver's possible returned
   vectors are RSD solutions; weight is not checked by A_sd. The deterministic
   uniqueness implication is proved, but no probability of uniqueness or
   conditional solver-success equality follows from it. Distributional
   correspondence, success loss and runtime accounting remain unproved.

   The larger-field counting issue can now also be stated precisely:
   `Proofs/ScaledWitness.regular_vector_count` proves (m*(q-1))^w regular
   vectors for q field elements, while the heuristic on p. 43 uses m^w-1
   competing vectors and 2^(n-k_rsd) syndromes despite stating an arbitrary
   finite field. How that heuristic is intended beyond the binary case remains
   unresolved; no missing amplitude factor or field-size correction is assumed.
3. **§5.3, printed p. 44.** The submission explicitly defers its formal EUF-CMA
   proof to a future version. Establishing that claim requires a new proof.
4. **§3.1.1 / Algorithm 2, printed pp. 11–12.** The prose specifies `[H′ | I]`,
   but line 5 prints `[I | H′] · x_A`; `x_A` has not been defined. Must be resolved
   before asserting exact key generation correspondence. The staged definitions
   in `Spec/KeyGeneration.lean` now preserve the missing binding. A checked
   block permutation relates the orientations, and a binary counterexample
   shows that leaving the coordinates unchanged can change the syndrome.
5. **§3.2.2, printed p. 18.** ExpandH prose says row-wise; the pseudocode fills
   columns. SampleIntegers assigns `B % m` although its assembled integer is `v`.
6. **§3.2.2, printed pp. 19–20.** Cipher grinding initializes XOF with a counter
   but the following prose says lines 1–4 are independent of the counter. The
   claimed omission of challenge expansion when grinding is zero also needs
   review. Bit/byte units in `GetBytes(4 · λ)` need clarification. Line 10 uses
   a single-subscript `Extract_(wpow−1)`, whereas the text defines only the
   two-endpoint `Extract_(m→n)`. The counter's `MapToBits` order is also unstated.
   Both page images were inspected; no extraction slice or endianness is invented.
7. **Algorithms 8–9, printed pp. 23–24.** Algorithm 8 pads `path` to exactly
   `Topen · λ` bits. Algorithm 9 line 12 reads a sibling only when the remaining
   path length is strictly smaller than that bound, so the first non-sibling
   branch rejects a correctly sized path. The page image confirms the guard.
   `Proofs.reconstruction_rejects_full_path` proves this for arbitrary parameters;
   `Final.commitment_discrepancies` includes a concrete Table 4 instance.
   Algorithm 7's construction and Algorithm 8's literal loop are now transcribed.
   `Proofs.BAVC.categoryI_opening_rejected` checks a complete successful opening:
   tau = 11, N = 2048, lambda = 128, Topen = 109, hidden index 1 in repetition
   10 and index 0 in the other repetitions. All 35 loop iterations append six
   sibling seeds, then Algorithm 9 rejects on its first iteration. The result
   holds for every key, independently of cipher/hash outputs. It still does not
   execute a full signature. The full staged Algorithm-9 body is now transcribed;
   `Proofs.BAVCReconstruction.categoryI_full_rejection` and the strengthened
   final statement prove its explicit capacity rejection for every supplied
   nodes binding, before that variable is accessed.
   Both algorithms also test `|queue| ≥ 2` after dequeuing, which needs review.
   Algorithm 9 switches from `tree` to an undefined `nodes` array on line 21.
8. **Algorithms 10 and 12, printed pp. 28 and 30.** Algorithm 10 line 24 hashes
   `(haux, α′plain, α′base, Δwit)`; Algorithm 12 line 26 hashes only the first three
   fields. Both page images confirm this. For ordinary concatenation of serialized
   components, `Final.commitment_discrepancies` proves distinct inputs whenever
   the last field has positive length. Distinct hash inputs do not by themselves
   prove distinct hash outputs or an end-to-end verification failure.
9. **§2.2 and Table 3, printed pp. 8 and 40.** The text requires
   `n = w · ∏ μj`. The printed binary parameter rows instead give:

   | Category | Printed n | w · ∏ μj | n / w | ∏ μj |
   |---|---:|---:|---:|---:|
   | I | 10360 | 10752 | 185 | 192 |
   | III | 18396 | 18688 | 252 | 256 |
   | V | 19864 | 19968 | 191 | 192 |

   `Final.table3_dimension_mismatch` checks all three inequalities. An unstated
   shortening/padding convention may be intended, but none has been invented.
10. **§3.2.5, printed pp. 26–30.** The prose orders the consistency mask as
    `[M | I]`, while Algorithms 10 and 12 use `[I | M]`. Algorithm 12 initializes
    `reval` but subsequently updates `rshare`; it also uses an undefined `φ_μe`.
    The evaluation challenge concatenates indices without explicitly applying the
    Gray map used in the line-opening formulas. These need a source policy.

    Algorithm 12 line 21 also subtracts `alpha_plain * Delta_inv` from a matrix
    typed over F2 while `Delta_inv` is typed as a single extension-field element.
    A representation map may be intended, but is not specified on that line.
    The new consistency proof uses the displayed per-execution phi challenge
    from the prose; it does not identify these two types without a map.
11. **§3.2.6, printed pp. 31–36.** The mask polynomial is variously written with
    exponent `i` and `d−2−i`. The mux gate defaults to the first coordinate while
    the witness representation omits the last coordinate. The arity indexing in
    Algorithms 17–20 and the degree annotation of Algorithm 15 need review.

    The mux mismatch is now proved in
    `Proofs.PIOPEncodingDiscrepancies.mux_disagrees_with_tensor_factor`: over F2,
    stored selector `(1,0)` completes to `(1,0,0)`. Its dot product with `(1,0,0)`
    is 1, while the printed mux returns 0. The page image confirms both formulas.
    A coordinate permutation could repair this relationship, but none is applied.

    The degree annotation is also refuted: the printed Algorithm 15 maps witness
    polynomials `(X,0)` to `X²−X`. Both witness bits at zero are zero, and the
    output constant term is zero, but the degree is 2. This is proved over any
    field in `Proofs.PIOPEncodingDiscrepancies.unitary_degree_annotation_counterexample`.
    The actual degree-at-most-two bound, and resulting degree-at-most-d PIOP
    output bound for `d ≥ 2`, are proved separately in `Proofs/PIOPDegree.lean`.

    The mismatch now also reaches the detailed PIOP's constant term through its
    actual flat parser. `Proofs/WitnessPIOPDiscrepancy.lean` uses radices (3,3),
    w=1, m=9 and sampled position 0. Algorithm 1 produces witness [1,0,1,0] and
    a checked exact-weight-one solution to the syndrome instance with matrix
    [1,0,...,0] and syndrome 1. With constant witness lines and zero randomness,
    the literal detailed PIOP has P_alpha(0)=-1, for every field generator and
    unitary batching challenge. Dimensions match in this example. It is not a
    submitted parameter row, full signature, or claim that a concrete BLC
    implementation produces these particular lines. No coordinate repair is used.
12. **Algorithm 11, printed p. 29.** The counter is explicitly 32 bits, but
    increment at `2^32−1` has no specified behavior. `Spec/BLCRetry.lean` marks
    this operation undefined; it neither wraps nor invents a rejection result.
    Termination is conditional on a first successful counter in range. No
    existence or probabilistic success bound is assumed.
13. **Algorithm 6, printed p. 17 / §3.2.1, p. 15.** The block count uses an
    otherwise undefined `nblock-bitsize`; the surrounding primitive definition
    instead defines `nctx-bitsize`. Line 5 declares `nblocks*(lambda/8)` parsed
    bytes, although Category III's Enc produces 256-bit outputs for lambda=192.
    `Proofs.categoryIII_prg_parse_width_mismatch` proves unequal incoming and
    declared output bit counts for every positive block count. A lossy parser
    might be intended, but no truncation rule is given. The PDF page was inspected;
    no substitution of Enc*, replacement width, or truncation has been applied.

## Detailed arithmetic correspondence boundary

`Spec/WitnessExpansion.lean` starts after Algorithm 1's still-unresolved PRG and
integer sampler. Its successive quotient/remainder updates, last-coordinate
omission, and increasing-loop concatenations are explicit. The solution is
constructed from the original positions, before local division. Its flat size
is w*m, leaving n=w*m separate. The inverse coordinate map is explicitly least
significant radix first, as dictated by line 9. For positions below the radix
product, both the structured and actual serialized witnesses recover the input.
The checked Table-3 range inequality is weaker than the false tensor dimension
equality and does not choose a padding or shortening convention.

Generated selectors pass the actual unitary arithmetic for all challenges.
The converse is now proved for the binary selector polynomial D(Y), together
with the packed-polynomial equivalence in all three exact Table-2 quotients.
`Proofs/UnitaryPacking.lean` links that result to the recursive unitaryLayers
implementation. This concerns binary constants and their defining constraints,
not arbitrary extension-field evaluations of witness lines.

The source's p. 32 exact-degree expression for D(Y) must be understood separately
from the proved upper bound: for a valid selector D is zero, so that exact degree
equality cannot hold literally. The proof uses only degree below 32 and the
checked arity/layer bounds, not the false equality.

`Spec/PIOPArithmetic.lean` uses the exponent `d−2−i` printed in Algorithms 13–14,
not the conflicting `i` in the prose. Layer widths store `μj−1`; layer order is
the displayed bottom-up recurrence. Flat input parsing is explicit, with bounds
carried by `Fin`; no default values mask out-of-bounds accesses. The recurrence
uses its bound row index, while Algorithm 17's `h`/`ℓ` variable mismatch remains
an unresolved pseudocode discrepancy.

`Spec/Batching.lean` implements Algorithm 21's `[I | H′]` orientation and the
zero-padding formula of equation (7). Its generic algebra map and parameter `ξ`
must still be connected to the specified extension fields. Linearity and the
residual identity are proved without assuming injectivity. Table-2 quotient power
bases and the injectivity of the full padded embedding are now established in
`Proofs/FieldRepresentation.lean` and `Proofs/ConcreteEncodings.lean`. Irreducibility,
the resulting field instances and byte representation remain mathematical and
correspondence obligations, not human-approved axioms.

`Spec/DomainSeparation.lean` implements Algorithm 5 with least-significant-first
bit indices. Its bit proofs require only `26 ≤ λ`, which the three source security
levels satisfy. Its hash-prefix theorem is about inputs, not collision resistance
or output inequality. Concrete primitives remain separate.

`Spec/BAVC.lean` gives Algorithm 7's increasing-index tree loop, interleaved leaf
layout, ordered digest concatenation, both hash levels and opening key. Node zero
is excluded from the key's allocated address type. The loop invariant proves
independence from arbitrary initial memory for every allocated node when tau*N > 0.
Domain byte 1 and all payload bits are explicit in the hash input.

`Spec/BAVCOpening.lean` preserves the post-dequeue queue-length guard verbatim.
The sum of queued addresses proves termination. Explicit source rejection is
separate from undefined queue/tree reads; these are not silently given default
seeds. The singleton-queue theorem demonstrates that the printed guard appends
no sibling seeds for one execution. This is an algorithmic observation, not a
claim about the security of the submitted multi-execution parameters.

`Proofs/BAVCOpeningSafety.lean` now proves that every legal hidden-index vector
with positive execution count excludes all undefined-operation outcomes. Every
queued parent and every read sibling stays inside allocated addresses. The only
possible non-success result on those inputs is the explicit capacity abort.

`Spec/GrayCode.lean` uses most-significant-first row positions as displayed in
the PDF, unlike the least-significant-first salt indexing. Gray-word and F2-row
injectivity are proved, together with consecutive one-bit transitions and the
last-word transition to zero. The source explicitly requires phi(N)=0 in the
optimized fold; `extendZero` implements that boundary rather than evaluating
the unbounded Gray formula at N. The prefix fold's equality with Algorithm 10's
direct loop is proved for the full typed arrays. The claim of exactly 2N bit
operations still needs an operation model and a vector/bit unit interpretation.

`Spec/BLCArithmetic.lean` starts at the expanded PRG and consistency-challenge
boundary. Its direct fold is an initialized increasing-index loop. The code
constructs the source's power-sum psi map, auxiliary corrections, consistency
fields, mask-first slices, and polynomial lines. The integrated consistency and
witness/randomness evaluation theorems derive the displayed arithmetic without
an assumed BLC/VOLE correctness contract. They require the actual phi-based
challenge and its nonzero merged value; they do not repair Algorithm 12's
undefined variables or raw-index challenge, nor identify the conflicting
matrix orientations. The actual psi map is now proved injective in the Table-2
quotients, with its size precondition checked for Tables 4 and 5. These quotients
now have proved field instances. The concrete BLC inversion/bit-matrix
correspondence, hash serialization, PRG/XOF behavior and end-to-end BLC security
remain separate work.

`Spec/BLCCommit.lean` now extends that arithmetic boundary through the actual
seed tree, per-leaf/per-execution PRG byte sampling, Gray rows, corrections,
typed Hashaux/Hashlines inputs and consistency-XOF matrix. The correction
indexing is proved to include exactly executions 1,...,tau-1. Concrete Enc*,
The reusable interface accepts PRG/XOF and hash functions;
`Spec/ConcreteBLC.lean` now instantiates their bodies at the explicit PRG and
serialization boundaries detailed below. Typed hash inputs
preserve source component order but do not choose unspecified serialization of
field arrays or matrices. Byte consumption counts remain explicit. Line degrees
and witness constants are proved from the construction, not supplied contracts.

`Spec/Signing.lean` composes Algorithm 3 phases 1–3 using that commitment and
the actual retry loop. Its initialization boundary takes decoded key data,
expanded H', salt and root seed. The typed signature record preserves the printed
field order; its conversion to/from source bytes is unfinished. Messages remain
arbitrary bit strings, including non-byte-aligned messages.

`Spec/SignatureComposition.lean` implements Algorithm 4 after its unresolved
BLC recomputation. Its comparison theorems use an explicitly constructed record
of committed evaluations and do not assert that Algorithm 12 returns that record.
On these exact evaluations, at nonzero delta, alpha_1 recovery yields
alpha_1 + delta^(-1)*alpha_0. The signing and verification typed hash inputs
coincide iff the actual output polynomial has zero constant. The earlier valid
small SD witness produces different coefficient tuples at every nonzero delta.
No collision-resistance premise or unequal-hash-output conclusion is introduced.
Successful signing observations do imply nonzero header challenges and actual
BAVC openings; later reconstruction may still fail as already proved.

`Spec/SeedPrimitives.lean` connects the BAVC seed calls to the two Enc* calls in
the source. Its modulo totalization outside the 24-bit tweak domain cannot be
used to justify overflowing source calls. The exact-value theorem and checked
parameter-table bound certify non-overflow for the relevant seed-call ranges.
The source introduces these routines for Categories I/V despite defining Enc*
also for Category III; extending their applicability needs correspondence review.
The Category-III zero extension and truncation are specified without presuming
that the truncated cipher is invertible.

## Model choices requiring human review

`Spec/BLCRetry.lean` uses the actual BAVC opening and takes challenge expansion
and index encoding as explicit functions. Its return theorem certifies the
Algorithm-12 header check and a successful BAVC opening, not later reconstruction
or a full signature. Finite observation is metatheoretic execution accounting;
running out of observation fuel is not an algorithm rejection.

`Spec/CipherGrinding.lean` starts after the unresolved XOF parsing boundary with
four lambda-bit windows. It preserves the printed counter dependence in material
expansion. The keys' first bits and plaintexts' low 32/top bits follow the given
concatenations. Counter encoding remains an input. The separately named candidate
`counterBitsLE` is not selected by default. Its injectivity and that of prepared
counter fields imply no cipher-security or ciphertext-inequality claim.

`Spec/ByteSampling.lean` transcribes conversion of already supplied bytes. The
source specifies only a sufficient consumed-byte count n'; that count remains an
input, and the reader advances by it without choosing an unstated buffering rule.
The matrix loop uses a fixed explicit count for each equal-sized call. Its
ExpandH wrapper follows column-sampling pseudocode, not conflicting row-wise prose.
The generic decoder boundary is now supplemented by `Spec/FieldBytes.lean`, a
family of polynomial-basis decoders with explicit byte/bit coefficient ordering.
The PDF page was rechecked: unlike its binary branch, the extension branch does
not specify that ordering. The separately named little-endian order is not
installed as a default or claimed as the source's wire format. Humans must
resolve the convention and compare it to any external implementation.

The full coefficient linear isomorphism, byte-pack bijections and both round
trips are proved. Sampling recovers precisely the bytes used by its returned
field elements, not any extra consumed bytes. The explicit uniform-byte model
proves joint uniform laws for binary and extension samples and for the two
sequential batching vectors, with distinct used coordinates even when there
are unused gaps. The derived batching law equals the existing detailed PIOP
challenge law and preserves every subsequent randomized computation.
The finite reader's zero extension is never read in these proofs. These results
do not establish a concrete PRG/XOF distribution, choose buffering rules, or
justify replacing the undefined `B` in SampleIntegers with `v`.

`Spec/FieldRepresentation.lean` uses the exact modulus polynomials from Table 2,
whose PDF page was visually inspected. The standalone specification introduces
quotient rings without assuming irreducibility. Their power bases, low-degree
evaluation property and encoding injectivity follow from monicity and degree.
`Proofs/FieldIrreducibility.lean` now proves all three moduli irreducible, supplies
their field instances and proves cardinalities 2^128, 2^192 and 2^256.

The binary-polynomial interpreter, Frobenius factor-degree criterion and
Euclidean-transcript checker are proved in Lean. Generated data in
`Proofs/FieldCertificates/` is checked with ordinary `decide`, including each
repeated-square identity and the final Euclidean remainder one. The Python
generator is outside the trusted proof boundary: an incorrect transcript cannot
supply a proof merely because Python produced it. PDF transcription and the
byte/bit decoding convention still require human correspondence review;
irreducibility is now proved mathematical work.

`Assumptions.lean` provides definitions, not assumed propositions. It presently
uses a planted uniform full-matrix SD distribution with an explicitly exact-weight
error sample space. The PDF does not fully specify the meaning of a random SD
instance, and the actual key generator instead uses seed-expanded systematic
matrices. Connecting these distributions is unproved. A caller supplies an
adversary class and runtime accounting; there is no machine-cost semantics yet.

The random-oracle query model preserves repeated outputs, and the ideal-cipher
model samples keyed permutations. Adaptive oracle programs, concrete SHAKE and
Rijndael correspondences, Category-III padding/truncation, and end-to-end game
reductions are unfinished. No final theorem depends on these security models.

## Cryptographic assumptions versus missing proofs

`Spec/IntegerSampling.lean` deliberately ends the sampling prefix at the first
accepted candidate. Printed p. 18 line 7 uses B % m while defining only B_j and
the assembled v; the rendered page was rechecked. A candidate result is not a
sampled position, and no implicit B=v binding has been introduced. The checked
all-zero-stream example shows this boundary is reachable for every legal positive
m, without asserting that a concrete PRG produces that stream. The largest-
multiple threshold, four-byte encoding/recovery, cursor accounting and explicit
uniform-word acceptance/residue laws are proved. The modulo theorem concerns
v % m as arithmetic only. Choosing an accepted-value assignment, completing the
output vector and establishing a concrete PRG law remain separate obligations.

`Spec/UniformChallenges.lean` and `Spec/PIOPChallenges.lean` specify the ideal
fresh uniform challenge experiments explicitly. The new probability theorems
require a fixed invalid committed witness, the stated degree bounds and
consistent polynomial evaluations. Responses may be randomized and depend on
gamma, with delta sampled afterwards. These experiments do not establish
commitment binding or infer an invalid witness from a prover's lack of knowledge.
Knowledge extraction, concrete challenge generation and Fiat–Shamir security
remain mathematical obligations. The literal algebraic bound uses d+1, with
the extra factor preserved, and cannot certify the printed d-based claim.

`Spec/PIOPComposition.lean` and `Spec/DetailedPIOPChallenges.lean` separately
model the detailed Algorithms 19–21 after challenge expansion. The composition
requires leafCount(widths)*w = r+k, exactly the dimension condition already
refuted for Table 3. Its local theorems apply to parameters satisfying that
condition; they do not certify those inconsistent parameter rows. The actual
mux recurrence defines the residual used in the probability proof. Identifying
that residual with the intended omitted-last-coordinate SD witness would
conflict with the existing mux counterexample and is not assumed here.

The unitary batch and the two-batch constant-term experiment now have exact
uniform probability proofs. The detailed comparison bound is
2^(-lambda) + (1-2^(-lambda))*d/|S| for invalid literal constraints, with a
randomized response after both batching vectors and before delta. Consistent
openings, polynomial degree bounds and a zero-constant response comparison are
explicit parts of this experiment. Concrete XOF challenge generation, BLC
binding/extraction and the signature's coefficient hash verification are still
unproved integration obligations. Algorithm 20's comparison has no extra delta;
keeping it separate from introductory equation (2) is essential for fidelity.

SD hardness, a random oracle, and an ideal cipher are the explicit model assumptions
listed in §5.3. They do not authorize assuming BAVC security, PIOP soundness,
zero knowledge, the SD-to-RSD reduction, or EUF-CMA itself. Missing proofs remain
unfinished work, not assumptions in the final theorem interface.

## Variant correspondence

Section 6 explicitly outlines possible future variants rather than giving full
formal instances. The rendered printed pages 45–48 were inspected. Tables 8–10
and all displayed size formulas are now transcribed in `Spec/VariantParameters.lean`.
Key/signature calculations, byte rounding, reported percentage intervals and
the numerical security-budget inequalities are proved. The budget predicates
are equivalent to the displayed rational error expressions, not assumptions
about a protocol's soundness. Table 10 uses the explicit main-construction B=16
in its size theorem, and the formula's final 32 bits are preserved despite the
prose saying there is no grinding.

The F256 rows have three tensor factors [4,4,4], while their printed signature
sizes match constraint degree four. `Proofs/ScaledWitness.lean` proves that an
amplitude line increases the mux degree bound by one. An explicit [4,4,4] example
over any field attains degree four with amplitude constant one. Tensor depth and
constraint degree therefore remain separate parameters; the source's use of d
in both contexts needs human correspondence review rather than silent unification.

The mathematical scaled-witness relation requires nonzero amplitudes and is
proved equivalent to regular vectors, with exact weight, syndrome, injectivity
and vector count. This data requirement does not establish that the outlined
proof system enforces nonzero values against a malicious prover. Section 6.1
does not give that constraint, a complete variant transcript/algorithm, a concrete
F256 polynomial or its embedding/serialization in the larger field. Generic
algebra-map arguments remain explicit; they are not a chosen implementation.
The known first-default versus omitted-last-coordinate mux discrepancy also
remains applicable and is not fixed by multiplying its output by an amplitude.

The new scaled-arithmetic specification formalizes the explicitly described
post-mux multiplication and retained earlier arithmetic, using separate scalar
amplitude lines and binary-position lines. Its mask degree and syndrome packing
width are independently parameterized. No scalar-to-bit parser, inverse-value
witness, or nonzero constraint is added. Raw-vector regularity is proved
equivalent to nonzero amplitudes. All-zero raw values are not regular when
chunks exist, but zero positions/amplitudes/masks and zero syndrome yield the
zero arithmetic polynomial for every matrix/challenge. This is a limitation
of those arithmetic constraints, not a forged complete F256 transcript.

The exact constant-term and probability proofs concern the actual computed
packed syndrome and unitary vectors. The scaled comparison experiment uses
fresh independent uniform challenges and a response selected before a fresh
evaluation sample; it does not give that distribution to SHAKE or grinding.
Its 1/|F| + (1-1/|F|)*degree/|S| bound therefore remains an algebraic model result,
without an assumed link from invalid regular witnesses to nonzero constraints.

Packing needs an explicit variant definition. For every Table-7 row, cardinality
alone proves that an injective encoding of its F256 syndrome into the retained
large field requires at least four elements. Reusing the binary lambda-wide
block shape would produce only one; any such map is noninjective, and the
actual linear power-sum formula has a nonzero vector annihilated for all gamma.
The source does not specify this reuse, so the theorem is a necessary boundary
for a future completion, not a claim against a uniquely specified F256 scheme.
Neither a new packing basis nor an embedding is silently selected here.

The complete TCitH commitment/opening construction, variant protocol correctness,
zero knowledge, extraction, Fiat–Shamir security and concrete runtime claims are
still obligations. The statement that worst-case time equals average-case time
for the simple variant is not inferred from a size formula or numerical table.

## SHAKE and external-standard correspondence

SDitH Table 1 selects SHAKE128 for Category I and SHAKE256 for Categories III/V.
The concrete body is transcribed from the final August-2015 FIPS 202, whose PDF
hash is pinned alongside the submission's hash. It specializes the standard to
width 1600, lane width 64, 24 rounds, rates 1344/1088 and the SHAKE suffix 1111.
State strings use 64*(5*y+x)+z indexing; byte readers preserve consecutive low-bit
first bytes. Human review must still confirm the definitions match those source
pages and that these are the intended referenced primitive versions. The proof
of refinement is between explicit Lean definitions, not an automated theorem
about the semantics of the English PDF. Source and worked-example provenance is
in `source/standards/index.json`.

The worked examples use NIST's empty, 5-bit and 1605-bit messages for both SHAKE
functions. PDF extraction proposes state/step certificates; Lean checks every
absorption transition and the first 64 output bytes. The checked source example
prefixes are not a claim of NIST validation or certification. The generator and
byte/bit transcription remain reviewable source correspondence, with all other
published output bytes retained as unproved test data. The generic bit-equation,
padding and squeeze-loop results apply beyond these examples.

Actual SHAKE hash and XOF outputs now share the proved deterministic prefix law,
and the existing binary sampler reads the actual stream bits. This does not
transfer any uniform-byte probability theorem to deterministic SHAKE, prove
collision resistance, prove Keccak bijective, or establish a random-oracle
security reduction. The ideal-oracle model remains separate. BAVC's actual bit
serialization is instantiated, while unspecified field/counter/typed-transcript
serializations and Algorithm-6 source gaps remain visible obligations. AES/Rijndael
now have concrete bodies and the separate correspondence ledger below.

## AES/Rijndael and cipher serialization correspondence

Table 1's two full-block ciphers are transcribed from the pinned final
FIPS 197-upd1 and the designers' original version-2 Rijndael proposal.
Rijndael-256-256 uses both a 256-bit key and a 256-bit block; AES-256 has a
128-bit block and is not substituted. Human review should check the exact
polynomial, S-box entries, column-first state order r+4*c, round counts,
wide-block offsets, key recurrence and final-round omission against the
reference pages listed in `source/standards/index.json`.

The byte-field theorem is derived from the actual polynomial quotient: the
coefficient decoder is a bijection, arithmetic preservation is proved, and
every nonzero inverse witness is kernel-checked. The S-box table has exactly
the standard inverse-and-affine behavior. The witness generator, PDF parser
and reference tables carry no logical authority. The AES example checks every
displayed intermediate state and key; the wide Rijndael examples check the two
published complete input/output pairs. These are conformance evidence, not
NIST certification or a proof about the semantics of the English documents.

The cipher's external byte interface has unchanged byte order. The SDitH
wrapper uses the existing low-bit-first Bits convention: byte i contains bits
8*i through 8*i+7, matching the earlier tweak/byte-reader representation.
FIPS displayed bitstrings put the highest bit of each byte first; a named
within-byte conversion and its bit theorem make the distinction reviewable.
Human review must confirm the chosen SDitH representation matches the intended
implementation convention. It does not select an unstated extension-field
coefficient order or a counter/transcript serialization.

Category III appends 64 zero bits to the key and plaintext in this convention,
uses the complete 256-bit cipher output for Enc, and takes the low 192 bits
for Enc*. The full Enc mapping is proved injective, with no surjectivity claim
across the different sizes. No bijectivity claim is made for truncated Enc*.
The source's restriction of some displayed seed routines to Categories I/V
still requires correspondence review before claiming a complete Category-III
protocol, even though the Table-1 primitive family is defined for all three.

The fixed-key permutation theorems do not show that distinct keys are
independent or uniformly sampled permutations. Concrete ciphers are not
identified with the ideal-cipher model, and neither their functional
correctness nor their test vectors prove the submitted scheme secure.
Source gaps, commitment correctness/security, zero knowledge,
Fiat–Shamir and the absent end-to-end proof remain explicit obligations.

## Algorithm-6 interpretation and concrete BLC boundary

The visually inspected printed page 17 is transcribed in `Spec/PRG.lean`.
`BlockSize` is a supplied positive value for the undefined `nblock-bitsize`;
no value is selected by default. Positivity is a well-defined-denominator
precondition, not a statement that the PDF supplies that parameter. The byte
parser is a complete consecutive partition in the existing low-bit-first
representation. Human review must confirm this interpretation or supply a
source correction if a lossy/truncating parser was intended.

`run = none` means that this partial transcription cannot interpret a printed
assignment. It is not a newly invented rejection result. The proved positive
Category-III failure retains the 256-bit Enc output and the line-5 192-bit-per-
block destination. A present salt with no tweak also has no specified formula;
no default tweak is supplied. The zero salt for absent salt follows the explicit
line-2 comment. The full cipher byte stream exists independently of these gaps;
its Category-III definition does not resolve the finite algorithm.

The fixed-width LittleEndian representation keeps low lambda bits and therefore
wraps integers beyond that range. This total encoding and its intended input
bounds require review: the source permits an arbitrary byte request but gives
no counter exhaustion behavior. Kernel proofs show exact block repetition
modulo 2^lambda and byte-stream periodicity. Tweak/counter separation is proved
only below 2^16 blocks. At the next counter, tweak 0/counter 2^16 and tweak 1/
counter 0 coincide for every salt and key. This local input identity is not an
attack on the submitted signature parameters or a claim about practical usage.

Sampler proofs require actual successful finite PRG calls and explicit byte
bounds. They never use the finite reader's zero extension. Consumption counts
and extension-field coefficient order remain supplied, as already recorded.
PRG-stream/ExpandH correspondence follows the printed column loop and leaves
the conflicting row-wise prose unresolved. None of the uniform-byte theorems
is applied to deterministic cipher output without a separate distribution proof.

`Spec/ConcreteBLC.lean` fixes actual ciphers, SHAKE and all top-level hash
components: hcom followed by positive-index corrections, and haux followed by
plain/base checks and witness correction. Binary-vector and base-matrix wire
encodings remain explicit functions in `Serialization`, not assumed injective,
length-preserving or source-correct. No arbitrary whole-transcript hash remains
inside this family, but external serializer correspondence is still needed.
The existing Nat-indexed execution interface is totalized by zero outside the
source's byte-tweak range. All tabulated execution ranges are proved within
0..255, so that extension is not a source behavior used by those loops.

The finite PRG correspondence is proved for Categories I/V with the explicit
block-size bound, or conditionally on the actual run equation. The Category-III
cipher stream is a mathematical object, not a claim that its contradictory
Parse line executes. Commitment opening/recomputation, raw/Gray challenges,
missing serialization, correctness, hiding/binding, zero knowledge and the
absent end-to-end security proof remain unfinished.

## Staged key generation and typed initialization

Algorithm 2's seed draws are modeled as independent uniform lambda-bit values.
Their exact joint law and independence after arbitrary deterministic expansions
are proved. This does not prove uniformity of PRG-derived positions or matrices,
identify their distribution with the hardness model, or certify an external
random-number generator. The source sampling notation and this probability
model still require correspondence review.

The actual post-position Algorithm-1 expansion and concrete ExpandH column loop
are composed in `prepareAfterPositions`. Position sampling remains outside this
stage because its accepted-value assignment uses undefined B. ExpandH retains
an explicit count per column; matrix reproduction is proved with the same count.
The source does not specify a general consumption/buffering rule. Category III's
PRG parsing gap is unchanged, and finite-call correspondence is conditional on
an actual successful Algorithm-6 transcription.

Line 5's x_A is represented by an optional external binding. Missing binding
produces no interpretation, not a keygen rejection. No relation to the generated
x is assumed. If a binding is supplied, the exact condition for the generated
vector to solve the returned instance is [I|Hprime]*(x_A-x)=0; its weight is
proved from the real expansion. The coordinate-preserving flat length cast uses
r+k=w*m only. The source's tensor dimensions remain independently inconsistent.
The orientation permutation theorem explains a possible relation between the
prose and pseudocode, without choosing it as a source correction. Its small
counterexample uses an arbitrary binary matrix, not an asserted PRG-generated
public key or attack.

Typed public and secret records retain seedpk, y and wit, with unspecified
whole-key serializers as separate functions. No serializer injectivity, fixed
length, byte order or decode/encode inverse is assumed. Typed initialization
only begins after Deserialize has returned; it does not implement raw parsing.
Algorithm 3 line 7 uses pk although its explicit input is sk. Reconstructing
its exact encoded public key from the decoded seed/y is a remaining interface
and serialization obligation, not silently supplied by a codec assumption.
The generated-vector theorem does not resolve the separate witness/mux error,
whole-keygen correctness, signing correctness or the absent security proof.

## Full staged BAVC reconstruction and undefined source reads

The physical-page-26 image was reviewed against all 32 Algorithm-9 lines.
The specification begins with the existing typed opening: a path bit list and
one 2*lambda-bit hidden commitment per execution. It does not implement a raw
opening decoder. Increasing row/leaf loops select the hidden commitment in
execution order; the structured input already supplies the stated digest count.
Source correspondence for any external flat serialization remains separate.

The post-dequeue queue-length comparison and the strict upper-bound comparison
on remaining path bits are unchanged. Short seed extraction, empty queue reads,
zero/out-of-range addresses, undeclared nodes and missing node values have
separate undefined-operation tags. Only boundRejected and paddingRejected
represent the printed bottom returns. No undefined read is silently converted
to a seed, zero bits or an ordinary verification rejection.

The array names are intentionally distinct. Line 20 tests the prefilled tree;
line 21 reads and updates nodes, and line 25 reads nodes again. No declaration,
copy or alias is present in the source. The optional NodesBinding argument in
reconstructWithNodes is an external environment value with no correctness
contract. The literal reconstruct leaves it absent. Assigning nodes=tree,
sharing mutable storage, testing nodes instead, or using the tested tree value
as the parent seed would all be source corrections requiring explicit resolution.
The checked no-return result for tau>0,N>1 is about this undeclared-read semantics,
not about an implementation that has corrected the array name.

Independently of that missing name, a padded-length path cannot enter any seed
extraction branch. A successful prefill therefore leaves all tree cells empty
and all remaining bits zero. Its expansion makes no updates even if an external
nodes binding is supplied. Revealed leaf values would then come entirely from
that external binding; no reconstruction correctness is inferred from providing
such values as an input. The successful-output theorems describe actual run
results and do not assume the desired revealed seeds or commitment agreement.

The final Category-I discrepancy now uses the entire reconstruction body and
proves explicit capacity rejection before any nodes access, for every cipher,
hash, salt and optional nodes binding. It retains the earlier complete
Algorithm-8 opening trace and the same submitted parameters. A separate
single-leaf example can return without nodes because it reveals no seed; it is
a degenerate case, not a submitted row or correctness claim for practical inputs.
General intended reconstruction correctness, exact raw parsing, BLC recomputation,
hiding/binding and end-to-end signature security remain open.

## Algorithm-12 staged recomputation and type-resolution boundary

The physical-page-32 image was checked against all 27 numbered lines.
Spec/BLCRecompute begins after parsing the typed auxiliary and decomposition.
Challenge expansion and the raw-index merge retain explicit subroutine inputs,
as in the retry model. The prefix tests grinding/nonzero before reconstruction,
then calls the full literal Algorithm-9 body. A failed reconstruction supplies
no hcom/seeds pair to line 8. Its cause is recorded as an undefined pair read;
the source provides no branch which converts it into the line-6 bottom tuple.

The successful reconstruction record contains `seeds`; line 12 instead reads
`seed`. The bindings for these names are separate. Likewise line 10 initializes
`reval`, whose zero is recorded in binary coordinates, while line 14 reads and
updates `rshare`. The latter is not initialized by that zero assignment.
The optional `phiMu` binding is not identified with Gray or raw binary encoding.
The external bindings carry values only, with no correctness, aliasing or
challenge-agreement contract. The literal prefix leaves all missing names absent.
Read failures occur at the actual operation, not at a blanket precheck.

The inner leaf loop is increasing and skips the hidden seed, then samples the
printed number of binary values from a newly initialized stream. Corrections
at positive execution indices use transmitted slot e-1. The outer execution
loop and Q concatenation preserve order. The exact sum theorem includes any
supplied initial share and the supplied phi_mu term; neither contribution is
discarded to recover a desired opening equation. The concrete BLC primitive
family may be used here with all of its existing PRG/serializer limitations.

The prefix ends immediately before line 21 with both typed operands visible:
an s by tau*kappa binary matrix and an extension-field scalar Delta_inv. The
printed subtraction lacks a specified conversion and columnwise meaning.
No inverse psi, Gray challenge, scalar broadcast, truncation or cast is chosen.
The stopped state is not a successful Algorithm-12 return. The separate suffix
accepts an explicitly supplied binary base matrix and computes lines 22–27;
there is no theorem claiming that this matrix implements line 21. Its witness
and randomness slices follow the algorithm, not the inconsistent preceding prose.

The suffix uses the three-field Hashlines tuple and actual SHAKE domain 3 when
the concrete hash is selected. Algorithm 10 appends the encoded witness
correction. Their messages differ whenever that encoded suffix is nonempty;
no claim about different hash outputs or an injective serializer is inferred.
The Category-I full reconstruction rejection now also yields an exact prefix
failure theorem for every external binding, given a passing header with that
hidden-index vector. This is a conditional call-site result, not a claim that
actual digest expansion produces those indices or that a full signature runs.

## Full integer sampling and concrete challenge call sites

The physical-page-21/22 images were reviewed for the three challenge expansions
and the cipher-grinding prose. Spec/IntegerSamplingVector now models the complete
outer SampleIntegers loop, including rejected four-byte attempts, successful
append operations and the final length-indexed vector. Partial states carry
their actual prefix and reader with a proved prefix-length bound. Fuel observes
attempts; pending execution is never changed into a source rejection.

The only external accepted-value binding is an optional fixed natural number
for the undefined name B. It carries no relationship to the local bytes or v.
With no binding, nonempty calls cannot return; a rejected candidate continues
normally, while an accepted candidate exposes the undefined assignment. For
m=2^kappa and kappa<=32, the threshold is exactly 2^32, so every stream reaches
that assignment on its first attempt. This includes all Tables-4/5 index ranges.
With an explicitly supplied fixed B, a power-of-two call instead returns n
copies of B%m and advances exactly 4*n bytes. That theorem explains this binding
semantics; it is not an intended uniform sampler or a proposed source correction.

ConcreteChallenges.hashEvaluation initializes the real SHAKE on hpiop followed
by an explicit 32-bit counter encoding and calls this actual integer loop. It
samples grinding bits only if that loop returns. There is no packing of kappa-bit
indices in place of the printed four-byte integer sampler. Under the fixed-B
comparison, the first grinding bit is SHAKE bit 32*tau, and the next reader
includes the explicitly supplied grinding-byte consumption. For a literal
nonempty call, the missing assignment is reached before grinding. A zero-tau
example returns its actual grinding bits without reading B; this is not a
submitted parameter row.

Counter XOF serialization and MapToBits are distinct supplied functions. Neither
has an unstated injectivity or endianness contract. Injective counter encoding
does imply distinct initial XOF input strings for distinct counters; no SHAKE
output or cipher-material inequality follows from that theorem. Thus the
printed counter argument is preserved and the prose factoring is not applied.

The cipher stage reads exactly the printed 4*lambda bytes and exposes that
unparsed data. Four lambda-bit windows cannot exhaust this read, but that size
comparison does not assert a unique source parser or reject longer p/k slices.
After explicitly supplied material, the two actual Enc* calls produce the
ciphertexts and XOR. The one-subscript Extract operation is a separate boundary;
no prefix, suffix, output width convention or correction is chosen for it.
After explicitly supplied grinding bits, lines 11–13 start a fresh SHAKE with
(hpiop, ctr, c0, c1) and execute the integer loop even for zero grinding. This
preserves the pseudocode rather than adopting the conflicting omission prose.

The concrete batching routine samples gamma then gamma-prime from the same
actual SHAKE stream and decodes through the Table-2 coefficient representation
with an explicit ByteOrder. Its exact byte locations, disjoint consumed ranges
and cursor are checked. Deterministic SHAKE outputs are not identified with the
fresh uniform laws in the probability modules. Whole signing/verification still
requires integrating these partial outcomes with the retry/caller interfaces;
the existing total-function challenge boundary is not filled by fabricated data.

## Complete staged cipher expansion and its callers

Printed p. 19 was rechecked against the rendered PDF. CipherEvaluation now
composes all thirteen lines with separate optional source interpretations for
the material parse, MapToBits order and one-subscript grinding extraction.
These are arbitrary supplied functions without correctness/security contracts;
their absence marks an unresolved interpretation, not an operational rejection
rule printed in the submission. Counter serialization into the XOF remains a
separate explicit input. A fixed optional natural number still binds B, without
identifying it with v or repairing the accepted assignment.

The material read is the actual SHAKE read of 4*lambda bytes from hpiop/ctr.
After a supplied parse and MapToBits, the existing actual Enc* preparation/calls
produce both ciphertexts and their xor. A supplied Extract interpretation is
applied to that xor, rather than supplying arbitrary output bits at the caller.
The final SHAKE is freshly initialized on hpiop/ctr/c0/c1 and feeds the complete
integer loop. No factoring removes the printed counter dependence, and no
zero-grinding shortcut omits the printed index expansion. The three source
boundaries keep their respective raw material, material windows or cipher state.

Every returned challenge exposes those supplied interpretations and the actual
final integer sample. Return stability follows from the sampler's observation
semantics. With B absent, nonempty calls cannot return at any finite fuel even
after earlier interpretations are supplied; for kappa<=32 and positive fuel,
the exact first missing assignment occurs on the fresh final SHAKE stream.
These statements do not claim that all possible parsers fail or that a corrected
sampler is unsound. The all-absent literal wrapper stops earlier, at material
parsing, so it is not claimed to execute the later missing-B read.

CipherBLCRetry preserves an unresolved source operation and its current counter.
It agrees with the earlier partial retry when every expansion returns an
EvaluationObservation, without requiring that observation to be a challenge.
Successful openings require genuine returned expansion, actual BAVC success,
passed grinding and a nonzero encoded challenge. Extra outer fuel preserves
returns. Fuel is an observation budget, never an added source abort.

CipherSignature uses these results after the existing BLC/PIOP prepared record.
It proves successful-signature provenance and stability for every such record,
including those from actual preparation. Verification uses the transmitted
counter and parsed digest, with exact provenance for the BLC consistency
boundary and the explicit header Reject. Undefined cipher interpretations do
not become either outcome. With B absent and nonempty executions, neither
outcome is reachable after expansion. No acceptance exists at the prefix;
Algorithm-12 line 21, codecs, intended source corrections, full correctness and
security remain unresolved.

## Binary/Gray challenge correspondence and partial retry integration

Spec/ChallengeEncoding names two concrete interpretations of the header's
unannotated index concatenation. binaryMerge uses the source's most-significant-
first bin_kappa rows, while grayMerge uses its folding Gray rows. Both use the
actual Table-2 generator and established psi power sum. Neither is selected as
the default source meaning. Other byte/bit order choices remain separate from
this precise comparison; no representation conversion is inserted into line 21.

The Gray transformation is a bijective relabeling of the bounded integer index
set and of its execution vectors. In every submitted quotient, when tau*kappa
fits the basis, both merges are injective and their merged field points agree
exactly when every hidden index is zero or one. Their inverse evaluation points
have the same equality condition. A constant index-2 vector gives distinct,
nonzero points whenever that index and an execution exist; all Tables-4/5 rows
satisfy those checked bounds. This vector is not asserted to be a SHAKE output
or a full signature transcript.

Both merges vanish exactly on the all-zero index vector. Consequently, the
existing Algorithm-11 retry attempts and every finite retry observation agree
between these two encodings, for the same returned challenge vectors and BAVC
key. The zero test therefore cannot resolve the difference in nonzero evaluation
points. The merge images coincide and have 2^(tau*kappa) elements when the basis
bound holds. Uniform *index vectors* give equal pushforward distributions by
the explicit relabeling; this is not a uniform law for the whole extension field,
for SHAKE expansion, or for a challenge selected by adaptive grinding.

Spec/PartialBLCRetry now calls partial challenge expansion at Algorithm 11's
actual line 3. It invokes BAVC.Open and the existing header/retry step only after
that expansion returns. A pending integer observation keeps the current counter;
an undefined assignment retains its state/candidate and does not increment the
counter. BAVC errors and counter overflow keep their existing distinct payloads.
Inner and outer fuel describe finite observations, not source abort behavior.

When every expansion returns, the partial loop is proved equal to the earlier
total loop with its result tags embedded. Every successful partial-loop return
has a genuine returned challenge, successful BAVC opening and passing grinding/
nonzero conditions at the reported counter. Increasing outer observation fuel
preserves such a return. The concrete hashOpen wrapper begins at zero, uses the
actual SHAKE/integer expansion with B absent and cannot return an opening for
nonempty execution sets. For kappa<=32 and positive observation budgets, its
exact outcome is the first missing-B read at counter zero, before any BAVC call.
This diagnoses the literal source, not a corrected sampler or implementation.
Full signing/verification integration and cipher parser/extraction resolution
remain outside this caller theorem.

## Partial signing and verification caller correspondence

Algorithm 3's opening call now uses PartialSignature.observeSigning, after the
actual existing BLC commitment and PIOP preparation. The source's salt, digest,
auxiliary and higher coefficients are retained when a real partial retry returns
an opening. The provenance theorem includes that returned challenge, actual
BAVC success, and passed grinding/nonzero conditions. Total-model refinement
and return stability are proved. No probability of success or concrete successful
SHAKE challenge is asserted. Source dimensions and the earlier primitive/
initialization boundaries remain explicit; this does not fill their gaps.

Algorithm 4's recomputation call now preserves partial expansion outcomes.
Only Algorithm 12's explicit header-bottom tuple reaches the source Reject.
An Algorithm-9 error remains the cause of an undefined pair read at line 8;
pending sampling and missing source variables are not invented rejection rules.
The returned prefix stops before the ill-typed line 21. The independent suffix
takes a supplied base matrix and composes the actual lines 22–27, detailed
PIOP, coefficient recovery and final digest comparison. That supplied matrix
has no asserted relationship to the unresolved line-21 expression.

Concrete SHAKE/integer expansion reaches the literal missing-B assignment in
both callers. Signing uses counter zero and cannot emit a signature for a
nonempty execution set at any finite observation budget. Verification uses the
transmitted counter and cannot reach the consistency boundary or explicit Reject
at any such budget. Positive integer fuel and kappa<=32 expose the exact first
candidate/state before header checks or reconstruction. The literal missing
assignment remains uncorrected. These statements do not diagnose a corrected
sampler or executable implementation. Raw codecs, cipher expansion gaps, line-21
resolution and whole-protocol correctness/security still require work/review.

## Partial witness expansion and key-generation callers

Spec/PartialKeyGeneration now connects the full partial integer loop to
Algorithm 1's actual deterministic witness expansion, then Algorithm 2's
cipher-stream matrix and printed syndrome/key computations. The actual PRG
stream is initialized with the secret seed for positions and independently
with the public seed for the matrix. This is the documented stream boundary;
it does not make finite Algorithm 6 well-formed for Category III or choose the
missing block-size denominator. Explicit successful finite-run premises are
required for the corresponding Algorithm-6 trace theorem.

The new finite trace projection retains the exact outcome tag, sampled values,
reader positions and offending integer, while dropping the unconsumed reader
function. Equality of traces follows from equality of the first four bytes per
observed attempt, including arbitrary rejection sequences. Successful finite
PRG output covering that range induces the same sampler and witness-expansion
trace as the actual cipher stream. No unbounded use of zero-extended finite data,
infinite-tail equality or independent-byte law is assumed.

The missing integer B and syndrome x_A have separate external bindings. Literal
wrappers leave both absent; no B=v or x_A=x assignment is inserted. A nonempty
literal witness request cannot return within any finite fuel, and either missing
binding prevents a corresponding returned key. Table-3 chunk ranges are 185,
252 and 191, so the power-of-two first-candidate argument used for signature
challenges is not applied here. Pending sampling is not a source timeout/reject.

Returned expansions have proved solution weight and witness length. Returned
keys expose actual sampler/expansion equations and satisfy precisely the earlier
conditional SD relation for the supplied x_A. Seed draws are independent uniform
bits, while deterministic expansion outputs use their actual pushforward laws.
The resulting keygen PMF is a distribution of partial observations. Its zero
mass at every returned key/encoded pair diagnoses the literal undefined reads;
it does not establish security, an operational rejection probability, or the
behavior of a corrected implementation. Serializers remain unvalidated external
functions. Raw codecs, PRG source resolution and whole-scheme correctness/security
remain human/source obligations and unfinished formalization work.

## Key-codec capacity, parameter tables and reported benchmarks

Algorithms 2–4 and §4.2 specify ordered key fields and size formulas but do not
provide a raw byte encoder/decoder, endianness convention or key padding rule.
The new KeySizeBoundary module therefore selects none. SizedSecretKey is only
the subtype of the existing SecretKey with the length expected by Algorithm 3;
it adds no witness-validity or SD premise. Public and sized secret keys are
proved equivalent to their actual field products, giving cardinalities
2^(lambda+r) and 2^(lambda+r+witnessBits). These count all typed parsed values,
not valid witnesses, generated-key support, or a uniform key-generation law.

The capacity theorems require explicit injectivity and fixed length of an
arbitrary encoding and derive necessary byte counts. These conditions are not
assumed for the source's Serialize functions, added to Assumptions, or used to
claim codec round trips. A codec restricted to a smaller set of valid keys is
outside that lower-bound statement. Table-3 payload sizes are checked; the
reported Category-III secret-key allocation has four spare bits. Their value,
placement and treatment by Deserialize remain unspecified.

Rendered printed pages 39–41 were inspected. MainParameterTables transcribes
all Table-4/5 columns and verifies their key/signature arithmetic and degree-four
error-budget inequalities. These are numerical checks, not a security proof or
an assertion that a concrete signature serializer emits that length. The
existing tensor-dimension contradiction is not repaired by matching sizes.

The p. 39 parameter-selection prose says short kappa [11,12,12] and fast kappa
8, while Table 4 gives [11,11,11] and 7. Its asserted fast grinding value 2 and
short grinding set {2,6,9} likewise do not match all table rows. Both passages
are separately represented and the disagreement is proved; deciding which
description is intended requires source resolution. The earlier numerical
budget checks alone do not choose or correct either passage.

ReportedBenchmarks isolates the Table-6 timings as data, including the reported
median over 10,000 runs on an Intel Xeon Platinum 8259CL CPU @ 2.50GHz. Mc values
are converted exactly at displayed precision, without asserting unrounded
median values. The row labels agree with Tables 4/5. No raw measurements or
rerun evidence is supplied here, and no theorem connects these reported numbers
to the Lean routines, a reference binary, its compiler/platform, or a security
cost model. Those are human/empirical obligations, not hidden axioms.

## Density formulas and the SD-to-RSD conditioning gap

The rendered printed p. 38 was checked. ParameterSelection retains the literal
integer formulas n-floor(w*log2(n/w)-log2(theta)) and
n-floor(log2(choose(n,w))). Integer results are not clamped to valid dimensions.
The density definition is candidate count divided by binary syndrome count;
its average-fiber theorem holds for any fixed candidate-to-syndrome map. It is
not the probability of some solution, a planted-instance success rate, or a
hardness assertion.

For positive candidate count and theta, the proved density target is equivalent
to log2(count)+log2(theta) <= codimension, and hence to its natural ceiling
being at most that codimension. Maximum-dimension and byte-alignment theorems
have explicit feasibility premises. They are consequences of this criterion,
not silently substituted definitions. The literal SD formula at n=3,w=1 gives
k=2 and density 3/2. The RSD formula at n=8,w=2,theta=2 gives k=5 and density 2,
not at most 1/2. More generally, when its floor gives a valid codimension, the
printed minus-theta formula produces density at least theta. These are source
resolution obligations independent of empirical hardness calibration.

SDReductionGame follows the actual displayed algorithm: sample an explicit
input law, sample a uniform permutation, call the supplied solver on the
truncated permuted instance, and apply the existing full-syndrome check and
inverse permutation. The output-law theorem connects this joint experiment to
the existing run function. Its proof uses the ordinary semantic premise that
supported nonfailure solver outputs are actual RSD solutions; it does not
assume any solver success rate, uniqueness estimate or desired reduction bound.

For inputs supported on solvable SD instances, the full-regularity event has
probability at least m^w/choose(w*m,w), independently of the supplied solver.
Conditional-product and uniqueness proofs give the corresponding success
lower bound with the actual conditional return and uniqueness probabilities.
Cancellation requires a nonzero conditioning mass; this premise is explicit.
All factors refer to the same joint experiment. Identifying its conditional
solver success with epsilon_rsd requires a separate distributional proof. The
source's change of conditioning events is not adopted without proof.

SDReductionConditioning gives a fully specified correct selective solver: it
returns a fixed regular witness only when both matrix and syndrome are zero.
The input law is the existing candidate planted model with a uniform binary
3-by-4 matrix and independent uniform weight-two vector, not a seed-generated
public key. Parameters n=4,w=2,k_sd=k_rsd=1,theta=2 satisfy Theorem 5.1's actual
inequality and give regular candidate/syndrome density 1/2. A zero-matrix input
and its joint outcome have positive probability. Two distinct regular witnesses
solve every returned instance, so uniqueness conditioned on return is zero;
conditioning additionally on full regularity still gives zero with positive
conditioning mass. The source's positive exponential heuristic therefore cannot
be a universal lower bound for arbitrary correct solvers.

This refutes an intermediate conditional estimate, not the final existential
Theorem 5.1 or the cryptosystem. No rows are removed in this example, and the
displayed reduction succeeds whenever this solver returns. The example has no
machine-time claim. Proving the intended final reduction requires a valid new
argument with justified distributions and costs; merely adding the failed
uniqueness estimate to Assumptions would be circular and is not permitted.

## Abstract signature game and first forgery reduction step

SignatureSecurity now models §5.3's adaptive chosen-message game. The adversary
receives the public key and retains its own state; it does not receive the
secret key, world or private request log. Its actions may request signatures,
query the final-hash oracle, query other public services, abort, or output a
message/signature. Every signing request is logged, including repetitions.
Freshness means that the output message is absent from that log. Fuel bounds
adversary actions, including finalization; it is not a machine-time bound or a
bound on honest-service internal oracle calls. Exhaustion, adversary abort and
completed verification rejection have distinct terminal constructors.

These are complete abstract service interfaces. They are not an instantiation
of the partial literal source. In particular, undefined variables, incomplete
recomputation and exhausted concrete observations must not be converted to
abstract verification rejection to obtain a vacuous security result. The
generic game asserts no property of the supplied keygen, sign or verification
functions. Its finalize operation performs the actual lazy final-hash query,
compares its answer to the signature's digest, and applies message freshness.

AbstractSignature makes the known HashPiop call sequence explicit. Keygen
starts an empty final-hash table and retains the public key inside the signing
key. Signing prepares the payload, queries the tuple (public key, message,
payload), then finishes the opening using that digest. The resulting signature
retains that digest. Verification prepares the tuple with the submitted message;
its final query is handled by the game. Other public services and the remaining
signing/verification computations have only Other state and cannot directly
change the final-hash table. They have no assumed correctness, hiding, binding,
soundness, zero-knowledge, simulation or extraction contract.

This typed separation of the final-hash domain from other oracle operations is
a declared abstract model choice. A byte-level input/domain correspondence and
an implementation of all source components must justify its application to
SDitH. The model does not infer independent oracle domains from merely naming
two functions, assert that SHAKE is random, or establish the ICM game. The
source's unresolved serializers and algorithm inconsistencies remain material.

The table-origin invariant is derived from the explicit lazy update and all
adaptive actions: each stored input came from an adversarial hash query or a
signing request on that input's message. For a winning fresh-message attempt,
the latter origin is impossible. An absent final input receives a fresh uniform
digest even after an arbitrary adaptive terminal law; its successful guess has
probability at most 1/|Digest|. The resulting proved first reduction step is
Pr[forge] <= Pr[forge with its exact final input previously queried by the
adversary] + 2^(-2*lambda). No independence of previously queried answers is
asserted. A prior-query witness is not an extracted RSD witness or a successful
fork. The replay and query-selection results below provide subsequent steps;
extraction remains open.

SignatureHashGame uses the existing verificationInput, PIOP evaluation and
coefficient recovery, and proves its resolved final hash test agrees with
verifyPostRecompute plus the EUF-CMA freshness condition. The oracle premise
for this correspondence is equality of the one required lookup with its
specified answer. Exact typed hash-input and signature-record equivalences are
also given. These are not raw codec equivalences, a proof of the supplied
recomputation result, or a whole-scheme instantiation. Existing dimension/source
premises remain explicit and fail for the submitted Table-3 tensor shapes.

The lazy query definition was moved unchanged to Spec/RandomOracle and
re-exported by Assumptions.randomOracleQuery. No new cryptographic hypothesis or
axiom was added. A full theorem still needs faithful
signing-oracle simulation, commitment security, consistency, RSD extraction,
distribution/runtime accounting and concrete correspondence.

## Signature replay, fork probability and answer consistency

SignatureReplay cuts the actual bounded game immediately before answering the
indexed adversarial HashPiop action. Indices count all adversarial hash requests,
including repeated inputs; honest signing calls do not advance this index.
Terminations before the selected index remain explicit ended cuts. A snapshot
retains the remaining action fuel, public/secret key, world, query log, input and
answer-dependent continuation. Resuming with the original lazy query reproduces
the entire original terminal law and finalized experiment exactly.

The snapshot contains the honest signing secret. This is an instrumented game
and replay experiment, not an algorithm already implementable by an SD/RSD solver
given only a public instance. The later signing-oracle simulation must remove
this dependence and prove its distributional and cost claims. No such simulator
is supplied as an assumed contract. The adversary itself still does not receive
the secret, world or snapshot.

At a saved absent input, freshBranch samples a uniform answer, updates that one
table entry, and runs the actual remaining game/finalization. Its checked-result
marginal agrees with ordinary resumption; its answer marginal is uniform.
Uniformity is not asserted after conditioning on winning. forkAt makes two
independent such draws from the same saved state, including independent future
random choices. It refuses an already stored input, returning none. This is a
fork result and does not turn a pending source algorithm into verifier rejection.
The proof does not assume replay on an identical future random tape.

The event requires both branches to win at exactly the selected input and their
sampled answers to differ. If epsilon is the one-branch probability of that
event's target-winning part, epsilon^2 <= Pr[fork wins] + epsilon/|Digest| is
proved from independence and a marginal uniform-answer collision bound. A
weighted-square inequality over arbitrary PMFs then gives the same bound over
the actual random cut experiment; no finite adversary-state assumption is added.
Ended and nonfresh cuts contribute zero single-success mass. Epsilon is not
overall forgery probability. The query-selection proof below now links these
quantities with an explicit action-budget loss.

SignatureReplayConsistency derives table-answer persistence from the defined
lazy oracle and AbstractSignature services, through all subsequent adaptive
signing/hash/public queries and verification preparation. A target-winning
branch contains an actual fresh-message accepted attempt at the saved input
whose tested target is the sampled answer. A successful fork therefore yields
two such attempts at the same typed input with different tested digests.
This is oracle consistency, not commitment binding or PIOP knowledge soundness.
In particular, different digest strings need not expand to different usable
algebraic challenges; retry, sampling, commitment consistency and extraction
need their own proved analysis. No RSD witness or machine-time guarantee follows
from the current fork theorem alone.

## Useful-query selection and the forgery-to-replay bound

SignatureQuerySelection instruments the same actual game with a chronological
log of adversarial hash inputs and their pre-query absence flags. This private
record does not change adversary observations or honest service calls. The
terminal marginal and finalized checked marginal equal the original laws.
For every fixed index, the marked event in the recorded execution equals the
single-success law of the existing cut/resume experiment. It is therefore not
a postselected guess at a convenient snapshot.

SignatureQueryProvenance derives that a final stored entry either was stored
initially, arose at an adversarial request that was fresh at that moment, or
belongs to a message in the final signing log. The proof also derives signing
log monotonicity and verification-input message correspondence. In the actual
key-generated experiment, the initial table is empty. Fresh-message acceptance
rules out the signing origin. Thus every table-present winning forgery has a
fresh target query in the recorded list, at an index below the action budget.
Repeated hash requests remain logged; they cannot be relabeled as fresh.

The defined randomCutExperiment chooses a uniform index in Fin(q), then runs
q positive actions and cuts before answering that indexed adversarial hash
request. The Lean fuel parameter is q-1 so nonempty uniform sampling is explicit.
If too few requests are made, the selected cut ends without fork success.
Here q bounds all adversarial actions, including signing/public-oracle queries
and finalization. It is not a machine-time budget or an honest-internal-query
count. No sharper hash-query-only budget is claimed.

Let e be original forgery probability, s the actual random selected-input
success probability, F the actual distinct-answer fork probability, and
delta = 1/|Digest|. A proved finite union bound and the exact uniform-index law
give e <= q*s + delta. The previous random-prefix replay bound gives
s^2 <= F + s*delta. These yield max(e-delta,0)^2 <= q^2*(F+delta).
Subtraction in the Lean ENNReal statement is truncated at zero. The squared
budget loss is a bound for this defined algorithm; it is not presented as an
optimal forking lemma or as a numerical theorem printed in §5.3, which defers
the full proof. The typed SDitH specialization has delta = 2^(-2*lambda).

All these distributions still execute the honest signing service using its
secret key. The new theorem does not establish a witness-free SD/RSD reduction,
commitment binding/hiding, soundness, signing simulation, ideal-cipher analysis,
or extraction from different digests. Source correspondence and the existing
literal inconsistencies are unchanged. The new generic probability helper's
event-cover premise is discharged by the fresh-query provenance theorem; it is
not an added cryptographic assumption. Assumptions and Final remain unchanged.

## Commitment collision reductions at actual source computations

BAVCBinding compares the two actual levels of Hashbavc. rowQuery and outerQuery
contain the literal domain-byte bits, increasing-index arrays and salt. The
fixed-width array serializer is proved injective, including zero-width boundary
cases. The explicit finder first compares outer query strings, then scans rows
in execution order. A returned pair comes from the two actual query lists; if
their roots agree, the two distinct strings have equal supplied-hash outputs.
Each reconstruction's hash-query list has tau+1 entries, including repetitions;
this is not a runtime bound or a count of all cipher/PRG calls.

The finder is a computable definition using finite list comparisons, not a
classically chosen arbitrary collision. Its none result proves equality of
both salts and the full leaf-commitment arrays. reconstructionRows instruments
the exact prefill/expansion/row computation; mapping it through reconstruction
hashing equals the original staged reconstruction, including every error. It
does not supply the absent nodes binding, equate nodes with tree, or change
the source's rejected-opening behavior.

For two successful reconstructWithNodes calls with equal roots and different
seeds at the same commonly revealed position, the actual reconstruction
collision finder returns a hash collision or returns none with a same-index
seed-commitment collision. Successful row equations prove the leaf digest is
computed from that revealed seed; this relationship is not an assumed binding
contract. The two external nodes environments stay explicit and no existence
of successful literal reconstruction at submitted parameters is asserted.

The source's CommitSeed collision is equivalent to equality of both Enc*
outputs under the two seed keys. With the existing lambda/tweak bounds, the
two plaintexts are distinct. This is an explicit cross-key cipher witness,
not a cipher permutation contradiction or an ideal-cipher probability estimate.
In Category III these are truncated Enc* outputs: equality does not imply
equality of the complete 256-bit Rijndael outputs. Adaptive ICM bounds must
handle this padding/truncation and all previous encryption/decryption queries.

BLCBinding defines the exact verifier Hashlines and Hashaux bit-string queries.
Equal concrete suffix line digests imply equal auxiliary digests or a collision
on the actual Hashlines query pair. The next step similarly yields equal BAVC
roots or a collision on the actual Hashaux pair. Only each payload's leading
fixed-width digest is recovered; no injectivity, fixed length or prefix-freeness
is assumed for the supplied vector/matrix encoders. The necessary auxiliary
digest equations are derived from prepareWithBindings; the combined theorem
uses two actual successful prefix equations and supplied-base suffixes.

This chain does not establish full BLC binding. The verifier's Hashlines still
omits the witness-correction field included by the signer, the supplied seed
array used in folding is not identified with reconstruction.seeds, and the
line-21 scalar/matrix operation is unresolved. None of these issues is repaired
by a collision-freedom premise. Nor do these deterministic collision reductions
bound the adaptive probability of their bad events, show hiding/zero knowledge,
make different digests produce usable distinct challenges, or extract an RSD
witness. Connecting them to the abstract signature game requires full concrete
correspondence. Assumptions and the small Final interface remain unchanged.

## Adaptive oracle collision probability and the remaining coverage obligation

Spec/RandomOracleCollision defines a procedure making adaptive queries to the
same lazy query function as the signature model. A step queries or stops; the
state may depend on all earlier answers. Every query, including repeats, uses
one unit of budget. The initially empty table and reverse-chronological log are
private instrumentation. The collision flag is raised only when a previously
absent input receives an answer already appearing in the earlier history.

Proofs/RandomOracleCollision derives the birthday bound by induction on actual
execution, without postulating any collision estimate or finiteness of the input
or state types. Proofs/RandomOracleCollisionInvariant proves exact table/log
correspondence and that a stored collision implies the flag. Repeats keep their
answers and cannot create a new flag. An arbitrary final selector, even one
inspecting the complete table, cannot exceed choose(q,2)/|Output| for a pair of
distinct queried inputs with equal stored answers. Unqueried guesses are outside
this event; this is not an assumption that a full verifier already queried them.

Spec/Proofs.BAVCBindingROM connects that result to the exact domain-separated
row and outer queries of Algorithms 7/9. It computes a view of the hash from
the final table, checks that every required row/outer input is present, and
checks equal roots and different salt or leaf-commitment data. The lookup's
default only totalizes its type; successful claims never use a missing entry.
The existing computable finder then returns an actual stored collision, giving
choose(q,2)/2^(2*lambda). This includes salt disagreement and arbitrary adaptive
selection of the two data sets. The seed operations in Primitives are unchanged
and unused by this hash-only experiment.

The bound is for this explicitly defined fully queried experiment. Proving that
full source signing/verification and replay produce such query coverage, and
counting all their internal calls, remain formal proof obligations. A coverage
check here must not be substituted for the source verifier or used to discard
forgeries in a claimed full reduction. Ideal-cipher seed binding, Category-III
truncation, the BLC field/alias gaps, challenge separation, extraction and signing
simulation are still unfinished. No security contract, cryptographic axiom or
source repair is introduced; Assumptions and Final remain unchanged.

## Executed BAVC hash verification and total query accounting

Spec/OracleProgram expresses finite adaptive return/query computations. Its
program syntax and array traversal are computable. The PMF interpreter uses the
same lazy random oracle. Bounded and Evaluates are semantic predicates whose
properties are proved: they are not correctness fields supplied by callers.
Proofs/OracleProgram establishes that any sufficiently budgeted run finishes,
and its answers occur in the actual final table. This uses proved persistence
of all stored answers, so later queries cannot invalidate earlier evaluations.

Spec/Proofs.RandomOraclePipeline compose an adaptive adversarial phase with an
answer-dependent second phase on the same table and history. The latter receives
the adversary's state, not direct access to the private instrumentation. Both
collision flags are retained. The full query-history length and conditional
collision estimates give choose(q+k,2)/|Output| for the combined procedure,
including second-phase answers colliding with first-phase answers.

Spec/Proofs.BAVCHashVerification implement the exact increasing-index row hashes
and subsequent salt-bound outer hash from Algorithm 7 lines 8–9 and Algorithm 9
lines 30–31. After the adversary selects two salt/leaf-commitment data sets, both
computations are executed against its existing oracle table. Each uses tau+1
query slots. Every run is proved to finish within 2*(tau+1) slots; the success
event's unfinished branch is unreachable. Successful binding claims test only
equal computed roots and different salt/commitment data, without a query-coverage
guard. Missing inputs are queried. Coverage and equality with rootHash in the
final table are derived from program evaluation, then fed to the actual finder.

The resulting hash-binding probability is bounded by
choose(q+2*(tau+1),2)/2^(2*lambda), counting all calls, including repetitions.
Here q counts adversarial oracle calls, not machine time or the interaction
fuel from the separate signature replay. This completes the explicit two-root
hash computation's query-coverage obligation. It does not account for cipher
seed/tree expansion or other signature services. Their composition, the shared
extendable-output oracle's other output lengths, adaptive ICM binding (including
Category III), source BLC gaps, challenge separation, extraction and signing
simulation remain open. No source error or guard is changed, and no cryptographic
assumption, success contract or new final theorem is introduced.

## Adaptive ICM semantics, conditional queries and truncated answers

Spec/IdealCipher samples a complete family of keyed permutations once and runs
an adaptive stop/encrypt/decrypt procedure against it. The family and transcript
are private interpreter state, not procedure arguments. Decryption uses each
permutation's inverse. A separate interpreter samples uniformly from families
compatible with the complete recorded graph. Its World.possible field only
ensures that this finite conditional sample space is nonempty. It does not
assert binding, pseudorandomness or an adversary success bound. The empty world
and every update construct the witness from the actual sampled family.

Proofs/FinitePosterior proves the finite conditional-resampling identity by
counting. Proofs/IdealCipher uses it to establish exact equality of the two
adaptive execution laws, for arbitrary randomized procedures and budgets, and
connects the result to Assumptions.idealCipherFamily. Queries may repeat, switch
keys or change direction after any answer. Proofs/IdealCipherTrace derives that
all recorded equations belong to one family and the history length is at most
the query budget. Conditioning was not assumed independent of adaptive choices.

Proofs/UniformSymmetry and IdealCipherFresh construct transpositions of unused
ciphertexts at a selected key while preserving every recorded equation. This
proves that a fresh encryption answer is uniform on the unused ciphertexts.
IdealCipherInverse reverses the same family and history to derive the decryption
law: fresh plaintexts are uniform on unused inputs. Recorded queries are
deterministic in either direction. All prior decryption/encryption observations
are included; the two directions are not separate random functions.

IdealCipherCapacity bounds unused inputs and outputs below by M-q, where M is
the full block-domain cardinality and q bounds the entire history, including
repeats and calls at other keys. A fresh full-block target has probability at
most 1/(M-q). A projected event has at most its full-block fiber size divided
by M-q. These ENNReal bounds use natural truncated subtraction; their displayed
denominators give a useful finite estimate when q<M. No runtime is inferred.

Spec/Proofs.IdealCipherSeed implement the Category-III query with both 192-bit
inputs padded to 256 bits and only its returned answer projected to 192 bits.
The transcript retains the full cipher block. Equality with the existing
SeedPrimitives.encStarIII function is proved. A fiber injects into its remaining
64 bits, giving size at most 2^64 without enumerating the block space. The
conditional fresh-query target probability is at most 2^64/(2^256-q).
No inverse or permutation property is assigned to the truncated Enc* function.

The conditional laws above are composed in the paired-cipher argument below.
Full BLC/signature composition, source ambiguities, challenge separation,
extraction and signing simulation remain open. The cryptographic definitions in
Assumptions are unchanged; Final still has three discrepancy statements.

## Paired-cipher collision argument and its remaining coverage boundary

SeedPairing proves that the source's two plaintexts differ by a fixed
lowest-bit flip, independently of the salt, key and in-range address. The flip
is an involution without fixed points for positive widths; pad192 commutes
with it. Bounds on the submitted tweak domain are explicit premises already
checked for the parameter tables. This is not a changed tweak encoding.

IdealCipherJoint proves the joint distribution of the terminal transcript and
the hidden cipher family equals execution with one initially sampled family.
The procedure is not given the family at any stage. IdealCipherComparison
exposes the other key's answer to derive a conditional projected comparison
bound when at least one side is unobserved; it does not assume independence.

IdealCipherPairCollision defines Witnessed as an observed matching half plus
a matching companion in the same hidden family. This is deliberately a larger
event than a completed four-query collision. Its first occurrence leaves one
companion unobserved: otherwise the companions give an earlier witness. A
repeated graph observation cannot create the first witness. The proof uses the
actual compatible graph, the involution and the absence of fixed points.

IdealCipherPairProbability bounds a newly witnessed pair by two conditional
factors. For a forward query the first target is a projection fiber; for an
inverse query it is a fixed plaintext. The fiber-capacity bound implies C>=1
whenever that target exists. The companion exposure consumes an extra virtual
graph entry, and the actual first query consumes another. IdealCipherPairAdaptive
sums over earlier observations and the adaptive execution, obtaining
choose(q,2)*C/(M-q)*C/(M-q-2). This is an upper bound, not an asserted optimal
loss or a bound copied from an unstated source theorem. Natural subtraction
and ENNReal division are used; q+2<M gives the useful finite form.

SeedPairBinding instantiates M=2^lambda,C=1 for full outputs, and M=2^256,C=2^64
for the Category-III projected model. In the latter, arbitrary full-width
encryption/decryption queries are allowed; seed keys and inputs are padded.
The source routine itself explicitly describes Categories I/V, so applying its
same body at lambda=192 retains the documented source-correspondence review.

The deterministic source-collision-to-Witnessed lemmas require that both
left-half entries occur in the transcript. The verification construction below
derives that coverage for two complete commitments. Seed/tree/BLC and
signature/replay composition, extraction and signing simulation remain.
No cryptographic assumption definition or final statement is changed.

## Fully queried seed-commitment binding

IdealCipherPipeline composes two adaptive phases on the same initially sampled
cipher family. Its posterior interpreter has an exactly equal joint law. Early
stopping in the first phase starts the second; it cannot skip verification. The
paired-collision bound composes with total query budget q+k and includes matching
entries across phase boundaries. Its state-to-next-phase function receives no
hidden family or private transcript.

IdealCipherProgram executes finite query programs against this one family and
logs every call. A proved program bound gives exact completion and the full
result/history equation. SeedVerification's program has four explicit calls:
left seed/left input, left seed/right input, right seed/left input, and right
seed/right input. Its exact trace is proved, including when calls repeat.
There is no membership or freshness test in its success event.

SourceSeedVerification discharges the companion relation from the literal
source tweaks and proves the two pairs of projected outputs concatenate to the
actual CommitSeed values. Padding injectivity preserves distinct Category-III
seed keys. Its success predicate is equivalent to two distinct source seeds
with the same commitment, salt and valid index. The fully queried experiment
has exactly the direct source collision law: the latter predicate contains no
program-completion, freshness or transcript-membership condition.

The source-specialized binding bound is choose(q+4,2)*C/(M-(q+4))*C/(M-(q+6)).
For full outputs, M=2^lambda and C=1; the premises lambda>=26 and
4*leaves<=2^24 establish the source input relation for every index:Fin leaves.
For the padded/truncated Category-III interpretation, M=2^256 and C=2^64;
the attacker may still query arbitrary full-width cipher keys/inputs in either
direction. As previously recorded, the printed seed routine explicitly names
Categories I/V; applying that body at lambda=192 retains its correspondence
review. The source algorithms' raw parsing and undefined names are not repaired.

Here q is the earlier cipher-query budget, not signature interaction fuel or
machine runtime. Four verification calls are included; the further two in the
second denominator come from the proved conditional-exposure bound. q+6<M is
needed for its useful finite-denominator form. Full seed-tree/reconstruction
executions and the shared hash/cipher game still need composition and honest
query accounting. The signature fork is not yet an RSD extractor; signing
simulation and end-to-end EUF-CMA remain unproved. Final and cryptographic
assumption definitions are unchanged.

## Shared hash/cipher execution and component program correspondence

Spec/HashCipher defines one interleaved experiment. A cipher family is sampled
once, the hash table begins empty, and the procedure receives only its state
and answers to its chosen hash/encrypt/decrypt calls. Each absent hash input
samples a uniform digest; repeats read that same table. These are probability
model definitions, not assertions that concrete SHAKE and AES/Rijndael jointly
realize the model. Hash inputs may be arbitrary List Bool; no finite message
universe or random-function PMF over an infinite domain is assumed.

Proofs/HashCipher proves exact equality to its joint posterior interpreter,
retaining the hidden family only for terminal analysis. The hash branch commutes
its lazy draw with the compatible-family law; the cipher branch uses the proved
posterior resampling identity. The once-sampled family is explicitly linked to
Assumptions.idealCipherFamily. No additional conditional-independence hypothesis
is imposed on adaptively chosen keys, inputs, query directions or hash calls.

HashCipherHash derives exact hash table/log correspondence, cipher graph
consistency, stored-hash-collision coverage by the flag, and the combined
history-length bound. Its birthday bound holds for each fixed family before
averaging. HashCipherPair derives the paired-cipher bound through both hash and
cipher branches of the same execution. HashCipherSecurity combines these bounds
for one joint event, yielding choose(q,2)*(1/|Digest|+C/(M-q)*C/(M-q-2)). q is
total hash/cipher query and stop fuel. It overestimates either separate count;
this is not a tight per-service bound, signature interaction bound or runtime.

HashCipherParameters discharges the cardinality and companion premises for
full outputs and for Category III (384-bit digests, 256-bit cipher blocks and
192-bit projected outputs). As before, q+2<M gives a useful finite-denominator
cipher term. This bound concerns observed hash collisions and the witnessed
paired-cipher event, not unqueried hash guesses or the entire signature game.

HashCipherProgram supplies finite mixed programs with composed query bounds
and a completion proof. Its hash/cipher lifts have exact operational equality
with the existing interpreters, including logs and result states.
HashCipherSourcePrograms derives exact execution and winning-to-collision
coverage for the source four-call seed check and the two complete BAVC row/outer
hash computations in this shared interpreter. This preserves the previously
proved CommitSeed and root equations. Supplied seed operations in the hash-only
program remain unused, and neither lift resolves a source ambiguity.

The generic bad-event transfer theorem has an explicit coverage premise.
That premise is discharged below for the reconstruction-disagreement event;
it remains a proof task for the signature services, not an assumed security
property. The sequential component execution and reconstruction are extended below; complete
BLC/signature/replay cost accounting, usable challenges, extraction and signing
simulation remain unfinished.
Assumptions.sharedOracleModel explicitly re-exports the candidate joint sampling
model. Uniform marginal hash/cipher models alone do not establish that sampling
relationship. The earlier model definitions and Final are unchanged; the new
definition asserts no concrete correspondence or security conclusion.

## Sequential mixed verification and actual reconstruction cipher stages

HashCipherPipeline uses the same initially sampled family, lazy table and both
histories across two adaptive phases. Stopping or exhausting the first phase
starts the second. Its result flag is the OR of the earlier and later flags;
discarding the earlier flag would invalidate stored-collision coverage. The
posterior law is proved equal to the fixed-family law, and joint_model_extension
identifies it as an extension of Assumptions.sharedOracleModel. No new sampling
or security assumption is added. Both bounds and their sum count q+k mixed
actions. The cipher term has a useful finite denominator when q+k+2<M.

HashCipherVerification executes the existing complete four-call seed program
or the two root-hash programs after a mixed adversary. Completion, actual trace
coverage and source output correspondence are proved. HashCipherSourceSeedVerification
equates the seed experiment to the literal distinct-seed/equal-CommitSeed predicate
with common salt/index, including Category III. No already-queried, freshness or
completion guard is added to that direct predicate. Budgets are q+4 for seeds
and q+2*(tau+1) for the two root hashes; q bounds mixed actions, not signature
queries or runtime. These are component binding bounds, not signature security.

BAVCCipherProgram replaces calls to source ExpandSeed and CommitSeed in the
expansion and leaf/row loops by their actual cipher-query programs. Its Layout
record contains only key/input/output conversions. fullLayout and truncatedLayout
have proved exact Enc* correspondence; no security/correctness field is supplied.
The source's literal prefill, tree test, distinct nodes binding, internal-index
order, hidden-leaf branch and leafOffset are retained. reconstruction_value
equals the earlier staged reconstructionRows for every initial cipher history,
including every error. The bound 2*(tau*N-1)+2*N*tau allows two calls per internal
node and per leaf; skipped, hidden and error branches may consume fewer. run_shared
returns the exact result and graph while retaining the earlier hash table/log.
An error is a completed computation returning that error, not an accepted or
rejected signature. No missing binding is invented and no error is filtered out.

BAVCCipherProgram is a projection onto Algorithm 9's cipher operations.
Source line 30 hashes each row before the next row's cipher calls; the complete
ordered execution and its collision coverage are supplied in the next section.
BLC's unresolved seed/Hashlines/scalar boundaries and the absent complete §5.3
reduction remain unchanged. Neither this component correspondence nor the
generic transfer theorem supplies an RSD extractor or a secret-free signing
simulation. Assumptions and the three-statement Final interface are unchanged.

## Complete ordered reconstruction and its disagreement bound

BAVCReconstructionProgram implements Algorithm 9's oracle calls in source order:
prefill and internal-node expansion; each leaf row followed immediately by its
row hash; then the salt-bound outer hash. It uses the same explicit nodes binding,
source guards, codecs and full/III Enc* layouts as the earlier literal staged
definition. reconstruction_evaluates and run_complete prove exact equality of
the returned value with reconstructWithNodes, for successful and error outcomes.
This proves value correspondence, not correctness of the source's opening routine.
No tree/nodes alias, missing seed, line-21 BLC operation or corrected source guard
is introduced.

HashCipherEvaluation is a derived execution certificate: each hash constructor
has a stored lookup in the actual final table, and each cipher constructor has
its actual entry in the final graph. run_evaluates proves this relation from the
operational run and a proved query budget. BAVCReconstructionCoverage derives
both commitment calls for every common revealed seed from those evaluations.
The totalized hash in primitives is only a way to state source equations;
successful reconstruction proves coverage of every row and outer input, so its
fallback is unused there. The final-table proof also covers repeats and prior
adversarial lookups.

BAVCReconstructionGame runs both selected computations after an arbitrary mixed
adversary using the same family/table. The second runs even if the first errors;
both Except results are retained. Its bad event is two successful outputs with
the same root and different seeds at a coordinate revealed by both. It is not
the signature acceptance predicate. Restricting this particular disagreement
event to successful reconstructions does not convert undefined source execution
into signature rejection or justify a vacuous EUF-CMA claim.

The existing deterministic finder is linked to these actual executions. A
returned hash pair has both lookups in the final table. If it returns none,
the common-index seed collision has its required cipher entries in the same
final graph. full_winning_covered and truncated_winning_covered discharge the
generic event-bound coverage obligation; no binding/coverage contract is assumed.
The companion, key-padding and projection-capacity facts are derived. Explicit
source width/tweak premises remain: lambda>=26 for the full-output routine and
4*(tau*N)<=2^24 for the tweak range.

Each reconstruction has B=2*(tau*N-1)+(2*N+1)*tau+1 query budget. With Q=q+2*B,
the proved bound is choose(Q,2)*(1/|Digest|+C/(M-Q)*C/(M-Q-2)). Full outputs use
|Digest|=2^(2*lambda), M=2^lambda, C=1; Category III uses 2^384, 2^256 and 2^64.
The useful finite denominator requires Q+2<M. These are query/action counts,
not runtime, signature-query counts or an optimal-loss claim. Both complete
reconstructions are included even if calls repeat. Category-III application of
the seed routine retains its previously documented source-scope interpretation.

This establishes the selected reconstruction disagreement property. It does
not prove the entire vector/line commitment secure, bind Algorithm 12's supplied
folding seeds to reconstruction, or connect to a signature forgery. The next
composition is the actual Hashaux/Hashlines chain on the same oracle, followed
by BLC/signature/replay query accounting, usable algebraic challenges, extraction
and signing simulation. The candidate joint oracle model, concrete-primitive
correspondence boundaries and three-statement Final interface are unchanged.

## Verifier hash chain after complete reconstruction

Spec/BLCHashChain models the Algorithm-12 lines 22–27 hash calls as a mixed
oracle program: the Hashaux query on the reconstructed root and the supplied
auxiliary tail, an arbitrary bounded intermediate program, then the Hashlines
query. The source constructor uses the exact auxQuery/linesQuery byte strings
already recorded in Spec/BLCBinding: domain byte 2 with hcom and the encoded
positive-index corrections, and domain byte 3 with the three-field payload. It
does not append the signer's fourth witness-correction field, so the recorded
Algorithm 10/12 payload mismatch is preserved. Its base-matrix program is the
explicit line-21 boundary; a caller must supply that program, and no claim is
made that any supplied program implements the ill-typed subtraction.

Spec/BLCReconstructionChain runs the complete ordered Algorithm-9 body, an
explicit pre-Hashaux program, and the chain in source order; every error is
retained as an Except value. The adversary selects both inputs after mixed
queries, including the nodes binding and the intermediate programs' bounds.
The winning event is two successful executions with equal line digests and
different seeds at a coordinate revealed by both. It is not signature
acceptance, and restricting it to successful executions does not turn the
literal source's undefined reads into rejection.

Proofs/BLCHashChain and Proofs/BLCReconstructionChain derive: completion,
each chain's two actual table lookups, root equality or a stored collision on
the exact query pairs (using the fixed-width digest header), and the seed
collision's cipher coverage through the existing reconstruction coverage proof.
The full/III bounds use Q = q + 2*(B + p + m + 2), where B is the reconstruction
budget and p, m are the supplied programs' bounds. The useful finite cipher
term requires Q+2<M; width/tweak premises remain explicit.

Human review items: the supplied intermediate programs are caller inputs
without correctness contracts; the auxiliary tail is the supplied encoding of
the transmitted corrections, not a proved codec; root consistency across the
chain still does not identify Algorithm 12's separate seed array or its
rshare/phi_mu bindings with reconstruction output. Full BLC binding, signature
and replay cost accounting, usable algebraic challenges, extraction and
signing simulation remain open.

## Seed-vector extraction from two chain executions

Spec/BLCSeedExtraction defines agreement of two revealed seed maps at the
commonly revealed leaves of one execution, a complete vector agreeing with
both maps, and the pointwise merge preferring the left map. Its failure event
on the chain game requires equal line digests, an execution with different
hidden indices on the two inputs, and the absence of a unique agreeing
complete vector. The hidden indices are the adversary-selected inputs of the
two reconstructions; nothing here derives them from a digest or from the
source's challenge expansion, whose literal integer sampler still reads the
undefined B.

Proofs/BLCSeedExtraction shows that a successful literal reconstruction has a
present seed at every non-hidden leaf, that consistency makes the merge agree
with both maps, and that differing hidden indices make the agreeing vector
unique. On the game's support, failure therefore implies the disagreement
event, and the failure probability is bounded by the continuation-40 chain
bounds. No source binding is repaired, and no contract about the supplied
intermediate programs or the nodes binding is added.

Human review items: the extracted vector is a leaf-seed vector of the staged
reconstruction, whose revealed values may originate from the external nodes
binding; whether such a vector corresponds to the signer's actual seed tree
depends on the unresolved nodes/tree aliasing in Algorithm 9. Turning the
seed vector into witness lines requires the folding computation of
Algorithm 12 lines 9–16 with its separate seed/rshare/phi_mu bindings, and
the usable-challenge separation between two accepted digests remains open.

## Extractor bindings for the Algorithm-12 fold

Spec/BLCSeedFold names an explicit environment for the undeclared names of
Algorithm 12 lines 9–16: `seed` is the array of a supplied complete seed
vector, `rshare` is initialized to zero, and `phi_mu` is the Gray row of the
leaf index. This is an extractor's own choice of computation, recorded as
reviewable input. It is not asserted to be the source's intended meaning;
the literal prefix with absent bindings and its no-return theorem are
unchanged. The correction term follows the printed read of slot e-1 for
positive e and nothing at e=0.

Proofs/BLCSeedFold derive, from the existing exact fold sum, that the share
at hidden index i equals slope*phi(i)+intercept in characteristic two, with
slope the direct fold accumulator plus the transmitted correction and
intercept the fold base. Reaching the line-21 operands under these bindings
gives the Q matrix columnwise in this form. The two-index difference identity
and the honest-slope identity (for Algorithm 10's corrections computed from
the same seeds) are proved by ring arithmetic.

Human review items: the transmitted corrections are adversarial signature
data, so the slope is only the committed accumulator when they are honest;
the extracted seed vector of the previous continuation is a reconstruction
output whose relation to the signer's tree depends on the nodes/tree
boundary; and connecting the affine Q to the suffix's witness lines and to
PIOP evaluation remains the next step. Line 21 is still unresolved.

## Suffix values and a candidate two-challenge consistency reading

Spec/BLCSeedLines defines the psi contribution of one execution's Gray row,
the share and intercept matrices of the extractor's fold, the masked slope
[I|M]·slope, and `CandidateConsistency`: the binary shape "consistency
columns = plain ⊗ Gray(hidden) + base". That shape is one possible reading
of line 21's scalar/matrix subtraction. It is introduced only as a hypothesis
for the two-challenge theorem and is not asserted to be the printed meaning;
`BLCRecompute.prepare` still stops at the line-21 operands.

Proofs/BLCSeedLines show psi of the affine matrix splits into per-execution
slope terms plus the intercept psi; the suffix witness/randomness values
take that form under the extractor's bindings; with a constant slope and
the Gray merge as encoding, the witness value is correction+slope plus
delta times the intercept psi; and under the candidate reading at two
hidden vectors differing at a Gray bit, the masked slope equals the plain
check and the intercept's columns equal the base at that coordinate.

Human review items: whether the candidate reading is the intended line 21;
the Gray merge is one of the two recorded header interpretations; the
constant-slope premise holds for honest corrections but is exactly what a
forger need not satisfy, so bounding non-constant slopes needs the random
consistency matrix and remains open; equal transmitted plain/base across the
two accepted attempts is a fork-consistency fact still to be connected.

## Uniform consistency-mask kernel probability

Spec/ConsistencyMatrix defines [I | M] applied to a fixed vector, its top and
payload parts, and two events over the explicit uniform matrix sampler of
`UniformChallenges.probability`: annihilation of a fixed vector, and equal
masked images of two fixed vectors. Proofs/ConsistencyMatrix proves the
split formula, the uniform fiber law for any surjective linear map into a
finite module, surjectivity of M ↦ M·v for nonzero v, the exact value
|F|^(-s) when the payload part is nonzero, impossibility when only the top
part is nonzero, the resulting bound for any nonzero vector, the bound for
two distinct vectors, and the binary instantiation 2^-(lambda+B).

Human review items: the source's mask is the XOF expansion of the auxiliary
digest, which the ROM would model as a fresh uniform matrix only after the
hcom/corrections query that fixes the slopes; that ordering and the bit-to-
matrix conversion (`expandConsistency` with `bitField`) are not yet connected
to this sampler, and the existing binary-sampling uniform law covers the
bits but not this composition. The vectors must be fixed before M is
sampled; an adaptive adversary choosing corrections after seeing M is
outside this statement and needs the oracle-order argument.

## Adaptive oracle trap for a fixed function of the query input

Spec/RandomOracleTrap defines, over the existing adaptive lazy-oracle
experiment, the event that some recorded query/answer pair satisfies a trap
predicate, and the mask trap for a fixed vector-valued function of the
input. Proofs/RandomOracleTrap derives the per-query step (a fresh uniform
answer contributes at most epsilon; a repeated query returns a pair already
in the history, by the recorded-table invariant), the budget*epsilon bound
for the whole experiment, the table-to-history transfer, and the mask
instantiation budget*|F|^(-s) with its binary form 2^-(lambda+B).

Human review items: the predicate must depend on the answer only through
the query input it was returned for, which is the oracle-ordering content;
the source mask is an XOF stream of the auxiliary digest rather than a
single fixed-width oracle answer, so modeling it as one matrix-valued lazy
oracle is an explicit model choice to be recorded when composed; the slope
vector is a function of seeds and corrections, while the auxiliary query
input contains hcom and corrections, so the composition needs the hcom-to-
seeds binding from the reconstruction collision bounds.

## Table-dependent trap on the instrumented oracle trace

Spec/RandomOracleTrace records, for each fresh query only, the table before
it together with the input and fresh answer. The trace event evaluates a
predicate at that earlier table. `Traced` states that every stored value has
such an entry whose earlier table lacked it and is extended by the final
table, and that every fresh entry persists. Proofs/RandomOracleTrace derive
the per-query step, the run induction and the budget*epsilon bound for
predicates with a uniform per-answer bound at every table, plus table growth
and the trace/table correspondence through any continuation.

Human review items: this instrumentation is experiment bookkeeping and
changes no oracle law, but no law equality with the uninstrumented run is
proved here, so results must be transferred by instantiating the same
procedure in both; a predicate evaluated at the final table is not bounded
by this lemma, so a commitment chain completed only after the mask query
must be charged to a separate fresh-answer-hits-earlier-input event, which
is not yet formalized.

## Fresh answers hitting values mentioned by earlier inputs

Spec/RandomOracleMention defines the prefix-dependent trap event on the
instrumented trace (each fresh entry is tested against the trace preceding
it) and the mention predicate for an explicit map from inputs to the finite
set of digests they mention. Proofs/RandomOracleMention derive the per-query
step, the run induction with a position-dependent epsilon, the experiment
bound as a sum over positions, the uniform membership mass |S|/|Output|,
the per-query mention bound n*m/|Output| after n fresh entries, and the
total choose(budget,2)*m/|Output|.

Human review items: the mention map is a caller-supplied parser of query
inputs (for example the hcom component of an Aux query or the row digests
inside an outer-hash input); its correctness is a serialization fact to be
proved when composed, not assumed here. Repeated query inputs contribute
nothing new because their first occurrence is a fresh entry. The bound
counts only values mentioned by earlier oracle inputs, not values the
adversary holds without querying.

## Product-valued oracle for hash and mask components

Spec/ProductOracle fixes a model in which one lazy oracle returns a pair
(digest, matrix) per fresh input; hash queries use the digest component and
mask queries the matrix component. The components are independent uniform
by construction. Proofs/ProductOracle derive the component marginals, the
table-dependent mask trap bound budget*|F|^(-s), the digest-component
membership mass |S|/|D|, the per-query mention bound and the total
choose(budget,2)*m/|D|.

Human review items: this is a modeling device, not the source's SHAKE/XOF
structure; the actual mask is an XOF stream of the auxiliary digest, and
a hash query and a mask query at the same input string would here share one
pair, which the composition must avoid by its input layout (hash inputs are
domain-prefixed byte strings, mask inputs are digests). The device is for a
standalone slope-consistency statement; integration into the shared
hash/cipher model used by the signature game is a further step.

## Ordered oracle log and dependency chains

Spec/OracleChain defines the newest-first ordering invariant of the
instrumented log, freshness of its entries, sink-first linked chains whose
inputs mention their predecessors' expected digests, and stored/present
predicates for a chain in a table. Proofs/OracleChain maintain ordering and
freshness through any continuation, prove that an entry whose input is
already stored in another entry's earlier table is the older one, and
derive the two-link and full-chain dichotomy: present at sink time, or a
fresh digest hit a mentioned value.

Human review items: the chain's links must have pairwise distinct inputs
and differ from the sink; in the concrete BAVC/BLC chain this follows from
the domain prefixes and lengths of the inputs and from the mask input being
a digest rather than a byte string, which must be checked when the chain is
instantiated. The mention map must actually extract the expected digests
from the serialized inputs; that parser is still to be written.

## Concrete chain strings and the mention parser

Spec/BAVCChainInputs defines the row, outer and auxiliary strings and the
mask input as strings of one product-valued oracle, the fixed-offset
digest windows (offset 0, offset 8, and 8+lambda+2*lambda*e for e below
tau) as the mention parser, and the sink-first chain per execution.
Proofs/BAVCChainInputs prove the string lengths, the indexing facts for
byte prefix, salt and fixed-width arrays, the three extracted windows, the
parser size bound tau+2, pairwise distinctness (domain byte 1 versus 2;
outer versus row by parity of lengths with lambda positive; mask input
versus the others by length with tau and N positive), the linked/distinct
chain facts, and the per-execution present-or-mention conclusion. The
row and outer strings are definitionally the reconstruction program's
inputs.

Human review items: modeling the mask input as the bare auxiliary digest
string is a layout choice for the product oracle; the source feeds the
digest to an XOF rather than to the hash. The parser extracts windows at
fixed offsets only, so inputs of other layouts mention unrelated windows,
which is harmless for the bound. Positivity of lambda, tau and N is
required for distinctness and holds for all submitted parameters.

## Chained claims, uniqueness and digest collisions

Spec/SlopeConsistency defines claims, their rows through a supplied per-
leaf commitment function, their tails through the supplied corrections
serializer, the chained-in-table predicate, digest-collision freeness and
the digest-collision prefix event. Proofs/SlopeConsistency prove the
injectivity of the auxiliary, outer and row strings in their fields, the
uniqueness of the slope-relevant components of chained claims with one
auxiliary digest in a collision-free table, that the slope depends on the
auxiliary data only through its corrections, the collision event's bound
choose(budget,2)/|Digest|, that distinct stored inputs with equal digests
raise it, and that collision freeness restricts to earlier tables.

Human review items: injectivity of the leaf commitment function is a
hypothesis here; in the source it is the seed-commitment binding already
bounded in the ideal-cipher model, and the two must be joined. Injectivity
of the corrections serializer is likewise a hypothesis, since the
serialization functions carry no contract in this development. The plain
check and witness correction are not determined by the chain and are not
claimed to be.

## The standalone slope-consistency bound

Spec/SlopeConsistencyGame fixes a setting (BLC primitives, PRG byte count,
per-leaf commitment function, corrections serializer), defines the slope of
a claim, the pairwise trap vector through classical choice of a claim
chained in the given table, the winning predicate and the any-pair trap
event. Proofs/SlopeConsistencyGame show that under uniqueness the trap
vector at a chained claim's mask input is that claim's slope difference,
that chaining restricts to the mask entry's earlier table, that a winning
run raised a trap, the mention event or the collision event, and the
three-term bound.

Human review items: the game is standalone, on the product-valued oracle
with the mask modeled as the matrix component answered at the bare
auxiliary-digest string; the mask trap carries a tau^2 union loss; the
commitment-injectivity hypothesis stands in for the cipher-model seed
binding and the serializer-injectivity hypothesis for an absent
serialization contract; the procedure's final claim is arbitrary, so the
bound does not yet speak about signatures, hidden-index challenges or
extraction.

## Instrumented shared hash/cipher execution

Spec/HashCipherTrace adds the fresh-query log to the shared execution's
result and run, with the same collision flag marking; cipher queries do
not touch the hash table or the log. Proofs/HashCipherTrace prove that
forgetting the log projects the instrumented run and its joint experiment
exactly onto the existing ones, maintain the traced/ordered/fresh and
table-growth invariants, and re-derive the table-dependent and prefix-
dependent trap bounds for a fixed family and for the uniform mixture.

Human review items: the digest type remains a parameter, so the product-
valued digest (hash and mask components) can be instantiated here, but
the mask component is then also returned for hash-only inputs and ignored;
the bounds count hash queries by the full budget, including cipher queries
and stops, which is conservative. No change was made to the shared model's
law; the projection equality is the stated correspondence.

## Unobserved-key double match

Proofs/IdealCipherUnseenMatch proves, by two posterior steps with the
existing fresh-target bounds, that a key with both paired inputs
unobserved matches two given outputs with probability at most
1/(M-q)*1/(M-(q+1)), and the union over a finite set of such keys. It
uses only the defined ideal-cipher posterior law.

Human review items: the intended use is the seed-collision case split in
the shared model, where a seed colliding with an executed named seed is
either queried, giving the witnessed pair event, or unqueried, giving this
bound with the key set of size at most 2^lambda; the resulting term is
about 2^lambda/(2^lambda-q)^2, roughly 2^-lambda per named seed, and is
multiplied by the number of named seeds tau*N. The companion input must
differ from the input, which holds for the source's lowest-bit flip.

## Slope-consistency game in the shared model

Spec/SharedSlopeGame defines the commitment through CommitSeed under the
hidden family at the claim's salt, the queried-claim predicate (both
commitment calls of every named seed in the cipher history), the local
no-collision predicate, the trap vector, the winning predicate and the
witnessed and unseen-match events. Proofs/SharedSlopeGame prove uniqueness
with injectivity only at the named seeds, the trap vector identity under it,
the chain presence from the log invariants, the collision case split via
the commitment equality and the companion structure, the history
consistency of the traced joint experiment through the projection, and the
five-way coverage theorem.

Human review items: the queried-claim condition is part of the winning
event, as in the earlier fully-queried commitment steps, and is to be
discharged by executing the named claim's commitments; the serializer
injectivity hypothesis remains; the width premise 26 <= lambda and the
tweak premise 4*tau*2^kappa <= 2^24 are the source's, as before; Category
III with padded keys and truncated outputs is not yet instantiated here.

## Probability assembly of the shared-model slope bound

Proofs/SharedSlopeBound prove a family-dependent version of the mixture
trap bound, a final-world lemma for the posterior execution (an event of
the family, final state and cipher history is bounded by its posterior
bound at the final world, with the history length at most the budget), the
fixed-world unseen double match bound as a union over leaf positions of
the unobserved-key bound, the transfer of the witnessed pair event and of
the unseen event through the projection, and the five-term total.

Human review items: two bridging lemmas transport bounds across
syntactically different but equal `Fintype` and `Decidable` instances,
needed because the generic cipher lemmas were elaborated with classical
decidability; they are proved from subsingleton-ness and change no law.
The unseen term carries the factor tau*2^kappa*2^lambda over the squared
unused range, roughly tau*2^kappa*2^-lambda, and the mask term carries the
tau^2 union loss; neither is claimed optimal. The queried-claim condition
and the serializer injectivity remain explicit.

## Instrumented two-phase shared execution

Spec/HashCipherTracePipeline runs the instrumented shared execution for
two procedures in sequence, the second from the first's selected state
with the first's table, histories and log, marking the earlier collision
flag as the existing two-phase execution does. Proofs prove the exact
projection onto `HashCipherPipeline.runFixed` and its joint experiment,
the invariants through both phases, that a run adds at most its fuel in
fresh entries, and the two trap bounds with total budget q+k, where the
prefix bound uses monotonicity of the per-position epsilon to shift the
second phase's positions to at most q.

Human review items: as in the single-phase case, the bounds count every
action of both phases; the second phase's budget k will be the number of
commitment calls of the named claim, 2*tau*2^kappa, when the slope game
is re-stated on this execution.

## Executed commitments in the slope game

Spec/SharedSlopeExec defines the list of all leaf positions, the program
making both commitment calls per position and returning the claim, its
budget 2*tau*2^kappa, the claim read from a final program state (with an
all-zero default outside a finished state), the two-phase experiment with
the program interpreter as second phase, and the winning predicate without
a queried condition. Proofs/SharedSlopeExec prove the program bound, the
evaluation certificate giving every call's entry and the returned claim,
the claim and queried facts from the two-phase projection and the existing
evaluation lemma, the coverage core from invariants, the two-phase final-
world posterior lemma, the transfers of the unseen and witnessed bounds,
and the assembled bound.

Human review items: the second phase is an honest verification program,
not adversarial, and its calls are charged to the budget; the claim's
corrections serializer injectivity remains a hypothesis; the default claim
is never reached on the experiment's support but is part of the reading
function; Category III is not yet instantiated in this chain.

## Shared-model scheme skeleton and the target decision

Spec/SharedScheme instantiates the abstract game's other-state with the
shared world and implements Algorithm 4's verification as an executed
oracle program, with two explicit parameters: the verifier's middle
program (Algorithm 12 lines 9–21) and the hidden-index expansion. Both are
parameters because the literal source does not define them: the fold
reads the undeclared `seed`/`rshare`/`phi_mu`, line 21 is ill typed, and
SampleIntegers assigns the undefined B. Proofs/SharedScheme prove the
typed fork glue and the lifted-program evaluation correspondence.

Decision required from the user: the final composition of the reduction
needs a declared verifier for those lines and a declared expansion, as an
explicitly identified corrected target, or the reduction must stay
conditional on any middle/expansion satisfying stated equations (the
candidate consistency reading and a balanced expansion). The loop will
proceed with the conditional form, keeping the literal source's defects
visible, unless a target is chosen. The honest signer as an oracle program
is also still to be written for both signing simulation and the game.

## Executed verification and the chain games

Proofs/SharedSchemeChain decompose a successful executed verification
(reconstruction on the digest projection, the two chain lookups, the
middle's evaluation and the recovered record), derive equal roots from
equal lines digests in a digest-collision-free table through the fixed-
width headers, view the projected table as a shared-model result for the
existing reconstruction collision lemma, and derive, for hidden indices
differing at an execution, the unique complete seed vector unless a digest
collision or a recorded seed collision occurs.

Human review items: the hidden indices are `V.expand piop counter`, the
explicit expansion parameter; the seed collision event is stated with the
projected table's primitives and the recorded entries exactly as in the
reconstruction game, so its probability is the earlier bound; the middle
program's value is carried but not yet related to the slope and fold
identities, which is the next step.

## Candidate verifier middle

Spec/CandidateVerifier binds the reconstruction's revealed seeds to the
undeclared seed array, zero to rshare, the Gray row to phi_mu, takes the
mask from the mask oracle at the auxiliary digest, and reads line 21 as the
binary base equation. The verifier middle's signature now also receives
the salt, auxiliary data and hidden indices. Proofs/CandidateVerifier
show the leaf fold reads only non-hidden seeds, so a partial array
agreeing with a complete vector gives that vector's prefix sums; the fold
and share matrix of the candidate equal the affine share matrix of any
agreeing complete vector; a successful evaluation records the mask lookup
and returns the suffix values and the candidate base; and the candidate
base equals the masked-slope form.

Human review items: this is a candidate corrected target for lines 9–21,
not the literal source, whose prefix with absent bindings cannot reach line
21 as proved earlier; the user's decision on the declared target remains
pending, and other candidates (for example raw-index rather than Gray
phi_mu, or a different line-21 reading) would need their own modules.

## Fork to slope claim

Proofs/ForkSlope: for a verifier setting whose middle is the candidate
middle, two successful executed verifications on one
digest-collision-free table with equal lines digests, hidden indices
differing at an execution, injective corrections serialization and
injective lines payload serialization, either exhibit a recorded seed
collision at that execution with equal salts, or give a complete seed
vector and mask with equal salts, corrections and plain checks such that
the masked slope of the execution equals the plain check in every
coordinate. The salt equality uses the recorded outer lookup of each
reconstruction and the outer-string injectivity; the agreement of the two
merge completions uses uniqueness of agreeing vectors; the slope identity
subtracts the two candidate base equations at a bit where the Gray rows
of the two hidden indices differ.

Human review items: the two serialization injectivity hypotheses are
explicit, not derived from the concrete encoding; the result is
conditional on the candidate target (undecided); and the recorded seed
collision disjunct is stated against the cipher entries of the executed
run, to be charged to the shared-model collision bound later.

## Honest signer commitment program

Spec/SharedSigner: the honest signer's commitment phase as an executed
hash/cipher program. Algorithm 7's expansion loop is written step by step
with both Enc* calls per parent through the layout; every leaf commitment
is CommitSeed at the leaf-count-shifted address; the row hashes and the
outer hash are the exact `rowQuery`/`outerString` strings; Algorithm 10's
PRG table and corrections are computed from the supplied PRG; the Hashaux
query is the chain's `auxQuery`; the consistency mask is the mask oracle's
answer at the auxiliary digest, as in the slope game, rather than an XOF
expansion; the commit arithmetic is the existing `commitArithmetic`; and
the Hashlines query is `linesQuery` with a parameter tail.
Proofs/SharedSigner: a successful evaluation equals `BAVC.commit` under
the primitives induced by the executed family and table (digest component
of the table, Enc* through the family), with all five chain lookups stored,
both commitment entries of every leaf seed in the cipher history and the
result's fields equal to the commit arithmetic at the stored mask; the
program is bounded by `commitBudget`.

Human review items: the Hashlines tail is a parameter because the literal
signer appends the witness correction while the shared verifier's chain
omits it, so honest signatures and the verifier's lines query agree only
under the verifier's tail, a source defect kept explicit through the two
named readings; the mask-oracle reading of the consistency expansion is
the same modelling decision as the slope game; the PIOP, retry and opening
phases and the abstract game's signing services are not yet attached.

## Shared-model signing services

Spec/SharedSigning instantiates the abstract game's components in the
shared model at a fixed PIOP shape: uniform salt and root, the executed
commitment program within its budget, the PIOP prover for the HashPiop
payload and the signer's state; Algorithm 11 observed on the HashPiop
digest with an explicit challenge expansion for the opening and the
parsed body; the executed verifier on existing bodies; and key generation
from a witness sampler at a fixed instance and public key with a uniform
cipher family. Proofs/SharedSigning characterize the supports: every
prepared state is read from a commitment that evaluates on the resulting
world's table and history, the opening is deterministic, and every honest
signature with a body carries the salt, auxiliary data, Algorithm-11
opening and higher coefficients of such a state with its digest stored at
the typed HashPiop input.

Human review items: the body type is optional so that a pending or
undefined Algorithm-11 observation yields no signature rather than an
invented one, a modelling choice to be charged or assumed away in the
final composition; the challenge expansion of the signer and the hidden
expansion of the verifier are separate parameters whose agreement is a
hypothesis of later theorems; key generation fixes the instance and public
key bits, which is the shape a reduction to a given RSD instance needs,
not the literal KeyGen; the unreachable non-returning branch of the
commitment run returns a default state and is excluded by the budget
lemma.

## Fork branches on a common prefix

Proofs/ForkSlopePrefix: the hash inputs visited by an evaluation are
listed by running the program against the table; an evaluation whose
visited inputs are all stored in a prefix table that the branch table
extends holds on the prefix, and evaluations are monotone in the cipher
history. The fork-to-slope lemma then applies to one verification per
branch on the prefix table with the union of the two histories.

Human review items: the hypothesis that every visited input of both
verifications lies in the prefix is exactly what the chain-mention and
fresh-digest bounds must deliver (a verification visiting a fresh input
after the fork can only accept with the guessing probability), and is
not yet discharged; the cipher family is fixed across branches by the
model, so no cipher-side prefix condition is needed beyond history union.

## Chains across the fork cut

Proofs/ForkCut: `Cut P log` says every fresh entry of a branch's log was
answered after the fork table P or is stored by P; a stored chain whose
sink is in P is present in P or a fresh digest hit a mentioned value
(through the existing sink-first chain lemma, using the sink's own fresh
entry, which is pre-cut); the Hashlines string mentions the auxiliary
digest at offset 8 and is separated from the auxiliary, outer and row
strings by its header byte 3; hence the verifier's chain for every
execution is in the cut whenever its lines string is, up to the mention
event.

Human review items: the cut property is a hypothesis to be derived from
the forking construction (the fork table is one state on the branch's
chain of tables); the lines string being in the cut is the fixed-target
event (a fresh post-fork digest equal to the lines value fixed in the
HashPiop input) to be bounded per branch by the budget times 2^-2λ; the
mask input is not linked to the lines string by any mention, so the two
branches may read different masks when the mask is queried after the
fork, which the fork-to-slope lemma does not yet cover, and the adversary
can choose the counter after seeing a mask, so a post-fork mask argument
would need a union over counters, which the s = λ + B margin is designed
for; this is the next structural decision.

## Fixed-target event along a branch

Proofs/ForkCutRun: a traced shared run from a table extending the fork
table preserves the cut and the extension; the fixed-target predicate
(a fresh post-fork answer whose digest equals a given target) has
per-query mass at most the inverse digest count by the product-oracle
digest-mass lemma and a monotonicity lemma for Boolean images; the
run-level bound is the initial log's indicator plus the budget times that
inverse; a pre-cut fresh log has indicator zero; a value stored after the
fork with the target digest raises the event, so a stored target value is
in the fork table or the event occurred.

Human review items: the target is a fixed digest (the lines value in the
fork point's HashPiop input), to be fixed per branch run by conditioning
on the snapshot; the cut and pre-cut hypotheses of the branch's start
state are to be derived from the forking construction; the bound is per
run of the traced interpreter, so a branch consisting of several service
runs will sum their budgets.

## Shared-world invariants along the game

Proofs/SharedGameInvariant: a `Preserves` record for a predicate on the
other-state (prepare, open, verify, oracle), with preservation along the
abstract scheme's sign, verification and oracle services, along `run`
to every attempt, along `cut` to every saved snapshot and attempt, and
across `forkAt` to both branches; the shared services preserve any
predicate preserved by program runs; well-formedness (traced, ordered,
fresh, extended, stored) holds from key generation and is preserved;
the cut at a fork table is preserved from a world extending it; a
well-formed world is pre-cut at its own table. The composite statement
`fork_cutAt` gives, at a saved snapshot of the shared game, a well-formed
snapshot world and well-formed, cut attempt worlds on both branches.

Human review items: the field type is restricted to `Type` in this
module so that one program-run hypothesis covers the digest, mask,
cipher and verifier programs (the repository's concrete fields are in
`Type`); the hidden `finalize` step preserves the terminal, which is
proved and used; no probability is computed here.

## Visited inputs of the verification

Proofs/VisitedInputs: the visited-input list of a bind is the first
program's list followed by the continuation's at the evaluated value; a
cipher lift visits nothing; the digest lift visits its projection's
inputs; a successful row loop visits exactly the row inputs of its rows;
a successful reconstruction visits only `hashQueries` of its row
commitments (row inputs and the outer input, the latter rewritten through
the covered row hashes); the candidate middle visits exactly the mask
input; a successful verification visits only the reconstruction's
queries, the auxiliary query, the middle's inputs and the lines query.

Human review items: the lists are computed against the branch table, so
they describe the inputs actually read by the accepting verification;
the middle's visited inputs are left abstract in the verification lemma
and instantiated by the candidate middle separately; no probability is
involved.

## One branch accounted

Proofs/BranchAccounting: `MaskAfterCut` names the event that a mask
input read by the branch is absent from the fork table. On a branch log
that is ordered, fresh and traced by the branch table, cut at the fork
table which the branch table extends, an accepting candidate-middle
verification whose lines value equals the fixed target visits only
inputs present in the fork table, or the fixed-target event, the mention
event or the mask event occurred. The proof reads the verification's
visited inputs, places the lines string by the fixed-target lemma, the
chain strings by the cut chain lemma (through the observed row and outer
lookups of the reconstruction) and the mask input by case analysis.
The reconstruction's visited-input lemma now also returns the
reconstruction record and the observed coverage.

Human review items: the mask event is not charged by any bound here;
both branches may read different masks when the forgery's mask input is
first queried after the fork, and the adversary may choose the counter
after seeing a mask, so a bound would need a union over counters or a
different argument; the fixed target is the lines value of the fork
point's typed input, to be instantiated from the fork's shared input.

## Deterministic fork outcome

Proofs/ForkOutcome: a run ending in a value evaluates to it (no budget
premise); every attempt of the abstract run, and of a fresh branch, is
the output of a verification service call; in the shared model that call
is an executed verification evaluating on the attempt's world, with the
input's lines value equal to the recovered lines and the family
preserved; `BranchEvent` collects the fixed-target, mention and mask
events of one branch world; `SlopeOutcome` is the fork-to-slope
disjunction; `fork_outcome` composes the successful-fork attempts, the
game invariants, the family preservation, the attempt provenance, the
branch accounting and the prefix restriction.

Human review items: the hidden indices in `fork_outcome` are the
verifier's expansion of each attempt's digest and counter, and the
theorem is stated per execution where they differ, so the separation of
hidden indices from distinct targets (a property of the declared
expansion) is still to be supplied; the branch events are not yet
charged with probabilities, and the mask event has no bound; the digest
collision of the snapshot's table is the earlier collision event; the
conclusion is conditional on the candidate middle and the two
serialization injectivity hypotheses.

## Game-level event bound

Proofs/GameEventBound: a `ServiceBound` record (each of the four services
raises a Boolean event on the other-state by at most a constant beyond
its indicator); the signing service's bound is twice the constant
through the HashPiop query that leaves the other-state unchanged; the
verification and oracle services' bounds are the constant; along `run`
the event at the attempt is at most its indicator at the start plus the
fuel times twice the constant, by induction with the mixture bound and
the bind-indicator bound; finalization keeps the terminal; a fresh
branch's attempt is bounded by the snapshot's indicator plus the
remaining fuel times twice the constant.

Human review items: the bound counts adversary actions, not honest
queries, so the service constant must already include the service's own
query budget; the bound is per event and generic in the components, to
be instantiated with the shared services' trace bounds; nothing here
concerns the mask event.

## Fixed-target event over the shared game

Proofs/SharedTargetBound: `targetEvent` is the fixed-target trace event
on a shared world; a program run raises it by at most its budget times
the inverse digest count; the shared services satisfy the service bound
with a common budget bound (commitment budget, verification budget and
one for a public query); at a well-formed snapshot the event at its own
table is absent; a fresh branch raises it with probability at most the
remaining fuel times twice the bound times the inverse digest count.

Human review items: the inverse digest count is `(Fintype.card (Bits
(2λ)))⁻¹`, that is 2^-2λ, left symbolic; the per-action factor two is
coarse (a signing request runs one program, the opening none) and could
be tightened; the bound is for a single fixed target, to be instantiated
with the snapshot's lines value in the fork experiment.

## Size-dependent game-level bound

Proofs/GameEventBoundLen: a traced run's log grows by at most one entry
per unit of budget; a `ServiceBoundLen` record (each service grows a
size by at most `growth` and raises the event by at most `epsilon` of
the size before); the composed sign, verification and oracle bounds
under a level; the run-level bound by induction on fuel with the
invariant "size plus remaining fuel times twice the growth is below the
level"; the fresh-branch bound.

Human review items: the level must dominate the size at the snapshot
plus the branch's remaining growth, which the fork experiment will have
to supply from the cut index and fuel; the function is applied at the
level uniformly, which is coarse but sound by monotonicity.

## Mention event over the shared game

Proofs/SharedMentionBound: `mentionEvent` is the mention trace event on
a shared world; `epsilonM` is the per-run bound at a length, the budget
bound times the mass at length plus budget, increasing; a program run
within a budget raises the event by at most that bound at the current
length (traced prefix bound with the product-oracle mention mass and
the mention count τ+2, summed crudely); a program run grows the log by
at most its budget; the shared services satisfy the size-dependent
service bound with the common budget bound; a fresh branch's bound
follows under a level on the snapshot's length plus the remaining growth.

Human review items: the mention map is the window map at offsets 0, 8
and the row offsets, so the count τ+2 is the chain's, as in the
standalone slope bound; the sum over a run is bounded by the budget
times the mass at the final length, coarser than the exact sum; the
indicator of the prefix's mention event remains to be charged by the
experiment-level mention bound of the cut.

## Event bound along the cut

Proofs/CutEventBound: `cutBad` reads the event at a saved snapshot's
world or an ended terminal; the size-dependent bound along `cut` mirrors
the run bound, with the saved snapshot contributing its indicator; a
saved snapshot's size plus its remaining growth stays below the level.

Human review items: the cut index counts adversarial hash actions and
is not otherwise used by the bound; the snapshot's remaining fuel is the
fuel left at the saving step, so the level premise transfers exactly to
the branch bounds.

## Collision event and prefix bounds

Proofs/SharedCollisionBound: `collisionEvent` is the digest-collision
trace event on a shared world; `epsilonC` the per-run bound at a length;
the program-run bound through the traced prefix bound and the digest-
collision query mass; absence of the event on a well-formed world gives
a digest-collision-free table; the shared services' size-dependent
service bound, reusing the mention instance's size facts; key
generation's empty log; the generic prefix bound of the cut experiment
for any size-dependent service bound with an empty-log-false event; the
snapshot's level premise from key generation; the prefix mention and
collision bounds.

Human review items: the prefix bounds use the level fuel times twice the
budget bound, which also serves the branch bounds; the events are
charged separately and will be summed by a union bound at the fork
experiment; no mask event is charged.

## Charged events of the fork experiment

Proofs/ForkEventUnion: Boolean union bounds for images of a
distribution; a saved snapshot's remaining fuel is at most the cut's
fuel; `branchBad` (fixed-target at the snapshot's table and lines value,
or mention) and `forkBad` (prefix mention or collision at the snapshot,
or a branch event at either attempt); `forkBadExperiment` over the cut
experiment and the fork; a saved snapshot's world is well formed; one
branch's charged event is at most the fuel times the target and mention
constants when the snapshot has no mention event; the fork's charged
events are at most the prefix mention and collision bounds plus twice
the branch bounds.

Human review items: the union over the two branches is a plain sum, as
the branches are independent given the snapshot; the mask event is not
part of the charged events and remains the recorded open question; the
bound is stated at the fixed level fuel times twice the budget bound and
the remaining fuel is bounded by the fuel, both coarse.

## Fork experiment split by charged events

Proofs/ForkGoodOutcome: a bind's success is at most the sum of two
binds' successes pointwise dominating it; a Boolean image splits as the
image with the event excluded plus the event; `goodForkExperiment` is
the fork's success without the charged events; the fork experiment's
success is at most the good success plus the charged events; a
successful fork without the charged events gives the slope outcome or a
branch's mask event at every execution with differing hidden indices,
through the deterministic fork outcome, the snapshot's collision freedom
and the exclusion of the target and mention events; the composed bound
with the explicit charged-event terms.

Human review items: the slope outcome is a disjunction whose first
member is a recorded seed collision, still to be charged by the
reconstruction collision bound; the good experiment's success is the
quantity to be related to the slope game and to extraction; the mask
event remains uncharged; nothing concerns hidden-index separation yet.

## Uniform fork-to-slope data, and the open decisions

Proofs/ForkSlopeUniform: the fork-to-slope lemma restated so that the
two reconstructions, the auxiliary digest and the stored mask are fixed
before the quantification over executions; at each execution with
differing hidden indices, a recorded seed collision there or the masked
slope identity for the merge completion at the stored mask.

Decisions required from the user (recorded 2026-10-08, continuation 80):

1. Mask input after the fork. The mask oracle's answer at the forgery's
   auxiliary digest is not linked to the lines string by any mention,
   so if the adversary first queries it after the fork point the two
   branches read independent masks. The current chain leaves this as the
   uncharged `MaskAfterCut` event. Options: (a) charge it by a per-branch
   fresh-mask argument, which needs a union over the 2^32 counters the
   adversary may choose after seeing the mask (the s = λ + B margin) and
   a treatment of the degenerate case where the base equation is mask-
   independent; (b) restrict the target theorem to adversaries whose
   forgery's mask input precedes the fork point (an explicit hypothesis);
   (c) fork at the mask query instead of HashPiop and rework the chain.

2. Single fork versus multi-fork extractor. One fork yields the slope
   identity only at executions where the two hidden indices differ, and
   the adversary can align them at any chosen execution by grinding the
   counter. SDitH's soundness over τ executions needs, per execution, a
   pair of accepting transcripts with different hidden indices, that is
   several forks or a different extractor. The present statements are
   per execution and leave the choice open.

The loop continues with the work that does not depend on these choices.

## Candidate verifier against the honest signer

Proofs/HonestCandidate: `honestAux` carries the transmitted corrections
computed from the seeds; with it every execution's slope is the common
accumulator (the generic form of the earlier honest-slope lemma), the
masked slope is the plain consistency check, the intercept matrix is the
base row matrix, and the candidate base of the honest shares at any
hidden indices equals the honest base check for any mask.

Human review items: this is completeness of the candidate reading's
arithmetic only; the executed completeness (an honest shared signature
verifying under the candidate verifier) also needs the reconstruction of
an honest opening to return the signer's seeds and hidden commitments
under a declared nodes binding, the same Hashlines tail (the verifier's
reading, which omits the witness correction), and agreement of the
signer's challenge expansion with the verifier's hidden expansion.

## Fork outcomes with uniform data

Proofs/ForkOutcomeUniform: `UniformSlope` packages the two
reconstructions, the auxiliary digest, the stored mask and the per-
execution alternative; the prefix restriction, the deterministic fork
outcome and the good-fork outcome are restated with it, by the same
proofs as their per-execution forms.

Human review items: none beyond those of the per-execution forms; the
uniform data is what a slope-game claim or an extractor would consume
once the two recorded decisions are made.

## From uniform fork data to slope consistency

Proofs/SlopeConsistencyLink: the masked slope is the masked image of the
slope; under separation at every execution the uniform data gives a
recorded seed collision at some execution or the plain check as every
execution's masked image at the stored mask; equal masked images give
two executions with distinct slopes and equal images or a common slope;
with a common slope and the psi-of-challenge-row encoding the candidate
witness value is the transmitted correction plus the common slope, plus
the inverted challenge times the psi image of the intercept row.

Human review items: separation at every execution is an explicit
hypothesis (decision 2); the slope-game winning condition is reached
only as a statement, with no reduction from the signature game to the
slope experiment yet; the encoding hypothesis fixes the merged challenge
as the psi image of the Gray challenge row, the reading used by the
earlier suffix lemmas; the extracted coordinate is the constant term of
a line whose two evaluations at distinct inverted challenges the PIOP
step must still consume.

## Witness line recovery, and the full decision list

Proofs/WitnessLineRecovery: `extractCoordinate` reads a line's constant
term from two evaluations; with a common slope, the psi-of-challenge-row
encoding and distinct merged challenges, the two branches' candidate
witness values give the correction plus the common slope.

Decisions required from the user (complete list as of continuation 84):

1. Mask input first queried after the fork (see continuation 80).
2. Single fork versus multi-fork extractor (see continuation 80).
3. Algorithms 8–9 target. The literal padded opening prefills an empty
   tree and the reconstruction then reads the undeclared nodes array,
   so an honest signature cannot be reconstructed by the literal
   verifier; executed completeness and signing simulation need a
   corrected opening/reconstruction target, declared as such.
4. PIOP target. The literal PIOP verifier rejects honest evaluations
   (`Final.literal_piop_not_complete`); the extraction's final step, two
   evaluations of the witness lines at distinct challenges feeding the
   PIOP relation, needs a declared complete PIOP verifier.
5. Reduction architecture for the cipher-side bounds. The seed-collision
   event and the slope game's kernel bound are proved for the shared
   traced experiment of a single procedure; charging them in the
   signature game needs either the game expressed as one traced
   procedure or service-wise cipher bounds in the lazy view.

The loop has completed the work that does not depend on these choices
and stops here; it can be restarted once a choice is made.

## Decisions taken by the user (2026-10-09)

The user chose the simplest option for every recorded decision and asked
that corrected algorithms be stated as explicitly named candidate targets.
The loop proceeds under the following declared choices; each appears in
the final statements as a named hypothesis or a named candidate target,
never as a silent correction of the source.

1. Mask input after the fork: an explicit hypothesis on the forging
   adversary that the forgery's mask input precedes the fork point
   (`¬ MaskAfterCut` on both branches).
2. Fork multiplicity: a single fork, with an explicit hypothesis that the
   two expanded hidden-index vectors differ at every execution.
3. Algorithms 8–9: a named candidate target in which the opening carries
   the revealed leaf seeds and the hidden commitments directly, and the
   reconstruction recomputes the commitments by the cipher and the same
   row/outer hash chain. The literal path compression is not modelled by
   it; the literal defects remain recorded.
4. PIOP: a named candidate complete verifier, chosen from the readings
   already compared in the repository, with the literal incompleteness
   theorem kept in `SDitH/Final.lean`.
5. Cipher-side bounds: the seed-collision and slope-game events are
   carried as named events whose probabilities are explicit terms of the
   final bound, to be discharged afterwards if time permits.

## Candidate BAVC target (decision 3)

Spec/CandidateBAVC: the candidate opening (revealed seeds, absent at the
hidden index, and the hidden commitments), the candidate opening of a
key, one leaf's commitment program (transmitted at the hidden index,
CommitSeed by the cipher otherwise, absent if the seed is missing), the
commitments function, the candidate reconstruction (all leaf commitments,
a presence check, the row hashes, the salted outer hash) and its budget.
Proofs/CandidateBAVC: the leaf program's value and recorded calls; a
successful reconstruction's seeds, root, stored row and outer queries,
hidden commitments and revealed commitments; the candidate opening of an
honest key reproduces its commitments; the budget.

Human review items: this candidate drops Algorithm 8's sibling-path
compression, so its signatures are larger than the submitted format;
it keeps Algorithm 7's commitments and hash chain unchanged, which is
what the binding and slope arguments use; a missing revealed seed is an
explicit error rather than an undefined read; nothing about the literal
Algorithms 8–9 is changed.

## Candidate scheme

Spec/CandidateScheme: the verification program over the candidate
reconstruction, the body type with the candidate opening, Algorithm 11's
attempt with the candidate opening (grinding test and nonzero merged
challenge; the opening always succeeds), the opening service, the
verification service and the components. Proofs/CandidateSchemeChain:
the four-stage decomposition of a successful candidate verification; a
leaf commitment program visits no hash input; a collector's visited
inputs come from its calls; the candidate reconstruction visits only its
row and outer queries; the verification's visited inputs.

Human review items: the verification service reads the transmitted
higher coefficients through the existing verification-input function,
passing a placeholder literal opening whose fields that function never
reads; the verifier setting's Topen and nodes fields are unused by the
candidate; the retry no longer has the literal opening's bound errors.

## Candidate fork-to-slope lemma

Proofs/CandidateForkSlope: an opening completed by another at its own
hidden index; the fork-to-slope lemma over the candidate reconstruction,
whose root and commitments are read directly from the stored outer and
row queries (salt and commitments agree by the collision-free table), and
whose seed-collision disjunct is a pair of revealed seeds with the same
recomputed commitment and both cipher calls recorded.

Human review items: the seed collision is stated against the induced
primitives of the executed family and table, matching the slope game's
commitment function at the full layout; no projection of the table is
needed since the candidate reconstruction reads the shared table.

## Candidate branch accounting

Proofs/CandidateBranch: one branch of a candidate fork accounted (the
chain strings are the recomputed commitments' row queries and the
salted outer query, read from the candidate reconstruction's stored
lookups); the candidate uniform slope data; the prefix restriction.

Human review items: none beyond the literal scheme's counterparts; the
candidate reconstruction's visited inputs are exactly the chain strings,
so no projection step is needed.

## Candidate game bounds

Proofs/CandidateGameBounds: the candidate services preserve any
program-run-preserved predicate; the snapshot and branch invariants; a
generic size-dependent service bound for the candidate components from
a per-run bound; the mention, collision and fixed-target service bounds;
the prefix bound of the cut experiment; the snapshot's level premise;
the prefix mention and collision bounds.

Human review items: the fixed-target bound is stated in the size-
dependent form with a constant function, equivalent to the earlier
constant form; the candidate verification's single program run and the
pure opening are what make the literal bounds carry over unchanged.

## Candidate fork outcomes

Proofs/CandidateForkOutcome: attempt provenance from the candidate
verification service; the deterministic fork outcome; the charged
events, their experiment and bound; the success split; the good-fork
outcome, all for the candidate components, by the same arguments as for
the literal scheme.

Human review items: as for the literal scheme; the mask event remains
the one uncharged term (decision 1 will add it as an explicit
hypothesis), and the separation at every execution (decision 2) is
supplied by the final theorem's hypothesis.

## Candidate executed completeness

Proofs/CandidateCompleteness: constructive evaluations of the expand and
commit calls, the hash call and the collector; success of the fold loop
and of the share collection with their coordinates; the candidate
middle's evaluation on a stored mask; a leaf commitment's evaluation; the
candidate reconstruction's evaluation under recorded calls and stored
queries; `honest_verifies`: the candidate verification of an honest
signature, on the signer's world, evaluates to the committed lines digest.

Human review items: the hypotheses are the agreement of the verifier's
layout, variant and encoding with the signer's, the candidate middle
with the signer's PRG primitives and sampling counts, and the signer's
Hashlines tail being the verifier's reading (which omits the witness
correction, the recorded source defect); the hidden indices are the
verifier's expansion of the digest and counter, so the signer's own
expansion must agree with it for the signature as transmitted, which the
signing services' retry will fix in the next step; the verification is
evaluated on the signer's own table, so completeness in the game follows
from table growth.

## PIOP extraction step (decision 4)

Decision 4 is resolved by naming the repository's composed verifier
(`PIOPComposition.verifierRun` with `restoredCoefficients`) as the
candidate PIOP target; it is what the shared and candidate schemes
already execute, and its completeness for valid witnesses is the
repository's `restored_eq_hashed_iff` with a zero constant term. The
literal equations' incompleteness theorem in `Final.lean` is untouched.

Proofs/PIOPExtraction: the candidate randomness value is affine in the
inverted challenge with constant term the common slope coordinate; the
extracted witness and the witness and randomness lines; the line
degrees; the composed verifier's recomputation is the composed prover
polynomial of the lines evaluated at the challenge; equal restored and
hashed tuples give the hashed tail and the hashed polynomial's value;
the difference polynomial vanishes at the challenge.

Human review items: the Schwartz–Zippel step over the challenge (with
the adversary's choice of counter) and the batching soundness of the
constant term are the next probabilistic steps; the extracted witness is
the vector of corrections plus the common slope's witness coordinates.

## Deterministic fork extraction (decisions 1, 2 and 5)

Proofs/ForkExtraction: from a good candidate fork, with both attempts'
masks read before the fork (decision 1) and the hidden indices differing
at every execution (decision 2), either a recorded seed collision with
its expansions on the two branches, or the slope-consistency game's
winning condition at the stored mask, or a common slope and the vanishing
of the extracted lines' prover polynomial minus the hashed coefficient
polynomial at the first branch's inverted challenge. The first two are
the events carried as explicit terms under decision 5.

Human review items: the seed-collision event is stated against the
induced commitment family on the snapshot's table; the slope-game event
is stated at the mask stored in the uniform slope data; the common slope
is the slope at execution zero, which exists since tau is positive. The
Schwartz–Zippel step must handle the adversary's choice of the counter
(hence of the challenge) after seeing the coefficient tuple.

## Event-union skeleton of the composed reduction

Proofs/CandidateReduction: the named events of a fork result and the
extraction event are explicit Boolean events (classical decidability);
the fork experiment's success is at most their probabilities' sum plus
the charged-event bound. Extraction yields the extracted lines' prover
polynomial equal to the hashed coefficient polynomial, hence a zero
constant term.

Human review items: the slope-game event quantifies over the mask, so
its bound must be stated for the mask stored at the fork; the
Schwartz–Zippel event is over the challenge chosen through the counter
after the coefficient tuple; the zero-challenge event is a field event
of the hidden indices' encoding; the batching randomness is the
expansion of the lines digest, so the batching step needs that digest's
freshness relative to the commitment. These remain open.

## Composed forgery bound skeleton

Proofs/ForgeryReduction: the forgery advantage against the candidate
scheme, less the fresh-hash guessing term, squared, is at most the
squared action budget times the random-index named events, the
extraction probability, the charged-event bound (at the enlarged budget
fuel + 1) and the guessing term.

Human review items: the bound uses the honest signer (no simulator
yet), so it is not yet a reduction to a witness-free solver; the
extraction event is the term that must become the RSD solver's success;
the named events are explicit terms to be bounded or carried per
decision 5.

## Extraction split (batching and solution events)

Proofs/ExtractionSplit: on extraction, the extracted witness is a
solution of the public instance (zero mux syndrome residual and unitary
selectors) or the batching event occurred; the batching event is the
exact cancellation of the batched residual and the batched unitary
checks at the batching challenges expanded from the lines digest.

Human review items: the solution predicate is the literal mux syndrome
residual of the repository, not an assumed encoding of the intended
syndrome decoding witness; the batching event's bound needs the lines
digest to be a fresh hash answer determined after the extracted witness
is fixed, which is the next random-oracle step.

## Solver and simulated statement

Proofs/SimulatedSolver: the solver's success on a scheme's fork
experiment, and the forgery bound against the candidate scheme in terms
of that scheme's events, the solver's success and a uniform per-event
simulation gap (a hypothesis of the statement, not an assumption file
entry).

Human review items: the scheme parameter is arbitrary; witness-freeness
of the intended simulator is not yet expressed or proved, and the gap
is the signing-simulation step (honest-verifier zero knowledge of the
PIOP with random-oracle programming) still to be formalized; the
solver's output is the literal extracted witness, whose solution
property is the mux syndrome residual of the repository.

## Named witness-free simulator

Spec/CandidateSimulator: the simulator's signing is a candidate
algorithm (decision-style naming), not a correctness or simulation
claim. It uses the honest commitment program with a uniformly random
fake witness, samples the digest first, and programs the hash table at
the input whose coefficient tuple it recomputes as the candidate
verifier would.

Human review items: the simulator reads the public half of the signing
key only (proved by reflexivity); the recomputed tuple uses the
committed seed array, which must be shown to agree with the candidate
verifier's recomputation (completeness of the simulated transcript);
the programming failure returns a bodiless signature and must be
charged as a salt-guessing event; the honest signer's behaviour at an
already-present input (reusing the stored answer) differs and must be
covered by the gap.

## Simulated transcript completeness

Proofs/SimulatedCompleteness: the recomputed verification input of an
executed commitment opened at the hidden indices is the committed lines
digest with the simulator's coefficient tuple, under the same
verifier/signer agreement hypotheses as the executed completeness
(layout, variant, encoding, candidate middle with the signer's encode,
verifier lines tail).

Human review items: the statement is on the signer's world at the end of
the commitment (the hash table and cipher history then); in the game
the verification runs on a later world, so monotonicity of the
evaluation under table growth is the next link; the hidden indices are
the verifier's expansion of the digest and counter, which the simulator
must match through its expansion parameter.

## Provenance of simulated signatures

Proofs/SimulatedSign: the simulated signing's outputs are executed
commitments with a fake witness and a chosen digest, with the programmed
entry at the recomputed input when a body is returned.

Human review items: the failure branch (input already present) returns
a bodiless signature and leaves the table unchanged, where the honest
signer would reuse the stored answer; this difference is part of the
gap and must be charged by a salt-guessing bound.

## Pending decision: challenge and batching expansions

The zero-challenge, Schwartz–Zippel, non-separation and batching terms
of the composed bound depend on the verifier's challenge expansion and
the signer's batching expansion, which the model takes as deterministic
parameters. An adversary with an unbounded counter can search them
freely, so these terms cannot be bounded in this model. Options: model
the expansions as random oracles with query accounting (the source's
XOF), or add a verifier-side counter bound as a named candidate check.
This is a human decision; until taken the terms stay explicit.

The PRG of the random table is now carried as the named predicate
`PRGHypothesis.PRGUniform` (a uniform seed's PRG vector is uniform), an
explicit theorem hypothesis of the hidden-share step; whether to adopt
it as a modelling assumption or to model the PRG as a random oracle is
the pending decision above.

## Pending decision: the PRG of the random table

The hidden party's random vector is the PRG of its seed (the signer
setting's `p.prg`), a deterministic parameter rather than an oracle. The
hidden-share independence step of the simulation gap needs the bits of
an unqueried uniform seed to be uniform and independent; with a
deterministic PRG parameter this is a cryptographic assumption (PRG
security, or a random-oracle model for the PRG), to be carried as an
explicit theorem hypothesis. The deterministic translation structure of
the transcript in the hidden random vector can be proved without it.

## Named event: the last row query stored (row-stored event)

The signing procedures' coupling (continuations 131–159) charges the
last execution's row query being stored at the head's initial result as
the named Boolean event `CommitLinesEvents.rowStored`. It is not a
source reading: a prior hash query equal to the last execution's row
string (its 2^kappa leaf commitments, which are ideal-cipher outputs of
the leaf seeds) would let the outer input's freshness argument fail, so
the event is carried explicitly in `commit_linesDigest_le_events` and
awaits its own bound (leaf commitment uniformity under fresh keys), or a
human decision to treat it as an explicit term of the composed bound.

## Named hypothesis: payload consistency of the honest signer

The comparison of the honest and simulated signing (continuations
161–163) uses the explicit hypothesis `SimulatedWith.PayloadConsistent`:
for a solution witness, the honest signer's hashed coefficient tuple of
an executed commitment equals the simulator's recomputed tuple at every
hidden vector with nonzero encoding. It is a PIOP completeness fact (the
prover polynomial's constant term vanishes for a solution, and the
verifier's recomputed value is the prover polynomial's evaluation at the
inverse challenge, so the restored tuple is the hashed one), recorded as
a hypothesis for a later proof rather than assumed silently. It is now
proved (`PayloadConsistent.payload_consistent`, continuations 189–191)
under the candidate encoding (the signer's encoding is the psi map of
the Gray challenge row) and at least one higher coefficient.

## Named terms of the simulation gap (continuations 160–171)

The simulation-gap hypothesis of the composed forgery bound is now
discharged (`SimulationGap.hgap_of_uniform`) from three explicit uniform
terms, each an explicit theorem hypothesis rather than a silent
assumption: a bound on the input-present event (the honest preparation's
PIOP hash input already in the table), a bound on the retry-failure
event (no returned observation of the candidate retry at the digest),
and a bound on the witness-swap term (the fixed-witness simulated
signing at the honest witness against a fake witness, under any
continuation); together with the payload-consistency hypothesis and a
witness sampler yielding solutions. Their bounds are the remaining proof
tasks or human decisions.

## Mention event relative to the starting log (continuation 181)

The input-present bound (`InputPresentBound.inputPresent_le`) charges the
prefix's cumulative mention event on the signing's trace. The prefix
trap bound (`PrefixMentionBound.prefix_mention_bound`) bounds that
event by the starting trace's event indicator plus the per-query mention
steps, so it is not uniform over worlds whose trace already carries a
mention event. The stored-mention lemmas of the chain locate the
mentioning entry among the signing's own fresh entries, so the event
can be restated relative to the starting log (the mentions raised by the
new entries only), whose trap bound has no indicator term. This
restatement is the planned next step; until then the mention term is an
explicit term of the input-present bound.

## Remaining terms of the simulation gap and what each needs (continuation 192)

With payload consistency proved, the simulation gap
(`SimulationGapTrace.hgap_of_uniform_trace`, used by
`ForgeryBoundTrace.forgery_le_trace`) carries three explicit terms:

- The row-stored bound: the probability that the last execution's row
  query is already in the shared hash table at the head's initial
  result. A bound needs the leaf commitments' distribution: each is the
  cipher output of the leaf seed under the layout's key, uniform when the
  key is fresh in the cipher history (the fresh-parent-key chain from the
  per-signature root), so the row string is unpredictable and a union
  bound over the supported table applies, with the row collisions among
  executions as a further small term. No human decision is needed; this
  is proof work.
- The retry-failure bound: the probability that the candidate retry
  observation does not return at a uniform digest, i.e. no counter within
  the fuel passes the grinding check with a nonzero encoding. This is a
  property of the evaluation expansion, a deterministic parameter; a
  bound needs the pending decision on the challenge expansion's model
  (random oracle with query accounting, or an explicit counter bound).
- The witness-swap bound: the fixed-witness simulated signing at the
  honest witness against a fake witness, under any continuation. This is
  the run-level form of the data-level hidden-share step
  (continuations 102–130): the commitment run's output distribution is
  witness-independent given the hidden leaf's uniformity, which follows
  from the fresh-parent-key event and the PRG hypothesis (`PRGUniform`,
  a pending decision). The lines digest part is done up to the mention
  and row-stored events.

## Finding: per-world cipher-dependent bounds are unsatisfiable; resampled-family restatement (continuation 193)

The composed bound's row-stored and witness-swap hypotheses quantify
over every world satisfying the counted invariant, including every
cipher family (the shared world fixes the family, sampled uniformly at
key generation). At a fixed family no nontrivial row-stored bound holds:
choose a family whose permutations ignore the key except at the leaf
keys, and at each leaf key send that leaf's commitment inputs to fixed
blocks; the last execution's commitment row is then the same string for
every salt and root, so an adversary who queried it has the row-stored
event with probability one. The same applies to the witness-swap term.
These hypotheses are therefore satisfiable only with the trivial value
one, and the bounds as instantiated would be vacuous.

The correction (the simplest option): the honest and simulated signing
oracles are compared with the family resampled from the posterior of the
cipher history before each signing query (`CipherResample.resample`),
which is distributionally equal to the fixed-family game by the
lazy-resampling law (`CipherResample.runFixed_resample`,
`runProgram_resample`; the game-level equality is the next target). The
row-stored, retry-failure and witness-swap hypotheses are then restated
over the resampled world, where fresh leaf keys give uniform
commitments.

Resolution (continuation 201): the game-level equality route was
abandoned, since the fork experiments of a resampling scheme are not
equal in law to the shared-family fork and the reduction chain is
specific to the real scheme. Instead the hybrids charge the per-call
term at the world of each signing query (`ChargeRun`, `ChargeCut`), and
the expected charges from the resampled key are bounded through the
oracles' resampling laws (`ChargeExpect`, `ChargeCutExpect`,
`SharedResample`, `CandidateResample`). The simulation gap in mean form
(`SimulationGapMean.hgap_of_mean`) takes the row-stored term and the
witness-swap slack as means over the resampled world. The earlier
statement `SimulationGapTrace.hgap_of_uniform_trace` remains valid but
its per-world cipher-dependent hypotheses are known to be unsatisfiable
below one.

## Finding: the witness-swap term needs the continuation's family resampled (continuation 218)

The composed bound `SimulationGapCipher.forgery_le_cipher` carries the
witness-swap hypotheses in the charged form: a per-world slack σ with
the honest and fake fixed-witness signings within σ(world) under every
continuation, and the mean of σ over the resampled family at most εS.
This form is unsatisfiable below one: at a fixed family the two
signings are deterministic given the salt, root and digest, and a
continuation that knows the family distinguishes their outputs, so σ
must be one at every world. The charged hybrid is adequate for the
row-stored and retry terms (events of the signing run alone) but not for
the swap, whose smallness is only over the family's randomness as seen
by a continuation that does not know it.

The correction: a mean-form hybrid in which the per-call swap bound is
stated for a fixed continuation with the family resampled before the
call, i.e. for every continuation h, the mean over the resampled world
of the honest signing bound to h is within εS of the mean of the fake
signing bound to h. Along a run the resampling is always from the
world's own history (the oracles' resampling laws), so this hybrid needs
no scheme change. In the fork, both branches share the family; by the
resampling law of the left branch, the right branch's family is
distributed as the posterior of the left branch's final history, so the
right branch is run from the snapshot's world with that history in place
of the snapshot's, which does not change the run (the history is a log)
and keeps the events when they do not read the cipher history. This is
the next target; the row-stored term's proof is unaffected. The
hypotheses `hswap`/`hswapMean` of the current composed statements are
therefore to be replaced, and the statements remain valid as stated.

## Finding: the mean-form swap bound over all continuations is also unsatisfiable; the swap needs oracle-access continuations and a forgetful signer (continuation 222)

The correction recorded at continuation 218 states the per-call
witness-swap bound for every continuation h of the signing's output,
with the family resampled before the call. This is still unsatisfiable
below one. The signing's commitment program expands the whole seed tree,
hidden leaf included, and records every cipher call in the world's
cipher history and the hidden leaf's commitment query in the inner hash
table; the output world handed to h carries the family, the history and
the table. A continuation that reads them recomputes the hidden leaf's
seed, its share, and from the opened shares and correction the witness,
and so tells the witness signing from the fake signing with certainty.
Resampling before or after the call does not help: the resampled family
is consistent with the recorded hidden path. The smallness of the swap
holds only against continuations that reach the world through the
oracles, which is what the game's run, cut and fork do, and against
events that do not read the hidden path's entries.

The corrected route (the simplest one found): (i) name the hidden path
of a signature, the cipher entries of its expansion and the inner-table
entry of its leaf commitment (`hiddenEntries`), and the pruned world
with them removed (`prune`); (ii) prove that under the posterior of the
pruned history the hidden seeds are uniform and independent of the
signature's data (the existing `posterior_node_uniform` and the PRG
hypothesis), so a continuation's cipher and inner-hash queries hit the
hidden path with probability at most the query budget times the fiber
bound over the number of seeds; (iii) prove the run, cut and fork from a
world and from its pruned world agree in law until a query hits the
hidden path (the posterior factorises over keys, so answers at other
keys have the same law), with the end-resampled family; (iv) in the
pruned world the witness and the fake signings have the same law
(`hidden_share_step`, `HonestViewUniform`); (v) the events must be
insensitive to the hidden entries, an explicit hypothesis to be checked
for each named event and for the solver's success. The per-call
hypotheses `hswap`/`hswapMean` of the composed statements are therefore
to be replaced by an identical-until-bad bound over the game's
continuation, not by a per-call mean bound. The composed statements
remain valid as stated; the mean-form hybrid, the run with its final
world and the oracle laws are the tools of step (iii).

## Finding: the pruned equality cannot hold exactly; the swap needs a pruned closeness with a hit term (continuation 293)

The named hypothesis `PrunedEqual` (continuation 285) asks, for every
world satisfying the counted invariant and every functional Ψ of the
signature and the pruned, end-resampled world, that the pruned mean of Ψ
be the same for the honest witness and a fake witness. This cannot hold
in general. The pre-call cipher history may already record an entry at a
key of the hidden path (the key of the hidden leaf's parent, say); on the
event that the per-signature root leads the tree through that key, the
hidden seed equals the recorded output, the hidden share is its PRG
expansion, and the correction in the signature then determines the
witness from the revealed shares. A functional Ψ that knows the recorded
entry (Ψ is quantified after the world) and tests the recovered value
against the honest witness has a strictly larger pruned mean for the
honest witness than for the fake one: on the hit event it is one for the
honest witness and zero for the fake one, and off the hit event the two
means agree. Pruning removes the hidden path's entries from the world Ψ
sees but not from the data the signature was computed with. The data-level
hiding results (`posterior_node_uniform`, `hidden_share_step`) indeed
require the parent key to be fresh.

The corrected named target is `SwapClose.PrunedClose S publicKey B ε`:
for every functional bounded by one, the pruned mean with the honest
witness is at most the pruned mean with a fake witness plus ε. The
expected value of ε is the probability that a key of the hidden path is
already in the pre-call history, a term of the same shape as the leaf
bounds `LeafR`/`LeafC` (the budget times the key fiber bound over the
number of seeds), plus the PRG hypothesis `PRGUniform` for the exact
agreement off the hit event. `prunedClose_of_equal` records that the
equality is the closeness with no slack. The swap's core, the two per-call
bounds, the per-event gap and the composed forgery bound are restated
under the closeness (`swap_core_close`, `signRunW_meanP_close`,
`signCutW_meanP_close`, `hgap_meanP_close`, `hgap_final_close`,
`forgery_le_final_close`), the slack entering the per-call constant beside
the two touching terms (`εSimP'`). The hypothesis list of the final
statement is otherwise unchanged; `forgery_le_final'` remains valid as
stated, but its `PrunedEqual` hypothesis is not satisfiable in the model
and `forgery_le_final_close` is the statement to use.

Continuation 294 splits the slack into two named targets
(`SwapCloseSplit`): the hit term `HitPre S publicKey B ε`, the
probability over the resampled world and the signing call that the
pre-call world records an entry at a key of the signature's hidden path
(`hitPre`, through `touchesG` at `outKeys`), and the off-hit pruned
equality `PrunedEqualOff S publicKey B`, the exact agreement of the two
signings' pruned means restricted to the calls without a hit
(`prunedMeanOff`). `prunedClose_of_split` derives the closeness with the
hit term as slack. The off-hit equality is the ideal-model zero-knowledge
content proper; the hit term is of the leaf bounds' shape.

Continuation 295 corrects the closeness's quantification. Stated at a
fixed salt, root and digest, the closeness is again unsatisfiable with a
small slack: for a root whose key is already recorded in the pre-call
history the hit is certain. `PrunedClose` is therefore stated over the
uniform salt, root and digest, which is the form the swap's core uses
after averaging (`swap_core_close` averages the forward agreement, the
closeness and the reverse agreement over the three draws). The split is
stated for any bad event of the call (`BadTerm bad B ε`, the probability
of the bad event over the three draws, the resampled world and the call;
`PrunedEqualOff bad B`, the exact off-bad agreement at fixed draws),
`hitPre` being the candidate bad event; a bad event may be enlarged (for
instance to the distinctness failure of the tree's keys) without changing
`prunedClose_of_split`.

Continuation 296 proves the bad term for the pre-call hit
(`HitTerm.badTerm_hitPre`): a key of the hidden path is the key of a tree
node below twice the leaf count, so a hit is a distinctness failure of
the tree's keys, whose probability under the joint draw of the root and
the posterior family is the first part of the uniform touching bound
(`εHit c cKey (commitBudget·B)`, with `εHit_le_εTouch`). What remains for
the closeness is the off-hit pruned equality `PrunedEqualOff (hitPre S)`
or, if a larger bad event is needed for it, that event's term.

## Finding: the off-hit equality is not exact either; the off-hit target is a closeness (continuation 297)

Even off the pre-call hit and with the tree's keys fresh and distinct,
the two signings' pruned means are not exactly equal. The hidden leaf's
seed is the layout's output of a cipher block drawn, under a fresh
parent key, as a uniform block distinct from its sibling's block (the
family is a family of permutations); the sibling's seed is revealed in
the signature. So, given the pruned view, the hidden seed is uniform on
the outputs of the blocks other than the sibling's, not on all seeds,
and the published witness-dependent data (the correction and the lines)
has, for the honest and the fake witness, laws that differ by the
sibling's exclusion, of the order of one over the number of blocks per
execution; the layout's output fibers add a further discrepancy unless
the output map is a bijection. The data-level uniformity
(`hidden_share_step`) is exact only for a uniform seed under the PRG
hypothesis. `PrunedEqualOff` is therefore replaced by the off-bad
closeness `SwapCloseSplit.PrunedCloseOff bad B ε₂`, and
`prunedClose_of_split'` gives the pruned closeness with the two slacks
added; `prunedCloseOff_of_equalOff` records the equality as the
closeness with no slack. The route for the off-bad closeness is the
exchange of the hidden leaf's value (the existing exchange machinery
covers internal nodes only: `TreeExchange`, `CommitRunExchange`,
`OwnViewExchange`), under which the pruned view is unchanged and the
published data moves by the hidden share's PRG expansion, followed by
the data-level step with its slack stated as an explicit hypothesis of
data-level form (the PRG hypothesis and the sibling and fiber terms).

Continuation 298 starts the leaf exchange with its generic tool
(`ProgramRelabel`): a program whose requests' keys lie in a set, run
against a family agreeing through a key relabelling on that set, gives
the relabelled result of its run (`runFixed_mapKeys`), and a relabelling
permuting a key list and fixing the other keys leaves the history pruned
at the list unchanged (`pruneAt_map`). The commitment phase under the
exchange of a leaf's value is the phase with the leaf's own key moved to
the new value's key, which these two facts compare.

Continuation 299 proves the commitment phase's leaf exchange
(`CommitPhaseLeaf`): the phase (the leaf commitments in the source's pair
order, the rest being the phase followed by the tail) at the tree with
the leaf set is the phase at the tree with the leaf's old and new keys
swapped, the exchanged family agrees with the family through that swap at
the leaves' keys, and so the run of the exchanged phase is the relabelled
run of the phase (`commitPhase_run_exchanged`). Remaining for the view:
the tail at the exchanged seeds and the pruned histories.

Continuation 300 proves the commitment run's leaf exchange
(`CommitRunLeaf.commitRun_leaf_exchanged`): under the exchanged family at
a leaf, the run is the phase's run under the family, relabelled, with
the exchanged expansion's history appended, continued by the tail at the
tree with the leaf set; and pruned at any list containing the three
exchanged keys, the history before the tail is the same as under the
family (`leaf_history_pruned`). The hidden seed thus enters the view only
through the tail's data, which is where the PRG share and the witness
enter.

Continuation 301 proves the phase view's leaf exchange
(`PhaseViewLeaf.phaseView_exchanged`): the phase view (the commitments,
the hash state and the cipher history pruned at a key list, after the
expansion and the leaf commitments) pruned at the exchanged family's own
hidden keys equals the family's view pruned at its own hidden keys, for a
path node including the leaf. This is the leaf counterpart of the
own-view exchange used by the touching bound, and the input of the
posterior bound for the leaf.

Continuation 302 proves the posterior bound for the phase view at a leaf
(`HonestLeafBound.honest_leaf_bound`): for a bounded function of the phase
view pruned at the family's own hidden keys, the weighted mass of the
families whose hidden leaf's block is a given value, on the good fiber of
a given parent seed, is at most the total weight over the number of
blocks less the bad targets. This is the one-sided uniformity of the
hidden leaf's block given the phase view; summed over the blocks it
yields the closeness of the leaf's conditional law to uniform, which is
the slack of the off-hit closeness.

Continuation 303 generalises the leaf's view exchange and posterior bound
(`PhaseViewLeafAll`): the phase view pruned at any family-dependent key
list with the expected members is unchanged under the exchange
(`phaseView_exchanged_of_mem`), in particular at the hidden keys of all
executions (`phaseView_exchanged_all`, `phaseViewAll_mean_exchanged`);
and the posterior bound at the leaf holds for any bounded weight
invariant under the exchange on the good fiber (`honest_leaf_bound_gen`),
which admits weights that also fix the other executions' hidden blocks,
the form needed for the joint uniformity of all hidden leaves.

Continuation 304 proves the exchange's effect on the tree's distinctness
and on the other leaves (`LeafExchangeDistinct`): with fresh and distinct
tree keys and a target block that is not bad, the exchanged tree's keys
are fresh and distinct, and every other leaf keeps its parent seed and
its block (the sibling's block is moved by neither block of the
transposition). These make the weight that fixes the other executions'
hidden blocks invariant under the exchange, as the joint uniformity
needs.

Continuation 305 proves the joint one-sided uniformity of the hidden
leaves' blocks (`LeafJointBound.jointWeight_bound`): for a bounded
function of the families invariant under the exchange at any hidden
leaf on the distinct trees, the mass of the families on which a set of
executions' hidden leaves have given parent seeds and blocks, on the
distinct trees, is at most the total mass over the number of blocks less
the bad targets, raised to the set's size. The induction fixes one leaf
at a time through the posterior bound, the weight with the other leaves
fixed being invariant by continuation 304's lemmas; a fiber with a
non-fresh or coinciding key is empty on the distinct trees.

Continuation 306 sums the parent seeds out of the joint bound
(`LeafBlockBound.blockWeight_bound`): the mass of the families on which a
set of executions' hidden leaves have given blocks, on the distinct
trees, is at most the total mass over the number of blocks less the bad
targets, raised to the set's size. Each step fixes one block by summing
the posterior bound over the leaf's parent seed, the weight with the
parent fixed being invariant since the exchange keeps the parent. This is
the form the uniform-mixture comparison of the two signings uses: the
hidden blocks' joint conditional law is one-sidedly close to uniform.

Continuation 307 proves the uniform-mixture comparison
(`LeafMixture.mixture_upper`, `mixture_lower`): for a family of bounded
functions of the families indexed by the hidden blocks' tuple, each
invariant under the exchanges, the mass at the family's own hidden blocks
times the number of blocks less the bad targets to the number of
executions is at most the sum of the masses over the tuples, and that sum
plus the distinct mass times the power is at most the distinct mass
times the number of tuples plus the mass at the own blocks times the
power. These two inequalities compare the honest and the fake signings
through their uniform mixtures over the hidden blocks, which is where the
data-level closeness hypothesis enters.

Continuation 308 proves the commitment tail's run facts (`TailRun`): a
hash-only program's run keeps the cipher history and does not depend on
the family, the continuation from a finished first run is the run at its
value, and the tail is hash-only. So the signing's data after the phase
is a function of the phase view, the tree's seeds and the hash oracle's
answers, with the cipher history untouched.

Continuation 309 proves the signing-data identity
(`SigningData.inner_eq_sum`): the inner mean of the off-hit pruned mean
at a family is the sum, over the hidden tuples, of the tuple's hit factor
times the mean, over the phase view pruned at the tuple's keys, of the
tuple's data at the expansion's tree, where the tuple's data runs the
tail from the commitments and the seeds, the post-processing, the tuple's
indicator and the functional over the world resampled from the pruned
history. The tail is hash-only, so the family and the cipher history
enter only through the pruned history, and the hidden leaves enter only
through the seeds handed to the tail.

Continuation 310 proves the sliced data's invariance under the leaf
exchange (`SlicedInvariance.sliced_exchanged`): with the tuple's leaves
replaced by given blocks, the sliced data at a family is unchanged by the
exchange at one of the tuple's leaves on the distinct trees with a target
that is not bad, and at the family's own blocks the replaced tree is the
expansion's tree (`sliced_blocks`). The sliced data therefore has the
form the uniform-mixture comparison takes, with the hidden blocks as the
mixing tuple.

Continuation 311 prepares the off-hit closeness: the mixture lower bound
relative to a bound function (`LeafMixtureGen.mixture_lower_gen`), so
that with the tuple probability as the bound the comparison's slack stays
independent of the number of tuples; and the setup
(`OffHitSetup`): the off-hit pruned mean is the posterior mean of the
inner mean, the sliced data and the inner mean are at most one, the
tuple probabilities sum to at most one and, at the expansion's tree, to
the no-hit mass whose complement is the hit mass, and the distinct-tree
failure and the hit mass over the uniform draws are at most the hit
bound.

Continuation 312 proves the two sides of the off-hit chain at fixed
draws (`OffHitChain`): the honest upper bound, the distinct mass of the
honest inner mean scaled by the number of blocks less the bad targets to
the number of executions is at most the sum over the tuples and the
block tuples of the mixing family's masses (`honest_upper`); and the
fake lower bound relative to the tuple probability, summed over the
tuples (`fake_lower`). The mixing family is the sliced data with the
tuple's leaves replaced, invariant under the exchange by continuation
310. What remains for the off-hit closeness is the data-level closeness
hypothesis on the mixing families and the arithmetic assembly.

## Finding: the tuple sum's slack, and the digest determining the hidden tuple (continuation 313)

The off-hit chain slices the signing's data by the hidden tuple (the
pruning keys depend on it). The fake side's lower bound through the
mixture, summed over the tuples, multiplies its slack by the number of
tuples (continuation 312's relative form does not help, since the tuple
probabilities at a tuple-replaced tree do not sum to one over the
tuples). The resolution is that the candidate attempt decides between
retry and ready from the challenge expanded from the digest and the
counter alone (the grinding test and the nonzero merged challenge); the
key enters only the opening. So the returned counter is the digest's
first passing counter, and a simulated signature's hidden tuple is the
digest's tuple when the body is present and the default tuple otherwise
(`TupleOfDigest.sigHidden_simPost`). At most two tuples carry mass, and
the tuple sum's slack is at most doubled.

Continuation 314 assembles the off-hit chain at fixed draws
(`OffHitAssembly`): the sliced data vanishes outside the digest's tuple
and the default tuple, the data-level closeness is stated as a named
hypothesis (`DataClose`: on the distinct trees, the honest mixing
family's sum over the tuples and the block tuples is within the number
of block tuples times the slack of the fake one), the honest side with
the closeness (`honest_side`) and the fake side over the two tuples
(`fake_side`). What remains is the arithmetic: cancelling the distinct
mass, dividing by the scaling, bounding the scaling uniformly through
the counted invariant, adding the distinct-tree term and averaging over
the draws.

## The data-level closeness discharges the pruned closeness (continuation 315)

`OffHitClose.prunedCloseOff_of_dataClose` proves the off-hit closeness
for the pre-call hit with the slack `εOff c cKey B δ`: the hit bound plus
twice the mixture's loss and the data-level closeness over the uniform
scaling to the number of executions, the scaling being the number of
blocks less the bad targets at the counted invariant's budget.
`prunedClose_of_dataClose` then gives the pruned closeness with the slack
`εHit + εOff`, and `ForgeryData.forgery_le_final_data` is the composed
forgery bound with the named data-level closeness in place of the pruned
closeness. The data-level closeness (`OffHitAssembly.DataClose S publicKey
B δ`) says: for every honest and fake witness, message and world under
the counted invariant, every salt, root and digest, every functional
bounded by one and every family with fresh and distinct tree keys, the
sum over the hidden tuples and the block tuples of the honest signing's
sliced data with the tuple's leaves replaced by the blocks is within the
number of block tuples times δ of the fake signing's. This is the
ideal-model zero knowledge at uniform hidden blocks: with the hidden
leaves' blocks uniform, the commitment data, the tail's hash chain and
the post-processing have the same law for the honest and the fake
witness, up to the PRG hypothesis and the output map's fibers. It is a
statement about the signing program's data alone, with no run-level
content left.

The final statement's named hypotheses are now: the data-level closeness
(`DataClose`), the leaf-term bounds (`LeafR`, `LeafC`), the retry bound,
the seed-collision bound, the layout's injectivity and fiber bounds with
the size conditions, and the structural hypotheses.

## The leaf hiding discharges the leaf-term bounds (continuation 316)

The leaf hit of the touching total at an execution's hidden leaf is the
sliced data of the functional recording the leaf's key, at the
expansion's tree (`LeafTermBound.leafHit_eq_slicedView`); with the
tuple's leaves replaced by a block tuple it is the mixing family of that
functional, invariant under the exchange. The named data-level
hypothesis `LeafHide S publicKey B δ` says: for every witness, message
and world under the counted invariant, every salt, root and digest,
every continuation, tuple, execution and family with fresh and distinct
tree keys, the sum over the block tuples of the continuation's
probability of recording the key of the replaced block at the execution
is at most the number of block tuples times δ. This is the hiding of a
hidden leaf's seed by the signing's data at uniform hidden blocks: the
continuation, given the data, records the leaf's key with probability
δ on average over the leaf's block. Its justification is the PRG
hypothesis on the hidden share together with the freshness of the
leaf's key in the resampled world (each cipher query tests one key).
`leafTerm_le` bounds the leaf term by `εLeafOf c B δ` (twice the number of
executions times the blocks' power over the scaling's power times δ),
`leafR_of_leafHide` and `leafC_of_leafHide` give the leaf-term bounds, and
`ForgeryHide.forgery_le_final_hide` is the composed forgery bound with the
leaf hiding in place of the leaf-term bounds.

The final statement's named hypotheses are now: the data-level closeness
(`DataClose`), the leaf hiding (`LeafHide`), the retry bound, the
seed-collision bound, the layout's injectivity and fiber bounds with the
size conditions, and the structural hypotheses.

## The candidate encoding and the distributional bound (continuation 336)

`CandidateSerialization.candidateSerialization` is a named reading of the
undefined wire encodings: one bit per coordinate in index order for
vectors, and the base matrix flattened row, execution, bit. Its two
injectivity facts (`sourceTail_injective`, `lines_injective`) discharge
the encoding hypotheses of the composed bound, which is restated at the
full layout as `forgery_le_final_full_enc`.

`DistributionalFinal.averaged_forgery_le_final` is the composed bound
with the setting, encoded public key and witness sampler drawn from a
probability mass function on a finite index type: the forger's averaged
advantage, minus the digest term, squared, is at most the budget squared
times the explicit terms with the hardness term `εSD`, under
`DistributionHard` (the witness-free solver's averaged syndrome-decoding
success is at most `εSD` of the budget) and the per-instance structural
hypotheses. `forgery_le_final_meanSquare` is the mean-square form over
any distribution.

Human review items: the candidate encoding is a reading, and its
agreement with the implementation's byte packing (field order, padding)
is unverified; the instance distribution is a parameter, since Algorithm
2's literal routine returns no key (`B`, `x_A` undefined) and so its law
cannot be formed without a decision; with a distribution fixed,
`DistributionHard` is the natural place for a hardness assumption over
instances, while `SDitH.Assumptions.SDHardness` (planted uniform matrices)
remains unconsumed. On the named simulator constants: discharging them
needs the challenge expansion modelled as a counted oracle of the digest
and counter; with the deterministic expansion parameter the forger tries
every counter for free, so no in-model bound is small. This is a
decision about the model (a refactor of the settings), recorded in
PLAN.md.

## The final statement at the full layout (continuation 335)

`FullLayoutFinal.forgery_le_final_full` is the composed forgery bound
with both cipher layouts equal to the submitted full layout
(`fullLayout lambda = ⟨id, id, id⟩`, Categories I and V): the seven
layout hypotheses (the signer's input injectivity and the fiber bounds of
its key-of-output, key and output maps; the verifier's input and key
injectivity and output fiber bound) are discharged and the fiber
constants are one, so the size conditions read
`commitBudget·(3(fuel+1)+2) + 1 + 2·τ·2^κ + 1 < 2^λ` and
`commitBudget·(3(fuel+1)+2) + 2·τ·2^κ < 2^λ`.

Human review items: the settings fix the cipher's key and block width to
the security parameter (`Layout lambda (Bits lambda) (Bits lambda)`), so
the submitted Category-III layout (`truncatedLayout : Layout 192 (Bits 256)
(Bits 256)`, 192-bit seeds in 256-bit blocks) is outside the type of the
reduction's settings: the reduction as stated covers the full-layout
categories (I and V); extending the settings to a separate block width is
a scope item, not a decision. The generic statement is kept for layouts of
the setting's type other than the identity.

## The simulator's seed-collision term is discharged (continuation 334)

`SeedTermDischarge.forgery_le_final_hard_C` is the composed forgery bound
with the simulated seed-collision term removed: the seed-collision event
is a cipher event (two recorded seeds with colliding commitments), so its
bound in the real experiment through the ideal cipher's pair mass
(`SeedCollisionBound.seedCollision_le`, continuation 320) is used
directly in the per-event split, and no simulated copy of the event is
needed. The earlier final statements carried the simulated copy as a
leftover slack of the generic event transfer. The named simulator
constants are now five, in `SimulatorTermBounds5`: mask-after-fork,
non-separation, zero-challenge, Schwartz–Zippel and batching.

Human review items: of the five, mask-after-fork is the hypothesis term
of decision 1 (a branch's mask input first queried after the fork), and
the other four depend on the challenge and batching expansions' model.
None is a cipher event, so no further term of the statement is
dischargeable by the ideal-cipher arguments alone.

## The hardness assumption on the instance (continuation 333)

`InstanceHardness.forgery_le_final_hard` is the composed forgery bound
with the solver's syndrome-decoding success replaced by `εSD fuel`, under
`InstanceHard S V verifyBudget publicKey sampleWitness εSD`: for every
adversary (any state type at the fixed universe), budget and `0 < tau`,
the witness-free solver built from that adversary returns a weight-`w`
solution of `instanceOf S.H' S.y` with probability at most `εSD fuel`.

Human review items: this is a hardness assumption on the fixed public
instance of the signing setting, in the style of a non-uniform assumption
on one instance, and it is quantified over solvers of the specific shape
produced by the reduction (the simulated fork experiment of an adversary),
not over arbitrary algorithms; a standard assumption would be stated over
a distribution of instances (`SDitH.Assumptions.SDHardness` is such a
statement, over the planted distribution) and over all algorithms within a
runtime bound. Neither gap is closable in the current model: the key
generation's instance is seed-expanded and systematic, not planted, and no
runtime model exists. The assumption is therefore the simplest named form
that makes the final statement explicit, and its adequacy is a review
decision.

## Review pass (continuation 332)

Checked for human review: the final statement
`NamedSimulatorTerms.forgery_le_final_named` has exactly the named
hypotheses listed in the continuation-331 section; `SDitH/Assumptions.lean`
declares no axiom and its `SDHardness` predicate is not consumed by any
theorem, because the hardness term `rsdSuccess` is stated on the fixed
public instance of the signing setting (the key generation's
seed-expanded systematic instance), not on the planted distribution
`plantedSD`; relating the two is the open correspondence obligation of
the "Sampler and keygen" row of the plan's review table. The remaining
proof obligations are the named hypotheses (`DataClose`, `LeafHide`,
`hretry`, `SimulatorTermBounds`), each of which would need an
idealization the user chose not to adopt (the PRG, the challenge and
batching expansions).

## The expansion-dependent simulator terms are named assumptions (continuation 331)

`NamedSimulatorTerms.forgery_le_final_named` is the composed forgery
bound with the witness-free simulator's six event probabilities
(mask-after-fork, non-separation, seed-collision, zero-challenge,
Schwartz–Zippel, batching) replaced by the named constants
`εMask εSep εSeed εZero εSZ εBatch`, under the hypothesis
`SimulatorTermBounds` that each event's probability in the simulated
experiment is at most its constant. These events depend on the
challenge and batching expansions' model (the deterministic expansion
of the hashed digest into challenges and batching coefficients), which
the formalization does not idealize, by the user's decision; they are
carried exactly like the retry bound (`hretry`).

Human review items: the hypothesis is a statement about the
witness-free simulator only (no secret witness is involved), so it is
the kind of bound an idealized expansion would give (a Schwartz–Zippel
or small-support count per attempt); a later idealization can discharge
it without touching the final statement's other hypotheses.

The final statement's named hypotheses are now: `DataClose`,
`LeafHide`, the retry bound, `SimulatorTermBounds`, the layout
conditions on the signer and the verifier, the size conditions and the
structural hypotheses. Its right-hand side is explicit: the named
constants, the proved slacks and the syndrome-decoding success
`rsdSuccess`.

## The hardness term is syndrome decoding on the public instance (continuation 330)

`ForgeryRSD.forgery_le_final_rsd` is the composed forgery bound with the
solver's success replaced by `rsdSuccess`: the probability that the
solver returns bits whose solution vector is a weight-`w` solution of
`Spec.KeyGeneration.instanceOf S.H' S.y` (the systematic instance
`[I | H']·x = y`, the key generation's own solution notion). The step is
`SolutionRegular.isSolution_sd`: a witness with zero mux syndrome
residual and unitary selectors selects one leaf per chunk
(`MuxSelect.muxTree_select`), and the vector with a one at each selected
leaf has syndrome `y` and weight `w`.

Human review items: the solution is regular (one nonzero entry per chunk
of `leafCount widths` columns), so the hardness term is regular syndrome
decoding of the public instance, matching the source's key generation;
the statement does not assert that this instance is hard, which stays
outside the formalization as the hardness assumption.

## The slope-game term is discharged (continuation 329)

`ForgerySlope.forgery_le_final_coll_S` is the composed forgery bound with
the slope term explicit: in place of the simulator's slope event (with
its simulation slack) the bound carries
`(fuel+1)·2·εTrap tau s bound + εWitOf lambda tau kappa fuel + unseenCost lambda tau kappa (commitBudget·(3·(fuel+1)+2))`,
under the verifier layout's identity `V.layout = fullLayout`. The chain
is: the good fork's case split with the stored-mask slope event; its
coverage by the mask trap, the witnessed pair and the unseen match; the
trap's bound through the hash answers over the cut run; the witnessed
pair's bound through the family-dependent fork bound and the pair-mass
chain; the unseen match's bound through the family-dependent fork bound
and the unobserved-key bound; and the regenerated skeleton.

The final statement's named hypotheses are now: the data-level closeness
(`DataClose`), the leaf hiding (`LeafHide`), the retry bound, the layout
conditions on the signer (injectivity and fiber bounds) and on the
verifier (identity layout, injective input and key maps, output fiber
bound), the size conditions and the structural hypotheses. Its remaining
simulator terms are the mask-after-fork, non-separation, zero-challenge,
Schwartz–Zippel and batching events (the expansion-dependent events,
explicit by the user's decision) and the solver's success.

## The composed bound's skeleton with the three events (continuation 328)

`SlopeChainReduction.forgery_le_simulated_events_S` is the per-event
simulation-gap statement with the slope event replaced by the mask trap,
the witnessed pair and the unseen match, which stay as real-experiment
terms (they read the snapshot's family, so they are not transferred to
the witness-free simulator; they are bounded directly instead, like the
seed collision). The skeleton follows the original one from the good
fork's case split with the three events (`good_implies_events_D`).

Human review items: the regenerated theorems are stated beside the
originals, which remain in place; the identity-layout hypothesis on the
verifier joins the layout conditions.

## The unseen match's bound in the real experiment (continuation 327)

`ForkUnseenBound.unseenFork_le`: the random event experiment of an unseen
seed matching a named seed's two recorded commitment halves (the seed
unqueried at both paired inputs in the union of the branches' histories)
is at most `unseenCost lambda tau kappa (commitBudget·(3·(fuel+1)+2))`.
Through the family-dependent fork bound the event is read at the family
resampled at the end of the restored second branch; the union of the
attempt histories is then the second branch's final history as a set,
so the event is the shared game's unseen event at that world, bounded by
the unobserved-key bound (`SharedSlopeBound.unseen_fixed_world_bound`)
at the history's length, itself at most the counted invariant's bound.

Human review items: the unseen predicate reads the claim from the
branches' bodies only, so it is invariant under the history shift and
the embedded families; the event's recorded halves are what the
coverage provides from the queried named seeds.

## The witnessed pair's bound in the real experiment (continuation 326)

`ForkWitnessedBound.witnessedFork_le`: the random event experiment of a
witnessed pair under the snapshot's family in the union of the two
branches' histories is at most `εWitOf lambda tau kappa fuel`, which is
`3·(fuel+1) · callCost 1 (commitBudget·(3·(fuel+1)+2)) commitBudget`. The
family-dependent fork bound reduces the event to the pair mass of the
restored second branch's final history (the union is within it, and the
witnessed pair is monotone), and the pair-mass chain bounds that by the
snapshot's mass plus two branches' costs; the cut run and the empty key
generation history give the total, with the identity projection (fiber
bound one) and the seed-pairing companion.

Human review items: the same cost shape as the seed-collision slack with
capacity one; both are coarse.

## The fork bound for family-dependent events (continuation 325)

`PairForkFamily.fork_family_bound`: for an event `E` that is off on a
refused fork, holds only with an attempt first branch, ignores the first
branch's embedded family, and at the snapshot with family `g` implies
`Φ left right g U` on the union `U` of the attempt histories (for a
predicate `Φ` invariant under the second branch's history shift, the
second branch's embedded family and set-equal histories), the plain
fork's probability of `E` is at most the mean, along the restored chain
(first branch, its final family resampled, the checked first branch,
the second branch from the restored world, and the family resampled at
its end), of `Φ` under that last family on the union. The plain fork's
second branch and the restored one are shifts of the same base branch by
the snapshot's and by the first branch's final history, and both unions
are the first branch's final history together with the base branch's
entries.

Human review items: the end resampling is the single-branch resampling
law (`right_end_resample`) at the restored snapshot; the predicate's set
invariance replaces the history-free hypothesis of the pair-mass bound.

## The mask trap's bound in the real experiment (continuation 324)

`SlopeTrapBound.slopeTrap_le`: the random event experiment of the mask
trap on the saved snapshot is at most `(fuel+1) · 2 · εTrap tau s bound`,
with `εTrap tau s b = tau² · b · 2^-s`. A hash answer's mask component is
uniform and independent of the table before it, and the trap vector (the
slope difference of the claim chained at the query's input, zero when
none) is a function of that table, so each answer is a trap with
probability at most `2^-s` per execution pair; a run of budget `b` from
a world without the trap raises it with probability at most
`tau² · b · 2^-s`, and the service-bound framework accumulates this over
the cut run.

Human review items: the bound is coarse (the per-run bound is applied at
the uniform budget and the prefix bound doubles the cost); the trap is
evaluated with the world's own family, which the runs keep.

## The fork-level coverage of the slope event (continuation 323)

`SlopeCoverFork.covered`: on a snapshot whose world is well formed (trace
traced, ordered and fresh), without the digest-mention and
digest-collision prefix events on its trace, and with both branches'
histories matching the snapshot's family, the stored-mask slope event
forces one of three events. If no other seed shares a named seed's
commitment, the claim's chain is present before the mask's query (the
mention event excluded) and the mask's answer kills the nonzero slope
difference at the chain's vector, a trap on the snapshot's trace
(`slopeTrap`). Otherwise the colliding seed is either queried (a
witnessed pair in the union, `witnessedFork`) or unqueried at both halves
(an unseen match, `unseenFork`). `good_implies_events_D` replaces the
slope event by these three in the good fork's case split, using the
snapshot's well-formedness and the branches' consistency
(`fork_consistent`).

Human review items: the mention and collision events are those of the
snapshot's world, already charged by the fork's bad event; the three new
events read the snapshot's family and are to be bounded in the real
experiment (the trap through the hash answers, the other two through the
family resampled at the end of the restored fork).

## The stored-mask slope event from the good fork (continuation 322)

`SlopeChainFork.good_implies_events_C` replaces the existential-mask slope
event in the good fork's case split. The claim is built from the first
branch's data: salt, the completed seed vector (its own revealed seeds and
the second branch's revealed seed at its hidden index), the recomputed
row hashes (the table's digests of the row queries), the root and the
auxiliary digest from the first branch's reconstruction on the snapshot's
table, and the auxiliary data. Its rows are the first branch's commitment
array (the hidden index's commitment is the second branch's by the equal
commitment arrays), so the chain is in the snapshot's table; every seed's
two expansion entries are in the union of the branches' histories by the
two reconstructions; the stored mask and the slope conditions come from
the extended extraction lemma.

Human review items: three existing lemmas were extended in place with
additional conjuncts that their proofs already established; no
statement was weakened. The identity-layout hypothesis is used to read
the induced primitives' commitment as the shared game's.

## The stored-mask slope event (continuation 321)

The slope-game event in the composed bound (`slopeWin`) asks for some
mask under which two differing slopes agree; such a mask always exists
when two slopes differ, so that event cannot be bounded. The extraction
actually provides the mask stored in the table at the claim's auxiliary
digest. `SlopeEventSetting.slopeWinC` is the event with the stored mask
and the chain: the first branch's claim (salt, completed seed vector,
auxiliary data, with recomputed row hashes, root and auxiliary digest) is
chained in the branch's table (`ChainIn'` of the shared slope game),
every seed's two expansion entries are in the union of the branches'
cipher histories (`Queried`), and two executions' slopes differ but agree
under the stored mask. The shared slope game has no layout, so the
correspondence (`induced_commitSeed`, `expandEntries_fullLayout`) is
stated under the identity layout `V.layout = fullLayout`, which is the
source's layout.

Human review items: the chain is stated on the first branch's table
while the mask is stored in the snapshot's table (the mask query precedes
the fork by the mask-after-fork event); the coverage will use the
first branch's trace. The identity-layout hypothesis will join the
layout conditions of the final statement.

## The seed-collision bound is discharged (continuation 320)

`SeedCollisionWitness.seedCollision_witnessed`: a recorded seed collision
(two distinct seeds at one leaf address whose four expansion entries are
in the union of the two attempt histories and whose commitments agree)
gives, for every family matching that union, a witnessed pair under the
verifier layout's output projection and the transported companion
`companionL` (the seed-pairing companion conjugated by the layout's
input map, bijective since injective on the finite block type): the two
left-half entries have distinct keys (the key map injective), the same
input, equal projected outputs, and their companion inputs' outputs are
the recorded right-half entries, equal under the projection.
`SeedCollisionBound.seedCollision_le` bounds the real experiment's
probability of the event by `εCollOf lambda tau kappa cOut fuel`, which is
`3·(fuel+1) · callCost cOut (commitBudget·(3·(fuel+1)+2)) commitBudget`: the
key generation's history is empty (mass zero), the cut spends at most
`fuel+1` calls, and the fork at most `2·(fuel+1)`. The final statement
`ForgeryColl.forgery_le_final_coll` replaces the seed-collision hypothesis
by this slack under the verifier layout's injective input and key maps
and its output map's fiber bound `cOutV`.

Human review items: the verifier layout's conditions are stated on
`V.layout` (the event reads the verifier's expansion), separately from
the signer layout's conditions; both hold for the identity layout. The
cost is coarse (every call charged at the largest history length and at
the commitment budget). The event's probability is bounded as a cipher
statistic; no hardness assumption is involved.

## The pair mass through the fork (continuation 319)

`PairFork.fork_pair_bound` bounds, from a resampled snapshot world at
invariant level `n` with `n + 2·(remaining + 1) ≤ B`, the probability of an
event `E` on the plain fork by the snapshot's pair mass plus
`2·remaining·ε`, for an event that is off on a refused fork and that,
whenever it holds on a pair of branches, is witnessed by every family
matching the union of the two attempt histories. The proof reads the
plain fork in the common form (`ForkRestoreEq.shared_eq_common`: first
branch, family resampled at its final history, second branch from the
snapshot's history with that family), writes the second branch as the
shift of the branch from the empty-history base by the snapshot's
history, and compares it pointwise with the same base branch shifted by
the first branch's final history, which is the restored second branch
(`event_le_shifted`): the union of attempt histories is contained in the
restored branch's final history, which has a matching family by the
invariant, so the event forces pair mass one there. The run bounds then
give the two branches' costs.

Human review items: the event's hypothesis is stated on the attempt
histories (empty for a non-attempt terminal), which is what the
seed-collision event reads; the attempt's embedded world is the branch's
final world (`runW_attempt`).

## The pair mass through the oracles and the run (continuation 318)

`PairOracles.callCost capacity L b` is `(b·L + C(b,2)) · pairCost capacity (L + b)`.
Under the counted invariant at level `n` (consistent history of length at
most `commitBudget · n`), the honest signing oracle, the public oracle and
the verification preparation (budget at most the commitment budget)
raise the pair mass by at most `callCost capacity (commitBudget · n) commitBudget`
from a resampled world. `PairRun.runW_pair_bound`, `cut_pair_bound` and
`freshBranchW_pair_bound` are generic in the invariant and the per-call
bounds: a run of `fuel` steps from a resampled world at level `n` with
`n + fuel ≤ B` raises the mass by at most `fuel · ε`; the oracles' resampling
laws insert a fresh resampling after each call so that the per-call bound
applies at every step, and the hash query and table update steps keep
the history.

Human review items: the per-call bound is used at the uniform level `B`
through the invariant's monotonicity; the cost is therefore the cost at
the largest history length, a coarse but simple choice.

## The posterior pair mass starts the seed-collision bound (continuation 317)

`PairMass.pairMass project companion history` is the probability, under
the posterior family of `history`, of the witnessed pair event
(`IdealCipherPairCollision.Witnessed`): two recorded entries with
distinct keys and a common input whose projected outputs agree and
whose projected companion outputs agree. `runProgram_pair_bound` reads
the single-run paired-cipher bound (`HashCipherPair.run_pair_bound`)
through the resampling law (`CipherResample.runFixed_resample`): from a
resampled shared world whose history has length `n`, a program run of
budget `b` with `n + b ≤ total` raises the mass by at most
`(b·n + C(b,2)) · pairCost capacity total`, where `capacity` bounds the
projection's fibers.

Human review items: the intended use is the seed-collision bound. The
event `seedCollision` is a pair collision (two distinct seeds with the
same leaf address whose four expansion entries are recorded in the
union of the two branches' histories and whose commitments agree) and
so is witnessed by every family matching that union; the union is the
final history of the second branch when it runs from the first branch's
final history with the family resampled, which the restored fork
already provides. The projection will be the layout's output map (fiber
bound `cOut`) and the companion the layout's transport of the
seed-pairing companion, which needs the layout's input map bijective
(injective on the finite block type) and the key map injective so that
distinct seeds give distinct keys.

## The final composed bound and its named hypotheses (continuation 292)

Review note (continuation 331): the current end of the reduction is
`NamedSimulatorTerms.forgery_le_final_named`; its current hypothesis
list is in the section "The expansion-dependent simulator terms are
named assumptions (continuation 331)". Of the hypotheses listed below,
`PrunedEqual` was found unsatisfiable and replaced by `DataClose`
(continuation 315), the leaf-term bounds by `LeafHide` (continuation
316), `hcoll` was discharged (continuation 320), the slope-game cast was
discharged (continuation 329), the solver's success became the
syndrome-decoding success on the key generation's instance
(continuation 330) and the simulator's six event terms became the named
constants of `SimulatorTermBounds` (continuation 331). The list below is
kept as the record of the state at continuation 292.

`EventRequirements.forgery_le_final'` was the end of the reduction at
continuation 292. Its conclusion bounds the squared advantage of a
chosen-message forger (minus the digest inverse) by the budget squared
times the sum of the witness-free simulator's seven event probabilities,
the solver's success on the syndrome-decoding instance, eight copies of
the per-event slack, and the mention, collision and digest terms of the
fork-and-extract core. The per-event slack is `εSimP c cKey cOut q εR
(εTouch c cKey (commitBudget·(3(fuel+1)+2)) (4(3(fuel+1)+2)+3) εLeaf)
fuel + εColl`. Everything is proved from the ideal hash and cipher model
except the following hypotheses, each stated as a named definition or an
explicit inequality in the theorem; none is a hardness assumption other
than the solver's success, which is the conclusion's hardness term:

- `PrunedEqual S publicKey (3(fuel+1)+2)` (`SimulationGapCompat`): for
  every honest witness and fake witness, message, salt, root, digest and
  world satisfying the counted invariant, and every functional Ψ of the
  signature and the world, the mean of Ψ over the commitment run from the
  world pruned at the signature's hidden keys is the same for both
  witnesses. This is the ideal-model form of honest-verifier zero
  knowledge: with the hidden leaf's seed removed from the cipher history
  and the hidden path removed from the family, the witness and fake
  signatures have the same law. The data-level step is proved
  (`hidden_share_step`, `HonestViewUniform`, `posterior_node_uniform`);
  what remains is the run-level statement over the pruned world's
  resampled family.
- `LeafR`/`LeafC … εLeaf (3(fuel+1)+2)` (`TouchBound`): the probability
  that the continuation's run (respectively cut run) records the cipher
  key of the hidden leaf's seed, for a compatible continuation under the
  counted invariant. The expected bound is the query budget times the
  key fiber bound over the number of seeds, from the hidden seed's
  uniformity under the pruned posterior.
- `hretry`: for every witness, message and world under the counted
  invariant, the probability that the candidate retry observation does
  not return at a uniform digest is at most εR. This is the grinding
  step; a proof needs the challenge expansion's model (a pending decision
  recorded at continuation 192). The simplest option is kept: an
  explicit bound εR.
- `hcoll` (discharged at continuation 320): the real experiment's
  probability of the seed-collision event is at most εColl. The event is
  a cipher collision spanning both branches of the fork; its bound is the
  explicit pair cost `εCollOf` through the restored fork
  (`SeedCollisionBound.seedCollision_le`).
- The layout conditions: input injectivity (`hin`), fiber bounds on the
  key-of-output map (`c`), the key map (`cKey`) and the output map
  (`cOut`), and the size conditions 26 ≤ λ, 4·τ·2^κ ≤ 2^24, 2 ≤ τ·2^κ,
  with the budget-dependent counting conditions `hNb`, `hNR`, `hq`.
  These are checkable per parameter set and hold for the source layouts
  with c = cKey = cOut = 1 (the identity layout).
- The structural hypotheses carried since the composed bound: the
  verifier's middle, the encoding injectivity facts, the candidate
  encoding and the signer's encoding, the budgets with the commitment
  budget at most the bound, at least one higher coefficient, the witness
  sampler returning solutions, and the verification budget within the
  commitment budget.

No human decision is needed for the first two items; they are proof
work. The retry bound's model and the acceptable form of the collision
and leaf bounds are decisions already taken in the simplest form (named
explicit bounds).

## Trusted implementation boundary

Lean's kernel and foundational axioms, the installed Lean/mathlib toolchain,
source retrieval, compilation tooling, correspondence with the PDF, and any
correspondence with executable cryptographic implementations require human review.
Performance benchmarks and concrete attack cost estimates are empirical claims.
