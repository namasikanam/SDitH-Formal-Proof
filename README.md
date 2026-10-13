# SDitH v3.0 Lean formalization

Work in progress. This repository does **not** yet establish correctness or security
of the submitted signature scheme.

Source: `sdith-v3.0.pdf`, dated 2026-08-31, 55 PDF pages (printed pages 1–53
following the cover and contents). SHA-256:
`22dfed06d179afa759139487dca9c8f8d4a7cfea22bcedcb7736b50ce5b01c83`.
`source/sdith-v3.0.txt` is a searchable extraction; the PDF remains authoritative.

The requested completion goal is active. Completion requires the full algorithm
specification, proofs, source correspondence, and trust audit. A successful build
of a partial development is not completion.

The main EUF-CMA reduction remains largely unfinished. A bounded adaptive game,
the first abstract forgery-to-prior-hash-query step, and a quantitative replay
bound are now proved, including useful-query selection. Signing simulation, commitment
consistency and RSD extraction remain open. The
priority is this security argument and its proved correspondence to the concrete
routines; declaration counts do not measure progress on the full reduction.

## Where the security reduction stands (continuation 332)

The composed forgery bound is `NamedSimulatorTerms.forgery_le_final_named`
(continuation 331; the chain of earlier forms is recorded in the
continuation paragraphs below). It bounds the squared advantage of a
chosen-message forger against the candidate scheme, minus the digest
inverse, by the budget squared times an explicit sum: the six named
simulator constants, the proved slacks (the per-event simulation slack,
the seed-collision pair cost, the slope-game slack, the mention,
collision and digest terms of the fork-and-extract core) and the
syndrome-decoding success of the solver on the key generation's
instance. Every term is either proved in the ideal hash and cipher model
or carried as an explicitly named hypothesis:

- Proved: the fork-and-extract core, the composed bound's structure, the
  solver's witness-freeness, payload consistency of the honest signer,
  the signing procedures' coupling and the hybrids over the game, the
  input-present, row-stored and staleness terms (continuations 192–218),
  the mean-form witness swap through the data-level closeness and the
  leaf hiding (continuations 219–316), the seed-collision bound
  (continuation 320), the slope-game term (continuations 321–329) and
  the hardness term's identification with regular syndrome decoding of
  the public instance (continuation 330).
- Named hypotheses (the user's decision, continuation 316 onward, to
  keep them as explicit cryptographic assumptions rather than idealize
  the PRG and the challenge and batching expansions): the data-level
  closeness `DataClose` (ideal-model honest-verifier zero knowledge at
  uniform hidden blocks), the leaf hiding `LeafHide`, the retry bound
  `hretry` and the six simulator constants of `SimulatorTermBounds`
  (mask-after-fork, non-separation, seed-collision, zero-challenge,
  Schwartz–Zippel, batching).
- Conditions on the parameters: the layout conditions on the signer
  (input injectivity, fiber bounds of its key and output maps) and the
  verifier (identity layout, injective input and key maps, output fiber
  bound), the size conditions (26 ≤ λ, four times the leaf count ≤ 2^24,
  the budget-dependent counts below the number of seeds) and the
  structural hypotheses (the verifier's middle, the encoding
  injectivity facts, the candidate encoding, the budgets, at least one
  higher coefficient, the witness sampler's solutions, the verification
  budget within the commitment budget).
- Not asserted: that the syndrome-decoding instance is hard. The
  standalone interface `SDitH.Assumptions` keeps the quantitative
  hardness predicate `SDHardness` as a definition; relating the key
  generation's seed-expanded systematic instance to the planted
  distribution is a human correspondence obligation (see the review
  ledger).

## Simulation gap status (continuations 102–191)

The simulation gap of the composed bound is the distance between the
honest signer and the named witness-free simulator. Its hidden-share step
is now proved at the data level, with the remaining inputs explicit:

- Proved: the prover polynomial splits into a mask part and a witness
  part; the hashed coefficients below the top are padded by packed layer
  constants of the hidden randomness coordinates, and the top one depends
  only on slopes; the witness correction, plain check and every positive
  execution's correction are translations by hidden vectors; the revealed
  view and the joint transcript over all executions are bijections of the
  hidden vectors, so independent uniform hidden vectors give a uniform
  transcript whatever the witness; the executed signer's prepared state
  carries exactly these data; the real and fake signers' data coincide in
  distribution under the PRG hypothesis and a uniform hidden seed; and a
  fresh parent key's expansion through either submitted layout is a
  uniform seed, in the lazy and the posterior family models.
- Explicit hypotheses: the PRG hypothesis `PRGUniform` (the random table's
  PRG of a uniform seed is uniform), and the hidden seed's uniformity per
  signature, which follows from the fresh-parent-key event.
- Proved since (continuations 126–130): a tree node is the cipher image of
  its parent and is determined by any family consistent with its recorded
  ancestry; the commitment's tree expansion records every expanded node's
  ancestry; under the posterior family, with the parent's ancestry
  recorded and the parent key fresh, the hidden leaf is uniform and the
  honest data of its PRG vector is uniform whatever the witness (the
  per-signature hidden-share step); a uniform parent's key is not fresh
  with probability at most the history's length over the number of seeds;
  both submitted layouts have injective keys and uniform outputs.
- Proved since (continuations 131–159, the signing procedures' coupling):
  the traced run of a program bind splits into the first program's run
  continued by the second's, with fuel accounting through boundedness;
  the commitment program decomposes into a witness-free prefix (tree,
  commitments, row hashes, outer, auxiliary and mask queries) and a
  witness-dependent tail (the lines query); the prefix's chain queries
  differ by byte prefixes or lengths, and a stored chain input after its
  predecessor's fresh entry raises the charged mention event; prefix
  events persist along runs; the prefix run either raises the mention
  event or finishes with the lines input of every witness fresh, with
  the last row query's stored case carried as the named row-stored
  event on the head's initial result; the tail's lines digest at a fresh
  lines input is uniform whatever the witness; so the honest and the
  simulated signers' commitment runs have lines-digest distributions
  within the mention event's probability (bounded by the prefix trap
  bound) plus the row-stored event's probability, unconditionally.
- Proved since (continuations 160–171, the per-signature comparison and
  the game composition): the honest signing unfolds to the commitment
  run, the PIOP hash query and the opening; it is within the named
  input-present event of its digest-first form; the digest-first form
  is within the named retry-failure event of the fixed-witness simulated
  signing under the named payload-consistency hypothesis; the simulated
  signing is the uniform mixture of its fixed-witness forms; all of this
  under any continuation; the hybrids over the game's run, cut,
  continuation, branch, fork, cut experiment and event experiment; and
  the simulation-gap hypothesis of the composed bound from uniform
  bounds on the two events and the witness-swap term.
- Proved since (continuations 172–188): the composed forgery bound
  restated with the gap explicit; the hybrids under a counted invariant
  (table support, shared-world well-formedness, trace-length budget)
  carried by every step of the game; the input-present event bounded
  uniformly at such worlds by the mention steps over the prefix budget
  from the trace budget (the mention event relative to the starting
  log, whose trap bound has no indicator), the row-stored term and the
  support budget over the digest count.
- Remaining: the row-stored event's bound (a prior query guessing the
  last execution's leaf commitments); the retry-failure event's bound
  (the grinding and nonzero-encoding retries, tied to the pending
  decision on the challenge expansion's model); the witness-swap term
  (the commitment run's coupling for the full output, where the lines
  digest is done up to the mention and row-stored events and the rest
  needs the data-level hidden-share step with the fresh-parent chain).
  Payload consistency is proved (continuations 189–191) under the
  candidate encoding and at least one higher coefficient.

## Composed reduction summary (continuations 85–100)

Under the user's decisions of 2026-10-09 (named candidate targets; the
simplest option for every decision; remaining events carried as explicit
terms), the composed forgery bound against the candidate scheme is proved
as `CandidateSimulator.forgery_le_simulator`: the forgery advantage of a
bounded adaptive adversary against the candidate scheme with the honest
signer, less the fresh-hash guessing term, squared, is at most the squared
action budget times the sum of

- the simulated scheme's named events at a uniformly random fork index:
  a branch's mask input first queried after the fork (decision 1), hidden
  indices not separated at some execution (decision 2), a recorded seed
  collision (decision 5), the slope-consistency game's winning condition
  (decision 5), a zero challenge, the Schwartz–Zippel event (a nonzero
  difference polynomial vanishing at the challenge) and the batching event
  (a non-solution whose batched residual and unitary checks cancel);
- the witness-free solver's success: the solver runs the simulated
  scheme's fork experiment and outputs the extracted witness, which is a
  solution of the public mux syndrome instance whenever the solution
  event holds;
- the per-event simulation gap between the candidate scheme and the
  named simulator (eight copies of an explicit hypothesis term);
- the proved charged-event bound (fixed-target, mention and collision
  events of the honest signing and verification services) and the
  guessing term.

The deterministic chain behind it is fully proved: forking, accepted
transcript provenance, candidate reconstruction and middle, uniform slope
data, slope dichotomy, witness line recovery, the composed verifier as
the extracted lines' prover polynomial, the split of extraction into the
batching and solution events, the solver's output, the simulator's
witness-freeness, the simulated transcript's completeness and the
provenance of simulated signatures.

What each remaining explicit term needs, and why it is not yet discharged:

- Simulation gap: honest-verifier zero knowledge of the BLC/PIOP
  transcript (the masked coefficients), independence of the hidden share
  (seed guessing against the ideal cipher) and the programming failure
  (salt guessing). The completeness and provenance halves are proved.
- Slope-game win: a cast of the forked adversary as a procedure of the
  shared slope-consistency game, whose bound is proved.
- Seed collision: a cross-branch collision bound over the product of the
  two independent branch continuations.
- Zero challenge, Schwartz–Zippel, non-separation and the batching event:
  these depend on the challenge expansion and the batching expansion,
  which the model takes as deterministic parameters of the verifier and
  signer settings. With an unbounded adversarial counter they cannot be
  bounded in this model; discharging them needs a modelling decision
  (expansion as a random oracle with query accounting, or a verifier-side
  counter bound), which is recorded as a pending human decision.
- Mask after fork: decision 1 keeps it as a hypothesis term.

Organization:

- [PLAN.md](PLAN.md): completed components, remaining work, dependencies and completion gates.
- `SDitH/Specification.lean`: specification interface, with source references.
- `SDitH/Assumptions.lean`: explicit security model and hardness assumptions.
- `SDitH/Proofs/`: kernel-checked derivations; no new axioms or proof placeholders.
- `SDitH/Final.lean`: a small interface of final established statements.
- `audit/HUMAN_REVIEW.md`: source discrepancies and human review obligations.
- `audit/COVERAGE.md`: exhaustive scope and unfinished work.

Lean 4.28.0 and mathlib v4.28.0 are pinned. Build with `lake build`.
Run the source-hash check, source scan, build, and transitive axiom audit with
`python3 scripts/check.py`. The only permitted transitive axioms are `propext`,
`Classical.choice`, and `Quot.sound`. This trust check is distinct from the human
review of statement adequacy and PDF correspondence.
No `sorry`, `admit`, unchecked native proofs, or user-defined axioms are permitted.
Cryptographic hardness must be an explicit theorem parameter, never an axiom
silently asserted by this repository. Source claims that are false or unsupported
must be recorded as such, rather than assumed in order to prove themselves.

The three final statements currently certify a literal PIOP completeness
counterexample, the Table 3 tensor dimension mismatch, and two delimited
commitment-algorithm discrepancies. Supporting proofs now include the detailed
PIOP's flat parsing, arithmetic evaluation agreement and output degree bound;
zero-padded syndrome batching; salt-domain encoding; seed-tree construction and
BAVC commitment; the literal opening loop and its padded length; and seed cipher
formulas with tweak-domain bounds. A complete successful BAVC opening is now
connected to explicit rejection by the full staged reconstruction body,
independently of every supplied binding for its undefined nodes array. Further checked source
discrepancies concern mux coordinate order and a unitary-check degree annotation. These
are not claims of an attack on a reference implementation, a refutation of the
whole cryptosystem, or a completed correctness/security formalization.

SignatureSecurity defines the adaptive signing/public-oracle game with a hidden
secret key and world, private adversary state, explicit request logs, and
distinct exhausted/aborted/rejected/final-attempt outcomes. AbstractSignature
implements the message-bound HashPiop call between preparation and opening.
Its initial table is empty; signing creates only its message's entry, and other
services cannot access that table directly. The resulting provenance invariant
is proved through the whole game. A fresh winning forgery therefore has an
earlier adversarial query to its exact final input, except for an absent-input
guessing term of 2^(-2*lambda). This is a ROM proof about the defined abstract
game, not a full security theorem or a claim about deterministic SHAKE.

SignatureHashGame connects the final test to the actual parsed Algorithm-4
verificationInput and verifyPostRecompute computations. Its typed hash-input
and signature-body records are equivalent to the existing records. The complete
honest components, byte encoding/domain separation, Algorithm-12 resolution,
and full source-to-abstract-game correspondence remain to be proved. No binding,
simulation, soundness or extraction contract is assumed by the new components.

SignatureReplay cuts the actual game before an indexed adversarial hash answer.
Ordinary resumption has exactly the original game distribution. At a fresh cut,
two independent continuations give the bound epsilon^2 <= fork probability +
epsilon/|Digest|, including averaging over the actual random prefix. Epsilon
here is the probability of winning at the selected fresh input. Query selection
now connects this quantity to overall forgery probability.
The successful fork produces two accepted fresh-message attempts at that same
typed input with distinct tested digests. These experiments still use the honest
signing secret, so they are not yet a witness-free reduction. Distinct digests
alone are not asserted to give distinct usable challenges or an RSD witness.

SignatureQuerySelection records query freshness when each request is made and
proves its selected-event law equals the actual cut/resume experiment. Provenance
shows every table-present winner has a recorded fresh target request below the
action budget, excluding signing on other messages and handling repeated queries.
SignatureForgeryFork derives, for q positive actions, forgery probability e,
delta = 1/|Digest| and the defined uniform-index fork probability F:
`max(e - delta, 0)^2 <= q^2 * (F + delta)`.
The exact intermediate bounds are `e <= q*s + delta` and
`s^2 <= F + s*delta`, where s is that algorithm's actual selected-input success.
This squared action-budget loss is not claimed to be optimal. SignatureHashGame
specializes delta to `2^(-2*lambda)` at the source's typed record shapes.
The experiment retains the honest signing key, so this remains a replay bound,
not a witness-free hardness reduction or the submitted full security claim.

BAVCBinding now supplies a computable collision finder for the exact row/outer
hash inputs. Fixed-width array serialization is proved injective; returned pairs
are actual queries from the two computations. For two successful staged
reconstructions with one root, disagreement on a commonly revealed seed yields
a found hash collision or a same-index seed-commitment collision. The latter is
reduced to equal outputs of the source's two cipher calls under distinct seed
keys. BLCBinding connects the verifier's concrete Hashlines/Hashaux calls to
equality of the BAVC roots or collisions on those exact query pairs. These are
deterministic reductions, not bounds on collision probability or full BLC binding.
Missing source bindings, the scalar consistency equation, serializer boundaries,
and the omitted witness-correction field remain explicit.

The adaptive shared-oracle collision experiment now has a proved birthday bound
and exact table/log invariants. BAVCBindingROM uses the actual two-layer finder
to bound fully queried, equal-root distinct salt/commitment data by
`choose(q,2) / 2^(2*lambda)`, counting all queries including repetitions.
The final choice may depend on the entire instrumented result. Query-coverage
checks are part of this limited experiment; embedding full source executions,
counting honest internal calls and handling seed/cipher collisions remain open.
This does not infer a random-oracle property of SHAKE or complete BLC binding.

BAVCHashVerification now removes the hash component's already-queried guard:
after adaptive selection it executes both row/outer computations against the
same oracle, including previously missing inputs. Every run finishes within
`2*(tau+1)` verification queries, and the computed roots equal the source hash
equations. The binding probability is at most
`choose(q + 2*(tau+1), 2) / 2^(2*lambda)`, including the adversary's earlier `q`
queries and all repetitions. Full source signature/replay composition, seed-tree
binding, challenge extraction and signing simulation remain open.

IdealCipher now defines adaptive encryption and decryption using one hidden
keyed-permutation family. Its posterior interpreter has exactly the same output
law as sampling that family once, and is linked to the standalone assumption
model. Repeats and inverse queries preserve recorded equations; fresh answers
are uniform over the corresponding unused range. The derived conditional
target bound is `1/(M-q)` for a full block of size M. Category III retains full
256-bit observations and has the projected target bound `2^64/(2^256-q)` for a
fresh Enc* query.

The paired-cipher reduction now uses the source's fixed companion plaintext
(lowest-bit flip), preserved by Category-III padding. Joint posterior sampling
retains the hidden family for the terminal test. A first matching observation
pair has an unobserved companion, yielding the adaptive bound
`choose(q,2) * C/(M-q) * C/(M-q-2)` for projected paired collisions, with M full
blocks and projection fibers of size at most C. Full-output calls have C=1;
Category III has M=2^256 and C=2^64. Encryption, decryption, repeated calls and
adaptive key changes are included. A useful finite denominator requires q+2<M.
SeedVerification now executes both full commitments after the adaptive adversary
against the same cipher family, including after early stopping. Every run makes
the four calls and completes; its output and success condition equal the literal
CommitSeed outputs and distinct-seed collision predicate. Equality with the
direct source experiment is proved, with no prior-query or freshness condition.
The binding bound is `choose(q+4,2) * C/(M-(q+4)) * C/(M-(q+6))`, including all
verification calls. Here q counts earlier cipher calls; q+6<M gives a useful
finite bound. This completes the cipher-only two-commitment coverage step.
The joint-model extension below also allows earlier hash queries. Complete
reconstruction and signature composition remain unfinished, along with extraction
and signing simulation.

HashCipher now supports hash, encryption and decryption in one adaptive
execution, with a single lazy hash table and a single hidden cipher family.
Its joint posterior/fixed-family law, table/graph consistency, collision-flag
coverage and total query count are proved. The combined collision bound is
`choose(q,2) * (1/|Digest| + C/(M-q)*C/(M-q-2))`, for q total query/action fuel.
Both source-width instantiations are checked. Existing BAVC hash and seed
verification programs embed exactly, with their output and coverage proofs
preserved. HashCipherPipeline now composes two adaptive phases, including early
stopping, with the same table/family and both histories. It retains the OR of
both collision flags and derives both bounds with q+k total actions. Source seed
and root-hash checks run after a mixed adversary with completion and coverage
proved. Their bounds include q+4 and q+2*(tau+1), respectively. The seed experiment
is exactly the direct source collision law, including Category III.
The joint sampling choice is explicit in `Assumptions.sharedOracleModel`;
independent fresh hash draws do not follow from uniform marginal models alone.

BAVCCipherProgram executes the internal-node expansion, revealed-leaf commitment
and row operations of Algorithm 9. Its exact result equals the existing staged
reconstructionRows definition, including errors; its bound is
2*(tau*N-1)+2*N*tau cipher calls. Full and padded/truncated layouts have checked
Enc* correspondence. The shared interpreter preserves the hash table/log and
records the actual cipher calls. BAVCReconstructionProgram now inserts each row
hash immediately after its row, followed by the outer hash. Supported runs
finish at the exact staged source result, including every error; actual table
lookups and revealed-seed cipher calls are derived from execution.

BAVCReconstructionGame executes both selected reconstructions after a mixed
adversary. It preserves both results, including errors. Successful equal-root
reconstructions with disagreeing common revealed seeds yield a stored hash
collision or a covered seed collision. The full/III bounds are
`choose(Q,2) * (1/|Digest| + C/(M-Q)*C/(M-Q-2))`, with
`Q=q+2*(2*(tau*N-1)+(2*N+1)*tau+1)`. All calls are included; no prior-query,
freshness or coverage guard filters the event. Q+2<M gives a useful finite cipher
term; source tweak/width bounds remain explicit. This is a reconstruction
disagreement bound, not signature security. Full BLC linkage, signature/replay
costs, usable challenges, extraction and signing simulation remain open.

BLCHashChain now executes the verifier's Hashaux and Hashlines calls as an
explicit oracle program on the same shared hash/cipher model, with the
intervening computation an explicit bounded program supplied by the caller.
Equal line digests give equal BAVC roots or a stored collision on the exact
two query pairs. BLCReconstructionChain composes each complete ordered
reconstruction with that chain and executes both selected chains after a
mixed adversary. Equal line digests with a disagreeing commonly revealed seed
have the full/III bound `choose(Q,2) * (1/|Digest| + C/(M-Q)*C/(M-Q-2))` with
`Q = q + 2*(B + p + m + 2)`, where B is the reconstruction budget and p, m
bound the supplied intermediate programs. The source constructor keeps the
three-field Hashlines payload; its base-matrix program is the unresolved
line-21 boundary, not an implementation of it. This still does not identify
Algorithm 12's supplied folding seeds with reconstruction output, and it is
not signature security.

BLCSeedExtraction turns that bound into a seed-vector extraction statement.
When two successful chain executions have equal line digests and different
hidden indices at some execution, every leaf of that execution is revealed by
one side. If the commonly revealed seeds agree, the pointwise merge is the
unique complete seed vector agreeing with both; extraction failure therefore
has at most the chain disagreement probability in both layouts. This does
not identify the hidden indices with concrete challenge expansion, does not
recover a witness, and is not a signature statement.

BLCSeedFold runs Algorithm 12's folding loop (lines 9–16) under explicit
extractor bindings: the undeclared `seed` array is filled from a complete
seed vector, each `rshare` starts at zero and `phi_mu` is the Gray row. The
verifier's share at any hidden index is then an affine function of that
index's Gray row, with slope the fold accumulator plus the transmitted
correction and intercept the fold base. Two hidden indices differ by the
slope times the row difference, and for honest Algorithm-10 corrections on
the signer's seeds the slope is the committed common accumulator. These are
deterministic identities under named bindings; the literal absent-binding
behavior of Algorithm 12 is unchanged, and no witness validity is claimed.

BLCSeedLines carries that affine share matrix into the suffix: each witness
and randomness value is the correction plus delta times a sum of
per-execution slope terms and the intercept's psi. With a constant slope
and the Gray merge as header encoding, the witness value is affine in delta
with constant term correction plus slope. Under one explicit candidate binary
reading of the ill-typed line 21, stated only as a hypothesis shape, two
hidden vectors whose Gray rows differ at a bit of some execution force that
execution's masked slope to equal the transmitted plain check and the
intercept's columns to equal the base there. No line-21 resolution is
selected and no soundness probability is claimed.

ConsistencyMatrix supplies the uniform-mask step behind that identity. Over
a uniformly sampled binary M, a fixed nonzero vector is annihilated by
[I | M] with probability exactly 2^-(lambda+B) when its payload part is
nonzero and never otherwise, so two distinct fixed slopes have equal masked
images with probability at most 2^-(lambda+B). The general statement is the
uniform fiber law of a surjective linear map into a finite module. The
sampler is the explicit uniform matrix law; identifying it with the XOF
expansion of the auxiliary digest remains a separate obligation.

RandomOracleTrap gives the adaptive form of that step. For the lazy oracle
of the existing collision experiment, a predicate that is a fixed function
of the query input and the fresh answer, holding for a uniform answer with
probability at most epsilon, is satisfied by some recorded query/answer pair
with probability at most budget*epsilon; a repeated query returns a recorded
pair and cannot create a new hit. Instantiated to masks, an adaptive
procedure sees a mask annihilating the fixed nonzero vector of its own query
input with probability at most budget*2^-(lambda+B). The vector must be a
function of the query input; composing this with the auxiliary-digest query
and the hcom binding of the slopes is the next step.

RandomOracleTrace instruments the same adaptive experiment with, for every
fresh query, the table as it stood before that query, and proves the same
budget*epsilon trap bound for predicates that may depend on that earlier
table. Repeated queries are answered from the table and recorded nowhere.
Every stored value has exactly such a fresh entry, whose earlier table lacked
it and is extended by the final table, and every fresh entry persists. This
is the shape in which a mask query can be related to the commitment chain
present when the mask was sampled; the chain-completed-later case is a
separate guessing event still to be bounded.

RandomOracleMention bounds that guessing event. On the same instrumented
trace, a trap predicate may depend on the whole fresh-query prefix, with a
per-query bound depending on the number of preceding fresh entries; the
total is the sum of those bounds over positions. For an explicit mention
map sending each query input to at most m digests it mentions, a fresh
answer equals a value mentioned by an earlier fresh input with probability
at most choose(budget,2)*m/|Output|. This is the term charged when a hash
preimage chain is completed only after one of its values was used.

ProductOracle models the hash and mask oracles as the digest and matrix
components of one product-valued lazy oracle, an explicit model choice. The
component marginals are uniform, the table-dependent mask trap on the
matrix component has probability at most budget*2^-(lambda+B), and a fresh
digest component hits a value mentioned by an earlier input with
probability at most choose(budget,2)*m/|Digest|. These are the three
ingredients of the slope-consistency composition, which remains to be
assembled with the hcom-to-seeds chain.

OracleChain proves the ordering facts that connect them. The instrumented
log is ordered (a newer entry's earlier table extends an older one's and
stores its value) and fresh. For a sink-first dependency chain of stored
hash queries, where each input mentions the digest expected of the next
older link, either every link is already present in the table before the
sink was answered, or some fresh digest equals a value an earlier input
mentioned. This is the generic ordering lemma for relating a mask query
to the commitment chain present when the mask was sampled.

BAVCChainInputs instantiates it with the concrete strings: row strings
(domain byte 1, N commitments), the outer string (domain byte 1, salt and
tau row digests), the auxiliary string (domain byte 2, root and
corrections) and the mask input (the auxiliary digest). A fixed-offset
digest-window parser mentions at most tau+2 values per input and extracts
the root from the auxiliary string, each row digest from the outer string
and the digest from the mask input. The four kinds of input are pairwise
distinct by domain byte or length. Hence, for every execution, the
auxiliary, outer and row strings are present before the mask input was
answered, or a fresh digest hit a mentioned value. The strings are the
existing reconstruction-program inputs by definition.

SlopeConsistency supplies the uniqueness step. A claim behind a mask query
consists of salt, leaf seeds, row digests, root, auxiliary digest and the
transmitted auxiliary data; it is chained in a table when its row, outer
and auxiliary strings are stored with its digests. In a table with no two
distinct inputs sharing a digest, two chained claims with one auxiliary
digest agree on everything the slopes depend on, under explicit injective
commitment and serializer hypotheses. A fresh digest equal to an earlier
fresh digest has probability at most choose(budget,2)/|Digest|, and any
two distinct stored inputs with equal digests raise that event, so the
collision-free premise holds on every earlier table except on it.

SlopeConsistencyGame assembles these into the standalone bound. In the
product-oracle game an adaptive procedure names a claim; it wins when the
claim is chained in the final table, the mask for its auxiliary digest is
stored, and two executions' slopes differ yet have equal masked images.
The trap vector of a pair of executions is the slope difference of the
claim chained in the table before the mask query, which uniqueness makes
the adversary's own. A winning run raised one of the tau^2 traps, the
mention event or the collision event, so its probability is at most
`tau^2 * budget * 2^-s + choose(budget,2) * (tau+2) / 2^(2*lambda) +
choose(budget,2) / 2^(2*lambda)`, with s = lambda + B in the source. The
injective commitment and serializer hypotheses are explicit; joining the
first to the cipher-model seed binding is the next step.

HashCipherTrace carries the fresh-query log into the shared hash/cipher
execution used by the signature-side games. Cipher queries leave the hash
table and the log untouched. Forgetting the log gives exactly the existing
shared execution, so every earlier result in that model transfers, and the
log satisfies the traced, ordered and fresh invariants. Both the table-
dependent trap bound budget*epsilon and the prefix-dependent bound summed
over positions hold for a fixed cipher family and for the mixture over the
hidden family. This is the model in which the slope-consistency game can
replace its injective-commitment hypothesis by the cipher seed binding.

IdealCipherUnseenMatch supplies the cipher-side step for that replacement.
Under the posterior family law of the ideal-cipher model, a key whose two
paired inputs are both unobserved matches two given target outputs with
probability at most 1/(M-q) times 1/(M-(q+1)), and some such key among k
candidates does so with at most k times that. A seed colliding with a
named seed's commitment is therefore either a queried seed, covered by
the witnessed pair event, or an unqueried one, covered by this bound with
k at most 2^lambda.

SharedSlopeGame re-states the slope-consistency game in the shared
hash/cipher model with leaf commitments computed by CommitSeed through the
hidden family at the claim's salt. The injective-commitment hypothesis is
replaced by a local condition, that no other seed shares a named seed's
commitment, and its failure is split: a colliding seed queried at either
paired input gives a witnessed pair collision, otherwise it is an unqueried
double match. A winning run, whose named claim is chained with its
commitment calls in the cipher history, therefore raised a mask trap, the
mention event, the digest-collision event, a witnessed pair collision or
an unseen double match.

SharedSlopeBound assembles the five terms. Over the hidden cipher family
the tau^2 mask traps cost `tau^2 * budget * 2^-s`; the mention and
digest-collision prefix events cost `choose(budget,2) * (tau+3) / 2^(2*lambda)`;
the witnessed pair collision transfers through the projection onto the
existing shared experiment and costs `choose(budget,2) * pairCost`; and the
unseen double match is bounded at the final world through the posterior
view by `tau * 2^kappa * 2^lambda / ((2^lambda - budget)(2^lambda - budget - 1))`.
The result is the slope-consistency bound in the shared model with no
commitment-injectivity hypothesis. The named claim's commitment calls are
still required in the cipher history, to be discharged by execution.

HashCipherTracePipeline carries the fresh-query log through two adaptive
phases of the shared execution, where the second phase starts from the
first's selected state with the same family, table, histories and log. It
projects exactly onto the existing two-phase execution, keeps the log
invariants, has at most q+k fresh entries, and satisfies the table-
dependent trap bound (q+k)*epsilon and the prefix-dependent bound summed
over q+k positions for monotone epsilon. This is the execution in which
the named claim's commitment calls can be made by a second phase.

SharedSlopeExec makes those calls. The adversary's selected claim becomes
the return value of a cipher program performing both CommitSeed calls of
every leaf seed, run as the second phase; the program is bounded by
2*tau*2^kappa, every call's entry is in the final cipher history, and the
final state carries the claim. The winning predicate therefore has no
queried condition, and the slope-consistency bound holds for the two-phase
experiment with budget q + 2*tau*2^kappa: the tau^2 mask traps, the mention
and digest-collision terms, the witnessed pair cost and the unseen
double-match term, the last two through the two-phase projection and the
two-phase final-world posterior lemma.

SharedScheme begins the connection to the signature game. Its other-state
is the shared hash/cipher/mask world; the public oracle answers hash
queries by the digest component, mask queries by the matrix component and
cipher queries by the block; and Algorithm 4's verification is an executed
program: the complete ordered reconstruction, the Hashaux query, an
explicit middle parameter for lines 9–21 of Algorithm 12, the Hashlines
query, and the existing Algorithm-4 suffix. The middle is a parameter
because the literal lines read undeclared names and line 21 is ill typed;
the hidden-index expansion is likewise a parameter because the literal
sampler reads the undefined B. The honest signing services are not yet
supplied. Two accepted attempts of a successful fork share the typed hash
input, hence the lines digest and coefficient tuple, and lifted digest
programs evaluate against the digest projection of the table.

SharedSchemeChain connects the executed verification to the chain and
seed-extraction results. A successful verification decomposes into a
successful reconstruction evaluation on the digest projection of the
table, the Hashaux and Hashlines lookups and the middle's evaluation. Two
successful verifications with equal lines digests have equal roots unless
two distinct inputs share a digest, and with hidden indices differing at
an execution they determine a unique complete seed vector for it unless
such a digest collision or a seed collision with recorded cipher entries
occurs. These are deterministic facts about two executions on one table.

CandidateVerifier names one candidate for Algorithm 12 lines 9–21 as a
verifier middle: the undeclared seed array is the reconstruction's own
revealed seeds, which the literal loop never reads at the hidden index,
the shares start at zero, phi_mu is the Gray row, the consistency mask is
the mask-oracle answer at the auxiliary digest, and line 21 is read as the
binary equation base = [I|M]·Q − plain ⊗ Gray(hidden). Its fold agrees
with the fold of any complete seed vector agreeing with the revealed
seeds, so a successful evaluation returns the affine share matrix of that
vector, the suffix's witness and randomness values at delta, and a base
equal to the masked slope minus the plain check times the hidden row plus
the intercept's columns. This is an explicitly identified candidate target,
kept separate from the literal prefix.

ForkSlope composes the candidate middle with the two-verification seed
vector. Two successful executed verifications of the candidate setting
on one digest-collision-free table with equal lines digests, under
explicit injectivity of the corrections serialization and of the lines
payload serialization, share the auxiliary digest, mask, plain check,
base, corrections, root and salt, the last through the recorded outer
lookup. Where their hidden indices differ, either a recorded seed
collision occurs at that execution, or the merge-based completions of the
two reconstructions agree there and the two base equations, read at a bit
where the two Gray rows differ, force the masked slope of that execution
to equal the transmitted plain check. This is the deterministic link
from a fork's accepted attempts to the slope-consistency claim; feeding
it into the probabilistic slope game still needs the signer program and
query accounting.

SharedSigner writes the honest signer's commitment phase as an executed
program in the same shared model: Algorithm 7's complete seed-tree
expansion and every leaf commitment as cipher calls, the row and outer
hashes, then Algorithm 10's PRG table and corrections, the Hashaux query,
the consistency mask read from the mask oracle at the auxiliary digest,
the commit arithmetic and the Hashlines query. The Hashlines tail is a
parameter with two named readings: the literal signer's, which appends the
witness correction, and the verifier's, which omits it. A successful
evaluation is Algorithm 7's commitment under the primitives induced by the
executed family and table, with the row, outer, auxiliary, mask and lines
lookups stored, both commitment calls of every leaf seed in the cipher
history, and the result's fields equal to the commit arithmetic at the
stored mask. The program is bounded by an explicit budget.

SharedSigning attaches the abstract game's signing services in the shared
model. Preparing a signature samples the salt and root uniformly, runs the
commitment program on the world within its budget and applies the PIOP
prover, returning the HashPiop payload and the signer's state; opening a
signature after HashPiop is Algorithm 11 observed on the returned digest
with the explicit challenge expansion, giving the parsed body, or no body
when the observation does not return; verification is the executed
verifier on bodies that exist and rejection otherwise; key generation is
a witness sampler at a fixed instance and public key with a uniform cipher
family and empty tables. Every prepared state comes from an executed
commitment evaluating on the resulting world, the opening service is
deterministic, and every honest signature with a body carries the salt,
auxiliary data, opening and higher coefficients of such a state with its
digest stored at the typed HashPiop input. The composed scheme is the
abstract scheme of these components.

ForkSlopePrefix handles the two branches of a fork, which run on tables
extending the shared prefix and on cipher histories extending the shared
history. An evaluation reads only the hash inputs it visits, so if every
visited input is in the prefix the evaluation holds on the prefix itself,
and evaluations are monotone in the cipher history. Two candidate-middle
verifications of a fork, one per branch, whose visited inputs lie in the
prefix therefore satisfy the fork-to-slope outcome on the prefix table
with the union of the two histories. Which visited inputs can lie outside
the prefix is the accounting left to the chain-mention bounds.

ForkCut starts that accounting. The fork table is a cut of a branch's
fresh-query log: every fresh entry was answered after the cut or is
already stored by it. A stored sink-first chain whose sink is present in
the cut is entirely present in the cut, or a fresh digest hit a mentioned
value. The verifier's Hashlines string mentions the auxiliary digest at
the same offset as the mask input, and its header byte separates it from
the auxiliary, outer and row strings, so for an accepted verification
whose lines string is in the cut, every auxiliary, outer and row string is
in the cut up to the mention event. Whether the lines string is in the cut
is the fixed-target event of the fork point, and whether the mask input is
in the cut is a separate question, both still to be charged.

ForkCutRun charges the fixed-target event along a branch. Running the
shared traced interpreter from a table extending the fork table preserves
the cut: every fresh entry made after the fork has an earlier table
extending the fork table. A value stored after the fork whose digest
equals a fixed target raises a trace event whose per-query probability is
the inverse digest count, so over a run the event is bounded by the
budget times that inverse, and an entirely pre-fork initial log
contributes nothing. Hence a stored value with the target digest is
present in the fork table or the event occurred.

SharedGameInvariant derives the cut from the forking construction. A
predicate on the shared world preserved by every service output is
preserved along the game's run and along the cut, so it holds at every
attempt's world, at every saved snapshot's world and at both branches of
a fork. The shared services preserve well-formedness of the fresh-query
log from the empty initial world and the cut at a fork table from a
world extending it. Hence at a saved snapshot of the shared game the log
is entirely pre-cut, and both branches' attempt worlds are well formed and
cut at the snapshot's shared table. Summing the fixed-target and mention
events over a branch's service runs remains to be done.

VisitedInputs lists the hash inputs an executed verification reads.
Visited inputs compose along binds, the cipher lifts visit none, the
digest lift visits the inputs of its projection, a successful
reconstruction visits only its row and outer queries, the candidate
middle visits exactly the mask input, and a successful verification
visits only the reconstruction's queries, the auxiliary query, the
middle's inputs and the lines query. These are the inputs the fork
accounting must find in the fork table for the prefix restriction.

BranchAccounting accounts one branch of a fork. On a well-formed branch
table cut at the fork table, an accepting candidate-middle verification
whose lines value is the fork point's fixed target visits only inputs
present in the fork table, unless a named event occurred: a fresh
post-fork digest equal to the target, a fresh digest equal to a
mentioned value, or the mask input of the forgery's auxiliary digest
absent from the fork table. The first two are charged by the trace
bounds; the third is the recorded open question of the mask's position
across the fork.

ForkOutcome states the deterministic outcome of a successful fork of the
shared game with the candidate-middle verifier. Every attempt of the run
is the output of a verification service call, which in the shared model
is an executed verification evaluating on the attempt's world with the
attempt's payload digest as its lines value; a run ending in a value
evaluates to it without any budget premise. At a successful fork both
attempts share the snapshot's typed input and both branch worlds are well
formed and cut at the snapshot's shared table, so at every execution
where the two hidden indices differ, the fork-to-slope outcome holds on
the snapshot's table with the union of the branch histories, or a branch
event occurred, or the snapshot's table has a digest collision. The
probability of the events, the separation of hidden indices from distinct
targets, and the slope game remain to be attached.

GameEventBound accounts per-run trace bounds over the whole game. If
every service call raises a Boolean event on the shared world with
probability at most its indicator before the call plus a constant, then
each adversary action contributes at most twice that constant, since a
signing request calls two services, so the event at the attempt is
bounded by its indicator at the start plus the fuel times twice the
constant; the same holds for a fresh branch from a snapshot, since
finalization keeps the terminal.

SharedTargetBound charges the fixed-target event over the shared game.
Every shared service runs at most one program within its budget, so the
event on the shared world's log grows by at most that budget times the
inverse digest count per call; with a common budget bound covering the
commitment, verification and single-query budgets this is a service
bound, and a fresh branch from a well-formed snapshot raises the event at
the snapshot's table with probability at most the remaining fuel times
twice the bound times the inverse digest count, with no initial term.

GameEventBoundLen extends the game-level bound to events whose
per-service probability depends on a size of the shared world, such as
the fresh-query log length. Each service grows the size by at most a
fixed amount and raises the event by at most an increasing function of
the size before the call; with the remaining fuel accounted, the size
stays below a fixed level throughout the run, so the event at the attempt
is bounded by its indicator at the start plus the fuel times twice the
function at that level, along the run and on a fresh branch. A traced
run adds at most one fresh entry per unit of budget.

SharedMentionBound charges the mention event over the shared game. A
fresh digest equal to a value mentioned by an earlier fresh query input
has per-query mass at most the log length times the mention count times
the inverse digest count, so a program run within a budget raises the
event by at most the budget times that mass at the final length. With
the log length as the size, each shared service grows it by at most the
common budget bound and raises the event by an increasing function of
the length, so a fresh branch raises the event with probability at most
its indicator at the snapshot plus the remaining fuel times twice the
per-run bound at a level dominating the snapshot's length plus the
remaining growth. The indicator at the snapshot is the mention event of
the prefix, to be charged by the cut experiment's own bound.

CutEventBound carries the size-dependent bound along the cut, the prefix
of the game up to the selected adversarial hash action. The event at a
saved snapshot's world or at an ended attempt's world is bounded as along
the run, and a saved snapshot's size plus its remaining growth stays
below the level, which is the premise the branch bounds need. Starting
from key generation with an empty log this charges the prefix.

SharedCollisionBound charges the digest-collision event over the shared
game and assembles the prefix bounds from key generation. A fresh digest
equal to an earlier fresh digest has per-query mass at most the log
length times the inverse digest count, the same shape as the mention
event with count one, so the shared services satisfy the size-dependent
service bound; without the event a well-formed world's table is
digest-collision free. From key generation, whose shared world has an
empty log, the cut experiment raises the mention or collision event at
the saved snapshot with probability at most the fuel times twice the
per-run bound at the level fuel times twice the budget bound, and the
saved snapshot satisfies the branch bounds' level premise.

ForkEventUnion unites the charged events of the fork experiment. The bad
event of a fork at a saved snapshot is the prefix's mention or collision
event at the snapshot's world, or a branch's fixed-target or mention
event at either attempt, with the snapshot's own table and lines value
as the cut and the target. Its probability over the fork experiment is at
most the prefix mention and collision bounds plus twice the branch
target and mention bounds, all at the level fuel times twice the budget
bound. The mask event is not charged and stays in the deterministic
outcome.

ForkGoodOutcome splits the fork experiment by its charged events. A
successful fork without the charged events yields, at every execution
where the two hidden indices differ, the fork-to-slope outcome on the
snapshot's table, unless a branch's mask input was first queried after
the fork. The fork experiment's success is at most its success without
the charged events plus their bound. This is the probabilistic form of
the fork's outcome, with the mask event the only uncharged term; the
hidden-index separation and the slope game remain to be attached.

ForkSlopeUniform restates the fork-to-slope lemma with the data shared
across executions explicit: two candidate-middle verifications of a fork
on one collision-free table determine the two reconstructions, the
common auxiliary digest and the mask stored at it, and at every
execution where the hidden indices differ either a recorded seed
collision occurs there or the masked slope of the merge completion of
the two reconstructions, at that stored mask, equals the plain check.
The mask and the completion are the same for all executions, as the
slope game needs.

HonestCandidate checks the candidate verifier against the honest signer.
With the honest corrections computed from the same seeds, the slope of
every execution is the committed common accumulator, so the masked slope
is Algorithm 10's plain check and the intercept matrix is its base row
matrix; hence the candidate base computed from the honest shares at any
hidden indices is exactly the honest base check, for any mask. This is
the algebraic half of the candidate target's completeness: an honest
signature recomputes the same lines payload under the candidate reading.

ForkOutcomeUniform restates the prefix restriction, the deterministic
fork outcome and the good-fork outcome through the uniform fork-to-slope
lemma: unless a branch event or a collision occurred, the two
reconstructions, the auxiliary digest and the stored mask are fixed, and
at every execution with differing hidden indices either a recorded seed
collision occurs there or the masked slope identity holds for the merge
completion at the stored mask.

SlopeConsistencyLink takes the uniform fork data to slope consistency and
the extracted line. Under separation at every execution and no recorded
seed collision, every execution's masked slope at the stored mask is the
plain check, so all masked images agree; then either two executions have
distinct slopes with equal masked images, the slope-consistency game's
winning condition at that mask, or all slopes are equal. With a common
slope the candidate middle's witness value is affine in the inverted
challenge, with constant term the transmitted correction plus the common
slope, which is the extracted witness coordinate. The separation and the
absence of seed collisions are explicit hypotheses, the former pending
the recorded decision.

WitnessLineRecovery reads the extracted witness coordinate from the two
branches: with a common slope, each branch's candidate witness value is
the same line at that branch's inverted challenge, two evaluations at
distinct points determine the constant term, and the constant term is
the transmitted correction plus the common slope.

The reduction now stands as follows. Proved: the forking step, the
chain and seed-vector extraction, the honest signer and signing services
in the shared model, the game-level accounting of the fixed-target,
mention and collision events, the fork's deterministic and probabilistic
outcomes, the uniform slope data, the slope dichotomy and the witness
line recovery. Open, each needing a user decision or a large refactor
recorded in the review ledger: the mask input first queried after the
fork, the single-fork versus multi-fork extractor, a corrected target
for Algorithms 8–9 (the literal padded opening cannot reconstruct), the
PIOP target (the literal verifier is not complete), the seed-collision
and slope-game bounds as reductions to the shared traced experiment, and
the signing simulation.

On 2026-10-09 the user chose the simplest option for each of these, with
corrected algorithms stated as explicitly named candidate targets. The
first is CandidateBAVC, a candidate target for Algorithms 8–9: the
opening carries every revealed leaf seed and the hidden commitments
directly, and the reconstruction recomputes each revealed leaf's
commitment by the cipher, takes the transmitted commitment at the hidden
index, and hashes the rows and the salted outer string as Algorithm 7
does. A successful evaluation returns the stored outer digest of the
recomputed commitments and the opening's revealed seeds, with every row
and the outer query stored and both cipher calls of every revealed seed
recorded; on the candidate opening of an honestly committed key the
recomputed commitments are the key's; the program is bounded. The literal
Algorithms 8–9 and their recorded defects are untouched.

CandidateScheme is the shared-model scheme over the candidate target: the
verifier runs the candidate reconstruction in place of the literal one,
then the same Hashaux query, middle and Hashlines query; the signer's
commitment phase is unchanged and its opening phase runs Algorithm 11's
retry with the candidate opening of the committed key, whose only retry
conditions are the grinding test and a nonzero merged challenge; the
abstract game's components are assembled with the candidate opening in
the signature body. A successful candidate verification decomposes into
its four stages and visits only the reconstruction's row and outer
queries, the auxiliary query, the middle's inputs and the lines query.

CandidateForkSlope is the fork-to-slope lemma for the candidate scheme.
Two candidate-middle verifications over the candidate reconstruction on
one collision-free table with equal lines digests share the auxiliary
digest, mask, plain check, base, corrections, root, salt and recomputed
commitments. Each opening is completed by the other's revealed seed at
its own hidden index; at every execution where the hidden indices differ,
either two revealed seeds with the same commitment differ, a recorded
seed collision, or the two completions agree there and the masked slope
at the stored mask equals the plain check.

CandidateBranch carries branch accounting and the prefix restriction to
the candidate scheme: on a well-formed branch table cut at the fork
table, an accepting candidate verification whose lines value is the fixed
target visits only inputs present in the fork table unless the
fixed-target, mention or mask event occurred, and two such verifications
on tables extending the fork table give the uniform slope data on the
fork table with the union of the two histories.

CandidateGameBounds carries the game invariants and event bounds to the
candidate components. They preserve any predicate preserved by program
runs, so well-formedness and the cut hold at snapshots and branch
attempts; the fixed-target, mention and collision events satisfy the
same service bounds as for the literal components, since the candidate
verification is one program run and the candidate opening service is
pure; the prefix bounds from key generation and the snapshot's level
premise follow.

CandidateForkOutcome restates the fork outcomes for the candidate scheme:
attempt provenance from the candidate verification service, the
deterministic outcome of a successful fork (uniform slope data, a branch
event, or a collision), the charged events and their bound, and the
good-fork outcome (uniform slope data or a mask event) with the success
split. The fork chain is now complete for the candidate target up to the
uniform slope data.

CandidateCompleteness proves executed completeness of the candidate
target. An honest commitment run leaves every chain query stored and
every leaf commitment recorded; the candidate opening of the committed
key reveals every other leaf seed, so the candidate reconstruction
evaluates to the committed root and the revealed seeds, the candidate
middle folds the committed seeds to the honest shares, its base is the
honest base check, and the lines query is the signer's when the signer
uses the verifier's Hashlines tail. Hence the candidate verification of
an honest signature evaluates on the signer's own world to the committed
lines digest. The constructive evaluation lemmas for the collector, the
fold loop and the share collection are proved alongside.

PIOPExtraction is the deterministic PIOP step of the extraction. The
composed verifier of the repository (the recomputation with restored
coefficients) is the named candidate PIOP target chosen under decision
4; the literal equations' incompleteness theorem stays in the final
module. With a common slope the candidate middle's witness and
randomness values are the evaluations, at the inverted challenge, of
explicit degree-one lines whose constant terms are the extracted witness
coordinates and the common randomness slopes; the composed verifier's
recomputation is then the composed prover polynomial of those lines
evaluated there, so an accepting transcript, whose restored coefficient
tuple is the hashed one, forces the difference between that polynomial
and the hashed coefficient polynomial to vanish at the challenge. The
probability that a nonzero difference vanishes at the challenge is the
Schwartz–Zippel step, and the batching soundness of the constant term is
the repository's constant experiment; both remain to be attached.

ForkExtraction is the deterministic end-to-end extraction from a good
candidate fork. Under decisions 1, 2 and 5, a winning fork of the
candidate scheme without the charged events, whose two attempts read
their mask before the fork and whose hidden indices differ at every
execution, yields from the two accepted transcripts one of three named
alternatives: a recorded seed collision at some execution (with the
colliding seeds expanded on the two branches), the slope-consistency
game's winning condition at the stored mask (two distinct slopes with
the same masked value), or a common slope for the first branch together
with the vanishing, at that branch's inverted challenge, of the extracted
lines' prover polynomial minus the hashed coefficient polynomial. The
extracted witness is the vector of corrections plus the common slope's
witness coordinates. The first two alternatives are the probabilistic
events to be charged in the final bound; the third feeds the
Schwartz–Zippel and batching steps.

CandidateReduction is the event-union skeleton of the composed reduction.
The named events of a fork result (a mask input first queried after the
fork, hidden indices not separated at some execution, a recorded seed
collision, the slope-consistency game's winning condition at some mask, a
zero challenge, and the Schwartz–Zippel event of a nonzero difference
polynomial vanishing at the challenge) and the extraction event (a common
slope whose extracted lines' prover polynomial is the hashed coefficient
polynomial) are explicit Boolean events. A winning fork without the
charged events is one of them, so the good-fork probability is at most
the sum of their probabilities, and the fork experiment's success is at
most that sum plus the charged-event bound. Extraction forces the prover
polynomial's constant term to vanish, which is the input of the batching
step. Each named event's probability remains to be bounded separately,
and the simulator remains open.

ForgeryReduction is the composed skeleton of the forgery bound for the
candidate scheme. The fork experiment at a uniformly random index is at
most the random-index union of the named events and the extraction
event plus the charged-event bound, and the repository's forgery-to-fork
inequality turns this into a bound on the forgery advantage: the
advantage less the fresh-hash guessing term, squared, is at most the
squared action budget times the sum of the random-index named events,
the extraction probability, the charged-event bound and the guessing
term. The named events' probabilities, the batching step and the
signing simulator remain open; the bound is stated against the
candidate scheme with the honest signer.

ExtractionSplit splits the extraction event into the batching event and
the solution event. On extraction the extracted lines' prover polynomial
has a zero constant term, which by the exact constant-term identity is
the batched mux syndrome residual plus the batched unitary checks of the
extracted witness at the signature's batching challenges; either the
extracted witness is a solution of the public instance (zero residual
and unitary selectors), or the batching event occurred (a non-solution
whose batches cancel). The forgery bound is restated with the two events
in place of the extraction event. The solution event is the term a
witness-free solver must inherit, and the batching event is to be
bounded by the freshness of the lines digest.

SimulatedSolver defines the solver and the simulated statement. The
solver runs a scheme's fork experiment at a uniformly random index and
outputs the extracted witness of the first branch (the corrections plus
the slope at the first execution); whenever the solution event holds,
that output is a solution of the public instance, so the solution event
is at most the solver's success. For any scheme sharing the candidate
scheme's types, a uniform per-event simulation gap between the candidate
scheme and that scheme transfers the forgery bound: the advantage less
the guessing term, squared, is at most the squared action budget times
the simulated named events, the simulated batching event, the solver's
success, the gaps, the charged-event bound and the guessing term. The
intended scheme is a witness-free simulator, still to be named, and its
gaps remain to be proved.

CandidateSimulator (specification and proof) is the named witness-free
signing simulator. The abstract scheme wrapper fixes the honest HashPiop
query, so the simulator is a direct scheme whose signing programs the
hash table: it commits with a uniformly random fake witness through the
honest commitment program, samples the HashPiop digest first, runs the
candidate retry on it, hashes the coefficient tuple the candidate
verifier will recompute from the simulated transcript (the restored
tuple at the inverted challenge on the affine share values of the
committed seeds), and programs the digest as the answer at the resulting
hash input, returning a bodiless signature when that input is already
present. Its signing provably never reads the witness half of the key,
and its other components are the candidate scheme's. The forgery bound
is instantiated at it, with the per-event simulation gap an explicit
hypothesis still to be discharged (programming freshness, hidden-share
independence and the PIOP's honest-verifier zero knowledge).

SimulatedCompleteness is the deterministic half of the simulator's
programming step: the candidate verification of an executed commitment
with any witness (in particular the simulator's fake one), opened at the
hidden indices, evaluates on the signer's world to the inverted
challenge, the affine share values of the committed seeds and the
committed lines digest, so the verification input recomputed from it
hashes the committed lines digest and exactly the simulator's coefficient
tuple. The probabilistic half (the programmed answer is what the game's
verification reads, and the failure event) remains open.

SimulatedSign is the provenance of simulated signatures: every output of
the simulated signing comes from an executed commitment with a uniformly
chosen fake witness and a uniformly chosen digest on the signer's world
with the family unchanged; a signature with a body carries the candidate
retry's return on that digest, and the digest is then stored at the hash
input of the committed lines digest and the simulator's coefficient
tuple, an input that was absent before; a bodiless signature leaves the
hash table unchanged.

PIOPMaskSplit is the algebraic input of the honest-verifier zero-knowledge
argument: the arithmetic body is the masking polynomial times the
evaluation point plus a mask-free part, so the prover polynomial is its
zero-randomness value plus the formatted mask of the randomness lines
times X; the mask is additive in the randomness, and two prover
polynomials with the same randomness differ by their zero-randomness
values. The uniformity of the packed mask constants and the one-time-pad
step on the hashed coefficients remain to be proved.

PIOPMaskCoeff gives the coefficients of the formatted mask: the generic
shifted-coefficient formula, the constant and linear coefficients of a
packed line, and for randomness lines the k-th mask coefficient as the
packed constant of layer d-2-k plus the packed slope of layer d-1-k; the
hashed coefficients of the prover polynomial are the zero-randomness
coefficients padded by the mask coefficients.

PackingUniform gives the probabilistic inputs of the zero-knowledge
argument: the full-width coefficient encoding in the submitted power
basis is a bijection (injective, with the quotient ring's cardinality),
so uniform bits pack to a uniform ring element; a uniform pad added to
any value, or to a value drawn from any distribution, is uniform; and a
uniform pad on one coordinate of a pair makes it an independent uniform
coordinate.

HiddenShareTranslation gives the translation structure of the committed
arithmetic in one party's random vector: the common accumulator is the
sum of execution zero's party vectors, hence any one party's vector plus
the others; the witness correction, the randomness lines' constants and
the plain consistency check are translations of values depending only on
the other parties by linear images of that party's vector. With the
hidden party's vector uniform and independent (a PRG hypothesis recorded
as a pending decision, since the random table's PRG is a deterministic
parameter), these are the one-time pads of the zero-knowledge argument.

RevealedBijection shows that the revealed triple (witness correction,
randomness constants, plain consistency check) is an affine bijection of
the hidden party's vector: the payload coordinates are read off the first
two components and the check coordinates from the third, so a uniform
hidden vector reveals a uniform triple whatever the constants, in
particular whatever the witness.

TranscriptRevealed connects the honest committed arithmetic to that
bijection: its witness correction, accumulator randomness coordinates and
plain check form the revealed map of the hidden party's vector with the
other parties' contributions as constants, the randomness lines'
constants are the algebra images of those coordinates, and replacing the
hidden party's vector by a uniform one makes the honest triple uniform
and independent of the witness. The PRG hypothesis that supplies the
uniform vector, and the pads on the hashed coefficients, remain open.

HashedPads gives the pads on the hashed coefficients: the hashed tuple of
the prover polynomial is the zero-randomness tuple plus the mask
coefficients; for randomness lines whose constants are algebra images of
bits, the mask coefficient at position k is the packed constant of layer
d-2-k plus a slope term; in the submitted quotient ring with its
generator a layer's packed constant is the coefficient encoding, so
uniform layer bits give a uniform pad on any value.

CorrectionTranslation gives the per-execution corrections as translations:
an execution's accumulator is its hidden party's vector plus the others,
so its correction (the common accumulator minus its accumulator) is a
value depending on the common accumulator and its other parties,
translated by its hidden vector; the transmitted corrections are the
positive executions' corrections. With the execution-zero translations,
every revealed auxiliary datum and every hashed coefficient below the top
is padded by a distinct block of hidden coordinates.

TopCoefficient shows that the top coefficient of the prover polynomial
depends only on the slopes: the degree-(a+1) coefficient of a mux of
degree-one selectors over degree-a values is the slope mux of the values'
top coefficients, so the top coefficient of the mux tree is the slope
tree of the leaves; with at least three layers the unitary layers do not
reach the top, and the mask contributes the packed slope of layer zero.
Hence the last hashed coefficient is independent of the lines' constants,
in particular of the witness.

ViewBijection assembles the revealed view of execution zero's hidden
vector over the binary field with the submitted quotient ring: the
witness correction, the per-layer packed constants (translated by the
other parties' packed constants) and the plain check. The randomness
coordinates are re-indexed into layers by the block index, each layer is
packed by the coefficient-encoding bijection, and the whole view is an
affine bijection of the hidden vector, so a uniform hidden vector gives
a uniform view whatever the constants, in particular whatever the
witness.

HashedView connects the hashed coefficients below the top to the view:
the packed constant is additive; for bit-constant randomness lines the
mask coefficient at position k (k at most d-2) is the packed constant of
layer d-2-k plus the slope term of layer d-1-k; a layer of the
accumulator's randomness coordinates splits into the hidden party's
layer and the others'; and the honest randomness lines format to the
bit-constant shape with the accumulator's layers as constants and the
base rows' images as slopes.

HonestView states the honest signer's revealed data in terms of execution
zero's hidden vector over the submitted field: each hashed coefficient
below the top is the zero-randomness coefficient plus the hidden party's
packed layer plus the other parties' packed layer plus a slope term, and
the witness correction and plain check are the revealed map's components.
The hidden-vector contributions are exactly the view map's components,
so the honest revealed data is a fixed function of the view and of
witness-free data; the PRG hypothesis supplying a uniform hidden vector
and the assembled gap remain open.

HonestViewUniform makes the honest revealed data (witness correction,
hashed coefficients below the top, plain check) a bijective image of the
view: the middle component is reversed in the layer index and translated
by the witness-dependent zero-randomness coefficients and the slope
terms, both bijections, so under a uniform hidden vector the honest data
is uniform and its distribution does not depend on the witness-dependent
constants. The PRG hypothesis supplying the uniform hidden vector is the
remaining input of the hidden-share step.

PRGHypothesis states that input explicitly: a party's random vector is
the binary sampling of the PRG stream of its seed with the salt and
execution tweak, so it is a fixed function of the seed; the named
predicate `PRGUniform` says that this function maps a uniform seed to a
uniform vector. It is the PRG assumption (or a random-oracle model for
the PRG), carried as an explicit theorem hypothesis, never as an
assumption-file entry. Under it the honest data of a uniformly seeded
hidden party is uniform and independent of the witness-dependent
constants.

SignatureData links the committed arithmetic's signature data to the
honest data map over the submitted field with its generator: the hashed
coefficients below the top are the honest data's middle component, and
the witness correction and plain check are its outer components, with
the other parties' packed layers, the zero-randomness hashed coefficients
and the slope terms as the constants. With the hidden party's vector the
PRG vector of its seed, the PRG hypothesis makes this data uniform over
the seed and independent of the witness.

PreparedData lifts that link to the executed signer: an executed
commitment over the submitted field with its generator has the committed
arithmetic's lines, auxiliary data and seeds, so the prepared signing
state's hashed coefficients, witness correction and plain check are the
committed arithmetic's with the random table of the committed seeds, and
the hidden party's vector at execution zero is the PRG vector of its
seed.

PreparedHonestData composes these: the prepared signing state's hashed
coefficients below the top, witness correction and plain check are the
honest data map, with the other parties' constants, the zero-randomness
coefficients and the slope terms, applied to the PRG vector of the hidden
party's seed at execution zero. With the PRG hypothesis this data is
uniform over that seed and independent of the witness; what remains for
the gap is the simulated transcript's matching form, the unqueried-seed
condition and the composition over the whole signing game.

DataSimulation is the simulation step at the data level: the honest
signer with the real witness and the simulator with a fake witness run
the same commitment program on the same salt, root and seeds, so their
revealed data are the honest data map with the same other-party
constants, mask and slope terms, differing only in the witness-dependent
constants; under a uniform hidden vector, and under the PRG hypothesis
with a uniform hidden seed, the two data distributions coincide. The
uniformity of the hidden leaf seed (an ideal-cipher step on unqueried
tree paths) is an explicit hypothesis, and the composition over the
signing game remains open.

FreshKeyUniform is the ideal-cipher input of the hidden leaf seed's
uniformity: the ideal cipher's fresh-input encryption is uniform over the
key's unused outputs, and for a key never used in the history every
output is unused, so the encryption of any input under a fresh key is
uniform over all blocks. The hidden leaf is the encryption, under its
parent seed, of a fixed tweak, so it is uniform whenever the parent seed
was never used as a key; the accounting of that event over the signing
game remains open.

LeafSeedUniform is the per-call form through the cipher layout: a seed's
expansion is the layout's output of the encryption, under the layout's key
image of the parent seed, of the layout's input image of the tweak; when
the parent key is fresh and the layout's output map carries the uniform
block to the uniform seed (the full layout does so trivially), the
expanded seed is uniform. The accounting of the fresh-parent-key event
over the signing game remains separate.

TruncatedLayoutUniform shows the Category III layout is output-uniform:
restricting a uniform bit vector to an injective set of coordinates is
uniform, so the 192-bit projection carries the uniform 256-bit block to
the uniform seed. Both submitted layouts are therefore output-uniform,
and the fresh-parent leaf seed is uniform for each.

CorrectionUniform completes the auxiliary pads: each positive execution's
transmitted correction is a value depending on the common accumulator and
that execution's other parties minus the execution's hidden vector, a
bijection of that vector (negation then translation), so a uniform hidden
vector gives a uniform correction whatever the constants. Every
transmitted auxiliary row and every hashed coefficient below the top is
thus padded by its own execution's hidden vector.

JointPads assembles the pads over all executions: execution zero's hidden
vector determines the revealed data through a bijection, and each positive
execution's correction is a constant (depending on execution zero's
vector) minus that execution's hidden vector, so the joint map from all
hidden vectors to the revealed data and corrections is a triangular
bijection (a shear); independent uniform hidden vectors give a uniform
joint transcript whatever the constants, in particular whatever the
witness. This closes the algebraic and probabilistic core of the
hidden-share step. What remains for the simulation gap is the game-level
lift: the salt, root and hash answers of the signing procedures, the
fresh-parent-key event for each hidden leaf (bounded by the ideal-cipher
query accounting) and the PRG hypothesis, composed over the signing game.

PosteriorLeafUniform is the per-call form of the leaf seed's uniformity in
the game's own model: the signing game answers cipher queries from a
family fixed at key generation, and the joint-law correspondence resamples
that family uniformly among those consistent with the history, so a
query's answer is the lazy query's; under a fresh parent key and an
output-uniform layout, the posterior family's answer to the leaf
expansion, through the layout's output, is a uniform seed.

HiddenLeafNode places the hidden leaf in the seed tree: every node below
the root is the layout's output of the family's encryption, under the
layout's key image of its parent, of the parent's tweak; and if the
expansion entries along a node's ancestry are recorded in a history, every
family consistent with that history computes the same node. So,
conditioned on the recorded history, the hidden leaf's parent is
determined, and the leaf's own expansion under a fresh parent key is a
uniform seed.

TreeEntries connects this to the commitment program: its tree expansion
records the expansion entries of every internal node it expands, at the
node's tree value, so every node within the expanded range has its
ancestry recorded in the cipher history; with the determination lemma,
the hidden leaf's parent and the leaf itself are fixed by the recorded
history of the commitment.

HiddenShareStep assembles the per-signature hidden-share step under the
posterior family: conditioned on a history that records the ancestry of
the hidden leaf's parent and in which the parent's key is fresh, every
consistent family computes the same parent, the leaf is a uniform seed,
its PRG vector is uniform under the PRG hypothesis, and the honest revealed
data of that vector is uniform whatever the witness-dependent constants.
Its two inputs are explicit: the fresh-parent-key event and the PRG
hypothesis.

FreshKeyProbability bounds the first input: for a uniform parent seed and
an injective key layout, the parent's key is used in a history only when
the parent is one of at most as many seeds as the history has entries, so
the probability that the parent key is not fresh is at most the history's
length over the number of seeds.

LayoutKeyInjective discharges the layout hypotheses for the submitted
parameters: the full layout's key is the identity and the truncated
layout's key is the zero extension, both injective, so the
fresh-parent-key bound holds for each layout, and both are output-uniform.
Every input of the per-signature hidden-share step other than the
fresh-parent-key event itself and the PRG hypothesis is thus discharged.

FreshHashUniform is the random-oracle input of the signing procedures'
coupling: the oracle answers an absent input by a uniform digest stored
at that input and a present input by its stored digest, so a fresh
answer's distribution is uniform whatever the input, and two fresh
queries at different inputs have the same answer distribution.

PublicHashFresh carries this into the shared world: the one-step run of a
single-hash program is the random oracle's query followed by the terminal
state, so the public oracle's digest answer at an absent input is the
uniform digest.

PublicMaskFresh adds the mask case: the public mask answer at an absent
input is the uniform mask component, so every public hash-side answer at
an absent input is uniform in its component.

SingleStepRuns records the elementary run facts of the shared world: a
finished program's run returns its value and leaves the world unchanged,
and a single cipher query's run returns the fixed family's answer
deterministically and records the entry.

RunFuel gives the fuel accounting of the traced run: with the
deterministic stepping procedure, a program bounded by a budget runs
identically under any larger budget, since each query consumes one unit
and the bound decreases while a finished program stops without consuming
the rest. This is the first lemma of the signing procedures' coupling,
whose remaining steps (the run-splitting lemma over a program bind, the
commitment program's prefix/tail decomposition, the lines-query
freshness, the fresh-parent chain and the composition over the game) are
listed in the plan.

RunBind is the run-splitting lemma: the traced run of a program bind with
the deterministic stepping procedure is the run of the first program
followed, from its final state, by the run of the continuation at its
value, with the collision flags combined; the first program's unused fuel
is absorbed by the continuation's bound through fuel monotonicity. The
signing procedures' runs can thus be split into a witness-free prefix and
a witness-dependent tail.

CommitDecomposition performs that split for the commitment program: the
witness-free prefix is the tree expansion, the leaf commitments, the row
hashes and the outer, auxiliary and mask queries, returning their results,
and the witness-dependent tail is the lines query and the committed
result; by associativity of the program bind the commitment program with
any witness is the prefix bound to that witness's tail, so the honest
signer and the simulator share the prefix exactly and differ only in the
tail.

CommitSplitRun applies the run-splitting lemma to that decomposition: the
prefix is bounded by the commitment budget less one and the tail by one,
so the traced run of the commitment program with the commitment budget is
the prefix's run continued by the tail's run, and in the shared world the
signer's commitment run with any witness is the common prefix run followed
by that witness's tail.

TailLinesDigest examines that tail: it is a single hash query at the
witness's lines input followed by the committed result, whose lines
digest is the query's digest answer; when the lines input is absent from
the table reached by the prefix, that digest is uniform whatever the
witness, so the honest and simulated signers' lines digests have the same
distribution whenever both lines inputs are fresh.

LinesMention turns that freshness into the charged mention event: the
lines query's window at offset eight is its auxiliary digest, so the
auxiliary digest is among the lines query's mentions, and the lines query
differs from the mask input by length. A lines input stored before the
auxiliary digest was answered is therefore a mention of that fresh
answer, the event already charged in the composed bound, and the lines
input cannot coincide with the prefix's own mask query.

QueryPrefixes separates the chain's queries by their byte prefixes: the
byte-bit encoding is injective and lists with different eight-bit
prefixes differ, so the lines query never coincides with the auxiliary
query, the outer string or a row query. Together with the length argument
for the mask input, the tail's lines query differs from every query the
prefix makes.

ThreeHashRun begins the prefix's trace shape at the support level: a
fresh hash step's run results are the continuation's runs at a stored
fresh answer with the entry recorded newest first, and the collision mark
changes no other field. Iterated over the prefix's last three queries
(outer, auxiliary, mask), this locates a stored lines input among the
older entries, which is the next step.

ThreeHashShape iterates that step: every run result of a program making
three hash queries at fresh inputs and finishing has the three answers
stored, the three entries recorded newest first on the trace, and the
finished state at the three answers. Applied to the prefix's outer,
auxiliary and mask queries, a lines input stored at tail time lies among
the entries older than the auxiliary query's, which is a mention of the
auxiliary digest.

StoredLinesMention proves that step generically: when the trace is a
newest entry over the auxiliary entry over older entries and the table
traces its stored inputs, a stored input differing from the two newest
inputs and mentioning the auxiliary answer has its entry among the older
ones, so the auxiliary answer is mentioned by an older input and the
mention event holds. Under the negation of that charged event the lines
input is fresh at tail time, whatever the witness.

PrefixLinesFresh applies this to the commitment's prefix: its last three
queries (outer, auxiliary, mask) run from the head's result; when they
are fresh, the result's trace is the three entries over the head's trace
and its state carries the three answers, and the table traces its stored
inputs; a lines input of the auxiliary answer stored at that point
therefore raises the mention event. Under the negation of that charged
event the lines input is absent after the prefix, whatever the witness.

PrefixHeadSplit splits the prefix itself into its head (tree expansion,
leaf commitments, row hashes) and its last three queries, with the head
bounded by the prefix budget less three and the last three queries by
three, so the prefix's traced run is the head's run continued by the
three queries' run; the stored-lines-input argument then applies to any
prefix run.

PrefixLinesFreshRun completes that application: a continuation result at
a finished head state is a run of the last three queries from the head's
result with the collision flag combined, so its state, table and trace
are those of that run; with the head's run invariants and the three
queries fresh at the head's result, a stored lines input of the auxiliary
answer raises the mention event after any prefix run.

ChainFresh turns two of the three prefix queries' freshness conditions
into the same charged event: a stored input whose entry is older than
the newest entry and which mentions the newest answer raises the mention
event, so after the outer query a stored auxiliary query of the outer
answer is a mention, and after the auxiliary query a stored mask input of
the auxiliary answer is a mention. Under the negation of the mention
event the auxiliary and mask inputs are fresh when the prefix asks them;
the outer input's freshness (a mention of a row hash) needs the head's
trace shape and remains open.

CollectLast starts that last piece: the collector over a list with a
final element is the collector over the initial segment bound to the
final call, which updates the accumulator at the final index; this
isolates the row hashes' last query, whose fresh run is the newest trace
entry after the head, so that a stored outer input (which mentions every
row hash) is a mention of that newest answer.

OuterFresh finishes the chain queries' freshness: the outer string and a
row query share a byte prefix but have lengths of different parity, so
they differ; the row hashes' collection splits at its last execution; and
after that last row query a stored outer string over the recorded row
hashes mentions the newest answer, raising the mention event. Under the
negation of the charged mention event every query of the prefix's chain
and the tail's lines query are fresh when asked, whatever the witness.

HeadLastSplit splits the head at its last row query: the head is its
initial part (tree expansion, leaf commitments, all row hashes but the
last) bound to the last row query, which updates the row hashes at the
last execution. With the fresh hash step this places the last row query's
entry newest after the head, where the outer string's mention argument
applies.

HeadLastRun runs the head split: the head's initial part is bounded by
the head budget less one and the last row query by one, so the head's
traced run is the initial part's run continued by the last row query's
run. A fresh last row query's run result has the newest trace entry at
that query with its answer recorded as the last row hash, so a stored
outer string over the recorded row hashes raises the mention event
(outer_mention_after_head). The remaining head queries (tree and
commitments) precede this entry, so the per-signature freshness statement
can now be assembled from the head, prefix-tail and tail splits.

TraceSuffix shows that the mention event persists along a run: a run's
trace is its starting log with new entries in front (the recorded log adds
at most one entry per hash step), so a prefix event raised on the starting
log is raised on the run's trace, and likewise for a continuation from a
finished state. The mention events raised after the head therefore carry
to the whole prefix run and to the tail's run, which the per-signature
freshness assembly needs.

PrefixTailOrMention steps through the prefix's last three queries (outer,
auxiliary, mask): each is either stored, in which case the stored-mention
lemmas raise the mention event on the current log and the suffix lemmas
carry it to the run's trace, or fresh, in which case the run continues
from the recorded entry. So the prefix run from a head result either
raises the mention event or finishes with the three answers, where a
stored lines input of the auxiliary answer raises the event. The only
remaining input to this disjunction is the outer string's stored case,
which the head's last-row shape supplies.

PrefixOrMention assembles the prefix run. A bounded program's run with
its bound as fuel finishes, so the head's initial part finishes; with the
last row query fresh at that result (an explicit condition, the named
candidate term for the leaf commitments' freshness, still to be bounded),
the head's result has the outer string's stored case raising the mention
event. The prefix run is the head's run continued by the last three
queries, so it either raises the mention event on its trace or finishes
with the head's data and the three answers, where a stored lines input of
the auxiliary answer raises the event. This is the per-signature
freshness statement for the witness-free prefix; the tail's lines query
then follows by the fresh lines-digest uniformity.

CommitLinesEvent carries the prefix statement into the tail. Each prefix
result either raises the mention event on its trace or finishes with its
data and the lines input of any witness fresh, and two continuations that
agree off an event have distributions within the event's probability. So
two witnesses' commitment runs (the honest and the simulated signer's)
have lines-digest distributions within the prefix's mention-event
probability, under the explicit last-row-query freshness condition.

PrefixMentionBound bounds the prefix's mention-event probability by the
prefix-dependent trap bound: the event's indicator on the starting log
plus, per query of the prefix budget, the current log length times the
mention-set size (tau + 2) over the digest count. Combined with the
commitment runs' comparison, two witnesses' lines-digest distributions
are within this explicit bound, under the last-row-query freshness
condition.

PrefixFromHead restates the prefix's event-or-fresh statement from the
head's initial result: a continuation from a finished result keeps the
run invariants, and from a head-initial result with the last row query
fresh, the rest of the prefix (the last row query, then the three
queries) either raises the mention event or finishes with the three
answers, where a stored lines input raises it. It also gives the bind
bound with pointwise costs, so the last-row-query condition can be
charged as a named event on the head's initial result.

CommitLinesEvents names the two events and removes the condition: the
row-stored event is the last row query stored at the head's initial
result, and the mention event is the prefix event on the prefix result.
Two witnesses' commitment runs (the honest and the simulated signer's)
have lines-digest distributions within the mention event's probability
plus the row-stored event's probability, with no further condition. The
mention event is bounded by the prefix trap bound; the row-stored event
is the named candidate term for the leaf commitments' freshness.

SignStep anchors the per-signature comparison: the honest scheme's
signing unfolds to a uniform salt and root, the commitment run, the PIOP
hash query at the prepared payload and the opening; a hash query at an
absent input binds like a uniform digest with the table programmed at
the input, and at a present input like the stored answer with the table
unchanged. The simulated signing draws the digest first and programs it
at the input, so the two differ only through the commitment run's
witness and the input's presence.

SignCompare names the input-present event (the honest preparation's PIOP
hash input already in the table) and defines the digest-first honest
signing, which draws the digest uniformly after the preparation and
programs it at the input when absent, giving no body when present. At an
absent input the honest signing and its digest-first form coincide, so
the honest signing is within the input-present event's probability of
the digest-first form. The simulated signing is the digest-first form
with a fake witness and the recomputed coefficients, which the next steps
compare.

SimulatedWith fixes the simulated signing's witness: the simulated signing
is the uniform mixture over the fake witness of the fixed-witness forms,
so the comparison with the honest signing proceeds at a fixed witness. It
also names the honest signer's payload consistency (for a solution
witness, the hashed coefficients of an executed commitment equal the
simulator's recomputed tuple at every hidden vector with nonzero
encoding) as the explicit hypothesis `PayloadConsistent`, a provable
PIOP completeness fact recorded for a later proof.

DigestFirstBody supplies the facts for the bodies: a ready candidate
attempt certifies the grinding check, a nonzero encoding of the hidden
vector and the candidate opening; a returned observation certifies these
at its counter; under payload consistency, for a solution witness and an
executed commitment, the honest prepared payload equals the simulator's
payload at the returned counter's hidden vector, so the two hash inputs
coincide. The retry-failure event (no returned observation at the
digest) is named.

DigestFirstVsSimulated compares the digest-first honest signing with the
fixed-witness simulated signing: under payload consistency and a
solution witness, at every salt, root, run result and digest with a
returned retry the two bodies coincide (same hash input, same opening,
same programmed table), so the digest-first honest signing is within the
retry-failure event's probability of the fixed-witness simulated
signing. With the input-present step this chains the honest signing to
the simulated signing at the honest witness, leaving the witness swap.

HonestToSimulated chains the steps: the honest signing is within the
input-present and retry-failure events of the simulated signing at the
honest witness, and with the witness swap of the fixed-witness simulated
signing carried as an explicit term (the commitment run's coupling for
the full output), it is within the two events plus the swap term of the
simulated scheme's signing. This is the per-signature statement the
composition over the signing game will iterate.

SignComparePost restates the per-signature comparison under any
continuation applied to the signing's output: the input-present step,
the retry-failure step, their chaining and the mixture over the fake
witness all hold with a continuation pushed through the binds, since the
bodies coincide off the events. This is the form the composition over
the signing game iterates: each signing call of the honest game is
replaced by the simulated one at the cost of the two events plus the
swap term.

RunHybrid is the hybrid over the game's signing calls: two schemes
agreeing off signing (same key generation, verification preparation,
signature digest and public oracle), with a per-call signing bound under
continuations for good secret keys, give runs within the fuel times the
bound, by induction on the fuel (each unit of fuel permits at most one
signing call; the other actions are identical).

CutHybrid extends the hybrid to the replay experiments: the cut run is
within the fuel times the per-call bound, the continuation and a fresh
branch within the snapshot's remaining fuel times it, the fork within
twice that, and the cut experiment within the fuel times it for good
generated keys. The event experiments of the composed bound are binds of
these, so the simulation gap follows once the per-call bound is uniform.

EventHybrid closes the hybrid at the event experiment: a saved snapshot
carries the cut's secret key and at most the cut's fuel, so for two
schemes agreeing off signing with a per-call bound for good keys, the
event experiments (cut, fork at the saved snapshot, evaluate the event)
are within three times the fuel times the bound. The composed bound's
simulation gap is this statement for the candidate scheme against the
witness-free simulator, with the per-call bound from the per-signature
comparison under uniform event bounds.

SimulationGap discharges the simulation-gap hypothesis of the composed
forgery bound from explicit uniform terms: the candidate scheme and the
witness-free simulator agree off signing, the game's generated keys
carry the public key with a solution witness (when the witness sampler
yields solutions), and for such keys the per-signature comparison gives
a per-call bound from uniform bounds on the input-present event, the
retry-failure event and the witness-swap term; the event-experiment
hybrid then bounds the honest random-index event experiment by the
simulated one plus three times the fuel plus one times that per-call
bound. The remaining inputs are the named explicit terms (the three
uniform bounds and the row-stored event inside the swap term) and the
payload-consistency hypothesis.

ForgeryBoundExplicit states the composed forgery bound with the
simulation gap discharged: under the composed bound's hypotheses,
payload consistency, a witness sampler yielding solutions and the three
uniform terms, the squared advantage is bounded by the simulated
scheme's event probabilities, the solver's success and the explicit
terms, with the gap three times the fuel plus one times the sum of the
three uniform terms.

TableSupport introduces hash tables supported by at most n inputs: a
query's table is the old table or its update at the queried input, so a
query adds at most one input; the honest signing performs one hash query
and the simulated signing programs at most one input, so both add at
most one. This invariant, carried along the game, is the size bound the
input-present event needs.

RunHybridInv refines the run hybrid to the table-support invariant: the
per-call signing bound is assumed only at worlds whose table is supported
by at most a global budget, and the invariant is carried along the run
(a query or a signing call adds at most one input, the public oracle
leaves the table), so the run bound holds when the starting support plus
the fuel is within the budget.

CutHybridInv carries the invariant through the replay experiments: a
saved snapshot's world is supported by the starting support plus the
cut's fuel, the continuation starts at the snapshot's world with one
programmed input, and the cut, continuation, branch, fork and cut
experiment hybrids hold with the per-call bound assumed only at
supported worlds, from empty initial tables.

SimulationGapInv restates the simulation gap with the per-call terms
assumed only at supported worlds: the event-experiment hybrid under the
invariant takes the budget twice the fuel plus one; for the candidate
scheme the honest signing adds at most one input for every secret key,
the simulated signing adds at most one, the public oracle keeps the
table and the generated keys start with empty tables, so the gap
hypothesis follows from the three uniform bounds assumed at worlds whose
table is supported by twice the fuel plus three inputs.

RunHybridGen and CutHybridGen generalize the invariant hybrids to an
abstract counted invariant on worlds: monotone in its count, growing by
one along a query, a signing call or a programmed input, kept by the
public oracle. The run, cut, continuation, branch, fork and cut
experiment hybrids hold with the per-call bound assumed only at worlds
satisfying the invariant at the budget, so the invariant can combine the
table-support count with the shared world's well-formedness, which the
per-signature events' bounds need.

SimulationGapGen instantiates the abstract invariant with the combined
one: the table supported by the count and the shared world well formed.
Both are carried by the candidate and simulated schemes (the candidate
services preserve well-formedness, the simulated signing's shared world
is a commitment run's world, queries and programmed inputs keep the
shared world, the generated keys start empty and well formed), so the
simulation-gap hypothesis follows from the three terms assumed only at
worlds satisfying the combined invariant at twice the fuel plus three.

HitCount gives the two ingredients of the input-present bound: a uniform
digest sent through an injective map into the inputs of a table
supported by n inputs is stored with probability at most n over the
digest count, and at a fresh lines input the tail's committed result,
through any function, is distributed as that function of the committed
result at a uniform lines answer.

InputPresentTail handles the input-present event over the tail: the
honest signing's hash input at a prefix result's data is an injective
function of the lines digest, so at a fresh lines input the tail stores
the input with probability at most the table's support count over the
digest count; a Boolean bind bounded off an event by a constant is
within the event's probability plus the constant.

InputPresentBound assembles the input-present bound: at a world with a
well-formed shared part and a hash table supported by n inputs, the
honest preparation's hash input is already present with probability at
most the prefix's mention term plus the row-stored term plus n over the
digest count, where the mention term is the mention event on the
witness-free prefix run over a uniform salt and root. The mention term
includes mention events already present in the starting trace (the
prefix trap bound carries their indicator), so a uniform bound needs the
event relative to the starting log; this is recorded as the next step.

NewMention defines the prefix event relative to a base log (the mentions
raised by the entries newer than the base, each checked against all
older entries): it persists under new entries, is monotone in the count,
splits at the base's head, and is raised by a stored input mentioning
one of the new entries' answers; its trap bound over a run is the sum of
the per-query steps alone, with no indicator for the base log. The
chain's stored-mention conclusions can be restated with it, which makes
the input-present bound's mention term uniform.

NewMentionChain restates the chain with the relative event: it persists
along runs and continuations, the auxiliary, mask, outer and lines
stored inputs raise it (their mentioning entries are the signing's own
fresh ones), and the prefix's last three queries either raise it or
finish fresh with the lines input's stored case raising it.

NewMentionPrefix carries the relative event through the head and the
prefix: a run's trace is at least as long as its starting log, after a
fresh last row query a stored outer string raises the relative event,
and the prefix run from a head-initial result either raises the
relative event or finishes with the lines input fresh unless it is
stored, which raises it.

InputPresentUniform restates the input-present bound with the relative
mention term, bounded by the per-query mention steps over the prefix
budget from the trace's length alone: at a well-formed world with its
table supported by n inputs, the honest preparation's hash input is
present with probability at most that sum plus the row-stored term plus
n over the digest count.

TraceLength shows that a run adds at most one trace entry per unit of
fuel and that the mention step is monotone in the trace length, so at a
world whose shared trace has at most T entries the input-present bound
reads: the mention steps over the prefix budget from T, plus the
row-stored term, plus the support count over the digest count. A
trace-length budget along the game, as a further component of the
counted invariant, makes this uniform.

TraceGrowth bounds the shared trace's growth along the game's services
(the honest and simulated signings add at most the commitment budget,
the public oracle at most one entry), and the generic hybrids now let
the public oracle advance the invariant's count, so a trace-length
budget can join the counted invariant.

SimulationGapTrace adds the trace-length budget to the counted invariant
(the commitment budget times the count), carried by every step of the
game, and discharges the input-present term of the simulation gap
uniformly: at worlds satisfying the invariant at the budget it is at most
the mention steps over the prefix budget from the trace budget, plus the
row-stored term's bound, plus the support budget over the digest count.
The simulation gap now takes this explicit value for the input-present
term, with the row-stored bound, the retry-failure bound and the
witness-swap term as the remaining explicit hypotheses.

PayloadBridge connects the honest commitment arithmetic to the verifier's
affine share matrix: the verifier's slope at every execution is the
random table's common accumulator (the transmitted corrections restore
it), so the share matrix at the hidden indices is the honest arithmetic's
corrected opening, and the honest witness and randomness lines evaluated
at the inverse challenge are the verifier's recomputed values. This is
the core of the payload-consistency hypothesis; the constant term's
vanishing for a solution witness and the assembly remain.

ConstantTermZero shows that the prover polynomial's constant term
vanishes for a solution witness: a binary at-most-one selector's unitary
check vanishes, the unitary layers vanish on binary at-most-one
selectors, and with the mux syndrome residual zero the composed prover
polynomial's constant term is zero. With the bridge this leaves only the
assembly of payload consistency.

PayloadConsistent discharges the payload-consistency hypothesis: under
the candidate encoding (the psi map of the Gray challenge row) and at
least one higher coefficient, for a solution witness the honest signer's
hashed coefficient tuple of an executed commitment equals the simulator's
recomputed tuple at every hidden vector with nonzero encoding. The
verifier's recomputed value is the prover polynomial's evaluation at the
inverse challenge, the polynomial has the bounded degree and a vanishing
constant term, so the restored tuple is the hashed one. The simulation
gap's remaining explicit terms are the row-stored bound, the
retry-failure bound and the witness-swap term.

ForgeryBoundTrace states the composed forgery bound with payload
consistency discharged and the input-present term explicit: under the
composed bound's hypotheses, the signer's candidate encoding, at least
one higher coefficient, a witness sampler yielding solutions, and the
row-stored, retry-failure and witness-swap bounds at worlds satisfying
the counted invariant, the squared advantage is bounded with the
simulation gap three times the fuel plus one times the sum of the
input-present term, the retry-failure bound and the witness-swap term.

CipherResample states the lazy-resampling law of the hidden cipher
family: the posterior family of a cipher history (uniform among the
families matching it), a shared program run against a posterior family
followed by any continuation of the result and the family equals the run
followed by a fresh posterior draw at the resulting history, and the same
law for the shared scheme's program runs (resampling a world's family
from its cipher history). This is the tool for restating the row-stored,
retry-failure and witness-swap bounds over the resampled family, since
at a fixed family they cannot hold: a family that maps every leaf key's
commitment input to a constant makes the last execution's row query a
constant string, so a per-world row-stored bound below one is false.

GameResample states the signature game under resampling of the hidden
state: with an idempotent resampling operator on the other-state that
commutes with the signing and public oracles (a run then a continuation
equals the run, a fresh resampling of the result, then the
continuation), the game run from a resampled world equals the run of the
scheme whose signing oracle resamples the world before signing, and when
key generation already yields a resampled world the terminal laws and
the advantages of the two schemes coincide (`run_resample`,
`terminalLaw_resample`, `advantage_resample`).

ChargeRun states the run hybrid with a world-dependent signing charge:
since a per-call bound that holds only on average over the hidden
cipher family cannot be a constant at every world, the hybrid charges
the current world's term at every signing query and sums the charges in
expectation along the run (`charge`, an expected cumulative sum defined
by recursion mirroring the run), and the run bound holds with the
expected cumulative charge of the first scheme's run in place of the fuel
times a constant (`run_le_run_add_charge`). The fork correlation through
the shared family is harmless for charges, since each branch's charge is
a marginal of that branch alone; the plan is to bound the expected charge
from a resampled world by the fuel times the per-call average bound using
the resampling law before each query.

ChargeExpect states the expected charge from a resampled world: the mean
of a function under a distribution with its bind, map, constant, sum,
monotonicity and exchange laws; an oracle's resampling law in joint-law
form (the output from a resampled world has the law of the output with
its world resampled afresh), with its continuation and mean forms; and
the bound that under the laws for the signing and public oracles, the
mean over the resampled world of the cumulative charge is at most the
fuel times the per-call average bound, the bound on the mean of the
charge over a resampled world at every invariant world within the
budget (`charge_mean_le`).

ChargeCut states the replay hybrids with the world-dependent charge:
the cut run's charge (`chargeCut`), a branch's charge from a saved
snapshot (the run from the snapshot's world with the programmed answer,
averaged over the answer; `chargeBranch`), the cut experiment's charge
(`chargeExperiment`) and the fork charge averaged over the second
scheme's cut experiment (`chargeFork`), with the cut, continuation,
fresh-branch, fork, cut-experiment and event-experiment hybrids within
these charges (`cut_le_cut_add_charge`, `continueWith_le_charge`,
`freshBranch_le_charge`, `forkAt_le_charge`, `cutExperiment_le_charge`,
`eventExp_le_charge`).

ChargeCutExpect states the expected replay charges from a resampled key:
the cut run obeys the resampling law with the saved snapshot's world
resampled (`cut_postLaw`), the expected cut charge from a resampled
world is at most the fuel times the per-call average bound
(`chargeCut_mean_le`), and from key generation yielding a resampled
world the cut experiment's charge is at most the fuel times the bound
(`chargeExperiment_le`) and the fork charge at most twice that
(`chargeFork_le`). With the event-experiment hybrid, the gap between the
two schemes' event experiments is three times the fuel times the
per-call average bound, the bound on the mean of the per-call term over
the resampled world, which is the form in which the row-stored,
retry-failure and witness-swap terms can be bounded.

SharedResample states the shared scheme's resampling laws in the forms
the charged hybrids use: binds agreeing on the support are equal, a
run's cipher history extends the starting history, an impossible
history's posterior is the identity family, so the program-run
resampling law holds without the possibility hypothesis
(`runProgram_resample'`); resampling is idempotent (`resample_idem`);
sampling before an oracle preserves the law (`postLaw_sample`); an
oracle that runs a program on the inner world and post-processes the
result with the outer hash table obeys the law (`postLaw_run`); and the
empty history's posterior is the uniform family (`posterior_nil`), so a
key generation drawing a uniform family yields a resampled world.

CandidateResample states that the candidate scheme's oracles obey the
resampling law: the honest signing is a uniform salt and root, the
commitment run on the inner world and a post-processing from the outer
hash table (the signature-level query and the body; `honest_sign_shape`,
`honest_postLaw`); the simulated signing is four uniform draws, the
commitment run and a pure post-processing (`simulated_sign_shape`,
`simulated_postLaw`); the public oracle is a one-step run and a pure
answer (`publicOracle_postLaw`); and key generation draws a uniform
family at the empty history, which is the posterior there, so it yields
a resampled world (`keygen_resampled`). These are the hypotheses of the
expected-charge bounds for the real and simulated schemes.

SimulationGapMean states the simulation gap with the cipher-dependent
terms in mean form (`hgap_of_mean`): the per-world charge of a signing
query is the prefix's mention steps, the row-stored term, the support
term, the retry bound and the witness-swap slack of the world
(`chargeOf`); the counted invariant ignores the family, so resampling
keeps it (`invT_resample`); and under the hypotheses that the mean of
the row-stored term over the resampled world is at most εRow and the
mean of the swap slack at most εS at every invariant world within the
budget, the random-index event experiment is within three times the
fuel plus one times the input-present term plus εR plus εS of the
simulated scheme's. This replaces the per-world row-stored and
witness-swap hypotheses, which are unsatisfiable below one at a fixed
family, by hypotheses that hold on average over the hidden family.

ForgeryBoundMean states the composed forgery bound with the mean-form
gap (`forgery_le_mean`): under the composed bound's hypotheses, the
signer's candidate encoding, at least one higher coefficient, a witness
sampler yielding solutions, the retry-failure bound at invariant worlds,
the witness-swap slack of each world, and the bounds on the means of the
row-stored term and of the swap slack over the resampled world, the
squared advantage is bounded by the simulated scheme's event
probabilities, the solver's success and the explicit terms, with the
simulation gap three times the fuel plus one times the sum of the
input-present term, the retry-failure bound and the witness-swap mean.
This is the current end-to-end statement of the reduction.

PosteriorFresh states fresh-input answers under the posterior family:
the posterior family's answer to a query is the lazily sampled answer
(`posterior_answer`), so at a fresh input of a key the answer satisfies
an event with probability at most the event's count over the remaining
block count (`posterior_event_le`), hits a target with probability at
most the inverse of the remaining block count (`posterior_target_le`),
and lies in a finite set with probability at most the set's size over
the remaining block count (`posterior_mem_le`). These are the per-call
facts for the row-stored mean bound.

HeadCommitSplit splits the head's initial part at its last commitment
call: the leaf pairs end with the last execution's last leaf
(`lastPair`), the commitments' collection splits there
(`commit_collect_split`), and the head's initial part is the tree, the
commitments but the last and the last leaf's first cipher call
(`headBefore`), bound to the last leaf's second cipher call completing
the last commitment and the partial row hashes (`headAfter`), with exact
budgets, so its traced run is the run before the last call continued by
the run after it (`runFixed_headInit_split`). The last call's output is
the block whose freshness under the posterior family gives the row-stored
bound.

RowsSupport states the facts about the partial row hashes used to reduce
the row-stored event: after a run of hash calls over a list followed by
a pure finish, every defined input of the resulting table was defined
before or is one of the calls' inputs (`rows_defined`), and a run of a
program bound to a pure finish that ends finished returns the finish of
some value (`runFixed_bind_done`), with the procedure's steps at a hash
call, a cipher call and a finished program as rewriting lemmas.

RowStoredReduce reduces the row-stored event to the last commitment
block: the last leaf pair lies in the last execution (`lastPair_eq`),
the commitments after the last call are those before with the last
completed by the layout's output of the family's answer (`lastBlock`,
`commitsWith`), the row-stored event after the run following the last
call says the last execution's row query is defined in the starting
table or equals another execution's row query (`rowStored_reduce`), and
that row query is injective in the last block
(`lastRowQuery_injective`), so the event is the last block's membership
in a set fixed before the last call.

RowStoredCount counts the last blocks that hit a fixed set: the cipher
outputs whose row query lies in a finite set number at most the fiber
bound of the layout's output map times the set's size, under any
finiteness instance (`count_hits`), so under the posterior family at a
fresh input the last execution's row query lies in the set with
probability at most that count over the remaining block count
(`posterior_row_le`).

RowStoredAfter states the row-stored event after the last call: a map's
truth is monotone on the support and a constant map's truth is the
indicator (`map_true_mono`, `map_const_true`, `map_true_le_indicator`),
binds are pointwise monotone at a value; the last call is stale in a
history when the history has its key and input (`stale`); the fixed
set is the trace's inputs with the other executions' row queries
(`fixedSet`, size at most the trace's length plus the execution count),
which do not depend on the last block (`rowQuery_other`); and when the
split point's table is traced by its trace, the row-stored event after
the last call puts the last execution's row query in the fixed set
(`rowStored_mem`).

RowStoredPosterior bounds the row-stored term's mean over the resampled
family (`rowTerm_mean_le`): a run's cipher history is matched by its
family and grows by at most the fuel, a family in the posterior's
support matches the history, and at a split point whose table is traced
by its trace, the run after the last call under the posterior family has
the row-stored event with probability at most the indicator of the last
call's staleness plus the fiber bound times the fixed set's size over
the remaining block count (`after_le`). Hence the mean is at most the
staleness term (`staleTerm`: over the salt, the root and the run before
the last call under the posterior family, the probability that the last
call's key and input already occur in the split point's history) plus
the fiber bound times the trace length plus the budget before the last
call plus the execution count, over the remaining block count. The
staleness term is the fresh-parent-key chain's remaining target.

TreeRunEntries states the tree expansion's run step by step: the
expansion through one more step is the expansion so far bound to the
node's expansion step (`expandStep`, `treeThrough_succ`), so its traced
run with the doubled budget is the run so far continued by the step's
run (`runFixed_tree_succ`); an expansion call bound to a pure finish
runs to exactly the two calls' entries and the finish of the two
outputs (`expand_run_support`); and every entry the tree expansion
records has as input the layout's input of a cipher input at an address
within the expanded range (`TreeInput`, `tree_entries`). This is the
first piece of the fresh-parent-key chain bounding the staleness term.

TreeStepFresh states one expansion step under the posterior family: the
keys of a history (`keysOf`), a tree good for a key set up to a step
(`Good`: no node's key within the expanded range lies in the set), the
count of outputs whose key through the layout lies in a set
(`count_key_hits`), the posterior key bound at a fresh input
(`posterior_key_le`), the freshness of both calls expanding a node whose
key is outside the starting keys (`step_inputs_fresh`: the tree's
earlier calls use other addresses, and the starting history does not use
the key), the step's union bound (`child_key_le`, `step_le`: twice the
fiber bound times the set's size over the remaining block count), and
the goodness step (`good_step`).

TreeGoodInduction states the tree's goodness along the expansion under
the posterior family (`tree_good_le`): over a family drawn from the
posterior of the starting history, the tree expansion's result fails to
be good for the starting history's keys with probability at most the
indicator of the root's key being among them plus the number of steps
times the step bound, by induction over the steps with the family
resampled at each step (`treeOf`, `notGood`, `expandStep_run_eq`).

CommitEntries states the commitment calls' run: the commitment calls over
a list of leaf pairs record only entries whose inputs are the layout's
inputs of cipher inputs at the leaf-count-shifted offsets of listed pairs,
over the starting history (`commitOf`, `commitEntry`, `CommitInput`,
`commit_entries`); the leaf pairs are without duplicates, so a pair of
the initial segment differs from the last pair (`allPairs_nodup`,
`ne_lastPair_of_mem_dropLast`); and the commitment addresses lie below
twice the leaf count (`commit_address_lt`).

StaleNotGood states that a stale last call forces the tree not to be
good: the run before the last call is the tree expansion continued by
the commitment phase (`commitPhase`, `runFixed_headBefore_split`), the
commitment phase records the other pairs' entries and the first call's
entry (`commitPhase_support`), at inputs differing from the last call's
input, and the tree records inputs at addresses below the leaf count, so
an entry with the last call's key and input lies in the starting history,
putting the last leaf's key among the starting keys (`stale_notGood`),
and the staleness event's probability is at most the not-good event's
(`stale_le_notGood`), under the injectivity of the layout's input and the
cipher-input bounds (26 ≤ λ, four times the leaf count ≤ 2^24).

StaleTermBound bounds the staleness term (`staleTerm_le`): a uniform
draw satisfies a predicate with probability its count over the type's
size (`uniform_event_eq`), the seeds whose key lies in a set number at
most the key map's fiber bound times the set's size (`count_key_root`,
`root_key_le`), and the staleness term is at most the root term (the
key map's fiber bound times the number of starting keys over the number
of seeds) plus the steps times twice the fiber bound times the number of
starting keys over the remaining block count. With the row-stored mean
bound, the row-stored term is now explicit: the staleness term's bound
plus the fiber bound times the trace length, budget and execution count
over the remaining block count.

RowBoundExplicit states the row-stored term explicitly: the explicit
row bound (`rowBound`: the key map's fiber bound times the starting
cipher entries over the number of seeds, plus the steps times twice the
key-through-output fiber bound times the starting entries over the
remaining block count, plus the output fiber bound times the trace
length, budget and execution count over the remaining block count), the
row-stored term's mean at an invariant world within it
(`rowTerm_mean_le_explicit`), and the composed forgery bound with the
row-stored term discharged (`forgery_le_row`), under the layout's input
injectivity, the three fiber bounds, the cipher-input bounds, and the
named hypothesis that every invariant world's cipher history is matched
by some family and bounded in length (to be discharged by extending the
counted invariant).

CipherInvariant states the cipher-history invariant: a shared world is
cipher-consistent when its family matches its cipher history
(`Consistent`); a program run keeps consistency and grows the history by
at most the budget (`runProgram_cipher`); the honest and simulated
signings add at most the commitment budget of cipher entries and the
public oracle at most one, all keeping consistency (`honest_sign_cipher`,
`simulatedSign_cipher`, `publicOracle_cipher`); and the extended counted
invariant (`InvC`: the counted invariant, consistency and a
cipher-history budget) is kept by every step, holds at key generation,
is kept by resampling, and yields the named cipher-history hypothesis
(`invC_mono`, `invC_query`, `invC_update`, `invC_pub`, `invC_honest`,
`invC_simulated`, `invC_keygen`, `invC_resample`, `invC_game`).

SimulationGapCipher states the simulation gap in mean form under the
extended invariant (`hgap_of_cipher`) and the composed forgery bound
with the row-stored term explicit and no cipher-history hypothesis
(`forgery_le_cipher`): under the composed bound's hypotheses, the
signer's candidate encoding, at least one higher coefficient, a witness
sampler yielding solutions, the layout's input injectivity, the three
fiber bounds, the cipher-input bounds, a remaining-block budget, the
retry-failure bound and the witness-swap slack with its mean bound at
worlds satisfying the extended invariant, the squared advantage is
bounded by the simulated scheme's event probabilities, the solver's
success and the explicit terms, with the simulation gap three times the
fuel plus one times the sum of the input-present term at the explicit
row bound, the retry-failure bound and the witness-swap mean. This is
the current end-to-end statement of the reduction.

MeanHybrid states the run hybrid in mean form (`run_le_run_mean`): with
the per-call signing bound stated for a fixed continuation with the
world resampled before the call (the mean over the resampled world of
the first scheme's signing bound to the continuation within a constant
of the second scheme's), the resampling is moved past each call by the
oracles' resampling laws and past each hash query by the hash-table
update, so the means of the two schemes' runs from a resampled world are
within the fuel times the constant. This is the form in which the
witness-swap term can be bounded.

RunWorld states the game run with its final world (`runW`): the run is
its first component (`run_eq_runW`), and under the oracles' resampling
laws (signing, public oracle and verification preparation) the run with
world from a resampled world has the law of the run followed by a fresh
resampling of its final world, with an attempt's embedded world replaced
alike (`withWorld`, `runW_postLaw`). This is the tool for the fork
identity in which the family is drawn at the end from the combined
history.

CandidatePrepLaw proves that the candidate scheme's verification
preparation obeys the resampling law (`verifyAnswer`,
`prepareVerification_postLaw`): a bodiless signature is rejected without
touching the world, and a signature with a body runs the verification
program on the inner world and post-processes its answer purely, so the
generic run shape applies. With the signing and public-oracle laws this
completes the hypotheses of the run-with-world law for the candidate
scheme.

Continuation 222 records a finding (audit/HUMAN_REVIEW.md): the
mean-form swap bound over every continuation is unsatisfiable too, since
the signer records the hidden path in the world's logs and a
continuation reading them recovers the witness. The swap holds only
against oracle-access continuations; the corrected route is an
identical-until-bad bound against the hidden path with a pruned world,
with the hidden entries named explicitly. No module was added.

HiddenEntries names the objects of that route (`pathAddresses`,
`pathKeys`, `entriesAt`, `pruneAt`, `pruneWorld`, `hiddenEntries`): the
hidden path of a leaf is the leaf and its proper ancestors below the
root (`mem_pathAddresses_iff`), its parent keys are the layout's keys of
the path nodes' parents, a history splits into its entries at a list of
keys and the pruned history (`matches_iff`), a possible history stays
possible when pruned, and every parent key of the hidden path is fresh in
the history pruned at them (`freshKey_pathKeys`), which is the fresh-key
input of the hidden-share step.

PosteriorPrune proves that the posterior factorises over keys
(`uniform_map_apply`, `matches_update`, `exchange`, `card_fiber_mul`,
`posterior_coord_eq`, `posterior_answer_eq_prune`): exchanging the
coordinates at a key outside the pruned keys between a candidate of a
world and one of its pruned world is a bijection between the fibers, so
the coordinate at such a key, and the answer to any request at it, have
the same law under the posterior of the history and of its pruned
history. This is the step that lets a continuation's queries at other
keys be answered alike in the world and in its pruned world.

PrunedRun proves the agreement of a run with its run from the pruned
history until a query hits the pruned keys (`posterior_cipher_step`,
`pruneResult`, `touches`, `run_le_prune`): against the posterior family a
cipher step is the answer followed by a fresh posterior draw at the
extended history, so by the factorisation the two runs are coupled step
by step at keys outside the pruned ones, and at a pruned key the pruned
run's result records the hit; the mean of a bounded function of the
pruned result under the run from the history is at most its mean plus the
touching indicator under the run from the pruned history.

PrunedRunReverse proves the reverse agreement (`prune_le_run`): the
mean of a bounded function under the run from the pruned history is at
most its mean of the pruned result under the run from the history plus
the pruned run's touching term, by the same coupling. Together the two
directions make the run and its pruned run interchangeable up to the
touching term.

SharedPrune lifts both directions to the shared scheme's program runs
(`pruneShared`, `touchesW`, `FamilyFree`, `runProgram_le_prune`,
`prune_le_runProgram`): the shared world pruned at a list of keys keeps
its family and other fields, and a program run from the resampled world
and from the resampled pruned world agree up to the touching term for
functions of the result that do not read the family, which every
continuation that resamples before reading satisfies.

GamePrune proves the game-level agreement (`pruneW`, `touchesG`,
`FamilyFreeG`, `FamilyFreeT`, `PruneLaw`, `Grows`, `touchesG_runW`,
`runW_le_prune`): an oracle's prune law says its call from the resampled
world and from the resampled pruned world agree up to the touching of
its result, a growing oracle keeps touching along the run, and under the
oracles' resampling laws, prune laws and growth the mean of a
family-free function of the pruned terminal and world under the game run
from the resampled world is at most its mean plus the final touching
indicator under the run from the resampled pruned world. The oracles'
prune laws for the candidate scheme and the touching term's bound are
the next targets.

The game-level statement carries the consistency invariant (the world's
family matches its history, `Consistent`, `Keeps`), which resampling
restores from possibility and which the oracles keep. PruneLawRun gives
the generic forms the oracles instantiate (`runOracle`, `pruneLaw_run`,
`grows_run`, `keeps_run`, and the sampling and pure-answer closures): an
oracle that runs a program on the shared world and post-processes from
the outer hash table obeys the prune law by the shared lift, grows by the
run's history extension, and keeps consistency by the run's matching.

CandidatePrune instantiates them for the candidate scheme's oracles
(`publicOracle_hash_eq`, `publicOracle_mask_eq`, `publicOracle_cipher_eq`,
`prepareVerification_none_eq`, `prepareVerification_some_eq`,
`honest_pruneLaw`, `honest_grows`, `honest_keeps`, `simulated_pruneLaw`,
`simulated_grows`, `simulated_keeps`, `publicOracle_pruneLaw`,
`publicOracle_grows`, `publicOracle_keeps`, `prepareVerification_pruneLaw`,
`prepareVerification_grows`): each oracle is program-shaped, and the
simulated scheme shares the public oracle and the verification
preparation with the candidate scheme. With these the game-level
agreement applies to both schemes; the touching term's bound is the
next target.

CandidateGamePrune states that agreement for both schemes
(`candidate_runW_le_prune`, `simulated_runW_le_prune`): from a
consistent world, the game run from the resampled world is below the
run from the resampled pruned world plus the final touching indicator,
for every family-free function bounded by one. What remains for the
witness swap is the touching term's bound (the internal path keys by an
exchange argument on the family, the leaf's key under an explicit
seed-hiding hypothesis on the pure PRG), the equal law of the witness and
fake signings in the pruned world, and the events' insensitivity to the
hidden entries.

HiddenKeys names the keys to prune for a leaf (`hiddenKeys`,
`mem_hiddenKeys`, `root_key_mem_hiddenKeys`, `leaf_key_mem_hiddenKeys`,
`parent_mem_pathAddresses`, `pathKeys_subset_hiddenKeys`,
`freshKey_hiddenKeys`, `pruneAt_hiddenKeys_pruneAt_pathKeys`): the keys
of the root, of the leaf's proper ancestors and of the leaf itself, since
the leaf's commitment is a cipher call at its key; the path's parent keys
are among them and every hidden key is fresh in the history pruned at
them.

NodeExchange defines the measure-preserving map behind the hidden
path's independence from the pruned data (`swapNode`,
`swapNode_involutive`, `swapNodeEquiv`, `matches_swapNode`,
`swapCandidates`, `posterior_swapNode`): given a parent key, two block
values and two keys, the exchange post-composes the permutation at the
parent key with the transposition of the two values and swaps the
permutations at the two keys; it is an involution fixing every other key,
so it preserves matching of a history in which the three keys are fresh
and leaves the posterior of such a history invariant.

TreeExchange computes the seed tree under that exchange (`parentKey`,
`nodeBlock`, `exchanged`, `nodeTweak_ne_of_sibling`, `node_exchanged`):
the exchanged family computes the same tree except at the exchanged node,
which takes the new value, since the ancestors are untouched, the
sibling keeps its value, the node's children are the old children (the
old key's permutation now sits at the new key), and every other node uses
a key the exchange fixes; the goodness of the tree (its nodes' keys
distinct from the three exchanged keys) is the explicit hypothesis that
the fresh-key counting will supply.

TreeRunClosed gives the tree expansion's run in closed form
(`treeHistory`, `tree_run_eq`): the expansion makes only cipher calls, so
its run against a fixed family is the point at the seed tree's
increasing-index run and the two recorded calls of every expanded node
over the starting history. The candidate opening reveals leaf seeds and
hidden commitments only, so an internal path node's value appears in the
signer's output only through its recorded calls, which pruning removes;
this is what makes the exchange argument apply to the internal keys.

TreeHistoryExchange carries the exchange through the expansion's run
(`exchangedKeys`, `run_exchanged`, `treeHistory_exchanged`): the seed
tree's run through the exchanged family is the run through the family
with the node's value replaced on the allocated addresses, and the
recorded entries pruned at the three exchanged keys coincide, since the
node's own calls move from the old key to the new one, its parent's calls
are at the parent key, and every other node's calls are unchanged.

RunCongr adds two generic facts about program runs (`QueriesIn`,
`queriesIn_bind`, `answer_congr`, `runFixed_congr_family`,
`runFixed_bind_done`): a program whose cipher requests all have keys in a
set runs identically against two families agreeing on that set, and a
program followed by a pure finish runs as the program with the finish
applied to its final state. These compare the commitment phase under the
exchange: its calls are at the leaves' keys, which the exchange fixes,
and the exchanged tree enters only its final value.

CommitPhaseExchange splits the commitment program into the expansion
and a rest (`commitFour`, `commitTail`, `commitRest`, `commitProgram_eq`)
and proves the rest's two properties (`leafKeys`, `queriesIn_commitRest`,
`setTree`, `commitRest_update`): it queries the cipher only at the
leaves' keys, and with an internal node's value replaced it is the rest
followed by a pure finish setting that node in the committed tree.

RunHistoryShift records that a run depends on its starting cipher
history only by appending to it (`appendHistory`,
`runFixed_history_shift`): the run from a history is the run from the
empty history with the history appended to the result's. With it the
commitment runs under the exchange, which start from the two expansions'
histories, are compared through their pruned histories.

CommitRunExchange assembles the commitment run under the exchange
(`restBudget`, `commitBudget_eq`, `commitRest_bounded`, `commitRun_eq`,
`commitRest_congr`, `baseTree`, `exchanged_tree_eq`, `exchanged_leafKeys`,
`commitRun_exchanged`): the commitment run is the rest's run from the
expansion's tree and history; under the exchange of an internal node the
expansion's tree is the tree with the node replaced, the rest becomes the
rest with a finish setting the node, it queries only the leaves' keys
where the exchanged family agrees with the family, and the starting
history only shifts the result's. So the commitment run under the
exchanged family is the base run (the rest from the empty history) with
the node set and the exchanged expansion's history appended.

CommitPruned records what the exchange leaves unchanged
(`treeHistory_exchanged_subset`, `openKey_setTree`, `attempt_setTree`,
`payloadOf_setTree`, `bodyOf_setTree`): the expansion's recorded entries
pruned at any key list containing the three exchanged keys coincide, and
the candidate signature's payload and body do not read an internal node
of the committed tree, since the payload is the lines and the hashed
coefficients and the body opens the key at the leaves only.

CommitViewExchange states the commitment run's view under the exchange
(`stripFamily`, `commit_view_exchanged`): for a post-processing of the
committed value that does not read an internal node, the commitment run
followed by it, viewed with the world's family stripped and its cipher
history pruned at a key list containing the exchanged keys, has the same
law under the exchanged family and under the family.

HonestViewExchange checks the candidate post-processings
(`internal_ne_leaf`, `honestPost_setTree`, `simPost_setTree`): the honest
one (the signature-level query and the body) and the simulated one read
the committed value only through its payload, its key at the leaves, its
seeds, lines and auxiliary data, so neither reads an internal node, and
the commitment run's view law applies to both signings.

FiberCounting is the generic counting behind the hidden path's
independence from the pruned view (`mean_label_eq`,
`mean_label_eq_of_involutive`, `sum_indicator_le_one`, `sum_mean_label`,
`sum_label_le`, `label_mass_le`): under a distribution invariant under a
bijection that fixes a weight on a label value's fiber and carries that
value to another, the two values' weighted masses coincide, so a value's
weighted mass is at most the total weight over the number of values it
can be exchanged with.

FiberCountingBad allows bad exchange targets (`mean_split`,
`sum_bad_mass`, `label_mass_le_of_bad`): when a label value's mass is
exchanged with every other value except a bounded number of bad targets
per point, the value's mass is at most the total weight over the number
of values less that bound. This is the form the node exchange needs,
since a target block is bad when its key is one of the tree's keys or it
is the sibling's block.

FiberCountingSided gives the one-sided fiber exchange, which needs no
inverse (`mean_label_le_of_map`): under an invariant distribution, the
mass of a label value restricted to the good points is at most the mass
of a target value whenever the map carries good points of the value to
the target without lowering the weight; and pruning a history at a key
none of its entries uses prunes it at the remaining keys
(`pruneAt_cons_of_no_entry`), which lets the views pruned at their own
hidden keys be compared through a common key list.

RunKeys records the keys a run uses (`runFixed_keys`): a program
querying within a key set records, over its starting history, only
entries whose keys lie in the set; with the rest's query locality this
bounds the commitment run's recorded keys by the tree's keys.

CommitHistoryKeys makes that explicit (`treeHistory_key`,
`commitRun_keys`): the expansion records the keys of the expanded nodes
and the rest queries only the leaves' keys, so every entry the
commitment run records over its starting history is at the key of a node
of the tree.

HiddenKeysExchange relates the hidden keys of the exchanged family to
the family's (`pruneAt_congr_mem`, `le_of_mem_pathAddresses`,
`mem_hiddenKeys_exchanged`): pruning depends on a key list only through
its members, and when the exchanged node lies on the hidden path, the
exchanged family's hidden keys with the old key added have the same
members as the family's hidden keys with the new key added.

OwnViewExchange proves the view each family prunes at its own hidden
keys the same under the exchange of a path node (`ownView`,
`ownView_cons_of_fresh`, `ownView_congr_mem`, `ownView_exchanged`):
neither history has entries at the other family's key of the node (the
tree's keys are good and the starting history is fresh there), so each
view prunes as well at the other key, the enlarged key lists have the
same members, and the common view is the commitment run's view under the
exchange.

PosteriorNodeBound is the posterior bound on a hidden node's block
(`OnFiber`, `Good`, `Bad`, `exchangeTo`, `goodness`, `label`,
`label_exchangeTo`, `bad_card_le`, `label_mass_le_of_bad_on`, `BadT`,
`posterior_node_bound`): against the posterior family, for a weight at
most one that is invariant under the exchange of the node's block on the
good fiber, the weighted mass of the fiber in which the parent is a given
seed and the node's block a given block is at most the total weight over
the number of blocks less the bad targets, which number at most the
fiber bound times the keys of the history, the parent and the tree, plus
one.

HonestNodeBound instantiates it for the commitment view (`Fresh`,
`weight`, `weight_exchanged`, `honest_node_bound`): the weight is the
mean of a bounded view function under the own-keys view, restricted to
the families with a given parent that are fresh at the node, and it does
not decrease under the exchange on the good fiber. KeyWeightSum sums the
hit weights over all blocks (`card_hits_le`, `sum_hit_weight_le`): the
sum over blocks of the probability that a continuation records the
block's key is at most the fiber bound times the expected number of
recorded entries. NodeTouchBound combines them (`hitWeight`, `GoodAll`,
`Hit`, `expectedNew`, `goodHit_le_sum`, `pair_bound`, `node_touch_bound`):
summing the posterior bound over the parent seed and the block, the
probability that a good and fresh family's node is touched by the
continuation is at most the fiber bound times the expected number of
recorded entries over the number of blocks less the bad targets.

The goodness hypotheses of the exchange chain now range over positive
addresses only, since address zero is the tree's unused totalization
cell. PathUnion gives the union bound over the hidden path (`pathSet`,
`touch_le_sum`): touching the hidden keys is at most the sum over the
root and the path of touching the node's key. TreeDistinct names the
tree's keys being fresh and pairwise distinct on the allocated addresses
(`Distinct`, `goodAll_of_distinct`), which makes every internal node good
and fresh. SiblingKeys bounds the two outputs of a fresh key at distinct
inputs sharing a layout key (`sibling_keys_le`) by the fiber bound over
the remaining blocks, the step the distinctness bound needs.

TreeDistinctBound proves that bound (`DistinctTo`, `keysTo`,
`notDistinct`, `distinct_step`, `treeHistory_key_le`,
`tree_distinct_le`): along the expansion, each step's two children must
have keys outside the starting history's keys and the keys of the nodes
so far, and distinct from each other, so the tree's keys are not fresh
and pairwise distinct with probability at most the root's indicator plus
the steps times the step bound (two fiber bounds times the keys so far
over the remaining blocks, plus one fiber bound over them).

DistinctBridge carries that bound to the family's tree
(`distinct_of_distinctTo`, `distinct_family_le`). The root needs its own
exchange, since it has no parent: RootExchange exchanges the root for
another seed while swapping the permutations at the two roots' keys
(`rootExchanged`, `node_root_exchanged`), RootHistoryExchange carries it
through the expansion's run and entries (`rootKeys`,
`run_root_exchanged`, `treeHistory_root_exchanged`), and ProductSwap
gives the product invariance for the joint draw of the root and the
family (`product`, `product_map_eq`, `uniform_map_swap`).

Continuation 256 simplified the root exchange: KeySwap swaps the
permutations at two keys directly (`swapKeys`, `swapKeys_involutive`,
`matches_swapKeys`, `posterior_swapKeys`), so the root exchange needs no
dummy key and the root keys are two. RootCommitRun carries it through the
commitment run (`root_exchanged_tree_eq`, `root_exchanged_leafKeys`,
`commitRun_root_exchanged`), RootCommitView through the commitment view
pruned at the root keys (`commit_view_root_exchanged`,
`mem_hiddenKeys_root_exchanged`), and RootOwnView through the view pruned
at a family's own hidden keys (`ownView_root_exchanged`), the root's
analogue of a path node's own-view exchange.

Continuation 257 proved the root's bounds against the joint draw of a
uniform root and the posterior family: RootPosteriorBound
(`rootDraw`, `GoodR`, `BadR`, `exchangeR`, `labelR`, `count_root_hits`,
`badR_card_le`, `rootDraw_map_exchangeR`, `posterior_root_bound`) gives
the posterior bound on the root for weights that do not decrease under
the root exchange, with the bad targets counted by a fiber bound on the
layout's key (an explicit hypothesis, `hfiberR`); RootHonestBound
(`FreshR`, `weightR`, `weightR_exchanged`, `honest_root_bound`) applies it
to the commitment view's own-keys view; RootTouchBound (`hitWeightR`,
`GoodAllR`, `HitR`, `expectedNewR`, `sum_root_hit_le`, `seed_bound`,
`root_touch_bound`) sums it over the seeds into the touching bound at the
root, the root's analogue of the node touching bound.

Continuation 258 prepared the sum over the hidden leaves: HiddenTuple
names the hidden keys of all executions (`hiddenKeysAll`,
`mem_hiddenKeysAll`) and bounds touching them by the sum over the
executions (`touchAll_le_sum`); HiddenSlice views the commitment run
pruned at keys chosen from the signature and the family (`viewPruned`)
and writes its mean as the sum over the choices of the fixed-choice views
with the view factor (`mean_viewPruned_eq_sum`), and restricts a
continuation to one choice (`sliceCont`, `sliceNew`) so that the hit
weights and the recorded length carry the choice's indicator
(`hitWeight_slice`, `hitWeightR_slice`, `length_slice`); the touching
bounds at a fixed choice then sum to the bound for the view-dependent
pruning.

Continuation 259 made the own-view exchange independent of the key list:
OwnViewExchangeGen proves it for any key list chosen from the family that
contains the moved keys and whose enlarged lists have the same members
(`ownView_exchanged_of_mem`, `ownView_root_exchanged_of_mem`);
HiddenKeysAllExchange gives these facts for the hidden keys of all
executions when the exchanged node lies on some execution's hidden path
(`lt_of_mem_path`, `key_mem_hiddenKeysAll`, `mem_hiddenKeysAll_exchanged`,
`mem_hiddenKeysAll_root_exchanged`); OwnViewExchangeAll instantiates them
(`ownView_exchanged_all`, `ownView_root_exchanged_all`), so the view
pruned at the hidden keys of all executions is the same under the
exchange of a node on any hidden path and under the root exchange.

Continuation 260 abstracted the node and root bounds over the view:
ViewNodeBound (`weightV`, `weightV_exchanged`, `honest_node_boundV`,
`HitV`, `expectedNewV`, `pairV_bound`, `node_touch_boundV`) and
ViewRootBound (`weightVR`, `weightVR_exchanged`, `honest_root_boundVR`,
`HitVR`, `expectedNewVR`, `seedVR_bound`, `root_touch_boundVR`) take any
view chosen from the family (and the root) whose law is the same under
the exchange on the good fiber, so the touching bounds apply to the view
pruned at the hidden keys of all executions.

Continuation 261 instantiated them and split the touching probability:
AllViewBounds names the view pruned at all executions' hidden keys for a
fixed tuple (`viewAll`), proves its invariance under the node and root
exchanges (`viewAll_exchanged`, `viewAll_root_exchanged`) and derives the
touching bounds (`node_touch_bound_all`, `root_touch_bound_all`);
TouchSplit names the view pruned at the signature's own hidden keys
(`viewAct`), the touching probability (`touchAll`), the expected recorded
length (`expLen`) and the leaf hit (`leafHit`), splits a leaf's path into
the root, the leaf and the internal path (`innerPath`,
`sum_pathSet_split`) and bounds the touching probability by the sum over
the tuples and the executions of the root hit, the leaf hit and the
internal path hits for the continuation restricted to the tuple
(`touchAll_le`).

Continuation 262 assembled the touching bound against the joint draw of
a uniform root and the posterior family: TouchAssembly (`mean_rootDraw`,
`GoodTree`, `goodAllR_of_distinct`, `leafTerm`, `sum_expected`,
`root_term`, `node_term`, `touch_assembly`) shows that on the pairs whose
tree keys are fresh and distinct, the probability that a continuation of
the view pruned at the signature's hidden keys records one of them is at
most the executions times the root rate plus the internal path depth
times the node rate, times the expected number of recorded entries, plus
the leaf term (the hits at the hidden leaves, kept explicit for the
seed-hiding hypothesis). The rates are the fiber bounds over the number
of seeds less the bad targets.

Continuation 263 closed the bound over all pairs: TouchTotal proves the
internal path depth is at most the binary logarithm of the leaf count
(`pathAddresses_length_le`, `innerPath_card_le`), bounds the probability
that the tree's keys are not fresh and distinct under the joint draw
(`bad_tree_le`, from the distinctness bound and the uniform root's key
hit), and combines them (`touchAll_le_one`, `touch_total`): the touching
probability is at most the distinctness failure plus the executions times
the root and depth-weighted node rates times the expected recorded
length, plus the leaf term.

Continuation 264 began the bridge from the signing call to the game:
TreeOfMatches shows that the expansion records both children's entries of
every parent (`childEntry`, `childEntry_even_mem`, `childEntry_odd_mem`),
so any family matching a history containing them computes the same tree
(`node_eq_of_matches`) and the same hidden keys of all executions
(`mem_hiddenKeysAll_of_matches`): the pruning keys do not depend on the
family actually used once it is resampled consistently with the history.

Continuation 265 proved that the commitment run records the expansion's
entries (CommitHistoryContains: `commitRun_contains`, `commit_contains`),
so any family matching a history extending the run's final history
computes the signature's hidden keys (`mem_hiddenKeysAll_commit`). It
also corrected a registration slip: the modules of continuations 262–264
(TouchAssembly, TouchTotal, TreeOfMatches) had been built and indexed in
the ledgers but their import lines were missing from the library root, so
validations 262–264 did not cover them; they are imported now and the
validation of continuation 265 covers them.

Continuation 266 proved the per-call bridge: SignBridge names the
signing-shaped oracle (the commitment run on the inner world, then the
post-processing with the outer hash table; `commitOracle`), its
resampling law and consistency (`commitOracle_postLaw`,
`commitOracle_consistent`), the output's hidden keys read from the output
world and the signature (`outKeys`) and their invariance under a
consistent resampling (`outKeys_congr`), and shows (`sign_bridge`) that
from a resampled start the call followed by the game run evaluated on
the result pruned at the output's keys is below the call followed by the
resampled pruned run with the touching indicator, for any game run with
the pruned-run agreement.

Continuation 267 restated the hybrid chain and the composed bounds with
the per-call swap taken only for the game's own continuations:
ChargeRunCont (`run_le_run_add_charge_cont`) and ChargeCutCont
(`SignRun`, `SignCut`, `cut_le_cut_add_charge`, `continueWith_le_charge`,
`freshBranch_le_charge`, `forkAt_le_charge`, `cutExperiment_le_charge`,
`eventExp_le_charge`) prove the replay hybrids from per-call bounds for
the simulated scheme's run and cut continuations, and SimulationGapCont
(`hgap_of_cipher_cont`, `forgery_le_cipher_cont`) gives the simulation gap
and the composed forgery bound with the witness swap hypotheses in that
shape, which the identical-until-bad route can discharge, in place of the
unsatisfiable swap over every continuation.

Continuation 268 added the reverse agreement (GamePruneReverse:
`mean_one_sub`, `prune_le_runW`): the game run from the resampled pruned
world is below the run from the resampled world on the pruned result plus
the touching indicator under the pruned run. It follows from the forward
agreement applied to the complementary event, since both evaluations are
probabilities; it is the fake side's half of the witness swap.

Continuation 269 instantiated the reverse agreement for the candidate and
simulated schemes (CandidateGamePruneReverse: `candidate_prune_le_runW`,
`simulated_prune_le_runW`) and proved the mean-form run and cut hybrids
with the per-call bound for the game's continuations (MeanHybridCont:
`SignRunMean`, `SignCutMean`, `run_le_run_mean_cont`,
`cut_le_cut_mean_cont`): the per-call swap holds only on average over the
hidden family, so the chain must carry it in mean form, with the world
resampled before each call, as the mean-form run hybrid does.

Continuation 270 proved that the cipher history is only a log
(HistoryShiftGame: `shiftG`, `ShiftLaw`, `shiftLaw_run`,
`shiftLaw_sample`, `shiftLaw_pure`, `shiftT`, `runW_shift`): appending
entries to a game world's inner history changes nothing in a
program-shaped oracle's answers nor in the game run with its final world,
beyond the appended suffix. This is what lets the fork's second branch
start from the first branch's final world, so that every continuation of
a signing call is a game run.

Continuation 271 instantiated the shift law for the candidate and
simulated schemes (CandidateShift: `honest_shiftLaw`,
`simulated_shiftLaw`, `publicOracle_shiftLaw`,
`prepareVerification_shiftLaw`, `candidate_runW_shift`,
`simulated_runW_shift`) and named the restored fork (ForkRestore:
`KeepsFamily`, `runW_family`, `freshBranchW`, `freshBranchW_fst`,
`restore`, `forkAtR`): the first branch with its final world, the family
resampled given its final history, and the second branch from the
snapshot's tables with that family and history.

Continuation 272 added the supporting facts for the fork's restoration
(ForkRestoreLemmas: `runW_history`, `eq_setFamily_of_mem_resampleW`,
`shiftBranch`, `finalize_shiftT`; ForkRestoreShift: `runW_postLaw_mean`,
`freshBranch_eq`, `freshBranch_shift`, `setFamily_eq_shiftG`,
`restore_eq_shiftG`): the game run only extends the history, a resampled
world is the world with its family replaced, a fresh branch from a world
with entries appended to its history is the branch with its attempt's
history shifted, and the resampling law of the run with its final world
holds in mean form.

Continuation 273 proved the restoration itself (ForkRestoreEq:
`forkEventR`, `common`, `shared_eq_common`, `restored_eq_common`,
`fork_restore_eq`): from a resampled snapshot world, for an event
insensitive to the second branch's history suffix, the shared fork and
the restored event fork have the same probability. It also added the
mean-form hybrid of the run with its final world for its continuations
(MeanHybridContW: `SignRunWMean`, `runW_le_runW_mean_cont`), which the
restored fork's first branch needs.

Continuation 274 moved the event's family to the end of the fork
(ForkRestoreEnd: `setFamilyT`, `setFamilyBranch`, `finalize_setFamilyT`,
`runW_attempt`, `freshBranchW_family`, `mean_resampleW_restore`,
`right_end_resample`, `forkEventE`, `forkEventR_eq_E`) and restated the
event experiment with the end-resampled restored fork (EventRestore:
`pmf_bool_ext`, `eventExpE`, `eventExp_eq_E`): from a resampled key, the
game's event experiment equals the one whose fork runs the first branch
with its final world, resamples, runs the second branch from the
snapshot's tables with the first's family and history, resamples again,
and evaluates the event at that family. In this form every continuation
of a signing call is a game run and the event reads no live family.

Continuation 275 began the mean-form hybrid of the restored fork
(MeanForkCont: `runW_inv`, `freshBranchW_le_mean`): the counted invariant
holds along the run with its final world, with the verification
preparation's preservation as a hypothesis, and a fresh branch with its
final world from a resampled snapshot world is within the remaining fuel
times the per-call bound for continuations of the run with its final
world.

Continuation 276 completed the mean-form hybrid chain over the restored
fork: MeanForkCont2 (`forkEventE_mean`, `forkEventE_le_mean`) replaces
the second branch and then the first, within twice the remaining fuel
times the per-call bound; MeanEventCont (`eventBranch`,
`eventExpE_eq_branch`, `eventExpE_le_mean`) composes the cut hybrid and
the fork hybrid into the event experiment's bound, three times the fuel
times the per-call bound, from a resampled key. CandidateKeepsFamily
instantiates family keeping for the candidate and simulated oracles, and
InvCExtra (`invC_restore`, `invC_prep`) extends the counted invariant to
the restored world and to the verification preparation when the
verification budget is at most the commitment budget.

Continuation 277 composed the bound in mean form: ForgeryEvents
(`forgery_le_simulated_events`) takes the simulation gap per event, and
SimulationGapMean2 (`εCall`, `EventOK`, `call_mean`, `signRunW_mean`,
`signCut_mean`, `hgap_mean`, `εSim`, `forgery_le_mean`) states the composed
forgery bound with the per-call witness swap in mean form for the
simulated scheme's run and cut continuations, the retry bound, and each
event's insensitivity to the second branch's history suffix and to the
attempts' embedded families as named hypotheses, at the budget three times
the fuel plus two.

Continuation 278 found that the swap's discharge cannot read the
evaluation at the pruned result with a family-free evaluation, since the
hybrid's continuation (the fork's resampling, finalization, restoration
and second branch) reads the history; GamePruneGen (`PruneCompat`,
`one_sub_le_iff`, `pruneCompat_compl`, `runW_le_prune_gen`,
`prune_le_runW_gen`, `runW_pruneCompat`) generalises the pruned-run
agreement to prune-compatible evaluations with a touching functional, read
at the actual result in both directions, and shows the game run preserves
the compatibility.

Continuation 279 closed prune compatibility under the steps of the
hybrid's continuations (PruneCompatClosure: `mean_resampleW_resampleW`,
`pruneCompat_free`, `pruneCompat_resample`, `pruneCompat_sample`,
`pruneCompat_restore`, `pruneCompat_update`, `finalize_withWorld_table`,
`pruneCompat_finalize`): a family-free and prune-free evaluation is
compatible with the touching indicator, and compatibility is kept by
resampling before the evaluation, averaging over a sample, restoring the
family and history into a base world, updating the hash table, and the
terminal's finalization.

Continuation 280 assembled the fork continuation's compatibility
(ForkPruneCompat: `pruneCompat_congr`, `rightEval`, `leftEval`,
`forkCont`, `leftTouch`, `forkTouch`, `forkCont_pruneCompat`): after the
first branch's run, the resampling, finalization, second branch from the
restored snapshot and end-resampled event are compatible with pruning at
any keys, given the event's compatibility read at the second branch's
final world and its insensitivity to the checked terminals' embedded
worlds, with the touching functional composed from the second branch's.

Continuation 281 restated the mean-form hybrid chain for compatible
continuations (MeanHybridCompat: `SignRunWMeanP`,
`runW_le_runW_mean_contP`, `freshBranchW_le_meanP`,
`rightCont_pruneCompat`, `forkProc`, `forkCont_pruneCompat'`,
`forkProc_inv`, `innerEval`, `stepA_core`, `stepA`, `stepB`,
`forkEventE_le_meanP`): the per-call bound is taken only for
continuations compatible with pruning at every key list, with the touching
functional of a process on the result keeping the invariant within an end
budget, and the run, fresh-branch and fork hybrids supply that
compatibility for their own continuations from the event's compatibility
at the end.

Continuation 282 added the cut with its final world (CutWorld: `cutW`,
`cutW_fst`, `withWorldC`, `touchesG_cutW`, `PruneCompatC`,
`pruneCompatC_compl`, `cutW_le_prune_gen`, `prune_le_cutW_gen`), since the
replay's cut forgets the final world on its ended outcomes without an
attempt and a touching functional of its results could not remember the
touching; and the cut hybrid in mean form for compatible continuations
over it (MeanCutCompat: `SignCutWMeanP`, `cutW_le_cutW_mean_contP`).

Continuation 283 proved the event branch's compatibility after the cut and
the event experiment's hybrid for compatible continuations
(EventCutCompat: `cutProc`, `branchEval`, `fork_pruneCompat`,
`innerEval_hist`, `forkProc_hist`, `forkProc_touches`, `cutProc_touches`,
`eventBranch_pruneCompatC`, `cutProc_inv`, `eventExpE_le_meanP`), with the
cut's per-call bound restricted to reachable cuts within the budget; the
event is required not to read the snapshot world's cipher history and to
be false without a fork result.

Continuation 284 discharged the two per-call witness swaps (SwapDischarge:
`prepareVerification_keeps`, `sigHidden`, `simulatedSignWith_eq`,
`prunedMean`, `touchInner`, `touchMean`, `swap_core`, `signRunW_meanP`,
`signCutW_meanP`): the fixed-witness simulated signing is a uniform salt,
root and digest followed by the signing-shaped oracle, and for any
compatible continuation the call with the honest witness is within the two
touching terms of the call with a fake witness, given the pruned
equality of the two signings (the law of the signature with the resampled
world pruned at the output's hidden keys does not depend on the witness)
as a named hypothesis and the touching bound as a hypothesis still to be
instantiated.

Continuation 285 composed the forgery bound with the per-call swaps
discharged (SimulationGapCompat: `EventOKP`, `eventOK_left`,
`eventOK_right`, `eventOK_shift`, `TouchR`, `TouchC`, `PrunedEqual`,
`hgap_meanP`, `εSimP`, `forgery_le_meanP`): the squared advantage is
bounded by the simulator's event probabilities, the solver's success and
explicit terms, under the pruned equality of the two signings, the two
touching bounds, the retry bound and each event's requirements (false
without a fork result, insensitive to the snapshot world's cipher history
and to the checked terminals' embedded worlds, compatible with pruning at
the end).

Continuation 286 found that the assembled touching bound's hypothesis of
post-processing invariance under setting any internal node of the
committed tree is false for the simulated post-processing: its opening
reveals the co-path of the hidden tuple. For a hidden tuple fixed by the
digest the invariance is needed only at the root and on that tuple's
internal paths, and the other tuples' slices vanish; TouchConst
(`hitVR_const_ne`, `hitV_const_ne`, `root_term_const`, `node_term_const`,
`touch_assembly_const`, `touch_total_const`) restates the bound so.

Continuation 287 corrected that finding: the candidate opening reveals the
leaves other than the hidden ones and the commitments, not a co-path, so
it never reads an internal node of the tree, and the simulated
post-processing is invariant under setting any internal node after all
(TouchPrep: `openKey_setTree`, `simPost_setTree`); the constant-tuple
restatement stands but is not needed. TouchPrep also shows that the
signing-shaped oracle with the simulated post-processing keeps the
extended invariant (`invC_commitOracle`) and that pruning keeps it
(`invC_pruneW`).

Continuation 288 identified the swap's touching term with the touching
total's probability (TouchIdentity: `postT`, `hiddenT`, `contT`, `newT`,
`touchInner_eq_touchAll`): for a fixed salt and digest, the call on the
resampled world followed by the touching functional from the resampled
pruned world, over the uniform root, is the touching probability of the
joint root-and-family draw with the view of the commitment run and the
continuation that resamples the family and runs the game's process; and
bounded the continuation's expected recorded length by the commitment
budget times the end budget (`invC_setFamily`, `expLen_le`).

Continuation 289 proved the two touching bounds of the swap discharge
(TouchBound: `εTouch`, `card_keysOf_le`, `mem_rootDraw`, `touchMean_le`,
`cutW_inv_sim`, `LeafR`, `LeafC`, `touchR_of`, `touchC_of`): the swap's
touching term is at most a uniform bound built from the touching total
with the history's key count replaced by the commitment budget times the
count and the expected recorded length by the budget times the end
budget, under the layout's fiber bounds and size conditions, with the
leaf term's bound as a named hypothesis. The per-call hypotheses now carry
the world's count so that the run's end stays within the budget.

Continuation 290 composed the final forgery bound (ForgeryFinal:
`εTouch_mono`, `touchR_mono`, `forgery_le_final`): the squared advantage
of a chosen-message forger against the candidate scheme is bounded by the
witness-free simulator's event probabilities, the solver's success and
explicit terms, under the pruned equality of the two signings (seed
hiding), the leaf-term bounds, the retry bound, the layout's fiber bounds
and size conditions, and the eight events' requirements. The events'
insensitivity to the attempts' embedded worlds was weakened to the
family and the cipher history, which the mask event (reading the
embedded world's inner hash table) can satisfy.

Continuation 291 discharged the events' requirements for seven of the
eight events (EventRequirements: `pruneCompat_const`, `rightEval_eq`,
`eventOKP_of`, `eventOKP_maskAfter`, `eventOKP_notSeparated`,
`eventOKP_slopeWin`, `eventOKP_zeroChallenge`, `eventOKP_schwartzZippel`,
`eventOKP_batchingBad`, `eventOKP_rsdSolved`), which read only the
attempts' signatures and bodies, the embedded worlds' inner hash tables
and the snapshot's input and inner hash table; the seed-collision event
reads the snapshot's family and the branches' cipher histories, so its
probability enters the composition directly (`hgap_final`,
`forgery_le_final'`). The final bound's remaining named hypotheses: the
pruned equality (seed hiding), the leaf-term bounds, the retry bound, the
seed-collision bound, and the layout's fiber bounds and size conditions.

### The final statement (continuation 291)

`EventRequirements.forgery_le_final'` bounds the squared advantage of a
chosen-message forger against the candidate scheme (minus the digest
inverse) by the forger's budget squared times the sum of: the
witness-free simulator's probabilities of the mask-after-fork,
non-separation, slope-game, zero-challenge, Schwartz–Zippel and batching
events, the solver's success on the syndrome-decoding instance, eight
copies of the per-event simulation term (three times the fuel plus one,
times the per-call constant: the input-present term, the row-stored
bound, the retry bound and twice the uniform touching bound) plus the
seed-collision bound, and the mention, collision and digest terms of
the fork-and-extract core. Everything in it is proved except the
following, which are explicit hypotheses:

- the data-level closeness of the two signings (`DataClose`, from
  continuation 315 in place of the pruned closeness, itself in place of
  the unsatisfiable exact `PrunedEqual`): with the hidden leaves' blocks
  replaced by a uniform tuple, the honest signing's sliced data is
  within an explicit slack of the fake signing's, on the trees with fresh
  and distinct keys (the ideal-model honest-verifier zero knowledge at
  uniform hidden blocks, a statement about the signing program's data);
- the leaf hiding (`LeafHide`, from continuation 316 in place of the
  leaf-term bounds): with the tuple's leaves replaced by uniform blocks,
  the continuation records the key of the replaced block at an execution
  with probability at most δ on average;
- the retry bound: the candidate retry not returning at the digest;
- (named at continuation 331) the expansion-dependent simulator terms:
  the mask-after-fork, non-separation, seed-collision, zero-challenge,
  Schwartz–Zippel and batching events of the witness-free simulator are
  bounded by the named constants of `SimulatorTermBounds`
  (`NamedSimulatorTerms.forgery_le_final_named`); they depend on the
  challenge and batching expansions' model, like the retry bound;
- (discharged at continuation 330) the hardness term: the solver's
  success is the syndrome-decoding success on the key generation's
  instance (`ForgeryRSD.forgery_le_final_rsd`), the extracted witness
  with zero mux residual and unitary selectors giving a weight-`w`
  solution of `instanceOf H' y` (`SolutionRegular.isSolution_sd`);
- (discharged at continuation 329) the slope-game term: the
  simulator's slope event is replaced by the mask trap, the witnessed
  pair and the unseen match, each bounded in the real experiment, so the
  term is the explicit slack `(fuel+1)·2·εTrap + εWitOf + unseenCost` under
  the verifier layout's identity (`ForgerySlope.forgery_le_final_coll_S`);
- (discharged at continuation 320) the seed-collision bound: a recorded
  seed collision in the real experiment is now the explicit pair cost
  `εCollOf`, under the verifier layout's injective input and key maps
  and its output map's fiber bound (`ForgeryColl.forgery_le_final_coll`);
- the layout's input injectivity and the fiber bounds of its key and
  output maps, with the size conditions on the security parameter
  (26 ≤ λ, four times the leaf count ≤ 2^24, and the budget-dependent
  conditions);
- the structural hypotheses carried since the composed bound: the
  verifier's middle, the encoding injectivity facts, the candidate
  encoding, the budgets, at least one higher coefficient, the witness
  sampler's solutions, and the verification budget within the commitment
  budget.

Continuation 332 is the review pass: the status summary above, the
plan's open lines, the review ledger's hypothesis record and the
standalone assumption interface's docstring are reconciled with the
current final statement (no new theorem; the assumption interface still
declares no axiom, and `SDHardness` is still not consumed).

Continuation 331 names the expansion-dependent simulator terms
(`NamedSimulatorTerms`): the witness-free simulator's mask-after-fork,
non-separation, seed-collision, zero-challenge, Schwartz–Zippel and
batching event probabilities are bounded by the explicitly named
constants `εMask εSep εSeed εZero εSZ εBatch` of the hypothesis
`SimulatorTermBounds` (the expansion-dependent events, carried like the
retry bound by the user's decision), and
`NamedSimulatorTerms.forgery_le_final_named` is the current final
statement: its right-hand side is explicit in the named constants, the
syndrome-decoding success and the proved slacks.

Continuation 330 ties the solver's success to syndrome decoding
(`MuxSelect`, `SolutionRegular`, `ForgeryRSD`): the mux tree with unitary
binary selectors reads one leaf per chunk, the vector with a one at each
chunk's selected leaf is a weight-`w` solution of the key generation's
instance `instanceOf H' y` whenever the extracted witness has zero mux
residual and unitary selectors (`isSolution_sd`), so the solver's
success is at most the regular syndrome-decoding success `rsdSuccess`
(the solver returning a syndrome-decoding solution of the public
instance), and `ForgeryRSD.forgery_le_final_rsd` is the current final
statement, with the hardness term stated on the key generation's
instance.

Continuation 329 discharges the slope-game term (`ForgerySlope`): the
four final statements are regenerated with the slope summand replaced by
the explicit slack (the trap cost over the cut run, the witnessed-pair
slack and the unseen cost) under the verifier layout's identity, and
`ForgerySlope.forgery_le_final_coll_S` is the current final statement.
Its remaining simulator terms are the mask-after-fork, non-separation,
zero-challenge, Schwartz–Zippel and batching events of the witness-free
simulator (the expansion-dependent events, left explicit), and the
solver's success.

Continuation 328 regenerates the composed bound's skeleton with the
three events in place of the slope event (`SlopeChainReduction`): the
union event, the fork-to-union and random-index steps, the forgery
skeleton, the extraction split and the per-event simulation gaps, the
mask trap, the witnessed pair and the unseen match staying in the real
experiment where they are bounded directly.

Continuation 327 bounds the unseen match in the real experiment
(`ForkUnseenBound`): the event (now with the named seed's two recorded
halves) implies, at the family resampled at the end of the restored
second branch, the shared game's unseen event on the final history,
whose probability is the unobserved-key bound at that world; the random
event experiment is at most the unseen cost at the counted invariant's
largest history length (`unseenFork_le`).

Continuation 326 bounds the witnessed pair in the real experiment
(`ForkWitnessedBound`): through the family-dependent fork bound, the
event under the snapshot's family is at most the restored chain's pair
mass of the second branch's final history, hence the snapshot's pair
mass and two branches' costs (`fork_witnessed_bound`), and over the random
event experiment at most the slack `εWitOf` (three times the fuel plus
one, times one call's pair cost with the identity projection,
`witnessedFork_le`).

Continuation 325 proves the fork bound for family-dependent events
(`PairForkFamily.fork_family_bound`): an event that, at the snapshot with
a family, implies a predicate of that family on the union of the two
attempt histories (a predicate reading the bodies, the union as a set
and the family) has probability at most the restored chain's mean of the
predicate under the family resampled at the end of the second branch;
the union of attempt histories is the same set for the plain and the
restored second branch.

Continuation 324 bounds the mask trap in the real experiment
(`SlopeTrapBound`): a program run raises the trap on its world's trace
with probability at most the trap cost `εTrap` (execution pairs times
budget times `2^-s`, each hash answer's mask being uniform), the
candidate services obey the service bound, and the random event
experiment of the trap is at most the fuel plus one times twice the
cost at the uniform budget (`slopeTrap_le`).

Continuation 323 covers the stored-mask slope event at the fork
(`SlopeCoverFork`): on a well-formed snapshot without the mention and
digest-collision events, with both branches' histories matching the
snapshot's family, the event forces a mask trap on the snapshot's trace
(`slopeTrap`), a witnessed pair in the union of the histories
(`witnessedFork`) or an unseen seed matching a named seed's two
commitment halves (`unseenFork`); the good fork then implies the named
events with these three in place of the slope event
(`good_implies_events_D`).

Continuation 322 derives the stored-mask slope event from the good fork
(`SlopeChainFork.good_implies_events_C`): the fork-slope lemma, the
uniform-slope predicate and the extraction lemma now also expose the
chain's auxiliary query, the equal commitment arrays and the salt
equality, and under the identity layout the first branch's claim is
built with the recomputed row hashes and root, chained in the snapshot's
table, with every seed's expansion recorded (the revealed seeds by the
first branch's reconstruction, the hidden ones by the second's).

Continuation 321 opens the slope-game milestone (`SlopeEventSetting`):
the shared slope game's setting read from the signer and the verifier,
the identity layout's commitments and expansion entries in the shared
game's form, and the stored-mask slope event `slopeWinC` (the first
branch's claim chained in the table, every seed's expansion recorded in
the union of the two histories, and two executions' slopes differing but
equal under the mask stored at the claim's auxiliary digest), which
implies the existential-mask event used so far. The plan: derive this
event from the good fork, cover it by the trace trap, the mention and
collision events, the seed collision and the unseen match, and bound
those in the real experiment.

Continuation 320 discharges the seed-collision bound
(`SeedCollisionWitness`, `SeedCollisionBound`, `ForgeryColl`): a recorded
seed collision is witnessed, under the verifier layout's output
projection and its transport of the seed-pairing companion, by every
family matching the union of the two attempt histories
(`seedCollision_witnessed`, with the layout's input and key maps
injective); the real experiment's probability of the event is at most
`εCollOf` (three times the fuel plus one, times one call's pair cost at
the counted invariant's largest history length), by the cut and fork
bounds from the key generation's empty history (`seedCollision_le`);
and `ForgeryColl.forgery_le_final_coll` is the composed forgery bound with
this explicit slack in place of the seed-collision hypothesis. The
remaining named hypotheses are the data-level closeness, the leaf hiding
and the retry bound, with the layout, size and structural conditions.

Continuation 319 carries the pair mass through the fork (`PairFork`):
an event that, whenever it holds, is witnessed by every family matching
the union of the two branches' attempt histories has probability at most
the snapshot's pair mass and two branches' costs (`fork_pair_bound`). The
plain fork is read in its common form, the second branch from the
empty-history base is shifted either by the snapshot's history (the
plain branch) or by the first branch's final history (the restored
branch), and the event on the former is at most the pair mass of the
latter's final world (`event_le_shifted`).

Continuation 318 carries the pair mass through the candidate scheme's
oracles and the game run (`PairOracles`, `PairRun`): from a resampled
world satisfying the counted invariant, the honest signing oracle, the
public oracle and the verification preparation raise the mass by at most
one call's cost (`callCost`), and the game run, the cut run and a fresh
branch with its final world raise it by at most one cost per step
(`runW_pair_bound`, `cut_pair_bound`, `freshBranchW_pair_bound`), the
oracles' resampling laws inserting a fresh resampling after every call.

Continuation 317 begins the discharge of the seed-collision bound
(`PairMass`): the posterior pair mass of a cipher history is the
probability, under the posterior family of the history, that two recorded
entries with distinct keys and a common input have equal projected
outputs and equal projected companion outputs; a shared program run from
a resampled world raises this mass by at most the adaptive pair cost of
its budget (`runProgram_pair_bound`, the single-run paired-cipher bound
read through the resampling law). The seed-collision event is a pair
collision in the union of the two fork branches' histories; the planned
chain carries the mass through the oracles, the cut run and the two
branches (the second from the first's final history, with the family
resampled), giving an explicit value for `εColl`.

Continuation 316 discharges the leaf-term bounds from the named leaf
hiding (`LeafSliced`, `LeafTermBound`): the leaf hit is the sliced data
of the functional recording the leaf's key, and the mixture bound turns
the hiding at uniform blocks into the leaf term. `ForgeryHide.forgery_le_final_hide`
is the composed forgery bound with the data-level closeness and the leaf
hiding as its cryptographic hypotheses.

Continuation 315 closes the off-hit chain (`OffHitClose`): the pruned
closeness follows from the pre-call hit term and the named data-level
closeness, and `ForgeryData.forgery_le_final_data` is the composed
forgery bound with the data-level closeness in place of the pruned
closeness. The remaining named hypotheses are the data-level closeness
(ideal-model zero knowledge at uniform hidden blocks), the leaf-term
bounds, the retry bound, the seed-collision bound and the layout,
size and structural conditions.

Continuation 314 assembles the off-hit chain at fixed draws under the
named data-level closeness hypothesis (`OffHitAssembly`): the honest
side with the closeness and the fake side over the two tuples.

Continuation 313 records that the tuple sum's slack would scale with
the number of tuples, and resolves it: the hidden tuple of a simulated
signature is determined by the digest (`TupleOfDigest`), so at most two
tuples carry mass.

Continuation 312 proves the two sides of the off-hit chain at fixed
draws (`OffHitChain`): the honest side bounded above through the mixing
family, the fake side bounded below relative to the tuple probability.

Continuation 311 proves the mixture lower bound relative to a bound
function (`LeafMixtureGen`) and the off-hit setup (`OffHitSetup`): the
posterior form of the off-hit pruned mean, the bounds by one, the tuple
probabilities, and the distinct-tree and hit terms over the uniform
draws.

Continuation 310 proves the sliced data's invariance under the exchange
at a tuple's leaf, with the leaves replaced by given blocks
(`SlicedInvariance`), the form the uniform-mixture comparison takes.

Continuation 309 proves the signing-data identity (`SigningData`): the
off-hit pruned mean at a family is the tuple-sliced data at the
expansion's tree over the phase view, so the hidden leaves enter only
through the seeds handed to the tail.

Continuation 308 proves the tail's run facts (`TailRun`): the tail is
hash-only, so it keeps the cipher history and ignores the family.

Continuation 307 proves the uniform-mixture comparison in both
directions (`LeafMixture`): a function of the view and the hidden blocks
has, at the family's own blocks, mass within explicit factors of its
uniform mixture over the blocks.

Continuation 306 sums the parent seeds out of the joint bound: the mass
at given hidden blocks is at most the total over the number of blocks
less the bad targets, raised to the number of fixed executions
(`LeafBlockBound`).

Continuation 305 proves the joint one-sided uniformity of the hidden
leaves' blocks given an invariant function of the families, on the
distinct trees (`LeafJointBound`).

Continuation 304 proves that the exchange at a leaf keeps the tree's
keys fresh and distinct and keeps every other leaf's parent seed and
block (`LeafExchangeDistinct`), the invariance the joint uniformity of
the hidden leaves needs.

Continuation 303 generalises the leaf's view exchange to the view
pruned at all executions' hidden keys and the posterior bound to any
invariant weight (`PhaseViewLeafAll`), the form for the joint uniformity
of the hidden leaves.

Continuation 302 proves the posterior bound for the phase view at the
leaf (`HonestLeafBound`): the hidden leaf's block is one-sidedly uniform
given the phase view, up to the bad targets.

Continuation 301 proves the phase view's leaf exchange: the view after
the leaf commitments, pruned at the family's own hidden keys, is the same
under the exchange of the hidden leaf's value (`PhaseViewLeaf`).

Continuation 300 proves the commitment run's leaf exchange: the run
under the exchanged family is the relabelled phase run continued by the
tail at the tree with the leaf set, and the history before the tail,
pruned at the exchanged keys, is unchanged (`CommitRunLeaf`).

Continuation 299 proves the commitment phase's leaf exchange: the run
of the phase at the exchanged leaf under the exchanged family is the
relabelled run of the phase (`CommitPhaseLeaf.commitPhase_run_exchanged`).

Continuation 298 adds the generic tool of the leaf exchange
(`ProgramRelabel`): runs under a key relabelling and the invariance of
the pruned history under a relabelling permuting the pruned keys.

Continuation 297 records that the off-hit equality is not exact either
(the hidden seed avoids its sibling's block, and the output map's fibers
add to the discrepancy), replaces it by the off-bad closeness
`PrunedCloseOff` and composes the pruned closeness from the two slacks
(`prunedClose_of_split'`). The route for the off-bad closeness is the
exchange of the hidden leaf's value, extending the internal-node
exchange machinery, then the data-level step with an explicit slack.

Continuation 296 proves the hit term: a pre-call hit is a distinctness
failure of the tree's keys, so `HitTerm.badTerm_hitPre` bounds it by
the first part of the uniform touching bound (`εHit`). The closeness now
rests on the off-hit pruned equality alone.

Continuation 295 corrects the closeness's quantification: at a fixed
root whose key is already recorded the hit is certain, so `PrunedClose`
is stated over the uniform salt, root and digest, as the swap's core
uses it after averaging; the split is stated for any bad event of the
call (`BadTerm`, `PrunedEqualOff`), the pre-call hit `hitPre` being the
candidate.

Continuation 294 splits the closeness slack into two named targets: the
pre-call hit term `HitPre` (the world before the call already records a
key of the hidden path) and the off-hit pruned equality `PrunedEqualOff`
(exact agreement of the two signings on the calls without a hit);
`prunedClose_of_split` derives the closeness from them.

Continuation 293 corrects the pruned equality: it cannot hold exactly,
because the pre-call cipher history may already record a key of the
hidden path, and a functional knowing that entry then tells the honest
signing from the fake one on the hit event. The corrected named target
`SwapClose.PrunedClose` allows an explicit slack for functionals bounded
by one; the swap's core, the two per-call bounds, the per-event gap and
the composed bound are restated under it (`forgery_le_final_close`), the
slack entering the per-call constant beside the two touching terms
(`εSimP'`). The expected value of the slack is a hit term of the leaf
bounds' shape together with the PRG hypothesis.

Continuation 292 records the content of each named hypothesis of the
final statement in the review ledger (audit/HUMAN_REVIEW.md, "The final
composed bound and its named hypotheses"): what each says, what is
already proved towards it, and whether a decision is pending. The plan's
status lines now describe the reduction as composed end to end with
named unproved hypotheses rather than as largely unfinished.

The BLC arithmetic now includes its actual folding loop, psi power sum,
consistency check, corrections and bounded line slices. Its integrated evaluation
agreement uses the displayed phi-based challenge. The explicit binary and Gray
interpretations of the header indices are now compared in the submitted fields:
their points agree exactly when every index is 0 or 1, while their zero tests,
images and uniform-index pushforward laws agree. Their common image has
2^(tau*kappa) values under the checked basis-size condition. This does not select
the intended source interpretation or claim uniform SHAKE output. Gray encoding,
its one-bit transitions, and optimized/direct folding equality are also proved.

The retry loop uses the actual BAVC opening. Checked properties include first
success, stable and unique returns, and agreement with the verifier's header.
Challenge expansion/encoding remain explicit boundaries, and unspecified counter
overflow is kept separate from rejection. Cipher-input preparation and byte/field
sampling layouts are also formalized, without assuming random bytes or repairing
the source's parsing ambiguities.

The retry loop now also has a partial-expansion interface, proved to agree with
the earlier total interface whenever expansion returns. Pending or undefined
expansion preserves its counter and is not treated as a grinding retry. The
concrete hash-based Algorithm-11 caller uses actual SHAKE/integer sampling;
for submitted nonempty index ranges, the literal missing-B assignment is reached
at counter zero before any BAVC opening. The partial caller now extends through
signing and the verifier's recomputation prefix. Actual BLC/PIOP preparation
feeds signing; emitted signatures retain a genuinely returned challenge and
successful opening, and extra observation fuel preserves the result. The
literal hash signer cannot emit a signature for nonempty execution sets.

Verification preserves pending expansion, undefined operations and explicit
header rejection as distinct outcomes. Its concrete hash expansion reaches the
same missing-B assignment at the transmitted counter, before header checking.
The recomputation prefix stops at the unresolved consistency operands; its
independent suffix requires a supplied base matrix. That suffix uses the actual
PIOP, coefficient recovery and final hash comparison, but does not implement
the ill-typed Algorithm-12 line 21. Raw codecs, other primitive/source boundaries,
successful whole execution and correctness/security remain unfinished.

Algorithm 1's deterministic witness expansion now has checked mixed-radix
reconstruction, exact weight/length and serialized-witness injectivity. Its
generated selectors satisfy the unitary checks. Connecting a valid small SD
instance to the detailed PIOP's flat parser also exposes a nonzero constant term
caused by the recorded mux convention mismatch; matching dimensions do not
remove that discrepancy. This is not a full signature execution.

The binary unitary polynomial is now characterized in both directions, and its
packed-check equivalence is proved for the actual loop in all three Table-2
quotient constructions. Their checked power bases also establish injectivity of
the BLC merge and padded syndrome embedding. All three exact modulus polynomials
are now proved irreducible, with field instances and cardinalities established.
An untrusted generator produces Frobenius and Euclidean-remainder certificates;
Lean checks their arithmetic and the proof that the checks imply irreducibility.
Byte decoding, concrete algorithm integration and the full security reduction
remain unfinished.

The actual padded syndrome batch now has a checked cancellation probability
of exactly 2^(-lambda) under independently uniform coefficients. The introductory
literal PIOP has a checked algebraic probability bound with degree d+1, including
randomized responses after the first challenge and consistent openings. Its
printed bound with degree d is refuted: a constraint with no witness accepts with
probability one on the public set of three cube roots of one, in every submitted
field. This is a generic-protocol counterexample, not a signature execution.

The detailed Algorithms 19/20 are now composed with Algorithm 21 and the flat
parsers at the expanded-challenge boundary. Their literal mux syndrome residual
and unitary vector determine the constant term. Independent uniform batching
cancels any nonzero constraint vector with probability exactly 2^(-lambda).
A separate consistent-evaluation comparison experiment has the checked bound
2^(-lambda) + (1-2^(-lambda))*d/|S|, including randomized responses after both
batching vectors. Its degree-d comparison follows Algorithm 20; it does not
repair introductory equation (2). The source's chunk-size equality is explicit
and fails for Table 3. The intended witness/mux correspondence, concrete
challenge generation, coefficient hash check and signature security remain
outside these local probability results.

Signing phases 1–3 now compose the real BLC commitment, PIOP computation,
coefficient compression and retry/opening routines. BLC.Commit includes the
seed tree, initialized byte streams, Gray folding, positive-index corrections,
consistency matrix and line construction. A concrete primitive family now uses
the submitted ciphers and SHAKE; typed hash serialization and Algorithm 6
source gaps remain explicit boundaries. The polynomial degree needed
for compression is proved through that computation.

Verification after BLC recomputation now implements the PIOP evaluation,
omitted-coefficient recovery and final hash comparison. With exact evaluations
and nonzero delta, recovery produces alpha_1 + delta^(-1)*alpha_0. Thus the
signer/verifier coefficient tuples agree exactly when the computed constant
term is zero. The earlier valid small-witness counterexample yields different
tuples at every nonzero delta, without claiming different hash outputs. Raw
key/signature serialization, full initialization, Algorithm 12's source gaps
and end-to-end correctness/security remain unfinished.

Algorithm 12 now has a staged prefix through line 20 and an independently
defined suffix for lines 22–27. The prefix uses the actual BAVC reconstruction,
PRG sampling, ordered folding loops, auxiliary hash and consistency expansion.
Its undefined seed/rshare/phi_mu names have separate external bindings with no
correctness contracts. The literal prefix leaves them absent. Line 21 remains
an explicit type-resolution boundary: an extension-field scalar is used where
the displayed binary matrix needs a columnwise expression. No corrected
challenge representation or base matrix is silently supplied. Exact loop sums,
coordinate correspondence, header/delta properties and the Category-I
reconstruction failure at this call are checked separately. The suffix retains
the three-component Hashlines input, unlike Algorithm 10's four components.

The integer sampler's four-byte assembly, threshold, rejection prefix and full
staged vector loop are now specified. The word encoding is bijective, the threshold is the largest
allowed multiple, and its rejected range has fewer than half the words for
legal positive m. Uniform-byte acceptance and equal residue counts are proved
as explicit finite sampling laws. The literal routine still uses undefined
`B` in its accepted-value assignment; the literal loop stops there and does not
silently replace it with the assembled value `v`. A separate external binding
is a fixed natural-number value, without any correctness contract. For a
power-of-two range up to 2^32, every four-byte candidate passes the threshold.
The missing name is thus reached on the first read of any nonempty request.

Concrete challenge definitions now use the actual SHAKE input concatenations,
the complete integer loop, binary grinding sampling and the Table-2 batching
decoder. Counter representation, field byte order and consumption counts remain
explicit. Hash-based evaluation challenges retain the undefined integer read;
there is no invented conversion of this outcome to an ordinary challenge or
rejection. Cipher grinding retains its printed 4*lambda-byte material read,
actual Enc* calls, separate extraction boundary and fresh final XOF. Its
material parser and one-subscript Extract operation are still unresolved.
Concrete deterministic SHAKE outputs are not asserted to be uniform challenges.

The complete cipher-based expansion now composes these stages with explicit
optional interpretations for the material parse, MapToBits order and grinding
extraction. Extraction consumes the actual cipher xor. Returned challenges have
proved provenance through the actual final SHAKE integer sample, and successful
returns are stable under additional observation fuel. The literal wrapper stops
at the unresolved material parse; supplying earlier interpretations still leaves
the independent missing-B assignment visible.

Cipher retry, signing and verification callers now preserve those boundaries.
Successful openings/signatures require actual expansion, BAVC success and a
passing header. Verification uses the transmitted counter and reaches its BLC
prefix only after a returned challenge; an unresolved cipher operation is not
an ordinary Reject. The existing Algorithm-12 line-21 boundary, raw codecs and
whole-protocol correctness/security remain unresolved.

The displayed SD-to-RSD reduction is now specified as a randomized computation.
Permutation and truncation preserve the required equations; a returned regular
solver candidate yields a valid original SD solution. The exact probability
that a fixed weight-w witness becomes regular is (n/w)^w / choose(n,w).
Existence of some regular solution is a larger event: a checked binary example
has probability 1 for existence and 4/6 for its fixed witness. The deterministic
uniqueness step is proved, while the source's heuristic conditional estimate,
solver-distribution correspondence and runtime bound remain unproved.

The SD-to-RSD probability argument now uses an explicit joint input/permutation/
solver experiment whose output is proved equal to the actual reduction. Its
combinatorial factor lower-bounds the full-regularity event, and the remaining
conditional factors give a proved success lower bound without substituting an
advertised solver success or uniqueness estimate. A correct selective solver
has positive return mass but zero conditional uniqueness in the planted model,
even at the stated density bound. This invalidates a universal intermediate
uniqueness bound; it does not refute the final existential theorem. The full
distributional/security reduction remains unfinished.

The literal §4.1 dimension formulas are now separate from the proved density
criterion. Candidate/syndrome density is an exact average fiber size. The
printed SD floor can give density 3/2 where it claims at most 1; the RSD theta
sign can give density 2 where it claims at most 1/2. Necessary codimension and
byte-aligned maximum-dimension arithmetic are proved without silently changing
the submitted formulas or asserting their security calibration.

The submitted polynomial-basis encoding is now a proved linear isomorphism,
with byte-pack decoding and round trips for every explicit coefficient ordering.
The PDF leaves the extension-field byte order unstated, so no default is selected.
Uniform-byte laws cover binary samples, extension vectors and both sequential
batching vectors, including unused bytes. The batching law is connected to the
existing detailed PIOP challenge model; concrete PRG/XOF distributions remain
separate obligations.

Section 6's variant formulas and Tables 8–10 are now transcribed and checked,
including size rounding and numerical error budgets. Scaled witnesses have
proved regularity, exact weight, unique position/value recovery and count.
Multiplying a three-layer mux by an amplitude line can give degree four, as used
by the F256 size table. These results do not supply the omitted variant protocols
or their security proofs; nonzero-value enforcement and concrete representation
remain explicit review obligations.

The outlined scaled arithmetic now includes the actual flat parsers, mask,
post-mux multiplication and syndrome batching. Evaluation agreement, its degree
bound, exact constant-term identity and uniform-challenge comparison bound are
proved. The probability premise concerns the computed packed residual; F256
packing injectivity is not inherited from the binary proof. Raw candidates with
zero amplitudes are not regular when chunks exist, yet all-zero inputs give the
zero arithmetic polynomial for zero syndrome. A nonzero-value constraint remains
missing from the outline.

Table-7 syndromes need at least four large-field elements for any injective
encoding. Reusing the binary packing width gives only one and cannot be
injective; the actual linear formula then has a nonzero vector missed by every
batching challenge. These are necessary conditions on completing the outline,
not a claim that it specifies that reuse or a full-signature attack.

The concrete SHAKE128/256 functions now use the pinned FIPS 202 standard.
Keccak's lane implementation is proved to refine its bit equations through all
24 rounds. Padding, complete block absorption, arbitrary-length squeezing,
state serialization and byte-reader correspondence are checked separately.
BAVC can now use the actual SHAKE hash with its existing input serialization;
structured transcript encodings remain explicit. Deterministic SHAKE is not
assumed to have the ideal-oracle law.

NIST's empty, 5-bit and 1605-bit SHAKE examples have dedicated certificate
modules: every absorption-round transition and the first 64 output bytes are
checked by Lean kernel reduction. The generator only extracts proposed data.
For a fresh validation, `python3 scripts/check.py` builds these large certificates
one at a time before the full build and axiom audit, to limit peak memory use.
Additional source PDFs and their hashes are recorded in `source/standards/`.

AES-128 and Rijndael-256-256 now have complete byte-oriented definitions and
proved key-schedule recurrences. Byte operations agree with the specified
256-element polynomial field, and the literal S-box has the required
inverse-and-affine behavior. Each fixed-key full-block cipher is a permutation.
SDitH's bit packing, Category-III padding/truncation and BAVC primitive choices
are explicit. No permutation claim is made for Category III's truncated Enc*.

The complete FIPS AES worked example, including all intermediate states and
expanded keys, and both designer-published Rijndael-256-256 test vectors pass
kernel checks. Source correspondence remains in the human-review ledger; these
results do not establish pseudorandomness or the missing security reductions.
The full check script also builds the cipher certificates sequentially.

Algorithm 6 now has a partial literal transcription with an explicit positive
value for its undefined block-size denominator. Lean checks the actual cipher
counter loop, complete-byte layout, least block count and successful output
prefixes. Category III cannot satisfy the printed complete-Parse assignment
for any positive request. `none` records this undefined source interpretation;
it is not a rejection rule added to the submitted algorithm.

Finite outputs agree with binary/extension sampling and ExpandH within their
proved byte bounds. The BLC primitive family uses the actual ciphers, SHAKE and
ciphertext stream, with finite-call correspondence for Categories I/V and
submitted execution-tweak bounds checked. Hash component order is fixed while
vector/matrix encodings remain supplied functions. Counter wraparound and the
overlap between tweak bits and sufficiently large counters are proved explicitly.
These are deterministic results; whole-protocol correctness/security is unfinished.

Key generation now has a staged transcription of seed sampling, post-position
witness expansion, concrete ExpandH and the printed syndrome assignment.
Independent seed draws and the resulting independence of deterministic
expansions are proved, without claiming uniform expanded outputs. The undefined
`x_A` remains an explicit missing binding. Lean checks precisely when a supplied
binding makes the actual generated vector a valid SD solution. The conflicting
identity-block orientations agree after an explicit permutation and can differ
without it. Typed public/secret key initialization reproduces the generated
matrix with the same byte-consumption count; raw codecs remain unspecified.

The full binary key and signature size columns in Tables 4/5 now agree with
the printed formulas by kernel-checked arithmetic. Necessary size bounds are
also proved for any fixed-width injective encoding of all parsed key values,
using the actual public-key type and an explicitly length-bounded secret-key
view. These are conditional capacity bounds, not assertions that the unprovided
Serialize/Deserialize routines implement such a codec. The reported Category-III
secret key has four spare bits; their placement/value remain unspecified.

The parameter-selection prose disagrees with Table 4 on tree sizes and grinding
values. Both are retained and the disagreement is checked. Table 6's reported
timings, processor and median/run-count metadata are isolated in
`Spec/ReportedBenchmarks.lean` as empirical data, without a runtime claim about
this formalization or an executable implementation.

The partial integer sampler now feeds Algorithm 1's actual witness expansion
and Algorithm 2's matrix/syndrome/key computation. Both source bindings (`B`
and `x_A`) stay absent in the literal wrappers. Pending observations, undefined
reads and returned keys are separate outcomes. Returned results have actual
sampler provenance, exact weight/length, and the previously proved conditional
syndrome relation. The independent seed draws induce distributions of these
observations; they are not presumed to produce uniformly distributed keys.

Finite sampler traces are proved independent of bytes beyond four per observed
attempt, including repeated rejections. Successful finite PRG output covering
that range agrees with the actual ciphertext-stream observation. This proof
also reaches the witness-expansion suffix and retains fault values and cursors;
it does not equate unconsumed infinite reader tails. The undefined PRG block size,
Category-III Parse discrepancy and raw codec conventions remain explicit.

Algorithm 9 now has its full staged body through both commitment hashes.
The queue loop terminates, seed parsing consumes complete in-bounds blocks,
and successful leaf/row outputs match their actual computations. The source's
`tree` and undeclared `nodes` remain distinct; undefined reads are not presented
as explicit source rejection. A padded path can never enter the extraction
branch, so successful prefill leaves an empty tree. The final Category-I
statement now certifies rejection by the whole body before `nodes` is accessed,
for every possible binding. Intended reconstruction correctness remains unresolved.
