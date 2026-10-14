# Dispositions of the source items (input for the coverage and review audit)

Prepared 2026-10-14 as the input for PLAN.md, Track B item 7. Each source item
is given one of four dispositions:

- **proved**: a statement about the item as written (or as the named candidate
  reading says) is machine-checked;
- **assumption**: carried as an explicitly named hypothesis of a theorem;
- **refuted**: the literal claim has a checked counterexample;
- **obligation**: a human decision or review is needed before any statement
  can be made (undefined source element, correspondence, empirical claim).

An item may have several dispositions for its different parts. The modules are
those named in `source/index.json`; per-module detail is in `COVERAGE.md`, and
the review discussion is in `HUMAN_REVIEW.md`. This file does not itself
discharge the audit: the dispositions have to be reviewed by a person.

## Numbered algorithms

| Alg. | Title | Proved | Refuted | Obligation |
|---|---|---|---|---|
| 1 | ExpandWitness | Executed semantics at the cipher-stream boundary; returned weight and length; trace agreement with Algorithm 6 over four bytes per attempt. | — | PRG block size and the undefined bindings it reads. |
| 2 | Key generation | Seed-draw law, ExpandH correspondence, literal syndrome assignment, returned-key provenance, generated-solution SD condition; the literal routine returns no key (missing `B`, `x_A`). | — | `B`, `x_A`, systematic-matrix convention, raw codecs; the instance-to-hardness-distribution correspondence of the reduction's hardness assumption. |
| 3 | Signing | Prepared records, staged cipher opening, signature provenance, fuel stability; the honest candidate signer's commitment program and its coupling in the reduction. | — | Initialization, codecs, missing `B`; correspondence of the candidate signer to the literal algorithm. |
| 4 | Verification | Executed program on the shared world (reconstruction, Hashaux, middle, Hashlines, suffix); forked accepted attempts determine a seed vector up to collisions; the candidate verifier in the reduction. | — | Codecs, Algorithm-12 line 21, missing `B`; correspondence of the candidate verifier (its explicit middle and expansion parameters). |
| 5 | TweakSalt | Bit-level computation and recoverability. | — | — |
| 6 | PRG | Counter loop, parse shape, least block count, prefix/reader/sampler correspondence, counter and tweak bounds. | Positive Category-III calls cannot satisfy the printed complete-Parse assignment. | Block-size denominator; present-salt/absent-tweak case; byte representation. |
| 7 | BAVC.Commit | Full construction; tree recursion; serialization injectivity; computable collision finder; the commitment binding bounds in the ROM/ICM. | — | Hiding is in the reduction only through the named `DataClose`/`LeafHide` hypotheses. |
| 8 | BAVC.Open | Queue computation, termination, memory safety, padded length, trace. | — | Reveal correctness relative to a corrected reconstruction. |
| 9 | BAVC.Reconstruct | Full staged body; queue/loop/output; equal-root disagreement reduces to a hash or seed collision; executed cipher programs and budget. | The Category-I opening is rejected for every `nodes` binding (`Final.commitment_discrepancies`). | `tree` versus undeclared `nodes`; padding versus bounds; intended correctness. |
| 10 | BLC.Commit | Composed seed tree, sampling, Gray folding and corrections, typed hashes, consistency matrix, lines; concrete primitives with finite PRG correspondence. | — | Structured serialization, Category-III parse, recomputation integration. |
| 11 | BLC.OpenRandomEvaluation | Retry with full staged cipher expansion; provenance and stable returns. | — | Source overflow policy; missing `B`; the retry bound is the named hypothesis `hretry` in the reduction. |
| 12 | BLC.RecomputeEvaluation | Prefix and suffix execution; chain collision bounds; unique seed vector from two chains; the affine fold under explicit bindings; the slope-consistency bound; the candidate middle; the composed reduction (see `reduction_status`). | — | Line 21 (ill-typed; the candidate binary reading is a named definition); the seed array's binding; the omitted witness-correction field of `Hashlines` (`Final.commitment_discrepancies`). |
| 13–14 | PIOP Format | Parsing, mask computation, degree, evaluation. | — | — |
| 15–16 | PIOP UnitaryCheck | Arithmetic, evaluation, quadratic bound. | The degree-one annotation. | — |
| 17–18 | PIOP MuxTree | Recurrence, evaluation, degree; with unitary selectors the tree reads the selected leaf (`MuxSelect`). | — | Pseudocode indexing and witness-order conventions. |
| 19–20 | PIOP Run | Post-challenge composition, evaluation, degree, constant-term identity, uniform batching law, comparison bound. | The literal Category-I completeness (`Final.literal_piop_not_complete`); Table 3's tensor dimensions (`Final.table3_dimension_mismatch`). | Intended witness correspondence; concrete challenges. |
| 21 | BatchLinearEquations | Residual identity, padded embedding injectivity in all Table-2 fields, exact cancellation probability. | — | Concrete challenge integration (the batching event is the named constant `εBatch` in the reduction). |

## Unnumbered subroutines, tables and claims

| Item | Proved | Refuted | Obligation |
|---|---|---|---|
| SampleFieldElements, ExpandH, challenge layouts | Byte conversions, matrix loops, finite PRG and SHAKE correspondence. | — | Wire order, consumption policy, undefined integer assignment, distribution claims. |
| Concrete challenge evaluation and SHAKE batching | Transcripts, integer loop, grinding, batching; staged cipher body. | — | Default parser, `B = v` assignment, uniform SHAKE law (the ideal model is a definition). |
| Table 2 quotient representations | Rings, degrees, bases, injectivity, irreducibility, cardinalities. | — | Byte decoding integration. |
| Binary unitary polynomial, equation (6) | Coefficient characterization, packed-loop equivalence. | — | — |
| Introductory PIOP soundness claim | Batch and root probabilities, degree bounds, d+1 responses. | The printed d-based bound, in all Table-2 fields. | — |
| Detailed batching and comparison probabilities | Cancellation laws, comparison bound. | — | — |
| SampleIntegers | Full vector loop, completion stability, first-candidate acceptance for powers of two. | — | `B` is never replaced by `v`. |
| §5.1 SD-to-RSD reduction | Regularization law, permutation and truncation correctness, deterministic uniqueness step; the joint experiment's output law. | Pointwise instance-event equality; an intermediate universal conditional-uniqueness bound. | Heuristic conditional uniqueness, solver distribution, runtime (Theorem 5.1 itself is not refuted). |
| Polynomial-basis isomorphism and byte sampling | Isomorphism, pack bijections, uniform laws, batching law. | — | Wire order, PRG/XOF distribution. |
| §6 variants (scaled witnesses, packing, Tables 7–10) | Tables, formulas, composed arithmetic, comparison bound; missing nonzero enforcement exposed. | — | Full variant algorithms, scalar codecs, embedding, nonzero enforcement. |
| Key-generation seed law and matrix initialization | Seed-pair law, pushforward independence, ExpandH coordinates, SD kernel condition for a bound `x_A`. | — | `x_A`, raw codecs, consumption policy. |
| Key-codec capacity, Tables 4/5, Table 6 timings | Cardinalities, codec lower bounds, all sizes and budgets. | Prose tree-size/grinding disagreement. | Raw codecs; Table 6 is reported data, not certified. |
| Density dimensions and byte-aligned selection | Average-fiber density, ceiling criterion, byte-aligned maximum. | SD rounding and RSD sign formulas. | Greedy arity optimization; hardness calibration. |
| Commitment collision reductions (BAVC, BLC chain) | Finder, serialization injectivity, disagreement-to-collision, chain bounds (full and Category-III capacities). | — | Aliases and bindings; the composed reduction's settings cover Categories I and V only (Category III's block width is outside their type). |
| Adaptive ROM/ICM bounds (birthday, paired cipher, fully queried binding, shared execution, sequential verification, reconstruction programs) | All stated bounds, with exact laws and coverage. | — | Correspondence of the ideal model to SHAKE and Rijndael. |
| Signature game and forgery-to-replay | Game, cut/resume law, useful-index selection, replay bound; composed into the candidate-scheme reduction. | — | Runtime model (absent); concrete and domain correspondence. |
| Concrete SHAKE, AES-128, Rijndael-256-256 | Deterministic bodies with FIPS refinements, keyed permutations, test-vector certificates. | — | Transcription review; no randomness claim. |
| Concrete PRG | Counter loop and parse shape; periodicity and the tweak/counter coincidence. | Category-III complete-parse shape. | Block size, missing-tweak case, byte representation. |

## The reduction's own items

| Item | Disposition |
|---|---|
| Composed EUF-CMA bound for the candidate scheme | proved (`SeedTermDischarge.forgery_le_final_hard_C`; at the full layout `FullLayoutFinal.forgery_le_final_full`). |
| Data-level closeness `DataClose`, leaf hiding `LeafHide` | assumption (PRG not idealized). |
| Retry bound `hretry` | assumption (challenge expansion not idealized). |
| Mask-after-fork `εMask` | assumption (decision 1). |
| Non-separation, zero challenge, Schwartz–Zippel, batching | assumption (challenge and batching expansions not idealized). |
| Instance hardness `InstanceHard`, `DistributionHard` | assumption on the fixed public instance, or on an instance distribution given as a parameter (`DistributionalFinal`); forming Algorithm 2's own law is an obligation (undefined `B`, `x_A`). |
| Encoding injectivity hypotheses | proved at the candidate bit-per-coordinate encoding (`CandidateSerialization.forgery_le_final_full_enc`); the encoding's agreement with the implementation's packing is an obligation. |
| Expansion-dependent simulator constants and retry bound | assumption; discharging them needs the challenge expansion modelled as a counted oracle (a refactor of the settings), since the deterministic parameter lets the forger try every counter for free. |
| Candidate scheme versus submitted routines | obligation (blocked by Algorithm 12's line 21 and seed array, the `Hashlines` payload, the undefined bindings). |
