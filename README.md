# SDitH v3.0 Lean formalization

A Lean 4 / Mathlib development around the SDitH v3.0 signature submission.
It contains a typed specification of the submission's algorithms, machine-checked
refutations of several literal source claims, and a composed EUF-CMA reduction
for an explicitly named candidate scheme in an ideal hash-and-cipher model.

This repository does **not** establish correctness or security of the submitted
scheme. The reduction's final statement carries named cryptographic hypotheses
that are not proved, and the correspondence between the formal candidate scheme
and the concrete submission is a recorded human obligation. Build and declaration
counts measure nothing about completion.

## Source

`sdith-v3.0.pdf`, dated 2026-08-31, 55 PDF pages. SHA-256:
`22dfed06d179afa759139487dca9c8f8d4a7cfea22bcedcb7736b50ce5b01c83`.
`source/sdith-v3.0.txt` is a searchable extraction; the PDF is authoritative.
`source/index.json` maps the 21 numbered algorithms, the unnumbered subroutines
and the concrete primitives to their specification and proof modules, with a
status line each.

## Building and validating

Toolchain: `leanprover/lean4:v4.28.0` with the pinned Mathlib in
`lake-manifest.json`.

```sh
lake build SDitH          # builds every module imported by SDitH.lean
python3 scripts/check.py  # full validation
```

`scripts/check.py` checks the source PDF's hash, builds the project, scans every
Lean file for `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
`implemented_by` and `extern`, and audits the transitive axioms of every project
declaration. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
The last run's output is `audit/validation.log`. The script never labels the
formalization complete.

## Repository layout

| Path | Contents |
|---|---|
| `SDitH/Spec/` | Typed specifications: the submission's algorithms, parameters and tables, the concrete primitives (SHAKE, Rijndael, the PRG), the hash and cipher models, the signature games and the candidate scheme. |
| `SDitH/Proofs/` | All proofs. Every module is imported by `SDitH.lean` and listed in `source/index.json`. |
| `SDitH/Assumptions.lean` | The standalone assumption interface: candidate readings of the submission's §5.3 assumptions (planted syndrome decoding, lazy random oracle, ideal cipher, their joint model). It declares no axiom. |
| `SDitH/Final.lean` | The public theorem interface: three discrepancy theorems, nothing else. |
| `audit/` | `COVERAGE.md` (what each module establishes), `PROGRESS.md` (chronological record), `HUMAN_REVIEW.md` (source-correspondence and review obligations), `DISPOSITIONS.md` (proposed disposition of every source item, for the review audit), `Axioms.lean`, `validation.log`, `REPORT.pdf` (the paper-to-theorem report: how each step of the security argument corresponds to a Lean theorem), and the archived earlier versions of this file and of `PLAN.md`. |
| `PLAN.md` | The checklist of completed components, remaining work, the composed bound's terms, the review table and the completion gates. |

## Conventions

- The literal source is specified as written. Where a literal claim is false, the
  refutation is kept and the corrected reading is introduced as a separately
  named candidate definition (`Candidate…`). Nothing in the source is silently
  repaired.
- Every hardness or model assumption is an explicit hypothesis of the theorem
  that uses it, stated as a named definition. No assumption is an axiom, and no
  unproved reduction is admitted under an assumption's name.
- Proof-wide settings are unchanged: no heartbeat, recursion or trust options
  are raised anywhere.

## What is established

### Discrepancy theorems (`SDitH/Final.lean`)

- `literal_piop_not_complete`: the literal Category-I PIOP check rejects an
  honest input, with an explicit nonzero challenge.
- `table3_dimension_mismatch`: Table 3's tensor dimensions do not match in any
  of the three categories.
- `commitment_discrepancies`: a BAVC opening at a hidden index that the literal
  reconstruction always rejects by its bound, and the signer's and the
  verifier's `Hashlines` inputs differ whenever the witness correction is
  nonempty.

### Component results

For each algorithm, `source/index.json` names the specification module, the
proof modules and the status of what is proved: executed semantics of the
concrete routines (witness expansion, key generation, the seed tree and BAVC
commitment, reconstruction, the BLC chain, the PIOP arithmetic, challenge
encoding, serialization boundaries), adaptive binding bounds for the hash and
cipher layers, the slope-consistency game, and the concrete primitives with
certificates for the test vectors. `audit/COVERAGE.md` gives the per-module
detail. Source items that remain undefined or contradictory are listed in the
review table of `PLAN.md`.

### The security reduction

The composed forgery bound is
`SDitH.Proofs.SeedTermDischarge.forgery_le_final_hard_C`, with its form at
the submitted full layout `SDitH.Proofs.FullLayoutFinal.forgery_le_final_full`
(the layout hypotheses discharged, fiber constants one), at the full layout
and the candidate encoding
`SDitH.Proofs.CandidateSerialization.forgery_le_final_full_enc` (the encoding
hypotheses discharged), and averaged over a distribution of instances
`SDitH.Proofs.DistributionalFinal.averaged_forgery_le_final` (the hardness
assumption on the distribution). It is stated for the
candidate scheme (the named corrected reading of the signer and verifier) in the
shared ideal hash-and-cipher model, against a bounded adaptive chosen-message
forger. It bounds the forger's squared advantage, minus the digest-guessing
term, by the budget squared times an explicit sum of:

- five named constants bounding the witness-free simulator's events
  (mask-after-fork, non-separation, zero-challenge, Schwartz–Zippel,
  batching);
- proved slacks: the per-event simulation slack (input-present, row-stored,
  staleness, retry, touching and leaf terms), the seed-collision pair cost,
  the slope-game slack (mask trap, witnessed pair, unseen match), and the
  mention, collision and digest terms of the fork-and-extract core;
- the named hardness bound `εSD` on the solver's syndrome-decoding success
  `rsdSuccess`, the probability that the witness-free solver returns a
  weight-`w` solution of the key generation's instance `instanceOf H' y`.

**Proved in the model.** The forgery-to-fork step with useful-query selection
and replay, extraction of a witness line from two accepted transcripts, the
solver's witness-freeness, the hybrids over the signing game, the honest
signer's coupling with the witness-free simulator up to the named closeness
and hiding hypotheses, the real-experiment bounds of the seed-collision and
slope-game events, and the identification of an extracted witness (zero mux
residual, unitary selectors) with a regular syndrome-decoding solution of the
public instance.

**Named hypotheses.** These are explicit theorem parameters, each a named
definition, kept by decision as cryptographic assumptions rather than derived
from an idealization of the PRG or of the challenge and batching expansions:

| Hypothesis | Meaning |
|---|---|
| `DataClose` (`OffHitAssembly`) | With the hidden leaves' blocks replaced by a uniform tuple, the honest signing's data is within an explicit slack of the fake signing's: ideal-model honest-verifier zero knowledge at uniform hidden blocks. |
| `LeafHide` (`LeafTermBound`) | With the hidden leaves replaced by uniform blocks, a continuation records a replaced block's key with probability at most δ. |
| `hretry` | The candidate retry returns at the digest except with probability εR. |
| `SimulatorTermBounds5` (`SeedTermDischarge`) | The five simulator event probabilities are at most their named constants. Mask-after-fork is the hypothesis term of decision 1; the other four depend on the challenge and batching expansions. |
| `InstanceHard` (`InstanceHardness`) | Every budgeted adversary's solver returns a weight-`w` solution of the key generation's instance with probability at most `εSD` of the budget. |
| `DistributionHard` (`DistributionalFinal`) | The same averaged over the instance distribution: used by the averaged form of the bound in place of `InstanceHard`. |

**Parameter conditions.** Injectivity and fiber bounds of the signer's and the
verifier's cipher layouts (discharged at the full layout; the settings fix the
cipher's key and block width to λ, so the Category-III truncated layout is
outside their type and the statement covers Categories I and V), the verifier's identity layout, the size conditions
(26 ≤ λ, four times the leaf count ≤ 2^24, the budget-dependent counts below
the number of seeds) and the structural hypotheses (the verifier's middle, the
encoding injectivity facts (discharged at the candidate bit-per-coordinate
encoding of `CandidateSerialization`), the candidate challenge encoding, the
budgets, at least one higher coefficient, the witness sampler's solutions, the
verification budget within the commitment budget).

**Not asserted.** That the key generation's instance is drawn from a hard
distribution. `InstanceHard` is an assumption on the fixed instance of the
setting and over the reduction's solvers, and `DistributionHard` on an
arbitrary instance distribution given as a parameter; Algorithm 2's own law
is not formed, because the literal routine returns no key (`B`, `x_A`
undefined). `SDHardness` in `SDitH/Assumptions.lean` is a definition over the
planted distribution and is not consumed by any theorem, because the
seed-expanded systematic instance is not related to that distribution and no
runtime model exists. That correspondence, the correspondence of
the candidate scheme to the submitted routines, and the ideal model's relation
to concrete SHAKE and Rijndael are human review obligations recorded in
`audit/HUMAN_REVIEW.md`.

## Trust boundary

The results depend on Lean 4, the pinned Mathlib, and the three standard
axioms. The ideal hash-and-cipher model is a definition, not a property of the
concrete primitives. No runtime or machine model is formalized; the forger's
budget counts oracle actions. Reported benchmarks and attack-cost estimates are
transcribed, not certified.

## Status and open work

`PLAN.md` is organised in two tracks. Track A, the security reduction, is
complete modulo the named assumptions above. Track B, the whole-scheme
formalization (correctness, concrete bytes, variants, the §5.1 mathematics),
is blocked on human decisions about the source's undefined and refuted parts;
each item there carries its blocker. The review table of unresolved source
items and the completion gates follow the tracks. The chronological record of the development is
`audit/PROGRESS.md`; the earlier narrative version of this file is
`audit/README_HISTORY.md`.
