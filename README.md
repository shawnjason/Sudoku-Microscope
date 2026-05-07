# Sudoku-Microscope — Lean Proofs

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20072389.svg)](https://doi.org/10.5281/zenodo.20072389)

Machine-checked Lean 4 proofs for:

**"Sudoku as a Microscope for Non-Extendable Commitment: Empirical Validation of Global Admissibility Filtering"**

Paper DOI (concept, always resolves to latest): [TBD](https://doi.org/10.5281/zenodo.20072389)

---

## Author

Shawn Kevin Jason — Independent Researcher, Las Vegas, NV
ORCID: [![ORCID iD](https://orcid.org/sites/default/files/images/orcid_16x16.png)](https://orcid.org/0009-0003-9208-1556) [0009-0003-9208-1556](https://orcid.org/0009-0003-9208-1556)

---

## What This Repository Contains

Four standalone Lean 4 proof files covering the principal formal results of the paper. The proofs split into three groups: a **foundations** group establishing the local-global separation that anchors the paper's microscope framing — global admissibility implies local validity, but local validity is strictly insufficient (zero-bucket candidates are the structural witness); a **catastrophic commitment** group defining the event criterion and proving foreclosure permanence — once a move transitions the completion bucket from non-empty to empty, no subsequent move can recover; and a **safety architecture** group establishing forced-gate safety (globally-admissible commit policies preserve non-emptiness across the entire trajectory) and bucket sufficiency (the 0/≥1 completion bucket loses no safety information vs the full cardinality count).

The proofs are formulated over an abstract `ConstraintSystem` framework — a state space, a move type, an `apply` function, a finite completion-set assignment, and either a coherence axiom (linking completion existence to local validity) or a monotonicity axiom (committing a move can only restrict the completion set), depending on which theorem the file proves. Sudoku is one instance; the framework also covers Hamiltonian path-games, scheduling, and any constraint domain whose completion structure satisfies the relevant coherence and monotonicity axioms.

Each file is independent and verifies against the current Mathlib release.

---

## Files

### Foundations: Local-Global Separation

**`247_local_global_separation.lean`** — Local-Global Separation (Necessity and Strict-Insufficiency)
Two structural facts about any constraint system equipped with the coherence axiom `(comp (apply s m)).Nonempty → locallyValid s m`. The necessity direction (`global_admissible_implies_locally_valid`): if a move has any globally valid completion, it must have respected immediate local constraints — proven directly from the coherence axiom. The strict-insufficiency direction (`locally_valid_not_globally_admissible`): under the assumption that the system exhibits non-extendable commitment (i.e., zero-bucket candidates exist — empirically observed in Paper 7's Sudoku layers), there is an explicit witness move that is locally valid but not globally admissible. Together these establish `GloballyAdmissible ⊊ LocallyValid` — the structural foundation of the microscope framing. Every empirical zero-bucket candidate Paper 7 reports is a concrete instance of the strict-insufficiency witness.

### Catastrophic Commitment

**`217_catastrophic_commitment.lean`** — Catastrophic Commitment (Definition and Foreclosure Permanence)
Two contributions in a single file. The definition (`catastrophicCommitment`): a move (s, m) is a catastrophic commitment iff the pre-move state has at least one valid completion but the post-move state has none — `|Comp(s)| > 0 ∧ |Comp(apply s m)| = 0`. The foreclosure permanence theorem (`catastrophic_commitment_forecloses`): under the framework's monotonicity axiom (`comp (apply s m) ⊆ comp s`), once a catastrophic commitment has occurred, applying any subsequent move keeps the completion set empty. By iteration through the helper `empty_preserved`, this extends to any sequence of subsequent moves — once `comp = ∅`, it stays `∅` forever. The 0/≥1 bucket transition `1 → 0` is monotone-irreversible. Anchors §2's catastrophic-commitment event criterion used by the harness as the termination condition for an attempt.

### Safety Architecture

**`250_forced_gate_safety.lean`** — Forced-Gate Safety Theorem
Trajectory-level non-emptiness preservation. For any starting state `s₀` with non-empty completion and any sequence of moves `ms = m₀, ..., m_{k-1}` such that every intermediate post-move state has non-empty completion (`(comp (apply s_i m_i)).Nonempty` for each step `i`, where `s_{i+1} = apply s_i m_i`), the terminal state `applyTrajectory s₀ ms` also has non-empty completion. The structural reason forced-gate / auto-GAF / check-until-admissible policies achieve zero catastrophic commitments empirically — abstracted from any specific experiment. Proves by induction on the trajectory length that the safety invariant (non-empty completion) is preserved at every step under the forced-gate condition.

**`251_bucket_sufficiency.lean`** — Bucket Sufficiency Theorem
The catastrophic-commitment predicate stated on the 0/≥1 bucket of `|Comp|` is equivalent to the same predicate stated on the full cardinality count: `((comp s).Nonempty ∧ comp (apply s m) = ∅) ↔ ((comp s).card ≥ 1 ∧ (comp (apply s m)).card = 0)`. The bucket abstraction loses no safety information for first-foreclosure detection — verifiers returning a 2-valued bucket signal are equipotent with verifiers returning the full `ℕ`-valued count for the purpose of detecting catastrophic commitment. Justifies §3's bucket-coarsening protocol decision: the harness can use the cheaper 0/≥1 verifier output without compromising safety detection accuracy.

---

## Mapping to the Paper

| Paper Result | File | Lean Theorem |
|---|---|---|
| Local-Global Separation, Necessity (§1, §2 — global admissibility implies local validity) | `247_local_global_separation.lean` | `global_admissible_implies_locally_valid` |
| Local-Global Separation, Strict-Insufficiency (§1, §2 — locally valid does not imply globally admissible; zero-bucket witness) | `247_local_global_separation.lean` | `locally_valid_not_globally_admissible` |
| Catastrophic Commitment Definition (§2 — bucket transition from non-empty to empty) | `217_catastrophic_commitment.lean` | `catastrophicCommitment` (definition) |
| Catastrophic Commitment Foreclosure Permanence (§2 — once foreclosed, always foreclosed) | `217_catastrophic_commitment.lean` | `catastrophic_commitment_forecloses` |
| Forced-Gate Safety (§3, §7 — globally-admissible policies preserve non-emptiness) | `250_forced_gate_safety.lean` | `forced_gate_safety` |
| Bucket Sufficiency (§3 — 0/≥1 bucket equivalent to full cardinality for safety) | `251_bucket_sufficiency.lean` | `bucket_sufficiency` |

---

## How to Verify

1. Open [live.lean-lang.org](https://live.lean-lang.org)
2. Confirm the dropdown in the upper right is set to **Latest Mathlib**
3. Paste the contents of any `.lean` file into the editor
4. Wait for checking to complete — "No goals" on each theorem and no errors in the Problems pane confirms verification

Each file is independent; no cross-file imports are required.

---

## Scope

These proofs verify the formal logical structure of the principal abstract results: the local-global separation in any constraint system with the coherence axiom, the catastrophic-commitment definition and its foreclosure permanence under monotonicity, the trajectory-level safety invariant under forced-gate policies, and the equivalence of 0/≥1 bucket and full-cardinality formulations for safety detection. They do not establish:

- The full empirical content of the paper — the cross-suite Sudoku runs, layer-by-layer catastrophic-commitment counts, model-specific failure-mode breakdowns (GPT-5.5 baseline, default-mode determinism observations), the experimental protocol calibration, and the policy comparisons (no-tool, optional-tool, dummy-tools, forced-gate, named-dummy, neutral)
- The specific witness construction for any concrete Sudoku state — strict-insufficiency is established under the existential hypothesis `hasNonExtendableCommitment`, parameterizing over the witness rather than constructing a specific 9×9 grid
- The conjectures and predictions in the paper's discussion sections about generalization to non-Sudoku constraint domains, learned admissibility classifiers, or production-deployment routing
- The cross-provider replication claims developed in Paper 8 (Path-Game GAF Pilot) — the Sudoku-Microscope abstract framework covers path-games as another instance, but the cross-provider empirical findings live in their own paper

The framework is deliberately abstract: any constraint system satisfying the coherence and monotonicity axioms inherits these structural results. Sudoku and 4×4 Hamiltonian path-games are the empirically tested instances; the theorems cover the general case.

---

## Related Work

The foundational projection-theoretic result underlying the framework is developed in:

*Projection Insufficiency and Trajectory Realization: A Unified Constraint-Based Framework for Bounded Systems* — [DOI: 10.5281/zenodo.19633241](https://doi.org/10.5281/zenodo.19633241) (Lean proofs: [10.5281/zenodo.19687629](https://doi.org/10.5281/zenodo.19687629))

The forward-case impossibility result establishing the divergence kernel and arithmetic-witness machinery is developed in:

*The Non-Locality of Extendability: An Impossibility Theorem for Bounded Information Systems, with Applications to Generative Sequential Systems* — [DOI: 10.5281/zenodo.19688367](https://doi.org/10.5281/zenodo.19688367) (Lean proofs: [10.5281/zenodo.19687799](https://doi.org/10.5281/zenodo.19687799))

The stochastic extension establishing the admissibility-dynamics framework is developed in:

*Inconsistency Accumulation in Forward-Local Sequential Policies: A Lower Bound under Delayed Constraints* — [DOI: 10.5281/zenodo.19688628](https://doi.org/10.5281/zenodo.19688628) (Lean proofs: [10.5281/zenodo.19687094](https://doi.org/10.5281/zenodo.19687094))

The language-model specialization providing the structural-ceiling and certification-depth context for bounded-context generative systems is developed in:

*Language Model Hallucinations: An Impossibility Theorem and Its Architectural Consequences* — [DOI: 10.5281/zenodo.19715059](https://doi.org/10.5281/zenodo.19715059) (Lean proofs: [10.5281/zenodo.20059771](https://doi.org/10.5281/zenodo.20059771))

The theoretical analysis of Recursive Language Models through the admissibility-dynamics framework is developed in:

*Recursive Language Models Through the Admissibility-Dynamics Framework: A Principled Theory of When Recursive Scaffolding Succeeds* — [DOI: 10.5281/zenodo.19753549](https://doi.org/10.5281/zenodo.19753549) (Lean proofs: [10.5281/zenodo.20060154](https://doi.org/10.5281/zenodo.20060154))

The pair-construction empirical companion paper applying the framework to OOLONG-Pairs is developed in:

*From Recursive Scaffolding to Admissibility-First Construction: Mechanism, Stability, and Failure-Mode Decomposition on OOLONG-Pairs* — DOI: TBD (archival pending) (Lean proofs: TBD)

---

## License

MIT
