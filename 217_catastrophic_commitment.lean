/-
  217_catastrophic_commitment.lean

  Catalog ID 217 (primary, catastrophic commitment definition) +
  ID 249 (secondary, foreclosure permanence theorem).
  Paper 7 (Sudoku-Microscope), abstract formalization companion.

  Author : Shawn Kevin Jason
  Repo   : github.com/shawnjason/Sudoku-Microscope  (forthcoming)

  Catastrophic Commitment (ID 217) and Catastrophic Commitment
  Forecloses (ID 249).

  A move (s, m) is a *catastrophic commitment* in a constraint system
  iff the pre-move state has at least one valid completion but the
  post-move state has none — the move forecloses the puzzle.  Once a
  catastrophic commitment occurs, the completion set remains empty
  under any subsequent moves: the 0/≥1 bucket transition 1 → 0 is
  monotone-irreversible.  This is the foreclosure direction of the
  bucket dynamics on which Paper 7's safety reasoning is built.

  ID 217 catalogs the catastrophic-commitment definition (the abstract
  signature that the Sudoku protocol instantiates).  ID 249 catalogs
  the foreclosure-permanence theorem (the structural reason that
  ID 226's operational detection rule terminates the run).  See also
  catalog ID 226 (the empirical/operational first-foreclosure rule)
  for cross-reference.

  Per-file standalone: the `ConstraintSystem` structure is repeated
  here in the unified five-field form shared across all four files
  in this formalization.  This matches the established repo
  convention of declaring identical structures across files that
  share a conceptual object (cf. 061/062a's shared `DelayedBlock`).
  The theorems in this file use only `apply`, `comp`, and
  `comp_monotone`; the remaining fields (`locallyValid`,
  `comp_implies_local`) are present for structural unification and
  are exercised in other files (247_local_global_separation.lean).

  Standalone (deliberately so for per-file verification on
  live.lean-lang.org).
-/

import Mathlib

namespace SudokuMicroscope.CatastrophicCommitment

/-- Abstract constraint system.  Unified structure used across the
    Sudoku-Microscope formalization.  Each file declares this same
    structure independently for per-file standalone verification;
    individual theorems use only the subset of fields they need. -/
structure ConstraintSystem (State Move Completion : Type) where
  locallyValid       : State → Move → Prop
  apply              : State → Move → State
  comp               : State → Finset Completion
  comp_implies_local : ∀ (s : State) (m : Move) (c : Completion),
                        c ∈ comp (apply s m) → locallyValid s m
  comp_monotone      : ∀ (s : State) (m : Move),
                        comp (apply s m) ⊆ comp s

namespace ConstraintSystem

variable {State Move Completion : Type}

/-- **Catastrophic Commitment** (Paper 7, ID 217).

    A move (s, m) is a catastrophic commitment iff the pre-move state
    has at least one valid completion but the post-move state has none —
    the move forecloses the puzzle.

    Equivalently: |Comp(s)| > 0 ∧ |Comp(apply s m)| = 0.  This is the
    1 → 0 transition in the 0/≥1 bucket abstraction (cf.
    251_bucket_sufficiency.lean, ID 251). -/
def catastrophicCommitment (cs : ConstraintSystem State Move Completion)
    (s : State) (m : Move) : Prop :=
  (cs.comp s).Nonempty ∧ cs.comp (cs.apply s m) = ∅

/-- Helper lemma: if a state's completion set is empty, applying any
    move keeps it empty.  Direct consequence of monotonicity — the
    post-move completion set is a subset of the pre-move set, and any
    subset of `∅` is `∅`. -/
theorem empty_preserved
    (cs : ConstraintSystem State Move Completion)
    (s : State) (m : Move)
    (h_empty : cs.comp s = ∅) :
    cs.comp (cs.apply s m) = ∅ := by
  have h_sub : cs.comp (cs.apply s m) ⊆ cs.comp s := cs.comp_monotone s m
  rw [h_empty] at h_sub
  exact Finset.subset_empty.mp h_sub

/-- **Catastrophic Commitment Forecloses** (Paper 7, ID 249).

    Once a catastrophic commitment has occurred at (s, m), applying any
    subsequent move m' keeps the completion set empty.  The attempt
    cannot recover after a catastrophic commitment — it terminates as a
    permanent foreclosure of solutions.  By iteration of `empty_preserved`,
    this extends to any sequence of subsequent moves: once `comp` is `∅`,
    it stays `∅` forever.  The 0/≥1 bucket transition 1 → 0 is therefore
    monotone-irreversible. -/
theorem catastrophic_commitment_forecloses
    (cs : ConstraintSystem State Move Completion)
    (s : State) (m : Move)
    (h_cc : cs.catastrophicCommitment s m)
    (m' : Move) :
    cs.comp (cs.apply (cs.apply s m) m') = ∅ := by
  obtain ⟨_, h_empty⟩ := h_cc
  exact cs.empty_preserved (cs.apply s m) m' h_empty

end ConstraintSystem

end SudokuMicroscope.CatastrophicCommitment
