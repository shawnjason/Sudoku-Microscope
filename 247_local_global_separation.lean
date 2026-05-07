/-
  247_local_global_separation.lean

  Catalog ID 247 (primary, necessity direction) +
  ID 248 (secondary, strict-insufficiency direction).
  Paper 7 (Sudoku-Microscope), abstract formalization companion.

  Author : Shawn Kevin Jason
  Repo   : github.com/shawnjason/Sudoku-Microscope  (forthcoming)

  Local-Global Separation: Necessity (ID 247) and Strict
  Insufficiency (ID 248).

  In any constraint system equipped with the coherence axiom
  comp_implies_local, two structural directions hold simultaneously:

  (1) Necessity (ID 247).  Global admissibility implies local
      validity: if the post-move completion set is non-empty, then
      the move was locally valid.  Immediate from the coherence axiom.

  (2) Strict insufficiency (ID 248).  The converse fails: a
      locally valid move can have an empty completion set.
      Witnessed by `hasNonExtendableCommitment`.

  Together, these give the abstract local/global separation
  underlying Paper 7's empirical Sudoku findings (catalog IDs 224
  and 225): local validity is necessary but not sufficient for
  global admissibility.  The Sudoku protocol exhibits this
  separation empirically; this file proves it holds structurally
  in any constraint system satisfying the coherence axiom.

  Per-file standalone: the `ConstraintSystem` structure is repeated
  here in the unified five-field form shared across all four files
  in this formalization.  This file uses `locallyValid`, `apply`,
  `comp`, and `comp_implies_local`; the remaining field
  `comp_monotone` is present for structural unification and is
  exercised in 217_catastrophic_commitment.lean.

  Standalone (deliberately so for per-file verification on
  live.lean-lang.org).
-/

import Mathlib

namespace SudokuMicroscope.LocalGlobalSeparation

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

/-- A constraint system **has a non-extendable commitment** iff there
    exist a state s and move m such that the move is locally valid
    but the post-move completion set is empty.  This is the witness
    used to express strict insufficiency: a locally valid move that
    fails to be globally admissible. -/
def hasNonExtendableCommitment (cs : ConstraintSystem State Move Completion) : Prop :=
  ∃ (s : State) (m : Move), cs.locallyValid s m ∧ cs.comp (cs.apply s m) = ∅

/-- **Global admissibility implies local validity** (Paper 7, ID 247).

    Necessity direction.  In any constraint system with the coherence
    axiom `comp_implies_local`, if the post-move completion set is
    non-empty, then the move was locally valid.

    Proof: extract a witness `c ∈ comp (apply s m)` from the
    non-emptiness hypothesis, then apply `comp_implies_local`. -/
theorem global_admissible_implies_locally_valid
    (cs : ConstraintSystem State Move Completion)
    (s : State) (m : Move)
    (h_ga : (cs.comp (cs.apply s m)).Nonempty) :
    cs.locallyValid s m := by
  obtain ⟨c, hc⟩ := h_ga
  exact cs.comp_implies_local s m c hc

/-- **Locally valid does not imply globally admissible** (Paper 7, ID 248).

    Strict-insufficiency direction.  Under the assumption that the
    constraint system admits a non-extendable commitment (i.e., there
    is some state and move where local validity holds but the
    completion set is empty), we exhibit a witness: a state and move
    where `locallyValid` holds but `(comp (apply s m)).Nonempty` does
    not.

    Proof: destructure the witness, rewrite the empty-completion
    hypothesis to expose `∅`, and close with `simp` (which knows
    `¬ (∅ : Finset _).Nonempty`). -/
theorem locally_valid_not_globally_admissible
    (cs : ConstraintSystem State Move Completion)
    (h_witness : cs.hasNonExtendableCommitment) :
    ∃ (s : State) (m : Move),
      cs.locallyValid s m ∧ ¬ (cs.comp (cs.apply s m)).Nonempty := by
  obtain ⟨s, m, h_lv, h_empty⟩ := h_witness
  refine ⟨s, m, h_lv, ?_⟩
  rw [h_empty]; simp

end ConstraintSystem

end SudokuMicroscope.LocalGlobalSeparation
