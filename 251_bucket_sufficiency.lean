/-
  251_bucket_sufficiency.lean

  Catalog ID 251.  Paper 7 (Sudoku-Microscope), abstract formalization companion.

  Author : Shawn Kevin Jason
  Repo   : github.com/shawnjason/Sudoku-Microscope  (forthcoming)

  Bucket Sufficiency.

  The catastrophic-commitment predicate, defined on the 0/≥1 bucket
  of |Comp|, is equivalent to the same predicate stated on the full
  cardinality count.  The bucket abstraction therefore loses no
  safety information relative to retaining the full count: the same
  set of catastrophic commitments is detected in either representation.
  The cardinality |Comp| tracks more than safety reasoning needs.

  ID 251 catalogs the abstract bucket-sufficiency theorem (the
  structural reason that the bucket form and cardinality form of the
  catastrophic-commitment predicate coincide).  See also catalog
  ID 246 (the protocol-design corollary that the Sudoku microscope
  uses bucketed safety signal rather than full admissibility entropy)
  for cross-reference.

  This justifies the bucket abstraction used throughout the
  Sudoku-Microscope formalization: any safety question we ask
  factors through the binary 0/≥1 distinction.  Cardinality could
  matter for non-safety questions (rate of completion-set shrinkage,
  branching-factor estimation, search-difficulty heuristics), but
  bucket sufficiency makes no claim about those.

  Per-file standalone: the `ConstraintSystem` structure is repeated
  here in the unified five-field form shared across all four files
  in this formalization.  The theorems in this file use only `apply`
  and `comp`; the remaining fields are present for structural
  unification.  The `catastrophicCommitment` predicate is also
  restated here (cf. file 217) for self-containment.

  Standalone (deliberately so for per-file verification on
  live.lean-lang.org).
-/

import Mathlib

namespace SudokuMicroscope.BucketSufficiency

/-- Abstract constraint system.  Unified structure used across the
    Sudoku-Microscope formalization. -/
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

/-- The catastrophic-commitment predicate in **bucket form** — the
    formulation used in file 217_catastrophic_commitment.lean (Paper 7,
    ID 217).  The pre-state has a non-empty completion set; the post-
    state's completion set is empty. -/
def catastrophicCommitment (cs : ConstraintSystem State Move Completion)
    (s : State) (m : Move) : Prop :=
  (cs.comp s).Nonempty ∧ cs.comp (cs.apply s m) = ∅

/-- The catastrophic-commitment predicate in **cardinality form** — the
    same condition stated in terms of the full count |Comp| rather than
    the bucket.  The pre-state has at least one completion; the post-
    state has zero. -/
def catastrophicCommitmentByCard (cs : ConstraintSystem State Move Completion)
    (s : State) (m : Move) : Prop :=
  (cs.comp s).card ≥ 1 ∧ (cs.comp (cs.apply s m)).card = 0

/-- **Bucket-card equivalence (non-empty side).**  A `Finset` is non-empty
    iff its cardinality is at least one.  This is the basic lemma that
    makes the bucket equivalent to a card-threshold check at 1. -/
theorem nonempty_iff_card_pos (s : Finset Completion) :
    s.Nonempty ↔ s.card ≥ 1 := by
  rw [← Finset.card_pos]
  omega

/-- **Bucket-card equivalence (empty side).**  A `Finset` is the empty
    set iff its cardinality is zero. -/
theorem empty_iff_card_zero (s : Finset Completion) :
    s = ∅ ↔ s.card = 0 :=
  Finset.card_eq_zero.symm

/-- **Bucket Sufficiency** (Paper 7, ID 251).

    The catastrophic-commitment predicate, defined on the 0/≥1 bucket
    of |Comp|, is equivalent to the same predicate stated on the full
    cardinality count.  The bucket abstraction therefore loses no
    safety information relative to retaining the full count: the same
    set of catastrophic commitments is detected in either
    representation.  The cardinality tracks more than safety reasoning
    needs.

    Proof: unfold both predicates, then rewrite the bucket conjuncts
    using the basic bucket-card equivalences.  The two forms become
    syntactically identical and `rw` closes by reflexivity. -/
theorem bucket_sufficiency
    (cs : ConstraintSystem State Move Completion)
    (s : State) (m : Move) :
    cs.catastrophicCommitment s m ↔ cs.catastrophicCommitmentByCard s m := by
  unfold catastrophicCommitment catastrophicCommitmentByCard
  rw [nonempty_iff_card_pos, empty_iff_card_zero]

end ConstraintSystem

end SudokuMicroscope.BucketSufficiency
