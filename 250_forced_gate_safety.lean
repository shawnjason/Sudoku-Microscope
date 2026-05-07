/-
  250_forced_gate_safety.lean

  Catalog ID 250.  Paper 7 (Sudoku-Microscope), abstract formalization companion.

  Author : Shawn Kevin Jason
  Repo   : github.com/shawnjason/Sudoku-Microscope  (forthcoming)

  Forced-Gate Safety.

  A *forced gate* is one that admits only globally-admissible moves —
  those whose post-move completion set is non-empty.  Forced-gate
  enforcement preserves non-emptiness across the whole trajectory: if
  the starting state has at least one completion and every move along
  the trajectory passes the gate, then the terminal state also has at
  least one completion.  This is the per-step safety guarantee that
  the optional/voluntary verification mode fails to provide, and the
  asymmetry the Sudoku microscope is constructed to expose.

  ID 250 catalogs the abstract forced-gate safety theorem (the
  structural reason that admissibility-conditioned policies preserve
  safety across the trajectory).  See also catalog ID 228 (the
  empirical finding that admissibility-conditioned commitment prevents
  observed first foreclosure in the reported Sudoku suites) for
  cross-reference.

  Per-file standalone: the `ConstraintSystem` structure is repeated
  here in the unified five-field form shared across all four files
  in this formalization.  The theorem in this file uses only `apply`
  and `comp`; the remaining fields (`locallyValid`, `comp_implies_local`,
  `comp_monotone`) are present for structural unification and are
  exercised in other files in the framework.

  Standalone (deliberately so for per-file verification on
  live.lean-lang.org).
-/

import Mathlib

namespace SudokuMicroscope.ForcedGateSafety

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

/-- A move (s, m) is **globally admissible** iff applying it leaves the
    completion set non-empty.  This is the gate condition: a "forced
    gate" is one that admits only globally-admissible moves. -/
def globallyAdmissible (cs : ConstraintSystem State Move Completion)
    (s : State) (m : Move) : Prop :=
  (cs.comp (cs.apply s m)).Nonempty

/-- Apply a list of moves to a starting state, threading state through
    each step. -/
def applyTrajectory (cs : ConstraintSystem State Move Completion)
    (s₀ : State) : List Move → State
  | []       => s₀
  | m :: ms  => cs.applyTrajectory (cs.apply s₀ m) ms

/-- A trajectory is **forced-gate safe** from s₀ iff every move it
    contains is globally admissible at the state to which it is applied.
    This is the runtime invariant a forced gate enforces. -/
def forcedGateSafe (cs : ConstraintSystem State Move Completion)
    (s₀ : State) : List Move → Prop
  | []       => True
  | m :: ms  => cs.globallyAdmissible s₀ m ∧ cs.forcedGateSafe (cs.apply s₀ m) ms

/-- **Forced-Gate Safety** (Paper 7, ID 250).

    If a trajectory is forced-gate safe starting from a state with a
    non-empty completion set, then the completion set at the terminal
    state is also non-empty.  Forced-gate enforcement preserves non-
    emptiness across the whole trajectory.

    Proof: induction on the trajectory list, generalizing over the start
    state.  The empty case is the initial hypothesis.  In the cons case,
    `globallyAdmissible s₀ m` directly gives non-emptiness at the post-
    head state `cs.apply s₀ m`; apply the IH from there. -/
theorem forced_gate_safety
    (cs : ConstraintSystem State Move Completion)
    (ms : List Move)
    (s₀ : State)
    (h_init : (cs.comp s₀).Nonempty)
    (h_safe : cs.forcedGateSafe s₀ ms) :
    (cs.comp (cs.applyTrajectory s₀ ms)).Nonempty := by
  induction ms generalizing s₀ with
  | nil => exact h_init
  | cons m ms ih =>
    obtain ⟨h_ga, h_rest⟩ := h_safe
    exact ih (cs.apply s₀ m) h_ga h_rest

end ConstraintSystem

end SudokuMicroscope.ForcedGateSafety
