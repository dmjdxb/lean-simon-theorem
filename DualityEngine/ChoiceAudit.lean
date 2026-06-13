/-
Copyright (c) 2026 DualityEngine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DualityEngine.Green
import DualityEngine.Syntactic
import Mathlib.Logic.Basic

/-!
# Choice audit (PRD E5)

The `#print axioms` discipline: every completed theorem is audited for its axiom
dependencies, isolating exactly where `Classical.choice` (the proof-assistant
analogue of the Axiom of Choice) enters. This is the formal counterpart of the
hand-located **BPI / ultrafilter-lemma sites** in the project's P2 Stone-duality
construction (compactness of the dual space; injectivity and surjectivity of the
unit `η`). REGISTRY: Stone representation ⟺ BPI over ZF (strictly weaker than AC).

Below: constructive (choice-free) lemmas vs. a deliberately classical one,
demonstrating the audit. Run `lake build` and read the `#print axioms` output, or
open in an editor.
-/

namespace DualityEngine

/-- CONSTRUCTIVE: Green's `𝓙` is reflexive. Audit should show NO `Classical.choice`. -/
theorem audit_greenJ_refl {M : Type*} [Monoid M] (a : M) : greenJ a a :=
  greenJ_refl a

/-- CONSTRUCTIVE: Green's `𝓙` is symmetric. NO `Classical.choice`. -/
theorem audit_greenJ_symm {M : Type*} [Monoid M] {a b : M} (h : greenJ a b) :
    greenJ b a := greenJ_symm h

/-- CONSTRUCTIVE: any subsingleton monoid is `𝓙`-trivial. NO `Classical.choice`. -/
theorem audit_subsingleton_jtrivial {M : Type*} [Monoid M] [Subsingleton M] :
    IsJTrivial M := isJTrivial_of_subsingleton M

/-- CLASSICAL: excluded middle — the cleanest witness that `Classical.choice`
enters (em is derived from choice in Lean). The duality's BPI sites are of this
classical character. -/
theorem audit_uses_classical (p : Prop) : p ∨ ¬ p :=
  Classical.em p

-- The audit itself (visible in build output). Note: `propext` and `Quot.sound`
-- are NOT choice — only `Classical.choice` is the Axiom-of-Choice analogue.
#print axioms audit_greenJ_refl            -- expect: no Classical.choice
#print axioms audit_greenJ_symm            -- expect: no Classical.choice
#print axioms audit_subsingleton_jtrivial  -- expect: no Classical.choice
#print axioms audit_uses_classical         -- expect: Classical.choice present

end DualityEngine
