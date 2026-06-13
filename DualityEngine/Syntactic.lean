/-
Copyright (c) 2026 David Johnson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Johnson
-/
import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# The syntactic monoid of a language

Absent from Mathlib v4.29.1 (REGISTRY R4: only `Computability.Language` and
`MyhillNerode` exist; no syntactic monoid). We build it as the quotient of the
free monoid by the **syntactic congruence**: `u ≈ v` iff `u` and `v` are
interchangeable in every two-sided context.

Sorry-free: the congruence (reflexivity, symmetry, transitivity, and
multiplicative compatibility) is fully proved; `SyntacticMonoid L` is then a
`Monoid` by the generic `Con.Quotient` instance.
-/

namespace DualityEngine

variable {α : Type*}

/-- The **syntactic congruence** of a language `L ⊆ FreeMonoid α`. -/
def syntacticCon (L : Set (FreeMonoid α)) : Con (FreeMonoid α) where
  r u v := ∀ x y : FreeMonoid α, (x * u * y ∈ L ↔ x * v * y ∈ L)
  iseqv :=
    { refl := fun _ _ _ => Iff.rfl
      symm := fun h x y => (h x y).symm
      trans := fun h1 h2 x y => (h1 x y).trans (h2 x y) }
  mul' := by
    intro a b c d hab hcd x y
    have h1 := hab x (c * y)
    have h2 := hcd (x * b) y
    simp only [mul_assoc] at h1 h2 ⊢
    exact h1.trans h2

/-- The **syntactic monoid** `M(L) = FreeMonoid α / ≈_L`. -/
def SyntacticMonoid (L : Set (FreeMonoid α)) : Type _ := (syntacticCon L).Quotient

instance (L : Set (FreeMonoid α)) : Monoid (SyntacticMonoid L) :=
  inferInstanceAs (Monoid (syntacticCon L).Quotient)

/-- The syntactic morphism `FreeMonoid α → M(L)`. -/
def syntacticMorphism (L : Set (FreeMonoid α)) : FreeMonoid α →* SyntacticMonoid L :=
  (syntacticCon L).mk'

end DualityEngine
