/-
Copyright (c) 2026 David Johnson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Johnson
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fintype.EquivFin

/-!
# Green's relations on a monoid

Green's relations `𝓡, 𝓛, 𝓙, 𝓗` (J. A. Green, 1951) are the fundamental tool of
semigroup theory: they compare elements of a monoid by the principal ideals they
generate. They are the non-commutative generalization of divisibility and
associatedness (cf. `Associated`, `· ∣ ·`).

This file defines the three Green preorders and the four Green equivalences on a
`Monoid`, their basic order/equivalence structure, the triviality predicates
(`IsJTrivial` etc.), and the closure of `𝓙`-triviality under finite products and
under injective homomorphisms (submonoids).

## Main definitions

* `Green.RLe`, `Green.LLe`, `Green.JLe` : the Green preorders
  (`a ≤𝓡 b ↔ a ∈ b·M`, etc.).
* `Green.R`, `Green.L`, `Green.J`, `Green.H` : the Green equivalences.
* `Green.IsRTrivial`, `IsLTrivial`, `IsJTrivial`, `IsHTrivial`.

## Main results

* `Green.RLe_preorder`, … : the preorders are reflexive and transitive.
* `Green.R_equivalence`, … : the equivalences are equivalence relations.
* `Green.IsJTrivial.prod`, `Green.IsJTrivial.of_injective` : `𝓙`-triviality is
  closed under finite products and under taking submonoids.

## Implementation notes

We work with `Monoid`, so the principal ideals are `b·M`, `M·b`, `M·b·M`
(the identity makes them contain `b`). For a bare `Semigroup` one would adjoin an
identity (`WithOne`); the monoid case is the common one and keeps statements clean.

## References

* J. A. Green, *On the structure of semigroups*, Ann. of Math. **54** (1951), 163–172.
* J.-É. Pin, *Mathematical Foundations of Automata Theory*.
-/

namespace Green

variable {M : Type*} [Monoid M]

/-! ### The Green preorders -/

/-- The `𝓡`-preorder: `a ≤𝓡 b` iff `a` lies in the principal right ideal `b·M`. -/
def RLe (a b : M) : Prop := ∃ x : M, a = b * x

/-- The `𝓛`-preorder: `a ≤𝓛 b` iff `a` lies in the principal left ideal `M·b`. -/
def LLe (a b : M) : Prop := ∃ x : M, a = x * b

/-- The `𝓙`-preorder: `a ≤𝓙 b` iff `a` lies in the principal two-sided ideal `M·b·M`. -/
def JLe (a b : M) : Prop := ∃ x y : M, a = x * b * y

@[refl] theorem RLe_refl (a : M) : RLe a a := ⟨1, (mul_one a).symm⟩
@[refl] theorem LLe_refl (a : M) : LLe a a := ⟨1, (one_mul a).symm⟩
@[refl] theorem JLe_refl (a : M) : JLe a a := ⟨1, 1, by simp⟩

theorem RLe_trans {a b c : M} (hab : RLe a b) (hbc : RLe b c) : RLe a c := by
  obtain ⟨x, hx⟩ := hab; obtain ⟨y, hy⟩ := hbc
  exact ⟨y * x, by rw [hx, hy, mul_assoc]⟩

theorem LLe_trans {a b c : M} (hab : LLe a b) (hbc : LLe b c) : LLe a c := by
  obtain ⟨x, hx⟩ := hab; obtain ⟨y, hy⟩ := hbc
  exact ⟨x * y, by rw [hx, hy, mul_assoc]⟩

theorem JLe_trans {a b c : M} (hab : JLe a b) (hbc : JLe b c) : JLe a c := by
  obtain ⟨x, y, hx⟩ := hab; obtain ⟨z, w, hz⟩ := hbc
  exact ⟨x * z, w * y, by rw [hx, hz]; simp only [mul_assoc]⟩

theorem RLe_of_JLe_left {a b : M} (h : RLe a b) : JLe a b := by
  obtain ⟨x, hx⟩ := h; exact ⟨1, x, by simp [hx]⟩

theorem LLe_of_JLe {a b : M} (h : LLe a b) : JLe a b := by
  obtain ⟨x, hx⟩ := h; exact ⟨x, 1, by simp [hx]⟩

/-! ### The Green equivalences -/

/-- Green's `𝓡`: `a` and `b` generate the same principal right ideal. -/
def R (a b : M) : Prop := RLe a b ∧ RLe b a
/-- Green's `𝓛`. -/
def L (a b : M) : Prop := LLe a b ∧ LLe b a
/-- Green's `𝓙`. -/
def J (a b : M) : Prop := JLe a b ∧ JLe b a
/-- Green's `𝓗 = 𝓡 ∩ 𝓛`. -/
def H (a b : M) : Prop := R a b ∧ L a b

theorem R_equivalence : Equivalence (R : M → M → Prop) where
  refl a := ⟨RLe_refl a, RLe_refl a⟩
  symm h := ⟨h.2, h.1⟩
  trans h₁ h₂ := ⟨RLe_trans h₁.1 h₂.1, RLe_trans h₂.2 h₁.2⟩

theorem L_equivalence : Equivalence (L : M → M → Prop) where
  refl a := ⟨LLe_refl a, LLe_refl a⟩
  symm h := ⟨h.2, h.1⟩
  trans h₁ h₂ := ⟨LLe_trans h₁.1 h₂.1, LLe_trans h₂.2 h₁.2⟩

theorem J_equivalence : Equivalence (J : M → M → Prop) where
  refl a := ⟨JLe_refl a, JLe_refl a⟩
  symm h := ⟨h.2, h.1⟩
  trans h₁ h₂ := ⟨JLe_trans h₁.1 h₂.1, JLe_trans h₂.2 h₁.2⟩

theorem H_equivalence : Equivalence (H : M → M → Prop) where
  refl a := ⟨R_equivalence.refl a, L_equivalence.refl a⟩
  symm h := ⟨R_equivalence.symm h.1, L_equivalence.symm h.2⟩
  trans h₁ h₂ := ⟨R_equivalence.trans h₁.1 h₂.1, L_equivalence.trans h₁.2 h₂.2⟩

theorem R_le_J {a b : M} (h : R a b) : J a b := ⟨RLe_of_JLe_left h.1, RLe_of_JLe_left h.2⟩
theorem L_le_J {a b : M} (h : L a b) : J a b := ⟨LLe_of_JLe h.1, LLe_of_JLe h.2⟩
theorem H_le_R {a b : M} (h : H a b) : R a b := h.1
theorem H_le_L {a b : M} (h : H a b) : L a b := h.2

/-! ### Triviality predicates -/

/-- `M` is `𝓙`-trivial if Green's `𝓙` is equality (every `𝓙`-class is a singleton). -/
def IsJTrivial (M : Type*) [Monoid M] : Prop := ∀ a b : M, J a b → a = b
/-- `M` is `𝓡`-trivial. -/
def IsRTrivial (M : Type*) [Monoid M] : Prop := ∀ a b : M, R a b → a = b
/-- `M` is `𝓛`-trivial. -/
def IsLTrivial (M : Type*) [Monoid M] : Prop := ∀ a b : M, L a b → a = b
/-- `M` is `𝓗`-trivial. -/
def IsHTrivial (M : Type*) [Monoid M] : Prop := ∀ a b : M, H a b → a = b

theorem isJTrivial_of_subsingleton (M : Type*) [Monoid M] [Subsingleton M] :
    IsJTrivial M := fun a b _ => Subsingleton.elim a b

/-! ### Functoriality and closure of `𝓙`-triviality -/

/-- The `𝓙`-preorder transports forward along any monoid hom. -/
theorem JLe.map {N : Type*} [Monoid N] (f : M →* N) {a b : M} (h : JLe a b) :
    JLe (f a) (f b) := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨f x, f y, by rw [hxy]; simp [map_mul]⟩

/-- **Submonoid / division closure.** An injective hom into a `𝓙`-trivial monoid has
a `𝓙`-trivial domain; equivalently, submonoids of `𝓙`-trivial monoids are
`𝓙`-trivial. -/
theorem IsJTrivial.of_injective {N : Type*} [Monoid N] (f : N →* M)
    (hf : Function.Injective f) (hM : IsJTrivial M) : IsJTrivial N :=
  fun a b hab => hf (hM (f a) (f b) ⟨hab.1.map f, hab.2.map f⟩)

/-- **Finite product closure.** A product of `𝓙`-trivial monoids is `𝓙`-trivial. -/
theorem IsJTrivial.prod {N : Type*} [Monoid N]
    (hM : IsJTrivial M) (hN : IsJTrivial N) : IsJTrivial (M × N) := by
  rintro a b ⟨⟨s, t, hab⟩, ⟨s', t', hba⟩⟩
  have hab1 := congrArg Prod.fst hab; have hab2 := congrArg Prod.snd hab
  have hba1 := congrArg Prod.fst hba; have hba2 := congrArg Prod.snd hba
  simp only [Prod.fst_mul, Prod.snd_mul] at hab1 hab2 hba1 hba2
  exact Prod.ext (hM a.1 b.1 ⟨⟨s.1, t.1, hab1⟩, ⟨s'.1, t'.1, hba1⟩⟩)
                 (hN a.2 b.2 ⟨⟨s.2, t.2, hab2⟩, ⟨s'.2, t'.2, hba2⟩⟩)

end Green
