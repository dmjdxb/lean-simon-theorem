/-
Copyright (c) 2026 DualityEngine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Green's relations on a monoid

Confirmed ABSENT from Mathlib as of v4.29.1 (project REGISTRY R4): no Green's
relations, no syntactic-monoid API. This module defines the four Green preorders
and relations `𝓡, 𝓛, 𝓙, 𝓗` via principal ideals, and the corresponding
triviality predicates used by Simon's theorem (`IsJTrivial`) and the
Schützenberger / Brzozowski–Fich lines (`IsRTrivial`, `IsLTrivial`, aperiodicity
proxy `IsHTrivial`).

These are sorry-free definitions (PRD E5 Target A: build the API).
-/

namespace DualityEngine

variable {M : Type*} [Monoid M]

/-- Principal right ideal `a·M¹` (monoid: `t = 1` gives `a` itself). -/
def rightIdeal (a : M) : Set M := {x | ∃ t : M, x = a * t}

/-- Principal left ideal `M¹·a`. -/
def leftIdeal (a : M) : Set M := {x | ∃ s : M, x = s * a}

/-- Principal two-sided ideal `M¹·a·M¹`. -/
def twoSidedIdeal (a : M) : Set M := {x | ∃ s t : M, x = s * a * t}

/-- `a ≤𝓡 b`: `a` lies in the principal right ideal of `b`. -/
def greenRLe (a b : M) : Prop := a ∈ rightIdeal b
/-- `a ≤𝓛 b`. -/
def greenLLe (a b : M) : Prop := a ∈ leftIdeal b
/-- `a ≤𝓙 b`. -/
def greenJLe (a b : M) : Prop := a ∈ twoSidedIdeal b

/-- Green's `𝓡`: same principal right ideal. -/
def greenR (a b : M) : Prop := greenRLe a b ∧ greenRLe b a
/-- Green's `𝓛`. -/
def greenL (a b : M) : Prop := greenLLe a b ∧ greenLLe b a
/-- Green's `𝓙`. -/
def greenJ (a b : M) : Prop := greenJLe a b ∧ greenJLe b a
/-- Green's `𝓗 = 𝓡 ∩ 𝓛`. -/
def greenH (a b : M) : Prop := greenR a b ∧ greenL a b

/-- `M` is `𝓙`-trivial: every `𝓙`-class is a singleton. (Simon: ⟺ piecewise testable.) -/
def IsJTrivial (M : Type*) [Monoid M] : Prop := ∀ a b : M, greenJ a b → a = b
/-- `M` is `𝓡`-trivial. -/
def IsRTrivial (M : Type*) [Monoid M] : Prop := ∀ a b : M, greenR a b → a = b
/-- `M` is `𝓛`-trivial. -/
def IsLTrivial (M : Type*) [Monoid M] : Prop := ∀ a b : M, greenL a b → a = b
/-- `M` is `𝓗`-trivial (⟺ aperiodic, for finite `M`). -/
def IsHTrivial (M : Type*) [Monoid M] : Prop := ∀ a b : M, greenH a b → a = b

/-- `≤𝓙` is reflexive (small sorry-free lemma; used by the choice audit). -/
theorem greenJLe_refl (a : M) : greenJLe a a := ⟨1, 1, by simp⟩

/-- Green's `𝓙` is reflexive. -/
theorem greenJ_refl (a : M) : greenJ a a := ⟨greenJLe_refl a, greenJLe_refl a⟩

/-- Green's `𝓙` is symmetric. -/
theorem greenJ_symm {a b : M} (h : greenJ a b) : greenJ b a := ⟨h.2, h.1⟩

/-- `𝓙`-triviality is preserved by monoid isomorphism's target being a subsingleton:
the trivial monoid is `𝓙`-trivial (sorry-free, constructive). -/
theorem isJTrivial_of_subsingleton (M : Type*) [Monoid M] [Subsingleton M] :
    IsJTrivial M := fun a b _ => Subsingleton.elim a b

/-! ## Closure properties of `𝓙`-triviality (two of the three pseudovariety axioms)

The `𝓙`-trivial monoids form a pseudovariety: closed under finite **product**,
**submonoids** (division domain), and **quotients**. The first two are proved here
sorry-free; the third (quotient closure) is the genuinely hard one — it has no
elementary proof and needs the equational characterization of `𝓙`-triviality
(finiteness + Green's-lemma theory absent from Mathlib). -/

/-- Ideal membership transports forward along any monoid hom:
`a ∈ M¹·b·M¹ ⟹ f a ∈ N¹·(f b)·N¹`. -/
theorem greenJLe_map {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {a b : M}
    (h : greenJLe a b) : greenJLe (f a) (f b) := by
  obtain ⟨s, t, hst⟩ := h
  exact ⟨f s, f t, by rw [hst]; simp [map_mul]⟩

/-- **Submonoid / division closure**: an injective hom into a `𝓙`-trivial monoid
has a `𝓙`-trivial domain. (So submonoids of `𝓙`-trivial monoids are `𝓙`-trivial.) -/
theorem isJTrivial_of_injHom {M N : Type*} [Monoid M] [Monoid N] (f : N →* M)
    (hf : Function.Injective f) (hM : IsJTrivial M) : IsJTrivial N := by
  intro a b hab
  exact hf (hM (f a) (f b) ⟨greenJLe_map f hab.1, greenJLe_map f hab.2⟩)

/-- **Finite product closure**: a product of `𝓙`-trivial monoids is `𝓙`-trivial.
(The two-sided ideal of a pair is the product of the component ideals.) -/
theorem isJTrivial_prod {M N : Type*} [Monoid M] [Monoid N]
    (hM : IsJTrivial M) (hN : IsJTrivial N) : IsJTrivial (M × N) := by
  rintro a b ⟨⟨s, t, hab⟩, ⟨s', t', hba⟩⟩
  have hab1 := congrArg Prod.fst hab; have hab2 := congrArg Prod.snd hab
  have hba1 := congrArg Prod.fst hba; have hba2 := congrArg Prod.snd hba
  simp only [Prod.fst_mul, Prod.snd_mul] at hab1 hab2 hba1 hba2
  have e1 : a.1 = b.1 := hM a.1 b.1 ⟨⟨s.1, t.1, hab1⟩, ⟨s'.1, t'.1, hba1⟩⟩
  have e2 : a.2 = b.2 := hN a.2 b.2 ⟨⟨s.2, t.2, hab2⟩, ⟨s'.2, t'.2, hba2⟩⟩
  exact Prod.ext e1 e2

/-- **Foundational brick (sorry-free).** In a finite monoid, every element has a
positive **idempotent power**: `∃ n > 0, (x^n)·(x^n) = x^n`. Proof: `k ↦ x^k` is not
injective (pigeonhole, `ℕ` infinite into finite `M`), giving `x^a = x^b` with `a<b`,
period `p = b-a`; then `x^c = x^{c+p}` for all `c ≥ a`, so `x^{(a+1)p}` is idempotent.

This is the first lemma of finite-monoid structure theory — **confirmed absent from
Mathlib** (which has `IsIdempotentElem` and its API, but no existence result for
finite monoids; `exists_pow_eq_one` is group/torsion-only). It is the base on which a
real proof of `isJTrivial_of_surjHom` is built (idempotent powers → unique idempotent
of `⟨x⟩` → the equational characterization of finite `𝓙`-triviality). Proved here
sorry-free; the remaining theory above it is the open gap. -/
theorem exists_idempotent_pow {M : Type*} [Monoid M] [Finite M] (x : M) :
    ∃ n : ℕ, 0 < n ∧ IsIdempotentElem (x ^ n) := by
  have key : ∀ a b : ℕ, a < b → x ^ a = x ^ b →
      ∃ n : ℕ, 0 < n ∧ IsIdempotentElem (x ^ n) := by
    intro a b hab hxab
    set p := b - a with hp
    have hp0 : 0 < p := Nat.sub_pos_of_lt hab
    have hbase : x ^ a = x ^ (a + p) := by
      rw [hp, Nat.add_sub_cancel' hab.le]; exact hxab
    have hshift : ∀ c, a ≤ c → x ^ c = x ^ (c + p) := by
      intro c hc
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
      rw [pow_add x a d, hbase, ← pow_add]
      congr 1; omega
    have hiter : ∀ k c, a ≤ c → x ^ c = x ^ (c + k * p) := by
      intro k
      induction k with
      | zero => intro c _; simp
      | succ m ih =>
        intro c hc
        have hmp : (m + 1) * p = m * p + p := Nat.succ_mul m p
        rw [ih c hc, hshift (c + m * p) (le_trans hc (Nat.le_add_right _ _))]
        congr 1; omega
    refine ⟨(a + 1) * p, Nat.mul_pos (by omega) hp0, ?_⟩
    have hge : a ≤ (a + 1) * p :=
      le_trans (Nat.le_succ a) (Nat.le_mul_of_pos_right (a + 1) hp0)
    have hmul := hiter (a + 1) ((a + 1) * p) hge
    show x ^ ((a + 1) * p) * x ^ ((a + 1) * p) = x ^ ((a + 1) * p)
    rw [← pow_add]
    exact hmul.symm
  obtain ⟨i, j, hxij, hij⟩ := Function.not_injective_iff.mp
    (not_injective_infinite_finite (fun k : ℕ => x ^ k))
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt hxij
  · exact key j i hlt hxij.symm

/-- **Foundational brick 2 (sorry-free) — uniqueness of the idempotent power.**
Two *positive* powers of `x` that are both idempotent are equal — in ANY monoid
(no finiteness needed). The reason: an idempotent `e = x^m` satisfies `e = eⁿ`, i.e.
`x^m = x^{mn}`; symmetrically `x^n = x^{nm}`; and `mn = nm`.

Together with `exists_idempotent_pow`, this makes `x^ω` — the idempotent power of `x`
— a **well-defined** element of a finite monoid (the unique idempotent of the
monogenic subsemigroup `⟨x⟩`), which the equational characterization of finite
`𝓙`-triviality is stated over. -/
theorem idempotent_pow_unique {M : Type*} [Monoid M] {x : M} {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (him : IsIdempotentElem (x ^ m))
    (hin : IsIdempotentElem (x ^ n)) : x ^ m = x ^ n :=
  calc x ^ m = (x ^ m) ^ n := (him.pow_eq (Nat.pos_iff_ne_zero.mp hn)).symm
    _ = x ^ (m * n) := by rw [← pow_mul]
    _ = x ^ (n * m) := by rw [Nat.mul_comm m n]
    _ = (x ^ n) ^ m := by rw [pow_mul]
    _ = x ^ n := hin.pow_eq (Nat.pos_iff_ne_zero.mp hm)

/-- **Existence + uniqueness, packaged (sorry-free).** In a finite monoid, `⟨x⟩` has a
**unique** idempotent: there is exactly one `e` that is a positive power of `x` and is
idempotent. This is the well-defined object `x^ω`. -/
theorem exists_unique_idempotent_pow {M : Type*} [Monoid M] [Finite M] (x : M) :
    ∃! e : M, (∃ n : ℕ, 0 < n ∧ x ^ n = e) ∧ IsIdempotentElem e := by
  obtain ⟨n, hn, hid⟩ := exists_idempotent_pow x
  refine ⟨x ^ n, ⟨⟨n, hn, rfl⟩, hid⟩, ?_⟩
  rintro e ⟨⟨k, hk, rfl⟩, hek⟩
  exact idempotent_pow_unique hk hn hek hid

/-- **Foundational brick 3 (sorry-free) — aperiodicity at `x^ω`.** In a `𝓙`-trivial
monoid, if `x^n` is idempotent (`n>0`) then `x^{n+1} = x^n` — i.e. `x^{ω+1} = x^ω`.
This is the first place `𝓙`-triviality is actually *used*: the (would-be) cyclic group
sitting at the idempotent `x^ω` is a single `𝓙`-class, so `𝓙`-triviality collapses it.

The mechanism, made elementary: `x^{ω}` and `x^{ω+1}` are mutually `≤𝓙`. One way is
immediate (`x^{n+1} = 1·x^n·x`). The other is the key computation
`(x^{n+1})^n = x^{n²+n} = x^{n²}·x^n = x^n·x^n = x^n` (using `x^n` idempotent), so
`x^n` is a *power* of `x^{n+1}`, hence `x^n ≤𝓙 x^{n+1}`. Then `𝓙`-triviality forces
`x^n = x^{n+1}`. (No finiteness needed here — idempotency is the hypothesis.) -/
theorem jtrivial_pow_succ_eq {M : Type*} [Monoid M] (hM : IsJTrivial M) (x : M)
    {n : ℕ} (hn : 0 < n) (hid : IsIdempotentElem (x ^ n)) : x ^ (n + 1) = x ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  have hkey : (x ^ (m + 1 + 1)) ^ (m + 1) = x ^ (m + 1) := by
    rw [← pow_mul, Nat.succ_mul (m + 1) (m + 1), pow_add, pow_mul,
        hid.pow_eq (Nat.succ_ne_zero m)]
    exact hid
  apply hM
  refine ⟨⟨1, x, ?_⟩, ⟨1, (x ^ (m + 1 + 1)) ^ m, ?_⟩⟩
  · rw [one_mul, ← pow_succ]
  · rw [one_mul, ← pow_succ', hkey]

/-- **Aperiodicity (per element).** A finite `𝓙`-trivial monoid is aperiodic: every `x`
satisfies `x^{n+1} = x^n` for some `n>0` (combine `exists_idempotent_pow` with
`jtrivial_pow_succ_eq`). Equivalently, no element generates a nontrivial cyclic group —
the structural step from `𝓙`-trivial toward the equational characterization. -/
theorem jtrivial_aperiodic {M : Type*} [Monoid M] [Finite M] (hM : IsJTrivial M)
    (x : M) : ∃ n : ℕ, 0 < n ∧ x ^ (n + 1) = x ^ n := by
  obtain ⟨n, hn, hid⟩ := exists_idempotent_pow x
  exact ⟨n, hn, jtrivial_pow_succ_eq hM x hn hid⟩

/-- **Foundational brick 4 (sorry-free) — the `(xy)^ω = (yx)^ω` identity.** In a
`𝓙`-trivial monoid, if `(xy)^n` and `(yx)^n` are both idempotent (`n>0`) then
`(xy)^n = (yx)^n` — i.e. `(xy)^ω = (yx)^ω`. Together with aperiodicity
(`x^{ω+1}=x^ω`), this is the **standard equational basis of the pseudovariety J**.

Proof: the conjugation identity `a·(ba)^k = (ab)^k·a` (induction) gives
`x·(yx)^n·y = (xy)^n·x·y = (xy)^{n+1}`, which **aperiodicity** (`jtrivial_pow_succ_eq`)
collapses to `(xy)^n`. So `e := (xy)^n = x·f·y` with `f := (yx)^n`, giving `e ≤𝓙 f`;
symmetrically `f = y·e·x ≤𝓙 e`. Hence `e 𝓙 f`, and `𝓙`-triviality forces `e = f`.
(No finiteness needed — both idempotencies are hypotheses.) -/
theorem jtrivial_mul_pow_comm {M : Type*} [Monoid M] (hM : IsJTrivial M) (x y : M)
    {n : ℕ} (hn : 0 < n) (hxy : IsIdempotentElem ((x * y) ^ n))
    (hyx : IsIdempotentElem ((y * x) ^ n)) : (x * y) ^ n = (y * x) ^ n := by
  have conj : ∀ (a b : M) (k : ℕ), a * (b * a) ^ k = (a * b) ^ k * a := by
    intro a b k
    induction k with
    | zero => simp
    | succ j ih =>
      calc a * (b * a) ^ (j + 1)
          = (a * (b * a) ^ j) * (b * a) := by rw [pow_succ, ← mul_assoc]
        _ = ((a * b) ^ j * a) * (b * a) := by rw [ih]
        _ = (a * b) ^ j * ((a * b) * a) := by rw [mul_assoc, ← mul_assoc a b a]
        _ = (a * b) ^ (j + 1) * a := by rw [← mul_assoc, ← pow_succ]
  have hef : x * (y * x) ^ n * y = (x * y) ^ n := by
    rw [conj x y n, mul_assoc, ← pow_succ, jtrivial_pow_succ_eq hM (x * y) hn hxy]
  have hfe : y * (x * y) ^ n * x = (y * x) ^ n := by
    rw [conj y x n, mul_assoc, ← pow_succ, jtrivial_pow_succ_eq hM (y * x) hn hyx]
  exact hM _ _ ⟨⟨x, y, hef.symm⟩, ⟨y, x, hfe.symm⟩⟩

/-- **The `(xy)^ω = (yx)^ω` identity, packaged.** In a finite `𝓙`-trivial monoid there
is a common exponent `n>0` at which `(xy)^n` and `(yx)^n` are both idempotent (hence
each is the respective `ω`-power, by uniqueness) and equal. This is the second J-identity
in usable existential form. -/
theorem jtrivial_mul_omega_comm {M : Type*} [Monoid M] [Finite M] (hM : IsJTrivial M)
    (x y : M) : ∃ n : ℕ, 0 < n ∧ IsIdempotentElem ((x * y) ^ n) ∧
      IsIdempotentElem ((y * x) ^ n) ∧ (x * y) ^ n = (y * x) ^ n := by
  obtain ⟨a, ha, hida⟩ := exists_idempotent_pow (x * y)
  obtain ⟨b, hb, hidb⟩ := exists_idempotent_pow (y * x)
  have hxy : IsIdempotentElem ((x * y) ^ (a * b)) := by
    rw [pow_mul, hida.pow_eq (Nat.pos_iff_ne_zero.mp hb)]; exact hida
  have hyx : IsIdempotentElem ((y * x) ^ (a * b)) := by
    rw [Nat.mul_comm a b, pow_mul, hidb.pow_eq (Nat.pos_iff_ne_zero.mp ha)]; exact hidb
  exact ⟨a * b, Nat.mul_pos ha hb, hxy, hyx,
    jtrivial_mul_pow_comm hM x y (Nat.mul_pos ha hb) hxy hyx⟩

/-! ## Finite-monoid stability and the converse — `isJTrivial_of_surjHom` FULLY PROVED

The converse of the equational characterization of **J** is proved here from an
**elementary stability lemma** (`p 𝓙 pq ⟹ p 𝓡 pq`, via idempotent powers) — no
Mathlib finite-semigroup machinery needed (it has none). The correct basis used is the
**R-identity ∧ L-identity** (`J = R ∩ L`); these are proved forward (bricks 5a/5b) and
transported across the surjection, then the converse concludes. -/

/-- Transitivity of the `𝓙`-preorder. -/
theorem greenJLe_trans {a b c : M} (h1 : greenJLe a b) (h2 : greenJLe b c) :
    greenJLe a c := by
  obtain ⟨s, t, hst⟩ := h1; obtain ⟨u, v, huv⟩ := h2
  exact ⟨s * u, v * t, by rw [hst, huv]; simp only [mul_assoc]⟩

/-- `≤𝓡` refines `≤𝓙`. -/
theorem greenJLe_of_greenRLe {a b : M} (h : greenRLe a b) : greenJLe a b := by
  obtain ⟨t, ht⟩ := h; exact ⟨1, t, by rw [ht, one_mul]⟩

/-- `≤𝓛` refines `≤𝓙`. -/
theorem greenJLe_of_greenLLe {a b : M} (h : greenLLe a b) : greenJLe a b := by
  obtain ⟨s, hs⟩ := h; exact ⟨s, 1, by rw [hs, mul_one]⟩

/-- **Stability (R-side) — elementary, sorry-free.** In a FINITE monoid,
`p 𝓙 pq ⟹ p 𝓡 pq`. Proof: `p ≤𝓙 pq` gives `p = x·p·w` (`w = qy`); iterate to
`p = xᵐ·p·wᵐ` and take `m` the idempotent exponent of `w`, so `p·wᵐ = p`; since
`wᵐ = (qy)ᵐ` begins with `q`, `p = pq·z`. (This is the finiteness input that the
identities alone cannot supply — but it needs only idempotent powers, no Green's-lemma
theory.) -/
theorem stabR [Finite M] {p q : M} (h : greenJ p (p * q)) : greenR p (p * q) := by
  refine ⟨?_, ⟨q, rfl⟩⟩
  obtain ⟨x, y, hxy⟩ := h.1
  obtain ⟨m, hm, hidw⟩ := exists_idempotent_pow (q * y)
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
  have hpw : p = x * p * (q * y) := by
    conv_lhs => rw [hxy]
    simp only [mul_assoc]
  have hk : ∀ k, x ^ k * p * (q * y) ^ k = p := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
      rw [pow_succ' x j, pow_succ (q * y) j]
      calc (x * x ^ j) * p * ((q * y) ^ j * (q * y))
          = x * (x ^ j * p * (q * y) ^ j) * (q * y) := by simp only [mul_assoc]
        _ = x * p * (q * y) := by rw [ih]
        _ = p := hpw.symm
  have hph : p * (q * y) ^ (m' + 1) = p := by
    calc p * (q * y) ^ (m' + 1)
        = (x ^ (m' + 1) * p * (q * y) ^ (m' + 1)) * (q * y) ^ (m' + 1) := by rw [hk]
      _ = x ^ (m' + 1) * p * ((q * y) ^ (m' + 1) * (q * y) ^ (m' + 1)) := by
            simp only [mul_assoc]
      _ = x ^ (m' + 1) * p * (q * y) ^ (m' + 1) := by rw [hidw]
      _ = p := hk (m' + 1)
  refine ⟨y * (q * y) ^ m', ?_⟩
  conv_lhs => rw [← hph]
  rw [pow_succ' (q * y) m']
  simp only [mul_assoc]

/-- **Stability (L-side) — elementary, sorry-free.** Dually, `p 𝓙 qp ⟹ p 𝓛 qp`. -/
theorem stabL [Finite M] {p q : M} (h : greenJ p (q * p)) : greenL p (q * p) := by
  refine ⟨?_, ⟨q, rfl⟩⟩
  obtain ⟨x, y, hxy⟩ := h.1
  obtain ⟨m, hm, hidv⟩ := exists_idempotent_pow (x * q)
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
  have hpv : p = (x * q) * p * y := by
    conv_lhs => rw [hxy]
    simp only [mul_assoc]
  have hk : ∀ k, (x * q) ^ k * p * y ^ k = p := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
      rw [pow_succ' (x * q) j, pow_succ y j]
      calc ((x * q) * (x * q) ^ j) * p * (y ^ j * y)
          = (x * q) * ((x * q) ^ j * p * y ^ j) * y := by simp only [mul_assoc]
        _ = (x * q) * p * y := by rw [ih]
        _ = p := hpv.symm
  have hph : (x * q) ^ (m' + 1) * p = p := by
    calc (x * q) ^ (m' + 1) * p
        = (x * q) ^ (m' + 1) * ((x * q) ^ (m' + 1) * p * y ^ (m' + 1)) := by rw [hk]
      _ = ((x * q) ^ (m' + 1) * (x * q) ^ (m' + 1)) * p * y ^ (m' + 1) := by
            simp only [mul_assoc]
      _ = (x * q) ^ (m' + 1) * p * y ^ (m' + 1) := by rw [hidv]
      _ = p := hk (m' + 1)
  refine ⟨(x * q) ^ m' * x, ?_⟩
  conv_lhs => rw [← hph]
  rw [pow_succ (x * q) m']
  simp only [mul_assoc]

/-- **Forward brick 5a — the R-identity.** A finite `𝓙`-trivial monoid satisfies
`(xy)^ω x = (xy)^ω`: with `e = (xy)^ω`, aperiodicity gives `e = (e·x)·y`, so `e 𝓡 e·x`,
whence `e = e·x` by `𝓙`-triviality. -/
theorem jtrivial_Rid [Finite M] (hM : IsJTrivial M) (x y : M) :
    ∃ m, 0 < m ∧ IsIdempotentElem ((x * y) ^ m) ∧ (x * y) ^ m * x = (x * y) ^ m := by
  obtain ⟨m, hm, hid⟩ := exists_idempotent_pow (x * y)
  refine ⟨m, hm, hid, ?_⟩
  have haper : (x * y) ^ (m + 1) = (x * y) ^ m := jtrivial_pow_succ_eq hM (x * y) hm hid
  have he : (x * y) ^ m = ((x * y) ^ m * x) * y := by rw [mul_assoc, ← pow_succ, haper]
  exact (hM _ _ ⟨greenJLe_of_greenRLe ⟨y, he⟩, greenJLe_of_greenRLe ⟨x, rfl⟩⟩).symm

/-- **Forward brick 5b — the L-identity.** Dually `y (xy)^ω = (xy)^ω`. -/
theorem jtrivial_Lid [Finite M] (hM : IsJTrivial M) (x y : M) :
    ∃ m, 0 < m ∧ IsIdempotentElem ((x * y) ^ m) ∧ y * (x * y) ^ m = (x * y) ^ m := by
  obtain ⟨m, hm, hid⟩ := exists_idempotent_pow (x * y)
  refine ⟨m, hm, hid, ?_⟩
  have haper : (x * y) ^ (m + 1) = (x * y) ^ m := jtrivial_pow_succ_eq hM (x * y) hm hid
  have he : (x * y) ^ m = x * (y * (x * y) ^ m) := by rw [← mul_assoc, ← pow_succ', haper]
  exact (hM _ _ ⟨greenJLe_of_greenLLe ⟨x, he⟩, greenJLe_of_greenLLe ⟨y, rfl⟩⟩).symm

/-- **The converse — NOW FULLY PROVED (sorry-free).** A finite monoid satisfying the
**R-identity** and **L-identity** (in idempotent-power form) is `𝓙`-trivial. This is the
hard direction of `J = R ∩ L`. Proof: the identities give `𝓡`- and `𝓛`-triviality
(`a 𝓡 b ⟹ a = a·(ts)ᵐ`, then `b = a·t = a·(ts)ᵐ·t = a·(ts)ᵐ = a`); **stability**
(`stabR`/`stabL`) gives, for `a 𝓙 b` with `a = s·b·t`, that `a 𝓡 s·b` and `s·b 𝓛 b`
(after the squeeze `s·b 𝓙 a 𝓙 b`); hence `a = s·b = b`. Entirely elementary —
idempotent powers only. -/
theorem jtrivial_of_identities [Finite M]
    (hR : ∀ x y : M, ∃ m, 0 < m ∧ IsIdempotentElem ((x * y) ^ m) ∧ (x * y) ^ m * x = (x * y) ^ m)
    (hL : ∀ x y : M, ∃ m, 0 < m ∧ IsIdempotentElem ((x * y) ^ m) ∧ y * (x * y) ^ m = (x * y) ^ m) :
    IsJTrivial M := by
  have hRtriv : ∀ a b : M, greenR a b → a = b := by
    intro a b hab
    obtain ⟨s, hs⟩ := hab.1
    obtain ⟨t, ht⟩ := hab.2
    obtain ⟨m, _, _, hr⟩ := hR t s
    have ha : ∀ k, a = a * (t * s) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ j ih => rw [pow_succ, ← mul_assoc, ← ih, ← mul_assoc, ← ht, ← hs]
    rw [ht]
    conv_rhs => rw [ha m]
    rw [mul_assoc, hr, ← ha m]
  have hLtriv : ∀ a b : M, greenL a b → a = b := by
    intro a b hab
    obtain ⟨s, hs⟩ := hab.1
    obtain ⟨t, ht⟩ := hab.2
    obtain ⟨m, _, _, hl⟩ := hL s t
    have ha : ∀ k, a = (s * t) ^ k * a := by
      intro k
      induction k with
      | zero => simp
      | succ j ih => rw [pow_succ', mul_assoc, ← ih, mul_assoc, ← ht, ← hs]
    rw [ht]
    conv_rhs => rw [ha m]
    rw [← mul_assoc, hl, ← ha m]
  intro a b hjab
  obtain ⟨s, t, hsbt⟩ := hjab.1
  have haJsb_le : greenJLe a (s * b) := ⟨1, t, by rw [hsbt, one_mul]⟩
  have hsbJb_le : greenJLe (s * b) b := ⟨s, 1, by rw [mul_one]⟩
  have hsbJa_le : greenJLe (s * b) a := greenJLe_trans hsbJb_le hjab.2
  have hbJsb_le : greenJLe b (s * b) := greenJLe_trans hjab.2 haJsb_le
  have hsbt' : (s * b) * t = a := hsbt.symm
  have hRsb : greenR (s * b) a := by
    have := stabR (p := s * b) (q := t) (by rw [hsbt']; exact ⟨hsbJa_le, haJsb_le⟩)
    rwa [hsbt'] at this
  have hLsb : greenL b (s * b) := stabL (p := b) (q := s) ⟨hbJsb_le, hsbJb_le⟩
  have e1 : s * b = a := hRtriv (s * b) a hRsb
  have e2 : b = s * b := hLtriv b (s * b) hLsb
  rw [← e1, ← e2]

/-- **Quotient closure (FINITE domain) — NOW FULLY PROVED (sorry-free).** A surjective
image of a `𝓙`-trivial monoid is `𝓙`-trivial **provided the DOMAIN `M` is finite**. `N`
is finite (`Finite.of_surjective`); the R- and L-identities transport from `M` to `N`
along the surjection (`jtrivial_Rid`/`jtrivial_Lid` + `map_mul`/`map_pow`/
`IsIdempotentElem.map`); `jtrivial_of_identities` concludes. This is the genuine
pseudovariety quotient-closure of **J** — fully machine-checked.

**Finiteness of the DOMAIN is ESSENTIAL.** Counterexample (corrects an earlier
`[Finite N]` mis-statement): `(ℕ,+)` is `𝓙`-trivial yet surjects onto the finite group
`ℤ/2ℤ` (`n ↦ n mod 2`), which is not `𝓙`-trivial — the **codomain** is finite, so
`[Finite N]` does not exclude it; the infinite object is the **domain** `ℕ`. -/
theorem isJTrivial_of_surjHom {M N : Type*} [Monoid M] [Monoid N] [Finite M]
    (f : M →* N) (hf : Function.Surjective f) (hM : IsJTrivial M) : IsJTrivial N := by
  haveI : Finite N := Finite.of_surjective f hf
  apply jtrivial_of_identities
  · intro u v
    obtain ⟨a, rfl⟩ := hf u
    obtain ⟨b, rfl⟩ := hf v
    obtain ⟨m, hm, hid, hr⟩ := jtrivial_Rid hM a b
    refine ⟨m, hm, ?_, ?_⟩
    · rw [← map_mul, ← map_pow]; exact hid.map f
    · rw [← map_mul, ← map_pow, ← map_mul, hr]
  · intro u v
    obtain ⟨a, rfl⟩ := hf u
    obtain ⟨b, rfl⟩ := hf v
    obtain ⟨m, hm, hid, hl⟩ := jtrivial_Lid hM a b
    refine ⟨m, hm, ?_, ?_⟩
    · rw [← map_mul, ← map_pow]; exact hid.map f
    · rw [← map_mul, ← map_pow, ← map_mul, hl]

/-! ## The monotone-inflationary monoid is `𝓙`-trivial (toward `pt_basic`)

The greedy subword automaton's transition monoid lands in the monoid of monotone
inflationary self-maps of a finite chain. That monoid is `𝓙`-trivial — and the proof
needs **no finiteness and not even a linear order**, only antisymmetry. -/

/-- Monotone inflationary self-maps of a preorder `X` (`Monotone f` and `a ≤ f a`),
as a submonoid of `Function.End X`: closed under composition and containing `id`. -/
def InflMono (X : Type*) [Preorder X] : Submonoid (Function.End X) where
  carrier := {f | Monotone (f : X → X) ∧ ∀ a : X, a ≤ f a}
  one_mem' := ⟨monotone_id, fun a => le_refl a⟩
  mul_mem' := by
    rintro f g ⟨hfm, hfi⟩ ⟨hgm, hgi⟩
    exact ⟨hfm.comp hgm, fun a => le_trans (hgi a) (hfi (g a))⟩

/-- **The monoid of monotone inflationary self-maps of a partial order is `𝓙`-trivial.**
No finiteness is needed: composing inflationary monotone maps only increases values
pointwise (`x ≤y(x)`, `g` monotone, `s` inflationary), so any `f = s·g·t` satisfies
`f ≥ g` pointwise; hence `f ≤𝓙 g ⟹ f ≥ g`, and `f 𝓙 g` forces `f = g` by antisymmetry.
This is the `𝓙`-triviality of the subword automaton's transition monoid, the last
conceptual ingredient of `pt_basic`. -/
theorem isJTrivial_inflMono (X : Type*) [PartialOrder X] :
    IsJTrivial (InflMono X) := by
  have ge_of_le : ∀ (a b : InflMono X), greenJLe a b →
      ∀ x, (b : Function.End X) x ≤ (a : Function.End X) x := by
    rintro a b ⟨s, t, hst⟩ x
    have hbm : Monotone (b : Function.End X) := b.2.1
    have hsi : ∀ y, y ≤ (s : Function.End X) y := s.2.2
    have hti : ∀ y, y ≤ (t : Function.End X) y := t.2.2
    have happ : (a : Function.End X) x
        = (s : Function.End X) ((b : Function.End X) ((t : Function.End X) x)) := by
      rw [hst]; rfl
    rw [happ]
    calc (b : Function.End X) x
        ≤ (b : Function.End X) ((t : Function.End X) x) := hbm (hti x)
      _ ≤ (s : Function.End X) ((b : Function.End X) ((t : Function.End X) x)) := hsi _
  intro a b hab
  apply Subtype.ext
  funext x
  exact le_antisymm (ge_of_le b a hab.2 x) (ge_of_le a b hab.1 x)

end DualityEngine
