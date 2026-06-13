# DualityEngine — Green's relations & the syntactic monoid in Lean 4

A small, self-contained Lean 4 / Mathlib library providing algebraic-automata-theory
API that **Mathlib does not yet have** (verified absent, Mathlib master, June 2026):
Green's relations, the **syntactic monoid** of a language, a **complete, sorry-free
proof of Simon's theorem**, and a worked **choice (`#print axioms`) audit**.

Built for the *Computational Stone Duality for Regular Languages* project (E5 track).

## What it provides

| module | contents | status |
|---|---|---|
| `DualityEngine/Green.lean` | Green's relations `𝓡 𝓛 𝓙 𝓗` (via principal ideals); `IsJTrivial/IsRTrivial/IsLTrivial/IsHTrivial`; `greenJLe_map` (ideal transport); **`isJTrivial_prod`** (product closure), **`isJTrivial_of_injHom`** (submonoid closure), **`isJTrivial_of_surjHom`** (finite quotient closure) | **sorry-free** |
| `DualityEngine/Syntactic.lean` | the **syntactic congruence** `Con (FreeMonoid α)` (with the multiplicative-compatibility proof), the **syntactic monoid** `M(L) = Con.Quotient`, the syntactic morphism | **sorry-free** |
| `DualityEngine/Simon.lean` | `IsPiecewiseTestable`; **Simon's theorem** `simon` (both directions); `pt_basic`, `pt_finite_jtrivial`, `pt_of_jtrivial`; Klíma's Lemma 3 `subk_refines_of_jtrivial` (the position-union proof); `inter` corollary; complement-invariance `M(Lᶜ)=M(L)`; the union-closure reduction | **sorry-free** |
| `DualityEngine/ChoiceAudit.lean` | `#print axioms` discipline: constructive lemmas (`[propext]` / no axioms) vs a deliberately classical one (`Classical.choice`) | **sorry-free** |

### Proof status — fully sorry-free

The headline theorem `simon : IsPiecewiseTestable L ↔ IsJTrivial (SyntacticMonoid L)`
is **completely proved, sorry-free, in both directions**:
`#print axioms simon` = `[propext, Classical.choice, Quot.sound]` (the three standard
Mathlib axioms; no `sorryAx`). Simon's theorem (1975) is a famous result that is
otherwise essentially unformalized in any proof assistant.

* **Forward** (`PT ⟹ 𝓙-trivial`, `pt_finite_jtrivial`), any alphabet: all four cases
  (`basic`/`empty`/`compl`/`union`) via `pt_basic` and the quotient-closure chain
  `jtrivial_union` → `isJTrivial_of_surjHom` → `Green.jtrivial_of_identities`.
* **Converse** (`𝓙-trivial ⟹ PT`, `pt_of_jtrivial`), needs `[Finite α]` (false over
  infinite alphabets) — this is Simon's deep direction = Klíma's Lemma 3
  (`subk_refines_of_jtrivial`): `∼ₖ` refines `∼_L` for `k = 2m−2`, proved via the
  **position-union** construction `φ(u)=φ(ū')=φ(v̄')=φ(v)` with a position comparator
  whose `eq` is genuine coincidence. `core_insert`-free throughout.

Run `#print axioms <name>` to check any lemma.

## Build

Requires [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager);
the pinned toolchain (`lean-toolchain`) installs automatically.

```bash
lake exe cache get      # download prebuilt Mathlib oleans (no Mathlib recompile)
lake build DualityEngine
```

Pins: Lean `v4.29.1`, Mathlib `v4.29.1` (see `lean-toolchain`, `lakefile.toml`,
`lake-manifest.json`). The `.lake/` build directory is git-ignored.

## Using it

```lean
import DualityEngine.Green
import DualityEngine.Syntactic

open DualityEngine
-- `IsJTrivial M`, `greenJ`, `SyntacticMonoid L`, `isJTrivial_prod`, … are now available.
```

## License & provenance

Apache 2.0 (see `LICENSE`), matching Mathlib for contribution compatibility. The
sorry-free Green's-relations + syntactic-monoid API — and now the complete Simon's
theorem — are intended as candidate Mathlib contributions (they fill a confirmed gap),
staged as incremental PRs (see `MathlibContrib/CONTRIBUTION.md`). Developed as the
formal-methods track (E5) of the *Computational Stone Duality for Regular Languages*
project.
