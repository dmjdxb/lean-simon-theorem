# Mathlib contribution package — Green's relations

Prepared, not submitted. Submitting is an outward-facing action (your GitHub
identity, a public review queue) — this package takes it up to that line.

## What is being contributed

`MathlibContrib/Green.lean` — **Green's relations on a monoid** (`𝓡 𝓛 𝓙 𝓗`), the
fundamental tool of semigroup theory, **confirmed absent from Mathlib** (direct
master audit, REGISTRY R4: no Green's relations anywhere). Sorry-free, 160 lines.
**Port-verified 2026-06-13**: builds cleanly against **Mathlib v4.30.0** (the latest
stable, one release past the v4.29.1 it was written on) with **zero changes**, and
`lake exe runLinter GreenPort.Green` reports **"Linting passed"** — so the file uses
only stable core API (`map_mul`, `Prod.fst_mul`, `Submonoid`) and the drift to master
is expected to be nil. (Verification project: a minimal Lake package requiring
mathlib @ v4.30.0; not committed here.)

Contents: the three Green preorders (`RLe/LLe/JLe`) with reflexivity/transitivity;
the four equivalences (`R/L/J/H`) with `Equivalence` proofs; basic containments
(`R ⊆ J`, `L ⊆ J`, `H = R ∩ L`); the triviality predicates (`IsJTrivial`, …); and
the closure of `𝓙`-triviality under **finite products** and **injective
homomorphisms** (submonoids) — the first two pseudovariety axioms.

### Scope — deliberately a small first PR
**Scope of THIS first PR** (and why): just Green's relations. The **syntactic
monoid** (sorry-free and wanted, but more entangled — `FreeMonoid`, `Con`, and a
likely design discussion with `Computability.Language`; better as a **follow-up
PR**). This first PR is the clean, self-contained, hard-to-object-to core.

## Proposed Mathlib location

`Mathlib/Algebra/Group/Green.lean` (or `Mathlib/GroupTheory/Green.lean` — reviewers'
call). Add the import to `Mathlib.lean`.

## Zulip proposal (draft — post to `#mathlib4` before opening the PR)

> **Adding Green's relations (𝓡, 𝓛, 𝓙, 𝓗) for monoids**
>
> Hi all — I'd like to contribute Green's relations (Green 1951), the standard
> equivalence relations of semigroup theory comparing elements by the principal
> ideals they generate. I checked and Mathlib doesn't currently have them (we have
> `Associated`/`Dvd`, of which Green's relations are the non-commutative
> generalization). Proposed first PR (≈160 lines, sorry-free, lint-clean): the three
> Green preorders + four equivalences for `Monoid`, the triviality predicates
> (`IsJTrivial` etc.), and closure of 𝓙-triviality under finite products and
> submonoids. A natural follow-up would add the syntactic monoid of a language.
> Two questions before I open the PR: (1) preferred home — `Algebra/Group/Green.lean`
> or `GroupTheory/`? (2) start at `Monoid` (cleaner) or go straight to `Semigroup`
> via `WithOne`? Happy to adjust naming. Is anyone already working on this?

## PR description (draft)

> **feat(Algebra/Group): Green's relations on a monoid**
>
> Adds Green's relations `𝓡, 𝓛, 𝓙, 𝓗` (J. A. Green, *On the structure of
> semigroups*, 1951) for monoids — the non-commutative generalization of
> divisibility/`Associated`, fundamental to semigroup and automata theory and not
> previously in Mathlib.
>
> * `Green.RLe/LLe/JLe`: the preorders, with `@[refl]` and transitivity lemmas.
> * `Green.R/L/J/H`: the equivalences, with `Equivalence` proofs; `R_le_J`, `L_le_J`,
>   `H_le_R/L`.
> * `Green.IsRTrivial/IsLTrivial/IsJTrivial/IsHTrivial`.
> * `Green.IsJTrivial.prod`, `Green.IsJTrivial.of_injective`, `Green.JLe.map`:
>   functoriality + closure of 𝓙-triviality under finite products and submonoids.
>
> Follow-up planned: the syntactic monoid of a language, and (longer-term) Simon's
> theorem. Sorry-free; builds + lints clean against Mathlib v4.30.0.

(See `NAMING.md` for the naming/generality decisions to settle on the Zulip thread.)

## Pre-submission checklist (do these before opening the PR)

- [x] **Port to current Mathlib.** Verified against `v4.30.0` (latest stable) — builds
      with **zero changes**. Re-confirm against literal master at PR time (trivial:
      file uses only stable core API).
- [x] **Run linters.** `lake exe runLinter GreenPort.Green` → "Linting passed" against
      v4.30.0. All `def`s docstringed.
- [x] **Authorship & copyright.** Header set to David Johnson with the `Authors:` line.
- [ ] **Search for prior/competing work.** Mathlib PR search for "Green" /
      "Green's relations"; check Sam van Gool's Stone-duality formalization thread
      (it may touch adjacent material). Mention findings on Zulip.
- [ ] **Naming review.** See `NAMING.md` — `Green` namespace, `R/L/J/H` names, `𝓡`-style
      scoped notation, and the tie to `· ∣ ·`/`Associated` are open; settle on Zulip.
- [ ] **Generality.** Decide `Monoid` vs `Semigroup` (via `WithOne`) per the Zulip
      reply. The current statements are `Monoid`.
- [ ] **Import index.** Add to `Mathlib.lean`.
- [ ] **Commit message** follows Mathlib convention (`feat(Algebra/Group): …`).

## Honest caveats

- As of 2026-06-13 the WHOLE library (incl. Simon's theorem) is sorry-free; this
  first PR is still scoped to just Green's relations as the cleanest opening move,
  with the syntactic monoid and Simon's theorem as planned follow-up PRs.
- Port-verified against **v4.30.0**, not literal master — but the file uses only
  stable core API, so the master delta is expected to be nil (re-check at PR time).
- The naming/generality choices (`NAMING.md`) are provisional pending the Zulip
  discussion — *don't* hard-finalize them before maintainers weigh in.
- Acceptance is the maintainers' decision; this package only prepares the submission.
