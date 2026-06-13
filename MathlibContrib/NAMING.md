# Naming & design decisions for the Green's-relations PR

These are the choices a `#mathlib4` reviewer will most likely weigh in on. **Nothing
here is settled** — raise them in the Zulip proposal and let the maintainers decide.
The candidate (`MathlibContrib/Green.lean`) currently reflects the *first column*.

| Decision | Candidate uses | Likely reviewer asks | Recommendation |
|---|---|---|---|
| **File location** | — | `Algebra/Group/Green.lean` vs `GroupTheory/Green.lean` | `Mathlib/Algebra/Group/Green.lean` (monoid-level algebra); defer to maintainers |
| **Generality** | `Monoid` | `Semigroup` (Green's relations are classically on semigroups, via `WithOne` for principal ideals *with* identity) | Start at `Monoid` (cleaner, matches the syntactic-monoid use case); offer to generalize to `Semigroup` if wanted |
| **Namespace** | `namespace Green` | keep, or top-level `Green`-prefixed | Keep `Green` namespace |
| **Relation names** | `R`, `L`, `J`, `H` (+ `RLe`/`LLe`/`JLe`) | single-letter `L`/`J` are clash-prone even namespaced | Consider `rEqv`/`lEqv`/`jEqv` or rely on notation; settle on thread |
| **Notation** | none | scoped `𝓡 𝓛 𝓙 𝓗` (Green's standard symbols) likely wanted | Add `scoped notation "𝓡" => Green.R` etc. |
| **Tie to divisibility** | standalone `∃ x, a = b * x` | connect `RLe`/`JLe` to existing `· ∣ ·` / `Associated` (Green's relations *are* the non-commutative generalization) | Note the correspondence; offer a bridge lemma. This is the most substantive design ask |
| **`IsJTrivial`** | `def _ : Prop` | `class` (for instance inference) vs `def` | `def` is fine to start; promote to a Prop-`class` only if downstream wants inference |

## Mechanical Mathlib requirements (do regardless)
- Copyright header with `Authors:` line — ✅ done (David Johnson).
- Module docstring `/-! # … -/` after imports — ✅ present.
- Docstrings on every `def`/`instance` (the `docBlame` linter; theorems are exempt) —
  add to any bare `def`.
- `lake exe runLinter` clean against the target Mathlib.
- One logical change per PR; `feat(Algebra/Group): …` commit message.
