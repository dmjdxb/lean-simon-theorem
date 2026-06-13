# Community announcement draft (for Lean Zulip — `#announce`, cc `#general`)

**Subject:** Simon's theorem (piecewise testable ⟺ 𝓙-trivial) formalized in Lean 4

> Hi all — I've formalized **Simon's theorem** (I. Simon, 1975): a regular language
> is piecewise testable iff its syntactic monoid is 𝓙-trivial. **Both directions,
> sorry-free** — `#print axioms simon` = `[propext, Classical.choice, Quot.sound]`.
>
> Repo (Apache-2.0, CI green against Mathlib v4.29.1):
> https://github.com/dmjdxb/lean-simon-theorem
>
> As far as I can tell Simon's theorem wasn't previously formalized in any proof
> assistant, and Green's relations (𝓡 𝓛 𝓙 𝓗) aren't in Mathlib yet either. The repo
> includes, all sorry-free:
> - Green's relations + closure of 𝓙-triviality under products, submonoids, and
>   finite quotients;
> - the syntactic monoid / congruence of a language;
> - `IsPiecewiseTestable`, the forward direction, and the deep converse (Klíma's
>   Lemma 3) via a "position-union" construction that's `core_insert`-free.
>
> I'd like to upstream this to Mathlib incrementally — starting with Green's
> relations as a small first PR (I'll open a `#mathlib4` thread for that). Feedback
> on naming/structure very welcome, and happy to hear if anyone has adjacent WIP.
