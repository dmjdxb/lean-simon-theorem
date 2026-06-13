# Simon's theorem, hard direction — paper proof (toward `pt_of_jtrivial`)

**Goal.** `Σ` finite. `L ⊆ Σ*` with syntactic monoid `M = M(L)` finite and `𝓙`-trivial
⟹ `L` is piecewise testable (PT) = a finite Boolean combination of subword up-sets
`⟨x⟩ := {w : x ⊑ w}` (`⊑` = scattered subword).

Recommended route: the **Simon congruence `~ₖ`**. The framework below is fully rigorous;
it reduces the theorem to ONE core lemma (the "Simon bound"), which is the genuine heart.

---

## 0. Notation

- `x ⊑ w` : `x` is a scattered subword of `w`.
- `Sub_k(w) := {x : x ⊑ w, |x| ≤ k}` (a subset of the finite set `Σ^{≤k}`).
- `u ~ₖ v` : `Sub_k(u) = Sub_k(v)` (same subwords of length ≤ k). The **Simon congruence**.
- `≈_L` : the syntactic congruence; `φ : Σ* ↠ M = Σ*/≈_L` the syntactic morphism.
- `≤𝓙` : the `𝓙`-order on `M` (`a ≤𝓙 b ⟺ a ∈ MbM`); a **partial order** since `M` is
  `𝓙`-trivial, with `1` as top, and `ab ≤𝓙 a`, `ab ≤𝓙 b` always.

---

## 1. Lemma I — `~ₖ` is a congruence of finite index  [RIGOROUS]

**Finite index.** The class of `w` is determined by `Sub_k(w) ⊆ Σ^{≤k}`, and `Σ^{≤k}` is
finite (Σ finite). So `Σ*/~ₖ` is finite.

**Congruence.** Suffices: `u ~ₖ v ⟹ ua ~ₖ va` and `au ~ₖ av` for a single letter `a`
(then extend to arbitrary contexts by induction). For the right case, the key identity is

> `x ⊑ ua  ⟺  x ⊑ u  ∨  (∃ x', x = x'a ∧ x' ⊑ u).`

(A subsequence embedding `x` into `ua` either avoids the final `a` — then `x ⊑ u` — or uses
it as `x`'s last letter — then `x = x'a` and `x' ⊑ u`.) For `|x| ≤ k`: `x ⊑ u ⟺ x ⊑ v` and
`x'` has `|x'| ≤ k-1 ≤ k` so `x' ⊑ u ⟺ x' ⊑ v`; hence `x ⊑ ua ⟺ x ⊑ va`. ∎

---

## 2. The wrapping — `PT ⟺ some ~ₖ saturates L`  [RIGOROUS]

"`~ₖ` saturates `L`" means `L` is a union of `~ₖ`-classes (`u ~ₖ v ⟹ (u∈L ⟺ v∈L)`).

**(⟸)** Each `~ₖ`-class `C` with subword-set `S = Sub_k(w₀)` equals
`C = (⋂_{x∈S} ⟨x⟩) ∩ (⋂_{x∈Σ^{≤k}∖S} ⟨x⟩ᶜ)` — a **finite** Boolean combination (`Σ^{≤k}`
finite). `L` = union of the finitely many classes it contains; a finite union of PT is PT.
So `L` is PT.

**(⟹)** `L` a Boolean combination of `⟨u₁⟩,…,⟨u_N⟩`; put `k = maxᵢ|uᵢ|`. If `u ~ₖ v` then
each `uᵢ ⊑ u ⟺ uᵢ ⊑ v` (`|uᵢ| ≤ k`), so `u,v` agree on every `⟨uᵢ⟩`, hence on `L`. ∎

---

## 3. Reduction to a single algebraic statement  [RIGOROUS]

`~ₖ` is a congruence saturating `L` ⟺ `~ₖ ⊆ ≈_L` (because `≈_L` is the **coarsest**
congruence saturating `L`, so any congruence saturating `L` refines it). And
`~ₖ ⊆ ≈_L = ker φ` ⟺ `φ` **factors through `~ₖ`**. Therefore:

> **It suffices to prove:** for `M` finite `𝓙`-trivial and `φ : Σ* → M`, `φ` factors
> through `~ₙ` where `n = |M|`  (i.e. `u ~ₙ v ⟹ φ(u) = φ(v)`).

### 3.1 Further reduction to the canonical product map  [RIGOROUS]

Let `π : M* → M`, `π(m₁…m_r) = m₁·…·m_r` (free monoid on the **alphabet `M`**; `π` is the
product). Let `σ : Σ* → M*` be the letter substitution `a ↦ (φ(a))` (length-1 sequence).
Then `π ∘ σ = φ`.

`σ` is `~ₖ`-compatible: subwords of `σ(w)` are exactly `{σ(x) : x ⊑ w}`, so
`Sub_k(σ w) = σ(Sub_k w)`, hence `u ~ₖ v ⟹ σu ~ₖ σv`. Therefore if **`π` factors through
`~ₙ`** then `φ = π∘σ` does too. So everything reduces to:

> ### CORE LEMMA (the Simon bound)
> `M` finite `𝓙`-trivial, `n = |M|`. For sequences `s, t ∈ M*`:
> `s ~ₙ t  ⟹  ∏s = ∏t`.   (Same subwords of length ≤ n ⟹ equal product.)

Everything in §1–§3 is rigorous and self-contained. **The Core Lemma is the entire
remaining difficulty** — it is the genuine heart of Simon's theorem.

---

## 4. Core Lemma — mechanism, and the precise crux

### 4.1 The prefix-product chain (rigorous structural facts)

For `s = (s₁,…,s_p)` put `P₀ = 1`, `Pᵢ = s₁…sᵢ`. Then:

- **(a)** `Pᵢ = P_{i-1}·sᵢ ≤𝓙 P_{i-1}` — the chain is `≤𝓙`-non-increasing.
- **(b)** `P_{i-1}·sᵢ = P_{i-1}` **or** `P_{i-1}·sᵢ <𝓙 P_{i-1}` (strict): because
  `P_{i-1} sᵢ ≤𝓙 P_{i-1}` always, and `=` iff `P_{i-1} ≤𝓙 P_{i-1}sᵢ` iff (𝓙-trivial) they
  are equal. So each letter **fixes** the running product or **strictly drops** it.
- **(c)** Strict drops happen `≤ n-1` times (a strict `≤𝓙`-chain has `≤ n` elements). So
  the distinct prefix-product values form a chain `1 = v₀ >𝓙 v₁ >𝓙 … >𝓙 v_d = ∏s`,
  `d ≤ n-1`.
- **(d) (zero short-circuit)** A finite `𝓙`-trivial monoid has a **zero** `0` (its minimal
  ideal is a singleton). If `0` occurs in `s` then `∏s = 0`; and `(0) ⊑ s ⟺ (0) ⊑ t` under
  `~₁`, so both products are `0`. Hence WLOG `0 ∉ s, t`.

### 4.2 The mechanism (why `Sub_n` determines `∏s`)

`∏s = v_d` is reached by `d ≤ n-1` strict drops. Between drops, the running product `vⱼ`
is **fixed** by every intervening letter (a "stable run"): each such letter `c` has
`vⱼ·c = vⱼ`, so `vⱼ·(any sub-product of the run) = vⱼ` (elementary, iterate the fixing —
note this also holds for any *subsequence* of the run, which is what the subword analysis
needs). So only the **drop-causing letters** and their **order** matter:

> `∏s` is determined by the sequence of "significant" elements
> `s_{i₁}, s_{i₂}, …, s_{i_d}`, where `i₁` = first index with `s_{i₁} ≠ 1`, and `i_{j+1}`
> = first index after `iⱼ` with `s_{i_{j+1}} ∉ Stab_R(vⱼ) := {x : vⱼ x = vⱼ}`. Then
> `v_{j+1} = vⱼ · s_{i_{j+1}}`, and `∏s = v_d`.

This recursion has **depth `≤ n`**, which is why **subwords of length `≤ n` suffice**.

### 4.3 THE CRUX (the one step to nail)

The recursion in §4.2 reads off the significant elements by **first-occurrence**:
"`v₁` = the first non-`1` element", then "`v₂`'s trigger = the first element, *after* that,
outside `Stab_R(v₁)`", etc. To conclude `s ~ₙ t ⟹ ∏s = ∏t`, we must show **this trace of
significant elements is determined by `Sub_n`** — i.e. first-occurrence/relative-order data
of bounded depth is captured by bounded-length subwords.

This is the delicate point (the "ranker"/"first-occurrence" lemma at the heart of every
proof of Simon's theorem). The subtlety: a length-2 subword `(x,y) ⊑ s` only says *some* `x`
precedes *some* `y`, **not** that the *first* `x` precedes the *first* `y` (e.g.
`s = (y,x,y)` has `(x,y) ⊑ s` yet first-`y` < first-`x`). So "first significant element" is
*not* directly a length-2 subword condition; it requires the careful bounded-depth encoding.

**Two ways to close it (to be worked out precisely — collaboration point):**

1. **Direct ranker encoding.** Prove by induction on the chain-depth `d ≤ n` that the value
   `vⱼ` and the suffix-restriction after the `j`-th drop are determined by `Sub_{j+1}`-data,
   using that the prefix *before* the first significant element lies in a *strictly smaller
   sub-alphabet* of `M` (so an alphabet/`|M|`-induction grounds the recursion). This is the
   route that matches §4.2 and is, I believe, the cleanest — but the first-occurrence
   bookkeeping must be done carefully.

2. **`|M|`-induction with the zero (§4.1d).** With `0 ∉ s,t`, reduce to a proper `𝓙`-trivial
   quotient/sub of `M` and a shorter chain. The reduction step (which smaller monoid, and
   why `~ₙ` on `s` gives `~_{n-1}`-type data on the reduced sequence) is the part to pin
   down.

### 4.4 What plugs in when formalizing

- §4.1(b),(c): `Green` — `𝓙`-order is a partial order (`IsJTrivial`), `ab ≤𝓙 a`
  (`greenJLe`), chain bound from `Finite`.
- §4.2 stable-run absorption: elementary (iterate `vⱼ·c = vⱼ`). The **R/L-identities**
  (`Green.jtrivial_Rid`/`jtrivial_Lid`, already proved) and the well-defined idempotent
  power `x^ω` (`Green.exists_unique_idempotent_pow`) are the tools that enter the **§4.3
  crux** (reordering/idempotent-absorption in the first-occurrence encoding).
- §4.1(d) zero: needs "finite monoid has a minimal ideal = singleton" (not yet in the
  project; a finite-semigroup fact to add).
- §1–§3: pure subword + congruence combinatorics; `~ₖ`-class = Boolean combination reuses
  `IsPiecewiseTestable` (`Simon.lean`) and the finite-union-of-PT lemma (small, to add).

---

## 4b. Route 1, worked — the value-parameterized induction

The naive "induct on the alphabet `A ⊆ M`" fails: factoring `s = s'·a·s''` by a first
occurrence puts `s'` over `A∖{a}` (good) but `s''` over the *full* `A` (no progress). The
fix is to **parameterize by a left-context value `ℓ ∈ M` and induct on its `≤𝓙`-depth**;
then the relevant sub-alphabet is the *right stabilizer* `Stab_R(ℓ)`, which provably
shrinks at every drop.

**Definitions.**
- `Stab_R(ℓ) := {x ∈ M : ℓx = ℓ}` — a submonoid (contains `1`; closed: `ℓxy = ℓy = ℓ`).
- `D_ℓ := M ∖ Stab_R(ℓ) = {x : ℓx <𝓙 ℓ}` — the **droppers** (since `ℓx ≤𝓙 ℓ` always).
- `depth(ℓ)` := length of the longest strict `≤𝓙`-chain descending from `ℓ`. In a finite
  `𝓙`-trivial monoid `0` is the unique minimum (`0 = 0·m·0 ∈ MmM`, so `0 ≤𝓙 m` ∀m), so
  `depth(ℓ)=0 ⟺ ℓ=0`, and `depth(ℓ) ≤ n-1`.
- `d(ℓ) := depth(ℓ) + 1`.

**Proposition `P(ℓ)`** (induction on `depth(ℓ)`):
> for all `s, t ∈ M*`: if `s ~_{d(ℓ)} t` then `ℓ·∏s = ℓ·∏t`.

The **Core Lemma is `P(1)`**: `d(1) = depth(1)+1 ≤ n`, and `~ₙ ⊆ ~_{d(1)}`, so `s ~ₙ t ⟹
1·∏s = 1·∏t`, i.e. `∏s = ∏t`. ✓

**Base** `depth(ℓ)=0` (`ℓ=0`): `0·∏s = 0 = 0·∏t`. ✓ [RIGOROUS]

**Inductive step** `depth(ℓ)=r≥1`. IH: `P(ℓ')` holds for every `ℓ'` with `depth(ℓ')<r`;
in particular for every `ℓ' = ℓ·x <𝓙 ℓ` (then `depth(ℓ') ≤ r-1`, since prepending `ℓ>𝓙ℓ'`
extends an `ℓ'`-chain). Let `s ~_{d(ℓ)} t`, `d(ℓ)=r+1`.

- **Same dropper-content.** `d(ℓ) ≥ 2 ≥ 1`, so `s, t` have the same length-1 subwords;
  hence a `D_ℓ`-element occurs in `s` ⟺ in `t`. [RIGOROUS]
- **Case 1 — no dropper occurs.** Every element of `s` is in `Stab_R(ℓ)`, so
  `ℓ·∏s = ℓ` (iterate `ℓx=ℓ`); likewise `ℓ·∏t = ℓ`. So equal. ✓ [RIGOROUS]
- **Case 2 — a dropper occurs.** Write `s = s₀·d_s·s₁` where `d_s` is the **first**
  dropper (`s₀ ∈ Stab_R(ℓ)*`). Then `s₀` stabilizes `ℓ`, so
  `ℓ·∏s = (ℓ·d_s)·∏s₁ = ℓ'_s·∏s₁` with `ℓ'_s = ℓ·d_s <𝓙 ℓ`. Likewise `ℓ·∏t = ℓ'_t·∏t₁`.
  By IH `P(ℓ'_s)` (valid since `depth(ℓ'_s)<r`), it would suffice that **(i)** `ℓ'_s = ℓ'_t`
  and **(ii)** `s₁ ~_{d(ℓ'_s)} t₁`.

  **This is the remaining crux.** (i)+(ii) are NOT immediate, and "first dropper is
  determined by `~_{d(ℓ)}`" is **false at face value**: `s=(a,b,b,a) ~₂ (b,a,a,b)=t` have
  different first droppers (`a` vs `b`) — they only separate at `~₃` (machine-checked). What
  rescues the induction is the **depth budget**: a genuine difference `ℓ'_s ≠ ℓ'_t` forces a
  strictly longer `≤𝓙`-descent, which forces a longer separating subword — so it cannot
  occur under `~_{d(ℓ)}` *when `d(ℓ)` already accounts for the remaining depth `r`*. Making
  this precise — i.e. proving (i)+(ii) hold under `~_{r+1}`, or directly that
  `ℓ'_s·∏s₁ = ℓ'_t·∏t₁` even when first droppers differ — is the one step still to nail.

**Assessment.** Route 1 is now on a correct, sharp footing: the induction measure
(`≤𝓙`-depth of the left context), the shrinking alphabet (`Stab_R(ℓ)`), and the budget
relation `d(ℓ)=depth(ℓ)+1` are all pinned down; base, Case 1, and the reduction in Case 2
are rigorous. The residual is a single, precisely-stated claim about Case 2 (the
"depth-budget / first-dropper" step), with the exact obstruction identified by the witness
pair `(a,b,b,a) ~₂ (b,a,a,b)`.

## 4c. The symmetric R∩L approach — what it gives, and where it stops

`M` `𝓙`-trivial `= R-trivial ∧ L-trivial`. Exploiting the **R-structure** (prefix
products, `≤𝓡`) yields a clean, rigorous, machine-checked lemma — but **not** a closure.

**Short-witness lemma [RIGOROUS, machine-checked].** Let `M` be finite `𝓙`-trivial,
`n=|M|`. For any `t ∈ M*`, `∏t = ∏x` where `x ⊑ t` is the **`≤𝓡`-dropper subsequence**,
`|x| ≤ n-1`.

*Proof.* Prefix products `T₀=1, Tᵢ=T_{i-1}·tᵢ` satisfy `Tᵢ ≤𝓡 T_{i-1}`; R-triviality makes
`≤𝓡` a partial order, so the distinct values form a strict `≤𝓡`-chain of `≤ n` elements,
i.e. `≤ n-1` strict drops at positions `i₁<…<i_d`. Between drops `T` is constant, so
`T_{i_{j}} = T_{i_{j-1}}·t_{i_j}`; telescoping from `T₀=1` gives
`∏t = T_q = T_{i_d} = t_{i₁}…t_{i_d} = ∏x`, `x = (t_{i₁},…,t_{i_d})`, `d ≤ n-1`. ∎
(Symmetrically, via suffix products and L-triviality, `∏t = ∏y` for an L-dropper subword.)

So every product is **witnessed by a length-`≤(n-1)` subword**. Since `s ~ₙ t`, that witness
`x_t` (`|x_t| ≤ n-1`) satisfies `x_t ⊑ s` as well.

**Why it does NOT close the Core Lemma (machine-checked).** Having `∏t = ∏x_t` and
`x_t ⊑ s` would close it only if `∏s = ∏x_t` — but `x_t ⊑ s ⟹ ∏s = ∏x_t` is **false**:
`s` may contain *additional* `≤𝓡`-droppers not in `x_t`, so `∏s ≠ ∏x_t` in general
(confirmed: among random `M*`-pairs over the 5-element J-trivial monoid of
monotone-inflationary maps on a 3-chain, ∏s ≠ ∏x_t in tens of thousands of cases). The R∩L
approach therefore **sharpens** the problem (reduce to comparing length-`≤(n-1)` canonical
witnesses) but reproduces the same obstruction one level down: showing `s`'s and `t`'s
canonical witnesses have equal products is again a witness-matching / first-occurrence
determination problem.

**Net.** R∩L is genuinely useful (the Short-witness lemma is clean and reusable, and it
caps the relevant subword length at `n-1`), but it does **not** by itself defeat the
Case-2 obstruction. The irreducible heart — that `~ₙ` forces the canonical short witnesses
to agree up to product — remains open in this development.

## 6. THE REFERENCE PROOF (faithfully transcribed) — COMPLETE

Source: **Ondřej Klíma, "Piecewise Testable Languages via Combinatorics on Words"**
(math.muni.cz/~klima, AutoMathA; cites Simon 1975, Pin, Almeida, Higgins). Retrieved and
transcribed from the actual PDF. This is a *complete, self-contained, purely combinatorial*
proof of the hard direction. It works directly with the syntactic **congruence** `∼_L` on
`A*` — no separate monoid/`M*` construction — which is excellent for formalization.

**Congruence-level `𝓙`-triviality.** `∼` (a congruence on `A*`) is **`𝓙`-trivial** iff
> `w₁ w₂ u w₃ w₄ ∼ u  ⟹  w₂ u w₃ ∼ u`   for all `u, w₁, w₂, w₃, w₄ ∈ A*`.
This is equivalent to `A*/∼` being a `𝓙`-trivial monoid: `[u] = [w₁][w₂uw₃][w₄]` gives
`[u] ≤𝓙 [w₂uw₃] = [w₂][u][w₃] ≤𝓙 [u]`, so `[u] =𝓙 [w₂uw₃]`, and 𝓙-triviality forces equality.

**Lemma 1** (= our §2 wrapping). `∃k, ∼_k ⊆ ∼_L  ⟺  L` is a finite Boolean combination of
the `L_u = A* a₁ A* … A* a_ℓ A*` (`u=a₁…a_ℓ`). [Proof = §2.] So `PT ⟺ ∃k, ∼_k ⊆ ∼_L`.

**Lemma 2** (forward, `PT ⟹ ∼_L` 𝓙-trivial). [Standard; = our `pt_finite_jtrivial`.]

**Lemma 3 (THE HARD DIRECTION).** `A` finite, `L` regular with `∼_L` `𝓙`-trivial of index
`m`. Then `∼_k ⊆ ∼_L` for **`k = 2m − 2`** (hence `L` is PT by Lemma 1).

### Proof of Lemma 3 (transcribed)

Take `u = a₁…a_p`, `v = b₁…b_q` with `u ∼_k v` (`k = 2m−2`). Show `u ∼_L v`.

Prefixes `u_i = a₁…a_i` (`u₀ = λ`). 𝓙-triviality gives: `u_i ∼_L u_j` (`i<j`) ⟹
`u_i ∼_L u_{i'}` for all `i' ∈ [i,j]`.

**Blue indices** (left/prefix side, from `u`). Call `i ∈ {1,…,p}` *blue* if
`u_{i-1} ≁_L u_{i-1} a_i`. The prefix-class can strictly change at most `m−1` times, so
there are `≤ m−1` blue indices `i₁ < … < i_r` (`r ≤ m−1`). For a non-blue `i`,
`u_{i-1} ∼_L u_{i-1} a_i`; chaining across a blue-free stretch gives, for blue `i_t` and
`i ∈ (i_t, i_{t+1})`, `u_{i_t} ∼_L u_{i_t} a_{i_t+1} ∼_L … ∼_L u_i`, and (congruence)
`u_{i_t} a_i ∼_L u_i ∼_L u_{i_t}`.

> **Claim 1.** Any subword `u'` of `u` that contains *all* blue-position letters satisfies
> `u' ∼_L a_{i₁} a_{i₂} … a_{i_r} ∼_L u`. (Write `u_left := a_{i₁}…a_{i_r}`; so `u ∼_L u_left`.)

Moreover the blue indices mark the **leftmost** occurrence of `u_left` in `u` (for any
`r' ≤ r`, `a_{i₁}…a_{i_{r'}}` is *not* a subword of `u_{i_{r'}-1}`). Since `u ∼_k v`, take the
leftmost occurrence of `u_left` in `v`, giving blue indices `ī₁ < … < ī_r` in `v`.

**Red indices** (right/suffix side, from `v`, *dual*). Call `j` *red* if `b_j v_{j+1} ≁_L
v_{j+1}`, where `v_{j+1}` is the suffix of `v` after the `j`-th letter. Red indices
`j₁ < … < j_s` (`s ≤ m−1`) mark the **rightmost** occurrence of `v_right := b_{j₁}…b_{j_s}`
in `v`; take its rightmost occurrence in `u`, giving red indices `j̄₁ < … < j̄_s` in `u`.

> **Claim 2 (crucial).** Let `ū` = the subword of `u` at its blue *and* red positions, and
> `v̄` = the subword of `v` at its blue and red positions. Then **`ū = v̄`** (equal words).

*Proof of Claim 2.* One shows the leftmost `u_left` and rightmost `v_right` are *shuffled the
same way* in `u` and `v`. For a blue letter `a_{i_{r'}}` (position `i_{r'}` in `u`) and a red
letter `b_{j_{s'}} = a_{j̄_{s'}}` (position `j̄_{s'}` in `u`):
- if they are **different letters**, then `i_{r'} < j̄_{s'} ⟺ w_{r's'} := a_{i₁}…a_{i_{r'}}
  b_{j_{s'}}…b_{j_s}` is a subword of `u` (`⟸` by an induction using leftmost-`u_left`:
  `i_t ≤ ℓ_t`, and dually `ℓ'_t ≤ j̄_t`, forcing `i_{r'} ≤ ℓ_{r'} < ℓ'_{s'} ≤ j̄_{s'}`);
- if they are the **same letter**, a three-case test (`w_{r's'} / u`; `w_{r's'} ⋪ u` but
  `a_{i₁}…a_{i_{r'}} b_{j_{s'}+1}…b_{j_s} / u`; or neither) pins `i_{r'} <`, `=`, or `> j̄_{s'}`.

Every test word here has length `≤ |u_left · v_right| ≤ (m−1)+(m−1) = 2m−2 = k`, so the
relative order of blue and red positions is **determined by `Sub_k`**. By `u ∼_k v` the same
holds in `v`, so the blue/red letters appear in the same order in `u` and `v`: `ū = v̄`. ∎

**Conclusion.** `ū` contains all blue letters of `u`, so by Claim 1 `u ∼_L ū`. Dually `v̄`
contains all red letters of `v`, so `v ∼_L v̄`. With Claim 2 (`ū = v̄`):
`u ∼_L ū = v̄ ∼_L v`. Hence `∼_k ⊆ ∼_L`. ∎  (Bound `k = 2m−2`; Simon's original was `2m−1`.)

### Why my reconstruction stalled, vs. what Klíma does

My §4c "R-dropper subword" **was exactly the blue construction** (and Claim 1: `u ∼_L u_left`).
The two things I was missing: (a) use **blue from `u` AND red from `v`** (left from one word,
right from the *other*) — not the same side of both; (b) **Claim 2** — the blue+red letters
form the *same word* in `u` and `v`, because their *shuffle* (not their identity in isolation)
is what `Sub_{2m−2}` determines. That defeats the witness-pair obstruction `(a,b,b,a)~₂(b,a,a,b)`
honestly: there `m` is large enough that `2m−2 ≥ 3` separates them.

## 5. Status

- **§0–§3 (framework + reductions): COMPLETE, RIGOROUS.** Simon's converse is reduced to
  the single Core Lemma (§3.1).
- **§4b (Route 1): the induction is set up correctly and sharply.** Value-parameterized by
  the left-context `ℓ`, induction on `≤𝓙`-depth, shrinking alphabet `Stab_R(ℓ)`, budget
  `d(ℓ)=depth(ℓ)+1`, target `P(1)` ⟹ Core Lemma. **Base, Case 1, and the Case-2 reduction
  are rigorous.**
- **Residual: one step.** Case 2's "depth-budget / first-dropper" claim (i)+(ii) — proving
  that under `~_{r+1}` the two reductions agree even though the first dropper need not be
  determined (witness `(a,b,b,a) ~₂ (b,a,a,b)`, machine-checked). This is the genuine heart
  of Simon's theorem; it is the precise thing to nail before any sorry-free formalization,
  per the standing rule (no sorry-free claim until the mathematics is in hand).

- **§4c (R∩L approach): attempted; yields the Short-witness lemma (rigorous,
  machine-checked) but does NOT close.** It caps the relevant subword length at `n-1` and
  reduces to comparing canonical length-`≤(n-1)` witnesses, but reproduces the
  witness-matching obstruction one level down (machine-confirmed that `x_t ⊑ s ⇏ ∏s=∏x_t`).

- **§6 — COMPLETE PAPER PROOF in hand (Klíma, transcribed from the actual PDF).** The hard
  direction is settled on paper: `∼_L` 𝓙-trivial of index `m` ⟹ `∼_{2m-2} ⊆ ∼_L` ⟹ PT, via
  blue indices (Claim 1, = my R-droppers), dual red indices, and Claim 2 (shuffle determined
  by `Sub_{2m-2}`). §4–§4c (my reconstruction) are superseded but kept for the record; §4c's
  Short-witness lemma = Klíma's Claim 1.

**Formalization status (session 8) — steps 1–3 + 5 DONE sorry-free; step 4 is the residual.**
1. ✅ `con_jtrivial` — congruence-level 𝓙-triviality (in `Simon.lean`, sorry-free).
2. ✅ test-word set `Bk = {x | |x|≤k}` finite (`List.finite_length_le`, `[Finite α]`); folded
   into Lemma 1.
3. ✅ **Lemma 1** = `pt_of_subk_refines` (sorry-free): `∼ₖ ⊆ ∼_L ⟹ PT`, via the finite
   Boolean combination of `∼ₖ`-classes; needs `IsPiecewiseTestable.biUnion`/`biInter`
   (both proved sorry-free).
4. ⏳ **Lemma 3** = `subk_refines_of_jtrivial` (the ONE remaining sorry). Building blocks
   formalized sorry-free (session 8):
   - **`prefix_squeeze`** — constant prefix-product stretch ⟹ constant at every prefix.
   - **`reduceWord`/`reduceWord_spec`** — the skeleton (value-changing "blue" letters),
     `φ(skel w)=φ(w)` in every left context.
   - **`GoodSub` / `GoodSub.value`** — **Claim-1 kernel, now clean and verified**: deleting
     value-*fixing* letters preserves `φ` (`val·φ(r)=val·φ(u)`). [Computationally established
     (exhaustive on the 14-elt monoid) that the naive routes fail — `x ⊑ y ⇏ φ(y)≤𝓙 φ(x)`,
     and `skel(t)⊑r⊑t ⇏ skel(r)=skel(t)` — but the value-fixer-deletion mechanism is correct:
     a non-blue letter `c` has `φ(prefix)·φ(c)=φ(prefix)`, so removing it keeps `φ` *and* all
     other prefix values, hence the blue/non-blue structure. `GoodSub` captures exactly this.]

   - **`goodsub_reduceWord`** — the skeleton *is* a `GoodSub` witness.
   - **`GoodSub.keepFixer`** — adding back a value-fixer preserves `GoodSub` (skeleton → any
     subword keeping all value-changers, e.g. `ū`).

   **Claim-1 machinery is now substantially in place** (the `GoodSub` framework + skeleton +
   value-preservation + add-back). What remains for Claim 1 is bookkeeping: define the blue
   indices and assemble `φ(ū)=φ(u)` for the specific `ū`.

   **Claim 2 — both position-bound foundations done (session 9).**
   - **`matchLen` / `matchLen_le`** — greedy matching is leftmost (`s ⊑ w.take n ⟹
     matchLen s w ≤ n`): the bound `i_t ≤ ℓ_t` (blue = leftmost occurrence of `u_left`).
   - **`matchLenR` / `matchLenR_ge`** — dual rightmost (via reversal): the bound
     `ℓ'_t ≤ j̄_t` (red = rightmost occurrence of `v_right`).

   **Blue-position connection — DONE (sessions 10–11).** The leftmost bound `i_t ≤ ℓ_t` is
   now fully machine-checked, sorry-free, via this chain (all in `Simon.lean`):
   - **`reduceWord_append`** — `skel(l₁ ++ l₂) = skel(l₁) ++ skel(val', l₂)`;
     **`reduceWord_take_prefix`** — `skel(u.take n) <+: skel(u)`.
   - **`reduceWord_head_changes`** — the head of the skeleton is a value-*changer*.
   - **`reduceWord_nil_forward`** — empty skeleton ⇒ every letter fixes the value.
   - **`reduceWord_trailing_fix`** (the sync) — after greedily matching the skeleton against
     `u`, every *remaining* letter fixes the final value `val·φ(u)`.
   - **`matchLen_drop_mem`** — if `s ++ [a] ⊑ w` then `a` lands in `w.drop (matchLen s w)`
     (greedy is leftmost).
   - **`leftmost_bound`** — Klíma's `i_t ≤ ℓ_t`. Assembled as a contradiction: an extra
     changer `a` past the blue skeleton would have to sit in the trailing region (where
     everything fixes the value) yet *changes* the value. So blue positions = leftmost
     occurrence of the blue word.

   **Red/dual side — DONE (session 11).** Obtained *for free* from the blue chain, no new
   induction:
   - **`opPhi`** — read letters into `Mᵐᵒᵖ` (`= lift(op ∘ φ)`), so prefixes of `u.reverse`
     track the *suffix* values of `u`; **`redSkel φ u := reduceWord (opPhi φ) 1 u.reverse`**.
   - **`rightmost_bound`** — Klíma's `ℓ'_t ≤ j̄_t`: if the last `t` red letters of `u` embed
     in the suffix `u.drop m`, that suffix has `≥ t` suffix-value changes. Proved by
     instantiating `leftmost_bound` at `opPhi φ` and `u.reverse`, then `List.reverse_drop`.

   Both position bounds (blue leftmost + red rightmost) are now machine-checked, sorry-free.

   **★ `shuffleWord ⊑ u` — DONE (session 12).** The two-cursor merge induction `merge_sub`
   (all three cases `lt`/`eq`/`gt`) is machine-checked — the hardest single proof in the
   development. Banked toolchain: `matchLen_append`, `matchLen_take_sublist`,
   `matchLenR_drop_sublist`, `matchLenR_localize`, `append_sublist_iff_matchLen`
   (order-determination), `emb_step`, `matchLen_single_drop`, `sublist_drop_single`,
   `matchLen_append_sublist`, `matchLen_append_strict`, `matchLenR_cons_lt` (red monotonicity),
   `blue_advance`, `matchLen_take_strict_mono`, and the rightmost-pinning chain
   `matchLen_single_get?`→`matchLen_getElem_last`→`matchLenR_get?`→`matchLen_single_le_matchLenR`.
   Invariant: blue cursor `matchLen (x.take i) u ≤ p`, next blue `> p`, next red `≥ p`; each step
   emits the position-minimal letter and advances `p`. **`shuffleWord_sublist`** falls out at
   `i=j=p=0`.

   **★ `bridge_u : φ(ū) = φ(u)` — DONE (session 12), `core_insert`-FREE.** The value half of
   Claim 1, by a value-tracking twin of `merge_sub`. New machinery, all sorry-free:
   - **`value_at_gap`** — between consecutive blue ends the running value is constant and equals
     `φ(u_left.take i)`. Pure, via `leftmost_bound` (`|reduceWord φ 1 (u.take q)| = i` squeezed
     both ways). This is the alignment that makes red letters *value-fixers*.
   - **`value_at_end`** — past the last blue end the value is `φ(u)`. Dual squeeze.
   - **`reds_fix_tail`** — every letter of a subword living past the last blue fixes `φ(u)`
     (base case: blues exhausted, reds remain).
   - **`value_merge`** — the value induction: same two-cursor invariant as `merge_sub`,
     concluding `φ(x.take i)·φ(mergeO … i j) = φ(u)` for `x = reduceWord φ 1 u`. Blue steps
     advance (`φ(x.take i)·φ a = φ(x.take(i+1))`); red steps fix (`value_at_gap` at `q,q+1`,
     `u[q]=b`); exhausted/trailing close via `φ(x)=φ(u)` / `reds_fix_tail`.
   - **`shuffleWord_value`** at `i=j=p=0`: `φ(shuffleWord (reduceWord φ 1 u) y u) = φ(u)`.
   This **bypasses the whole `core_insert`-gated `sandwich`/`subword_jle` section** — Klíma's
   route is now realised in Lean.

   **Dual length budget — DONE (session 12).** `redWord_length_lt : |(redSkel φ v).reverse| <
   card M`, "for free" via `Mᵐᵒᵖ`: `greenJLe_op`/`greenJLe_unop` (the `𝓙`-order is symmetric
   under `op`, witnesses swap) → `isJTrivial_op : IsJTrivial M → IsJTrivial Mᵐᵒᵖ` →
   `reduceWord_length_lt (opPhi φ) v.reverse` + `card Mᵐᵒᵖ = card M`. Also banked `opPhi_ofList :
   opPhi φ (ofList w) = op (φ (ofList w.reverse))` (the forward↔dual value bridge).

   **`bridge_v` — the remaining substantial piece (session 12 finding).** The economical route
   needs the reversal identity `(shuffleWord x y v).reverse = shuffleWord y.reverse x.reverse
   v.reverse`. **This is NOT a quick corollary** — empirically confirmed structurally adverse:
   `shuffleWord` is `mergeO (brCmp x y v) …`, and `brCmp x y v` is a *global* comparator (depends
   on the full `x`, not a localizable head), so structural induction on `x`/`y` cannot use its IH
   (the probe shows the `cons` case stuck on `brCmp (a::x') ≠ brCmp x'`); and `mergeO` is
   *front-consuming* while reversal needs back-consumption (suffix↔prefix mismatch defeats the
   measure-induction used for `merge_sub`/`value_merge`). Every route to `bridge_v` — word
   reversal, a right-anchored `value_merge_right`, or a position-list reformulation — re-derives
   merge machinery of comparable size to `value_merge`; it is the genuine remaining work, not a
   wrapper. The blues `u_left` are *right*-fixers of `v` and the reds `v_right` carry `v`'s value,
   so the closure is the exact left-right mirror of `bridge_u` (which is why no shortcut bypasses
   the reversal).

   **★ `bridge_v` REDUCED to one φ-free list lemma — DONE (session 12).** `bridge_v_of_reverse`:
   *given* the reversal identity `hrev`, `φ(v̄)=φ(v)` follows with **no new value machinery** — the
   entire value argument is `shuffleWord_value` (`bridge_u`) run in `Mᵐᵒᵖ` over `v.reverse`
   (`v_right.reverse = redSkel φ v = reduceWord (opPhi φ) 1 v.reverse` is the *left* skeleton
   there), translated back by `opPhi_ofList`. Banked sorry-free. **Consequence:** a
   `value_merge_right` is *not needed* — `bridge_v` has **no residual value content**; the sole
   gap is the pure combinatorial `hrev`.

   **⚠ The reversal lemma is FALSE — verified (session 12 continued).** `#eval` refutes it:
   `(shuffleWord [1] [0] [0,1]).reverse = [1]` but `shuffleWord [0] [1] [1,0] = [0]`. Cause:
   `brCmp`'s `eq` always emits the **blue** and drops the **red**, which is not reversal-symmetric.
   The position-list idea also fails for the same reason — `shuffleWord` is **not** `v` at the
   sorted union of (leftmost-x ∪ rightmost-y) positions: on the counterexample `shuffleWord
   [b][a][a,b] = [b]` drops the red `a` at position 0 even though `0 ∉` the blue position `{1}`.
   So `bridge_v_of_reverse` (though it compiles) rests on a **false** hypothesis — that route is
   dead and is marked as such in the source.

   **The correct reading of `brCmp.eq` (Klíma Claim 2).** Re-reading the source: cases (i)/(ii)/(iii)
   of Claim 2 map exactly to `brCmp` lt/eq/gt, and **(ii) says `eq ⟺ ir₀ = j_s₀`** — blue and red
   occupy the *same* index. So on Klíma's *valid* inputs (`u_left`/`v_right` genuine skeletons,
   `u ∼ₖ v`) the `eq` tie-break only fires on coincidence and `shuffleWord` *does* realise the
   blue∪red position union; the counterexample is an *invalid* input (different letters forced into
   `eq`). The construction is sound; only the **general** reversal law is false.

   **Correct route to `bridge_v` (Klíma's "Similarly v ∼L v"):** the **dual Claim 1** — `v̄`
   contains every **red** (rightmost `v_right`) position of `v`, hence `φ(v̄)=φ(v)` by the
   right-scan `GoodSub` (the `Mᵐᵒᵖ` mirror of `value_merge`/`shuffleWord_value`).

   **★ Feasibility of the right-anchored induction — CONFIRMED (session 12 continued).** Clean
   invariant **`φ(ofList (mergeO-suffix (i,j))) = φ(ofList (v.drop p))`** (no `φ(x.take i)`
   factor — simpler than `value_merge`). At `(0,0,0)` it *is* the goal `φ(v̄)=φ(v)`. Maintenance:
   emit `v[pos]`, recurse to `p'=pos+1`; `φ(v[pos]::suffix')=φ(v[pos])·φ(v.drop(pos+1))=φ(v.drop
   pos)`, so it suffices that `φ(v.drop p)=φ(v.drop pos)` — the skipped `v[p:pos]` are
   **right-fixers**. Cases: **lt** (next red `> bpos`) and **gt** (`q` is the next red) give
   `[p,pos)` red-free **unconditionally**. The right-fixer fact is *free* via `Mᵐᵒᵖ` —
   `suffix_value_at_end` (banked) = `value_at_end (opPhi φ) v.reverse` translated by
   `opPhi_ofList`.

   **⚠ The catch — the `eq` case needs the coincidence lemma (Klíma Claim 2 (ii)).** `eq` emits
   the blue and **drops** red `y[j]`. Since `y = v_right` is the right *skeleton*, every `y[j]`
   is a suffix-**changer**; dropping one strictly before `bpos` breaks the invariant. So `eq` must
   force `matchLenR (y.drop j) v = matchLen (x.take (i+1)) v − 1` (blue and red **coincide**,
   `a=b`). That is exactly Claim 2 (ii), and it is **not** a single-word fact for arbitrary
   `u_left` — it needs the `u ∼ₖ v` linkage (`leftmost_bound` + `rightmost_bound`). **Verdict:**
   the induction closes, helpers are free, but `bridge_v` is **not** a standalone dual of
   `bridge_u` — it is entangled with `∼ₖ` through the coincidence lemma, which is the substantial
   remaining content (the paper's stated "essence", §Lemma 3). Plan: (A) coincidence lemma
   `eq ⟹ coincide` from the two bounds + `∼ₖ`; (B) the ~120-line right-anchored induction modulo
   (A); (C) assembly threading `∼ₖ`.

   **★ Coincidence (A) sharpened to a single `∼ₖ` statement — session 12 continued.** Banked
   sorry-free: the comparator dictionary `brCmp_eq_iff`, **`brCmp_eq_iff_matchLen`** (`eq ⟺
   matchLenR (y.drop j) v < matchLen (x.take(i+1)) v ≤ matchLenR (y.drop(j+1)) v`), and
   **`coincidence_of_sameLetter`** — in the `eq` case, *if* the blue end `v[matchLen−1]` is the
   same letter as the next red `y[j]`, then `matchLenR (y.drop j) v = matchLen (x.take(i+1)) v −1`
   (the red sits exactly on the blue). Proof: `eq` puts `y.drop(j+1)` past the blue end
   (`matchLen_append_sublist`); same-letter lets all of `y.drop j` embed *starting at* the blue
   position, so its rightmost start `≥` it (`matchLen_le` on reverses), and `eq` gives `≤`. **No
   `∼ₖ`.** So the entire `∼ₖ`-dependent content of `bridge_v` is now the *single* sharp statement

   > **`eq ⟹ x[i] = y[j]`** (the leftmost blue end and the next rightmost red are the same letter)

   — Klíma Claim 2's irreducible heart (`different letters ⟹ never eq`; verified to fail without
   `∼ₖ`: `shuffleWord [1] [0] [0,1]` has `eq` with `1≠0`). Everything else around it is proved.

   **★ Option A (build `bridge_v`+assembly modulo same-letter) — dual machinery COMPLETE
   (session 12 continued).** All per-step ingredients for the right-anchored value induction
   `value_merge_right` are banked sorry-free:
   - **`suffix_value_at_gap`** — dual of `value_at_gap`: in the `t`-th red gap, `φ(v.drop p)`
     is fixed `= φ((redSkel φ v).take t).reverse`. Via `value_at_gap (opPhi φ) v.reverse`.
   - **`matchLenR_redWord_drop`** — index bridge `matchLenR ((redSkel φ v).reverse.drop j) v =
     |v| − matchLen ((redSkel φ v).take (|redSkel|−j)) v.reverse`, converting `matchLenR`-on-`v`
     cursor bounds to `matchLen`-on-`v.reverse` gap bounds.
   - **`suffix_fixer`** — the clean per-step interface: `p ≤ q` in the same red-gap `j` ⟹
     `φ(v.drop p) = φ(v.drop q)` (gap 0 via `suffix_value_at_end`, gaps `j ≥ 1` via
     `suffix_value_at_gap`).
   The induction's invariant is fully worked out: **`φ(ofList (mergeO-suffix (i,j))) =
   φ(ofList (v.drop p))`** with the cursor `p` tracked in red-gap `j`
   (`matchLenR (y.drop (j-1)) v < p ≤ matchLenR (y.drop j) v`), maintained across lt/gt/eq
   (eq uses the same-letter coincidence). Each emission's suffix-fixer is `suffix_fixer`; the
   `x.drop i = []` case uses the list identity `y.drop j = ((redSkel φ v).take (|y|−j)).reverse`
   + `suffix_value_at_gap`.

   **★★ `value_merge_right` + `bridge_v` DONE — Option A's induction complete.** Banked sorry-free
   (axiom-checked): **`value_merge_right`** (227-line dual induction) — with `y=(redSkel φ
   v).reverse` and coincidence hypothesis `hcoin`, proves `φ(mergeO-suffix (i,j)) = φ(v.drop p)`,
   cursor in red-gap `j`; helpers `redWord_value`, `reds_dump_value`, `ofList_phi_one` +
   `blues_dump_value` (changer-free ⟹ value 1), `suffix_fixer` per emission, `hcoin` for the `eq`
   drop. **`shuffleWord_value_right`** at `(0,0,0)`: `φ(shuffleWord x v_right v) = φ(v)` for any
   blue `x ⊑ v`, modulo `hcoin` — this *is* `bridge_v`. Both bridges now in hand. The entire
   `bridge_v` residual is `hcoin`, and `hcoin ⟸ same-letter` via `coincidence_of_sameLetter`.

   **Remaining:** (C) **assembly** of `subk_refines_of_jtrivial`: `φ(u)=φ(ū)`
   (`shuffleWord_value`), `ū=v̄` (`shuffleWord_eq`, fed by `∼ₖ` + budgets
   `reduceWord_length_lt`/`redWord_length_lt`, `k=2m−2`), `φ(v̄)=φ(v)` (`shuffleWord_value_right`
   with `hcoin` from `coincidence_of_sameLetter`) ⟹ `φ(u)=φ(v)` ⟹ `syntacticCon` — modulo the
   same-letter implication; (B) the same-letter implication itself (Klíma Claim 2). The whole
   development now reduces to the single `eq ⟹ x[i]=y[j]` statement.

   **★★★ (C) ASSEMBLY DONE — `subk_refines_of_jtrivial` fully wired, ONE `sorry` left.** The
   complete Klíma proof is now assembled in `subk_refines_of_jtrivial`: pick `k = 2·card M − 2`;
   from `∼ₖ` derive `hsim` (`Sublist`-agreement up to `k`); set `ul = reduceWord φ 1 (toList u)`,
   `vr = (redSkel φ (toList v)).reverse`; budgets give `|ul|,|vr| < m` so `|ul|+|vr| ≤ k`; `∼ₖ`
   transfers `ul ⊑ toList v` and `vr ⊑ toList u`; then `φ(u)=φ(ū)` (`shuffleWord_value`),
   `ū = v̄` (`shuffleWord_eq`), `φ(v̄)=φ(v)` (`shuffleWord_value_right` with `hcoin` via
   `coincidence_of_sameLetter`), so `φ(u)=φ(v)`, and `(Con.eq _).mp` gives `syntacticCon L u v`.
   `#print axioms subk_refines_of_jtrivial` = `[propext, sorryAx, Classical.choice, Quot.sound]` —
   the lone `sorryAx` is the **same-letter** `hsame`. **Everything else in Simon's converse is
   machine-checked sorry-free.** The single remaining gap is exactly Klíma Claim 2's
   `eq ⟹ x[i]=y[j]` (the `∼ₖ` cross-word order argument) — task (B).

   **★★★ (B) SCAFFOLDED — residual isolated to the named lemma `klima_sameLetter`.** The
   same-letter implication is extracted as a precise, documented theorem `klima_sameLetter`
   (`[Fintype M] (hJ : IsJTrivial M) (φ) (u v) (hsim : ∼ₖ on `Sublist`) (i' j') (heq : brCmp … = eq)
   ⊢ v[matchLen (u_left.take (i'+1)) v − 1]? = v_right[j']?`), and `subk_refines_of_jtrivial`'s
   proof now references it sorry-free. `#print axioms simon` = `[propext, sorryAx, Classical.choice,
   Quot.sound]` with the **sole** `sorryAx` being `klima_sameLetter`. **Finding on the fill:** the
   same-letter is *not* "brCmp eq ⟹ same letter" as a per-pair fact — verified that, even in `u`
   with `u_left` the genuine skeleton, "blue strictly inside a red-gap, different letters"
   (`j̄_{s0} < i_{r0} < j̄_{s0+1}`) is single-pair consistent. Klíma does **not** prove it directly;
   his bridge_v uses the *position-union* `v̄ ⊇ all reds`. My `mergeO`/`brCmp` `v̄` (which can drop a
   red in `eq`) needs it, and its truth is tied to the **global** order-consistency of the whole
   merge under `∼ₖ`. So the fill is genuinely Klíma's research-level global argument
   (`it≤ℓt` + order-determination + merge consistency), the paper's "essence". Documented plan in
   the `klima_sameLetter` docstring.

   **Assembly (after `hrev`):** `ū = v̄` (`shuffleWord_eq`, already proved, fed by the `∼ₖ`
   subword agreement), budgets `|u_left| < card M` (`reduceWord_length_lt`), `|v_right| < card M`
   (`redWord_length_lt`, DONE), `k = 2m-2`, then `φ(u)=φ(ū)=φ(v̄)=φ(v) ⟹ syntacticCon`.

   **Shuffle — design fixed + merge core started (session 11).** `ū` = merge of the blue word
   `u_left` and red word `v_right`, interleaved by position in `u`. Represented by an
   `Ordering`-comparator `cmp i j` (is the `i`-th blue position `lt`/`eq`/`gt` the `j`-th red
   position):
   - **`mergeO`** — the comparator-driven merge (`eq` = shared position, emitted once);
     **`mergeO_left_sublist`** — the blue word always embeds (Claim 1's hypothesis).
   - **Key payoff of this design: merge-determination is *free*.** `mergeO` is a function of
     `cmp`, so `ū = v̄` reduces to `cmp_u = cmp_v`.
   - Subword foundations: `GoodSub.sublist`, `reduceWord_sublist` (`u_left ⊑ u`),
     `redSkel_sublist`, `redWord_sublist` (`v_right ⊑ v`).

   **Shuffle equality `ū = v̄` — DONE (session 11).** The design collapsed the
   "multi-hundred-line core" to ~20 lines: define the comparator *directly from the subword
   tests*, then everything is a function.
   - **`brCmp x y w i j`** — Klíma's `(i)/(ii)/(iii)` test as an `Ordering`: `lt` ⟺
     `(x.take(i+1)) ++ (y.drop j) ⊑ w`; `eq` ⟺ shared-position variant embeds; else `gt`.
   - **`shuffleWord x y w := mergeO (brCmp x y w) x y 0 0`** = `ū`.
   - **`brCmp_eq`** — `brCmp x y u = brCmp x y v` whenever `|x|+|y| ≤ k` and `u ∼_k v` (every
     test word has length `≤ k`).
   - **`shuffleWord_eq`** — `ū = v̄`, immediate from `brCmp_eq` + `mergeO` being a function.

   This is the combinatorial heart of Claim 2, machine-checked.

   **Value side (Claim 1) — fully reduced to ONE standard monoid fact (session 12).** Verified
   chain, `core_insert` threaded as an explicit premise (no `sorry`):
   - **`subword_jle_gen` / `subword_jle`** — *subword order refines the J-order*
     `x ⊑ w ⟹ φ(w) ≤𝓙 φ(x)`, by a left-context induction whose only non-trivial step uses
     `core_insert`;
   - **`sandwich`** — Klíma's Claim 1 `skel(u) ⊑ r ⊑ u ⟹ φ(r) = φ(u)`, from `subword_jle`
     + antisymmetry of `≤𝓙` (`IsJTrivial`).

   This reduces to one atomic lemma `core_insert : ∀ P A Y, P·A·Y ≤𝓙 P·Y` (the
   Straubing–Thérien ordered-monoid property, subword order ⊆ J-order).

   **CORRECTION (session 12, from transcribing Klíma's Claim 1 verbatim).** `core_insert` is a
   **detour, NOT on the critical path.** Klíma proves Claim 1 by *positions + congruence*:
   a non-blue index has `u_{i−1} ∼_L u_{i−1} a_i` (a prefix value-fixer), and since `∼_L` is a
   congruence, deleting non-blue letters at their positions preserves `∼_L`. That is **exactly
   `GoodSub.value_one`** — it never uses subword⊆J-order. So the `subword_jle`/`sandwich` chain
   above is *correct but unnecessary* (kept, annotated as an alternative); `core_insert`'s real
   textbook proof is Straubing–Thérien via semigroup expansions (heavy), and is not needed.

   **Actual remaining path (Klíma's), Lemma 3:**
   1. define `ū` by **positions** — done as **`maskKeep φ 1 es u`** (forces every value-changer,
      admits a fixer "extras" mask `es` = the red positions);
   2. **Claim 1 (value side) — DONE, session 12, unconditional.** `maskKeep` is *always* a
      `GoodSub` (**`goodsub_maskKeep`**), so **`maskKeep_phi`** gives `φ(ū)=φ(u)` for *any*
      extras — no `core_insert`, no J-triviality. This is the real Claim 1.
   3. **Bridge** — `maskKeep φ 1 (redMask) u = shuffleWord u_left v_right u`, the
      `(i)/(ii)/(iii)` lemma (uses `leftmost_bound`/`rightmost_bound`). **← remaining core.**
   4. **Claim 2** — `ū = v̄` then reuses **`shuffleWord_eq`** directly.

   The genuine remaining core is now exactly the **bridge (step 3)** — the `(i)/(ii)/(iii)`
   index argument connecting positions to the length-`≤k` subword tests — plus the length
   budget `|u_left|+|v_right| ≤ 2m−2` and assembly. `k = 2·card(M)−2`. No open math; no deep
   monoid theorem (the position route sidesteps `core_insert`, now confirmed in code).

   **Progress on the final three (session 12):**
   - **Claim-1 value side — DONE** (`maskKeep`/`goodsub_maskKeep`/`maskKeep_phi`).
   - **Length budget (step 2) — DONE.** `reduceWord_idem`; `vals` (post-change values) with
     `vals_chain` (strict `≤𝓙`-descent *by construction*); `reduceWord_length_lt`:
     `|u_left| < card M`. With the `opPhi`/reversal dual, `|u_left|+|v_right| ≤ 2·card M − 2`.
   - **Bridge (step 1) — STILL OPEN, the genuine wall.** It is in fact *two* dual sub-lemmas:
     `φ(shuffleWord u_left v_right u) = φ(u)` (via blue/`mergeO_left_sublist`) and the red dual
     for `v`. Each needs `shuffleWord = maskKeep`-style positional alignment — the
     `(i)/(ii)/(iii)` argument. Confirmed: no shortcut (a merge of two subwords embeds in `u`
     only when the comparator is position-consistent; that consistency *is* `(i)/(ii)/(iii)`).
   - **Assembly (step 3)** — logically ready (`shuffleWord_eq` + length budget + the two bridge
     lemmas + `Con.eq`), blocked only on the bridge.
5. ✅ `pt_of_jtrivial` rewritten to `obtain ⟨k,href⟩ := subk_refines_of_jtrivial h;
   exact pt_of_subk_refines k href` — sorry-free *modulo* step 4.

So Simon's converse is now reduced, in Lean, to exactly Klíma's Lemma 3. Bound `k = 2m-2`.

---

## ⚠⚠⚠ COURSE CORRECTION (session 12, via computational testing): `klima_sameLetter` is FALSE

I scaffolded the last residual as `klima_sameLetter` (`brCmp = eq ⟹ same letter`) and then
**tested it on a concrete 𝓙-trivial monoid** (`M = Bool×Bool` under OR — the "contains a, contains
b" language, `m=4`, `k=2m−2=6`) before proving it. Findings:

1. **`klima_sameLetter` is refuted.** Witness `u=v=[1,1,0,0]`: `ul = reduceWord φ 1 u = [1,0]`,
   `vr = (redSkel φ v).reverse = [1,0]`, and at the **reachable** merge state `(1,0)` we have
   `brCmp ul vr v 1 0 = eq` while the emitted blue is `a` (`ul[1]=0`) and the dropped red is `b`
   (`vr[0]=1`) — **different letters**. So coincidence / `hcoin` fails *even on the merge path*.
   ⟹ `value_merge_right`, `shuffleWord_value_right`, and `klima_sameLetter` are **uninstantiable**
   (rest on a false hypothesis); the `value_merge_right` route to `bridge_v` is **dead**.

2. **Yet `φ(v̄)=φ(v)` and `vr ⊑ v̄` both hold for the `mergeO`-`v̄` under `∼ₖ`** (1683 `∼ₖ` pairs of
   length ≤5, **0 failures** of either). The "dropped" red is *compensated* — its letter reappears
   (the earlier emitted blue), so `mergeO`-`v̄ = [1,0,0]` still has `φ=(true,true)=φ(v)`.
   (Without `∼ₖ`, `φ(v̄)=φ(v)` fails for 2210/6561 pairs — so it genuinely needs `∼ₖ`.)

3. **This is circular, not a proof route.** Because `ū=v̄` (`shuffleWord_eq`) and `φ(ū)=φ(u)`
   (`bridge_u`), for *any* shuffle `φ(v̄)=φ(v) ⟺ φ(u)=φ(v) =` the goal. So `φ(mergeO-v̄)=φ(v)` is
   true *because* the goal is — not independently provable. The `mergeO` `eq`-case **drops red
   positions** (compensated), so Klíma's **dual Claim 1** (`v̄ ⊇ all red positions ⟹ φ(v̄)=φ(v)`,
   the `core_insert`-free `maskKeep_phi`/`opPhi` GoodSub closure) does **not** apply to it.

### Confirmed corrected route — the position-union (Klíma's actual `ū`/`v̄`)

`bridge_v` needs a `v̄'` keeping **every** red position (never dropping), so dual Claim 1 gives
`φ(v̄')=φ(v)` *independently* of the goal. Plan:
- `v̄' = v` restricted to the sorted union of (leftmost-`ul` positions ∪ rightmost-`vr` positions)
  — never drops;
- `φ(ū')=φ(u)`, `φ(v̄')=φ(v)` via Claim 1 / dual Claim 1 = the banked `maskKeep_phi` GoodSub closure
  (`core_insert`-free; Klíma's "non-blue letters are value-fixers");
- `ū'=v̄'` via **order-determination** (`append_sublist_iff_matchLen` + `∼ₖ`): the blue/red
  interleaving order is a function of length-`≤k` subword tests, identical in `u` and `v`.

**Salvageable banked work:** `merge_sub`/`shuffleWord_sublist`, `value_merge`/`shuffleWord_value`
(`bridge_u`), `shuffleWord_eq` (`ū=v̄`), the length budgets, and the `opPhi`/`redSkel`/
`maskKeep_phi`/`GoodSub` machinery. **Dead:** `value_merge_right`, `shuffleWord_value_right`,
`klima_sameLetter` (false), `bridge_v_of_reverse` (false `hrev`). The `mergeO`/`brCmp` design (which
drops reds in `eq`) stays for `bridge_u`/`ū=v̄` but cannot serve `bridge_v`; the position-union does.

---

## PROGRESS 2026-06-13 — position-union built, Claim 2 discharged (sorry-free)

The corrected route from the COURSE CORRECTION above is now substantially in Lean. Banked
sorry-free this session (all `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`):

- **`right_maskKeep_phi`** — dual Claim 1 closure (`Mᵐᵒᵖ` mirror of `maskKeep_phi`); makes
  `bridge_v` non-circular because the position-union keeps every red position.
- **`pcmp`** (position comparator) + `pcmp_lt_iff`, `pcmp_eq_iff` — compares the blue/red
  *positions* (`matchLen (x.take (i+1)) w − 1` vs `matchLenR (y.drop j) w`) directly. Its `eq` is
  *genuine coincidence*, so `mergeO (pcmp …)` never wrongly drops a red (the exact defect that made
  `klima_sameLetter` false).
- **`pcmp_eq_iff_brCmp`** — the key bridge: `pcmp = eq ⟺ brCmp = eq ∧ x[i]? = y[j]?`. Reuses the
  banked `coincidence_of_sameLetter`. Since `brCmp` transfers under `∼ₖ` and the carried letters
  `x[i]?, y[j]?` are word-independent, this is what makes `pcmp` transfer.
- **`mergeO_congr`** — comparators agreeing on the consulted rectangle `[i,i+|x|)×[j,j+|y|)` give
  the same merge (so `pcmp`'s *in-range* agreement suffices; out-of-range never consulted).
- **`pcmp_agree`** — order-determination: `pcmp x y u p q = pcmp x y v p q` for `p<|x|, q<|y|`
  (lt-boundary = subword test via `∼ₖ`; eq-boundary via `pcmp_eq_iff_brCmp` + `brCmp_eq`).
- **`posUnion x y w := mergeO (pcmp x y w) x y 0 0`** + **`posUnion_eq`** — **Klíma's Claim 2,
  corrected**: `posUnion x y u = posUnion x y v` (i.e. `ū' = v̄'`) via `mergeO_congr ∘ pcmp_agree`.
  No per-element coincidence needed — only the position *order*, which `∼ₖ` determines.

This is the genuinely combinatorial heart, and it is now done and verified. **Remaining:** the two
value-bridges for the position-union — `φ(posUnion ul vr u) = φ(u)` (Claim 1, `value_merge` adapted
to `pcmp`) and `φ(posUnion ul vr v) = φ(v)` (dual Claim 1; for `pcmp` the coincidence hypothesis
`hcoin` that doomed the `brCmp` version now holds **by definition**, since `pcmp = eq` *is*
position coincidence). Then rewire `subk_refines_of_jtrivial` through `posUnion`, discharging the
last (currently false) `klima_sameLetter` sorry.

---

## ✅ COMPLETE 2026-06-13 — Simon's converse is sorry-free

The position-union route is finished and wired in. `#print axioms simon` =
`[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**. The false `klima_sameLetter`
is deleted; nothing depends on it.

Final bridge lemmas banked this session (all axiom-clean):
- `value_merge_pcmp` + `posUnion_value` — `bridge_u`: `φ(posUnion u_left v_right u) = φ(u)`.
- `value_merge_pcmp_right` + `posUnion_value_right` — `bridge_v`: `φ(posUnion u_left v_right v) = φ(v)`,
  with **no `hcoin`** (the coincidence that doomed the `brCmp` version is definitional for `pcmp`).
- `posUnion_eq` — `ū' = v̄'` (Claim 2, order-determination).

`subk_refines_of_jtrivial` now reads: `hbu` (`posUnion_value`) ▸ `heqw` (`posUnion_eq`) ▸ `hbv`
(`posUnion_value_right`) ⟹ `φ(u)=φ(v)` ⟹ `syntacticCon` (`Con.eq`). Klíma's Lemma 3, hence
`pt_of_jtrivial`, hence `simon` (both directions), is fully proved.

**Key idea that closed it:** comparing blue/red *positions* directly (`pcmp = compare (matchLen …)
(matchLenR … + 1)`) instead of `brCmp`'s subword-test heuristic. `pcmp`'s `eq` is genuine
coincidence, so (a) `mergeO (pcmp …)` never drops a red ⟹ dual Claim 1 applies ⟹ `bridge_v`
non-circular; (b) `ū'=v̄'` needs only the position *order*, which `∼ₖ` determines via
`pcmp_eq_iff_brCmp` (`pcmp eq ⟺ brCmp eq ∧ x[i]?=y[j]?`) + the banked `coincidence_of_sameLetter`.
The whole proof remains `core_insert`-free (no J-trivial subword-order theorem needed).
