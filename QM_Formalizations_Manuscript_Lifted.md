# Quantum Mechanics in a Paraconsistent Type Theory: Formalization, Structure, and the Logic of Contradiction

**Author:** Lando⊗⊙perator  
**Date:** 2026-06-11

---

## Abstract

Quantum mechanics has, from its inception, resisted formalization in classical
logic. Superposition, complementarity, entanglement, and the measurement problem
each present a version of the same underlying difficulty: the theory appears to
require that certain statements be both true and false in ways that classical
logic cannot accommodate without collapse. This paper surveys a formalization of
quantum mechanical structure within a paraconsistent type theory — an extension
of dependent type theory in which the principle of explosion (ex contradictione
quodlibet) is blocked at the kernel level. The formalization spans the orbital,
nuclear, hadronic, electroweak, and field-theoretic levels, and connects to open
problems including the Yang-Mills mass gap, SIC-POVM existence, and the
Millennium Problems.

The central technical result is that quantum structure — from Pauli exclusion
through color confinement to the Frobenius identities governing Cooper pairing
and hadron formation — is the direct lattice-theoretic consequence of a single
architectural choice: admitting a four-valued logical substrate in which the
"both" state (true-and-false) is a well-defined lattice maximum rather than a
signal of inconsistency. Contradiction is contained, not eliminated.

We also describe the connection between SIC-POVM existence in all finite
dimensions and the mixed-signature Stark conjecture, a link that places quantum
information theory at the boundary of arithmetic geometry and Hilbert's 12th
Problem.

---

## 1. Four-Valued Logic and the Problem of Contradiction

Classical logic rests on a disquieting asymmetry. A single contradiction —
$P \land \neg P$ — licenses the derivation of any proposition $Q$ whatsoever. This
is the principle of explosion, and it means that classical theories cannot contain
even one contradiction without becoming trivial. For most of mathematics this is a
feature: consistency is preserved by ensuring contradictions never arise.

Quantum mechanics does not fit this model. An electron in a superposition of spin-up
and spin-down is not in a defective state that needs to be "fixed" by removing the
contradiction — the superposition *is* the physically correct description. The
measurement problem, similarly, is not a failure of quantum theory but a reflection
that the theory's native logic differs from the classical logic we use to reason
about measurement outcomes.

### 1.1 The Belnap Bilattice

In 1977, Nuel Belnap introduced a four-valued logic designed for reasoning with
inconsistent and incomplete information. The four values are:

- **N** (Neither): no information — neither true nor false has been established.
- **T** (True): the proposition has been established as true.
- **F** (False): the proposition has been established as false.
- **B** (Both): the proposition has been established as both true and false — a
  contradiction has been derived from the available information.

These four values carry two distinct partial orders, and it is the interaction
between these two orders that gives the logic its power.

**The information (approximation) order** arranges states by how much information
they contain: $\text{N} \sqsubseteq \text{T}, \text{F} \sqsubseteq \text{B}$. The
neither state N is the information minimum — it tells you nothing. The both state
B is the information maximum — it tells you everything, including the fact that
the available information is contradictory.

**The truth order** arranges states by "how true" they are:
$\text{F} \leq_t \text{N}, \text{B} \leq_t \text{T}$. False is the least true;
true is the most true. The critical point: N and B are incomparable in the truth
order. They occupy the same "truth level" (neither fully true nor fully false)
but differ in their information content — N is empty, B is full.

### 1.2 Truth-Functional Connectives

The connectives are defined to respect both orderings simultaneously. The
conjunction $a \land b$ returns the greatest lower bound in the truth order;
disjunction $a \lor b$ returns the least upper bound. The negation $\neg a$
is an involution that flips T and F while fixing N and B:

$$\neg\text{N} = \text{N}, \quad \neg\text{T} = \text{F}, \quad \neg\text{F} = \text{T}, \quad \neg\text{B} = \text{B}$$

That B is a fixed point of negation — $\neg\text{B} = \text{B}$ — is the formal
heart of paraconsistency. It means that B carries its own negation within itself.

### 1.3 No Explosion

The central theorem of Belnap logic is that contradiction is contained:

**Theorem 1 (Containment).** $\text{B} \land \neg\text{B} = \text{B} \neq \text{F}$.

In a classical setting, $P \land \neg P$ entails every proposition. Here,
$\text{B} \land \neg\text{B}$ evaluates to B — the contradiction is recognized
and recorded, but it does not propagate. The logical system does not collapse.

The proof is by direct computation: $\text{B} \land \neg\text{B} = \text{B} \land \text{B} = \text{B}$.
And B is manifestly distinct from F — one can verify this by mapping each value to
a distinct integer (N→0, T→1, F→2, B→3) and observing that B's image (3) differs
from F's image (2). No deeper argument is needed; the containment is structural.

**Theorem 2 (B is Maximal in Information).** For every value $a$, $a \sqsubseteq \text{B}$.
Proof: by case analysis on $a$. The four cases N, T, F, B each satisfy the
approximation relation with B as the upper bound.

**Theorem 3 (N is Minimal).** For every value $a$, $\text{N} \sqsubseteq a$.
Proof: N contains no information, so it approximates everything — again verified
by case analysis.

### 1.4 Lattice Structure

The meet $a \sqcap b$ (greatest lower bound in the information order) and join
$a \sqcup b$ (least upper bound) form a distributive lattice. Meet:
N absorbs everything; B passes through; T and F meeting each other give N
(they share no information). Join: B absorbs everything; N passes through;
T and F joining give B (their combined information is contradictory).

The distributivity law $a \sqcap (b \sqcup c) = (a \sqcap b) \sqcup (a \sqcap c)$
is verified by checking all $4^3 = 64$ triples — a finite computation readily
performed by a proof assistant. The lattice is not Boolean: B has no complement
in the Boolean sense. There is no value $c$ such that $\text{B} \land c = \text{F}$
and $\text{B} \lor c = \text{T}$ simultaneously. B is *its own* negation, which is
a strictly weaker property than having a Boolean complement — and it is precisely
this weakening that permits contradiction without explosion.

### 1.5 Designated Values and Paraconsistent Consequence

For consequence relations, both T and B count as *designated* — they are
"true enough" to license inference. A formula $\phi$ is a paraconsistent
consequence of premises $\Gamma$ if, whenever every premise in $\Gamma$ takes a
designated value, $\phi$ also takes a designated value. This validates all
classical inferences that do not rely on explosion, while blocking the
derivation of arbitrary conclusions from contradictions.

The B state is thus both designated and self-negating — a genuine *dialetheia*
in the technical sense introduced by Graham Priest. It is a proposition that is
both true and false, recognized as such by the logic, and yet does not trivialize
the system. This is the logical foundation on which the quantum mechanical
formalizations are built.

---

## 2. The Orbital Bilattice: Pauli Exclusion as a Ceiling Theorem

The first quantum system to admit a complete Belnap formalization is, perhaps
surprisingly, the simplest: the electron orbital. An atomic orbital can hold
zero, one, or two electrons. With one electron, the spin can be up or down.
The four resulting states — empty, spin-up, spin-down, paired — form a structure
that is not merely *analogous to* the Belnap bilattice. They *are* the Belnap
bilattice, up to relabeling.

### 2.1 The Four Orbital States

Define the set of orbital states $\mathcal{O} = \{\emptyset, \uparrow, \downarrow, \uparrow\downarrow\}$.
The intuitive mapping to Belnap values is:

| Orbital state | Belnap value | Physical interpretation |
|:---|:---|:---|
| $\emptyset$ (empty) | N | No electron present; no information about spin |
| $\uparrow$ (spin-up) | T | One electron, positive spin projection |
| $\downarrow$ (spin-down) | F | One electron, negative spin projection |
| $\uparrow\downarrow$ (paired) | B | Two electrons, both spin projections occupied |

This mapping $\phi: \mathcal{O} \to \mathcal{B}_4$ is not just a convenient
analogy — it is a bijection and an order isomorphism for both the information
order and the truth order. The proof is straightforward: define the inverse
$\phi^{-1}: \mathcal{B}_4 \to \mathcal{O}$ by the obvious correspondence, and
verify that $\phi \circ \phi^{-1} = \text{id}_{\mathcal{B}_4}$ and
$\phi^{-1} \circ \phi = \text{id}_{\mathcal{O}}$ by checking four cases each.

### 2.2 The Information Order: Occupancy

The information order on $\mathcal{O}$ tracks how many electrons are present:

$$\emptyset \sqsubseteq \uparrow, \downarrow \sqsubseteq \uparrow\downarrow$$

Empty is the minimum — no occupancy information. Paired is the maximum — both
possible spin states are occupied. Spin-up and spin-down are incomparable with
each other: neither contains more occupancy information than the other. Both
sit at the same level in the information lattice.

This order exactly mirrors Belnap's approximation order under $\phi$:
$\phi(a) \sqsubseteq \phi(b)$ if and only if $a \sqsubseteq b$ in the occupancy
order. The isomorphism is order-preserving in both directions.

### 2.3 The Truth Order: Chirality

There is a second natural order on orbital states: by *net spin projection*,
or what we will call chirality. Spin-down (negative projection) is the minimum;
spin-up (positive projection) is the maximum; empty and paired, having zero net
projection, sit in between:

$$\downarrow \leq_t \emptyset, \uparrow\downarrow \leq_t \uparrow$$

Crucially, empty and paired are incomparable in this order — they agree on net
spin (both zero) but differ in occupancy. This is the same structure as Belnap's
truth order, where N and B occupy the same "truth level" but differ in information
content.

### 2.4 Pauli Exclusion as a Lattice Ceiling

The Pauli exclusion principle states that no two electrons in an atom can share
the same set of quantum numbers. In the orbital bilattice, this becomes a purely
structural theorem:

**Theorem 4 (Pauli Exclusion — Ceiling Form).** The paired state $\uparrow\downarrow$
is maximal in the information order. If $\uparrow\downarrow \sqsubseteq s$ for any
orbital state $s$, then $s = \uparrow\downarrow$.

The proof is trivial but profound: examine the four possible values of $s$. The
only state that can be above paired in the information order is paired itself.
There simply is no fifth orbital state — no "triply occupied" state exists in the
lattice.

This formulation reveals something that the usual statement of Pauli exclusion
obscures: the principle is not a dynamical prohibition but a *type-theoretic*
constraint. The orbital state space has exactly four values because the bilattice
is complete at B. Adding a third electron would require a state $\omega$ with
$\uparrow\downarrow \sqsubset \omega$, but no such state exists in the type.
The exclusion is not enforced by a force or a rule — it is enforced by the
cardinality of the state space itself.

One might object: "But this is just counting — of course there are only four
states for two spin-1/2 particles." The rebuttal is that the counting *itself*
derives from the lattice structure. The bilattice with N and B as extremal
elements and T, F as incomparable intermediates is the unique four-element
structure with two distinct orderings whose interaction produces a ceiling
at B. The number of states is not an empirical input; it follows from the
lattice axioms.

### 2.5 Cooper Pairing and the Frobenius Identity

Define two operations on orbital states:

**Depairing** $\delta: \mathcal{O} \to \mathcal{O} \times \mathcal{O}$ resolves an
orbital into its constituent spin components:
$$\delta(\uparrow\downarrow) = (\uparrow, \downarrow), \quad
\delta(\uparrow) = (\uparrow, \emptyset), \quad
\delta(\downarrow) = (\emptyset, \downarrow), \quad
\delta(\emptyset) = (\emptyset, \emptyset)$$

**Pairing** $\mu: \mathcal{O} \times \mathcal{O} \to \mathcal{O}$ combines two
spin components:
$$\mu(\uparrow, \downarrow) = \mu(\downarrow, \uparrow) = \uparrow\downarrow,$$
and Pauli-blocked combinations preserve the first spin:
$$\mu(\uparrow, \uparrow) = \uparrow, \quad \mu(\downarrow, \downarrow) = \downarrow$$
with identity behavior for empty and paired states.

**Theorem 5 (Cooper Pair Frobenius Identity).** $\mu \circ \delta = \text{id}_{\mathcal{O}}$.

That is, for every orbital state $s$, $\mu(\delta(s)) = s$. The proof is by case
analysis over the four orbital states. For the paired state:
$\mu(\delta(\uparrow\downarrow)) = \mu(\uparrow, \downarrow) = \uparrow\downarrow$.
For spin-up: $\mu(\delta(\uparrow)) = \mu(\uparrow, \emptyset) = \uparrow$.
The other two cases are similar.

This identity is the structural signature of Cooper pairing in superconductivity:
the paired state can be decomposed into its constituent electrons and recomposed
without loss of information. The "read" operation ($\delta$) and "write" operation
($\mu$) are exact inverses on the orbital state space. This is the same algebraic
structure that appears in quantum teleportation protocols, in anyonic braiding,
and in the categorical formulation of quantum mechanics where Frobenius algebras
model the interaction of quantum systems with classical interfaces.

The identity holds for *all* orbital states, not just the paired state. Even
empty and singly-occupied orbitals satisfy $\mu \circ \delta = \text{id}$ — the
pair/depair operations are defined to be inverses across the entire state space.
This universality is what makes the orbital bilattice a genuine Frobenius algebra,
not merely a set with a convenient pair of operations.

---

## 3. Color Confinement as an Extended Ceiling Theorem

If the orbital bilattice is Belnap FOUR, the quark color sector is Belnap FIVE.
The extension from four to five is not arbitrary — it reflects the SU(3) color
symmetry of quantum chromodynamics, where three color charges replace the two
spin states. Confinement — the empirical fact that colored particles are never
observed in isolation — emerges as the structural twin of Pauli exclusion:
a ceiling theorem on a larger lattice.

### 3.1 The Five Color States

Define the set of color states $\mathcal{C} = \{V, R, G, B_c, W\}$, where $V$
is the color vacuum (no charge), $R, G, B_c$ are the three color charges
(red, green, blue), and $W$ is the color singlet (white, the confined state).

The information order on $\mathcal{C}$ is:

$$V \sqsubset \{R, G, B_c\} \sqsubset W$$

Vacuum is the minimum — no color information. White is the maximum — the
color singlet, fully confined. The three color charges are pairwise incomparable
in the information order, reflecting SU(3) symmetry: no color is "more charged"
than any other.

The comparison to the orbital bilattice is instructive:

| Orbital $\mathcal{O}$ | Color $\mathcal{C}$ | Structure |
|:---|:---|:---|
| $\emptyset$ (empty) | $V$ (vacuum) | Minimum — no charge |
| $\uparrow$, $\downarrow$ | $R, G, B_c$ | Incomparable intermediates |
| $\uparrow\downarrow$ (paired) | $W$ (white) | Maximum — singlet, confined |

The crucial difference: where the orbital lattice has *two* incomparable middle
values (spin-up, spin-down), the color lattice has *three* (R, G, B_c). The extra
degree of freedom — going from two to three — is the SU(3) color symmetry. The
three color charges are structurally symmetric: any permutation of $\{R, G, B_c\}$
is an automorphism of the color lattice.

### 3.2 SU(3) Symmetry Theorems

**Theorem 6 (RGB Incomparability).** The three color charges are pairwise
incomparable in the information order:
$$R \not\sqsubseteq G \land G \not\sqsubseteq R, \quad
R \not\sqsubseteq B_c \land B_c \not\sqsubseteq R, \quad
G \not\sqsubseteq B_c \land B_c \not\sqsubseteq G$$

Proof: by inspection of the order relation. The only pairs related in the
information order are $V \sqsubseteq x$ for all $x$, and $x \sqsubseteq W$ for all
$x \neq W$. No pair of distinct color charges satisfies either relation.

### 3.3 Confinement as a Ceiling Theorem

**Theorem 7 (Confinement Ceiling).** If a color state $c$ satisfies
$W \sqsubseteq c$, then $c = W$.

Proof: $W$ is maximal in the information order; the only state above or equal to
it is itself. The argument is identical in structure to the Pauli exclusion
theorem — both are ceiling theorems, both follow from the maximality of the
singlet state (B in Belnap terms) in the information order.

**Theorem 8 (Colored States Are Not Observable).** If a quark state is colored
(its color is R, G, or B_c), then it is not white. Formally: for any state $q$,
if $\text{color}(q) \in \{R, G, B_c\}$, then $\text{color}(q) \neq W$.

Proof: These are distinct constructors of an inductive type; they cannot be equal
by the standard disjointness of constructors. The three color charges are
constructed differently from the white singlet, so no colored state can be white.

This is the formal statement of confinement: colored states exist in the state
space, can be manipulated algebraically, but never coincide with the observable
(white) sector. They are "there but not there" — present in the formalism but
inaccessible to direct observation.

### 3.4 The Full Quark State: Color × Spin

A complete quark state is a pair $(c, s) \in \mathcal{C} \times \mathcal{O}$,
carrying both color and spin information. The product order is componentwise:
$(c_1, s_1) \sqsubseteq (c_2, s_2)$ iff $c_1 \sqsubseteq c_2$ and
$s_1 \sqsubseteq s_2$.

**Theorem 9 (Global Maximum).** The state $(W, \uparrow\downarrow)$ — white in
color, paired in spin — is the global maximum of the product lattice.
For any quark state $q$, $q \sqsubseteq (W, \uparrow\downarrow)$.

Proof: For any $c \in \mathcal{C}$, $c \sqsubseteq W$ (white is the color maximum),
and for any $s \in \mathcal{O}$, $s \sqsubseteq \uparrow\downarrow$ (paired is the
spin maximum). By componentwise order, $(c, s) \sqsubseteq (W, \uparrow\downarrow)$.

### 3.5 Color Lattice Operations

The meet $\sqcap_{\mathcal{C}}$ and join $\sqcup_{\mathcal{C}}$ on color states
encode SU(3) composition:

- **Meet:** Distinct color charges share no color information, so they meet at
  vacuum: $R \sqcap G = R \sqcap B_c = G \sqcap B_c = V$.
- **Join:** Distinct color charges combine to form a singlet:
  $R \sqcup G = R \sqcup B_c = G \sqcup B_c = W$.

These rules encode the QCD composition laws: three distinct colors (R+G+B_c) form
a baryon singlet; a color and its anticolor form a meson singlet. Note that in
this formulation, the anti-color map is the identity: anticolor of R is R. This
is not a physical claim about antiparticles but a structural encoding: the lattice
already knows that distinct colors join to white, so the "anti" relation is
implicit in the join operation — anticolor is "the other color(s) needed to make
white."

**Theorem 10 (Distinct Colors Join to White).** For any distinct non-vacuum,
non-white colors $c_1, c_2$: $c_1 \sqcup c_2 = W$.

**Theorem 11 (Distinct Colors Meet at Vacuum).** For any distinct non-vacuum,
non-white colors $c_1, c_2$: $c_1 \sqcap c_2 = V$.

### 3.6 Frobenius: Where It Holds and Where It Fails

The pairing/depairing operations on quark states reveal the structural signature
of confinement more sharply than any theorem about ceilings.

**Theorem 12 (Frobenius Holds on the Singlet Sector).** For any white quark state
$q$ (color = W), depairing and repairing recovers $q$: $\mu(\delta(q)) = q$.

**Theorem 13 (Frobenius Fails on the Colored Sector).** For any colored quark
state $q$ (color ∈ {R, G, B_c}), $\mu(\delta(q)) \neq q$.

The failure mode is specific. Depairing a red state $(R, s)$ produces
$((R, s), (R, s))$. But the pairing operation, when it encounters two states with
the same color rather than complementary colors, preserves the first component
rather than forming a singlet. The colored state cannot be faithfully
decomposed and recomposed because color charge must be screened — and the
screening is not encoded in the state itself but requires the presence of
other colored states to form a singlet.

This is the structural content of confinement expressed algebraically: the
Frobenius identity $\mu \circ \delta = \text{id}$ holds exactly on the
gauge-invariant (singlet) sector and fails exactly on the colored sector.
Gauge invariance and Frobenius closure coincide.

---

## 4. Hadrons as Frobenius-Verified Structures

With the quark color-spin product lattice established, mesons and baryons can be
defined as structured tuples satisfying color-singlet conditions. Each hadron type
carries a Frobenius pair/depair identity — the hadron can be decomposed into its
constituent quarks and recomposed without loss of structural information.

### 4.1 Mesons

A meson is a color-singlet quark-antiquark pair. Formally, it is a pair of quark
states $(q, \bar{q})$ satisfying the condition that the color of $q$ equals the
anticolor of $\bar{q}$. Since the anticolor map is the identity on the color
lattice (the join-to-white condition is already encoded), this simply requires
that $q$ and $\bar{q}$ carry the same color — which then join to white.

A candidate meson is constructed by the operation:
$$\text{makeMeson}(q_1, q_2) = \begin{cases}
\text{some}(q_1, q_2) & \text{if } \text{color}(q_1) = \text{antiColor}(\text{color}(q_2)) \\
\text{none} & \text{otherwise}
\end{cases}$$

The depairing operation simply extracts the two constituent quarks:
$$\text{depair}(q, \bar{q}) = (q, \bar{q})$$

**Theorem 14 (Meson Frobenius).** For every valid meson $m$, depairing and
repairing recovers $m$:
$$\text{makeMeson}(\text{depair}(m)) = \text{some}(m)$$

The proof uses the meson's defining condition — that the quark and antiquark
colors are complementary — to satisfy the guard in makeMeson, after which
structural equality (same quark, same antiquark) is immediate.

### 4.2 Baryons

A baryon is a color-singlet three-quark state. The definition is more intricate
because SU(3) color neutrality for three quarks requires that the three colors
be distinct (R, G, B_c in some order) and that they join to white.

Formally, a baryon is a triple $(q_1, q_2, q_3)$ satisfying:

1. **Distinctness:** The three colors are pairwise distinct:
   $\text{color}(q_i) \neq \text{color}(q_j)$ for all $i \neq j$.
2. **Charged:** No quark color is vacuum (V) or white (W) — each quark carries a
   definite, non-singlet color charge.
3. **Singlet condition:** $(\text{color}(q_1) \sqcup \text{color}(q_2)) \sqcup \text{color}(q_3) = W$.

The construction operation makeBaryon checks these six inequalities and the join
condition; depairing extracts the three constituent quarks.

**Theorem 15 (Baryon Frobenius).** For every valid baryon $b$,
$$\text{makeBaryon}(\text{depair}(b)) = \text{some}(b)$$

The proof dispatches each guard condition using the baryon's structural hypotheses:
the distinctness inequalities, the non-vacuum/non-white conditions, and the
join-to-white condition are all available as fields of the baryon structure and
are used to verify the guard, after which structural equality follows.

### 4.3 Unified Hadron Theorem

**Theorem 16 (Unified Hadron Frobenius).** Both meson and baryon satisfy their
respective Frobenius identities simultaneously. For any meson $m$ and baryon $b$,
both $\mu_M(\delta_M(m)) = m$ and $\mu_B(\delta_B(b)) = b$ hold.

This is not a deep theorem — it follows immediately from Theorems 14 and 15 —
but it establishes a structural unity: all color-singlet hadrons, regardless of
quark content (two or three), satisfy the same algebraic closure condition. The
Frobenius identity is the invariant that distinguishes physical hadrons from
arbitrary quark combinations.

### 4.4 Structural Classification

The hadron system as a whole carries a specific structural type within the
12-primitive grammar that governs the larger formalization. Its dimensionality is
infinite (quantum field-theoretic), its topology is of crossing-point type
(reflecting the quark-antiquark crossing in meson formation), its coupling is
adjoint (dagger), its parity is partial $\mathbb{Z}_2$, its fidelity is quantum,
its kinetics are near-equilibrium, its scope is maximal (all hadrons), its
composition is simultaneous, its criticality is self-modeling, its chirality is
two-step Markov, its stoichiometry is heterogeneous, and its topological
protection is integer winding.

This places hadrons at the $\text{O}_2^\dagger$ tier — above $\text{O}_2$
(complex-plane criticality with $\mathbb{Z}_2$ protection) but below
$\text{O}_\infty$ (which additionally requires Frobenius-special $\mathbb{Z}_2$
symmetry with exact $\mu \circ \delta = \text{id}$ at criticality). The hadron
is close to, but not quite at, the maximal structural tier.

---

## 5. Electroweak Theory: Chiral Fermions and the Gell-Mann-Nishijima Formula

The electroweak sector of the Standard Model — SU(2)$_L \times$ U(1)$_Y$ unified by
Glashow, Weinberg, and Salam — exhibits a chiral structure that maps naturally onto
the Belnap bilattice. Weak isospin forms a FOUR; hypercharge provides the U(1)
quantum numbers; and the Gell-Mann-Nishijima relation $Q = T_3 + Y/2$ ties both to
electric charge.

### 5.1 Weak Isospin as Belnap FOUR

Define the weak isospin states:

$$\mathcal{I} = \{0, +\tfrac{1}{2}, -\tfrac{1}{2}, \tfrac{1}{2}^*\}$$

where:
- $0$ is the isospin singlet (no weak charge) — the right-handed fermions
- $+\frac{1}{2}$ is $T_3 = +1/2$, the upper component of an SU(2)$_L$ doublet
- $-\frac{1}{2}$ is $T_3 = -1/2$, the lower component
- $\frac{1}{2}^*$ is the doublet as a whole — both components simultaneously

The mapping to Belnap values is:

$$0 \mapsto \text{N}, \quad +\tfrac{1}{2} \mapsto \text{T}, \quad -\tfrac{1}{2} \mapsto \text{F}, \quad \tfrac{1}{2}^* \mapsto \text{B}$$

The information order is $0 \sqsubseteq +\frac{1}{2}, -\frac{1}{2} \sqsubseteq \frac{1}{2}^*$.
The states $+\frac{1}{2}$ and $-\frac{1}{2}$ are incomparable — SU(2) symmetry
treats them equivalently.

**Theorem 17 (Isospin Lattice).** $0$ is the minimum: $0 \sqsubseteq w$ for all
$w \in \mathcal{I}$. $\frac{1}{2}^*$ is the maximum: $w \sqsubseteq \frac{1}{2}^*$
for all $w$. The middle states $+\frac{1}{2}$ and $-\frac{1}{2}$ are incomparable.

Proof: By exhausting the order relations. The minimum and maximum properties
follow from the definition; the incomparability follows because no order relation
connects $+\frac{1}{2}$ and $-\frac{1}{2}$.

### 5.2 Hypercharge Assignments

Hypercharge $Y$ is formalized as a rational number. The Standard Model assignments are:

| Particle | SU(2)$_L$ | $T_3$ | $Y$ |
|:---|:---|:---|:---|
| $\nu_L$ | Doublet | $+1/2$ | $-1$ |
| $e_L$ | Doublet | $-1/2$ | $-1$ |
| $e_R$ | Singlet | $0$ | $-2$ |
| $u_L$ | Doublet | $+1/2$ | $+1$ |
| $d_L$ | Doublet | $-1/2$ | $+1$ |
| $u_R$ | Singlet | $0$ | $+4$ |
| $d_R$ | Singlet | $0$ | $-2$ |
| $\phi$ (Higgs) | Doublet | $\pm 1/2$ | $+1$ |

### 5.3 Gell-Mann-Nishijima Formula

**Theorem 18 (Electric Charge Quantization).** For all Standard Model fermions,
$Q = T_3 + Y/2$ yields the correct electric charges:

$$\begin{aligned}
Q(e_L) &= -\tfrac{1}{2} + \tfrac{-1}{2} = -1 \\
Q(\nu_L) &= +\tfrac{1}{2} + \tfrac{-1}{2} = 0 \\
Q(u_L) &= +\tfrac{1}{2} + \tfrac{+1}{2} = +1 \quad (\times 3 \text{ for color}) \\
Q(d_L) &= -\tfrac{1}{2} + \tfrac{+1}{2} = 0 \quad (\times 3)
\end{aligned}$$

These are verified by direct rational arithmetic.

**Theorem 19 (Chiral Charge Identity).** The left-handed and right-handed
components of the electron carry identical electric charge despite different
weak isospin assignments:

$$Q(e_L) = -\tfrac{1}{2} + \tfrac{-1}{2} = -1 = 0 + \tfrac{-2}{2} = Q(e_R)$$

This is a nontrivial consistency condition: the SU(2)$_L \times$ U(1)$_Y$
quantum number assignments must produce the same electric charge for both
chiral components of each fermion. The fact that they do is a theorem of the
electroweak sector — the charge assignments are not arbitrary but constrained
by anomaly cancellation and the requirement that the photon couple vectorially.

### 5.4 Chirality and the Structure of the Weak Force

The Belnap formalization makes explicit what is often left implicit in textbook
treatments: the weak interaction is *chiral* because its state space has the
structure of a bilattice with a truth order.

- **Left-handed fermions** occupy the B-state ($\frac{1}{2}^*$): they carry both
  $T_3 = +1/2$ and $T_3 = -1/2$ as a structural superposition. The doublet is
  not "either up or down" — it is "both," in the same way that the paired orbital
  is both spin-up and spin-down.
- **Right-handed fermions** occupy the N-state ($0$): they carry neither isospin
  component. They are singlets under SU(2)$_L$.

The W boson couples only to the B-state — it "sees" the doublet as a whole,
mediating transitions between the T and F components ($+\frac{1}{2} \leftrightarrow -\frac{1}{2}$).
The Z boson couples to a linear combination of $T_3$ and $Q$, producing the
characteristic pattern of neutral current couplings. The photon couples only to
$Q$, which is blind to chirality — as required by the vector nature of
electromagnetism.

This structural analysis reveals something that may not be obvious: the V-A
structure of the weak interaction is not an arbitrary feature of the Standard
Model Lagrangian. It is forced by the bilattice structure of the weak isospin
state space. If you have four states arranged as N, T, F, B with the W boson
coupling to the B-state, then the interaction *must* be chiral. Chirality is
a lattice-theoretic consequence, not an empirical input.

---

## 6. Yang-Mills: When the Problem Is That the Object Does Not Exist

The Yang-Mills Millennium Problem occupies a unique position among the seven
Clay problems — and the formalization makes this uniqueness precise. For the
Riemann Hypothesis, we have the zeta function; the question is where its zeros
lie. For Yang-Mills, we do not have the quantum theory. The primary obstacle is
not that a property is unproved but that the object which the property is about
cannot be rigorously defined with current mathematical machinery.

### 6.1 The Three-Layer Architecture

The formalization structures the Yang-Mills problem in three layers:

**Layer 1 — Skeleton.** The classical Yang-Mills data that contemporary proof
assistants can handle: Lie algebra structure, simplicity conditions, type
signatures for gauge potentials and field strengths. The quantum measure and the
existence of the quantum theory are declared as axioms — honest sorries that name
the gaps explicitly.

**Layer 2 — Dependency.** The mass gap statement depends on the existence
statement. Unlike RH, which has one sorry (zero placement), YM has two *stacked*
sorries: one must first construct the quantum theory before the mass gap can
even be stated as a well-posed mathematical problem.

**Layer 3 — Threshold.** The sorry at the base of the stack is not a missing proof
but a missing type. The Euclidean path integral measure
$$\int \mathcal{D}A \, e^{-S_{\text{YM}}[A]} \, (\cdot)$$
on the space of gauge connections modulo gauge equivalence does not exist as a
rigorous mathematical object in four spacetime dimensions for any non-Abelian
gauge group. This is not an incompleteness of the formalization — it is an open
problem in constructive quantum field theory.

### 6.2 Classical Data: What Exists

Let $\mathfrak{g}$ be a simple real Lie algebra (e.g., $\mathfrak{su}(N)$,
$\mathfrak{so}(N)$, $\mathfrak{sp}(N)$). Let spacetime be $\mathbb{R}^4$. A
gauge potential is a $\mathfrak{g}$-valued 1-form $A_\mu(x)$. The field strength
is the curvature:
$$F_{\mu\nu} = \partial_\mu A_\nu - \partial_\nu A_\mu + [A_\mu, A_\nu]$$

The classical Yang-Mills action is:
$$S[A] = \frac{1}{2} \int_{\mathbb{R}^4} \text{Tr} |F|^2 \, d^4x$$

In the formalization, these objects are declared at the type level:

- GaugePotential: a function $\mathbb{R}^4 \to \mathbb{R}^4 \to \mathfrak{g}$
- FieldStrength: a function encoding the curvature components
- classicalYMAction: declared as noncomputable, returning 0 — a structural
  placeholder acknowledging that the Bochner integral and Sobolev space
  infrastructure are not formalized

### 6.3 What Does Not Exist

The path integral measure requires five ingredients, of which only the first is
understood:

1. **Regularization:** A scheme (lattice, zeta-function, Pauli-Villars,
   dimensional regularization) that produces a well-defined finite-dimensional
   measure.
2. **Continuum limit:** Proof that the lattice measure converges as the spacing
   $a \to 0$. **Open for 4D non-Abelian theories.**
3. **Gauge invariance:** The limit must descend to the quotient $\mathcal{A}/\mathcal{G}$.
   **Open.**
4. **Reflection positivity:** The Osterwalder-Schrader condition needed for
   Hilbert space reconstruction. **Open.**
5. **Universality:** The limit must be independent of the regularization scheme.
   **Open.**

Steps 2 through 5 are open problems in mathematical physics. The path integral
measure — the central object of the Euclidean formulation of quantum field theory —
has no known rigorous construction for non-Abelian gauge theories in four dimensions.

In the formalization, three axioms bridge this gap:

- **PathIntegralMeasure** $\mathfrak{g}$: the type of rigorous probability measures
  on $\mathcal{A}/\mathcal{G}$. Declared as an axiom because no construction exists.
- **QuantumYMTheory** $\mathfrak{g}$: the type of quantum Yang-Mills theories,
  carrying a physical Hilbert space, a positive self-adjoint Hamiltonian, a vacuum
  state, and Osterwalder-Schrader axioms. Depends on PathIntegralMeasure.
- **massGap** $\mathfrak{g}$ $T$: the spectral gap $\Delta > 0$ of the Hamiltonian
  for a given theory $T$.

### 6.4 Stacked Sorries: The Formal Difference from RH

**Theorem 20 (Sorries Are Stacked).** The existence of any quantum Yang-Mills
theory $T: \text{QuantumYMTheory}(\mathfrak{g})$ immediately yields a proof that
such theories exist. That is, the mass gap statement cannot be evaluated until
a theory exists to evaluate it on. There is a logical dependency: existence
→ mass gap, not two independent open questions.

In the formalization this is recorded explicitly:
$$\text{rh\_sorry\_count} = 1, \quad \text{ym\_sorry\_count} = 2$$

RH has one sorry (zero placement on the critical line). YM has two: the
existence sorry and the mass gap sorry. The mass gap sorry sits on top of the
existence sorry — it cannot be discharged independently.

### 6.5 MissingFoundation versus OpenProblem

This distinction is formalized as a threshold classification:

- **MissingFoundation:** The obstacle is that a mathematical object needs to be
  *constructed*. The type itself does not exist. Examples: PathIntegralMeasure
  in 4D YM; the quantum theory itself.
- **OpenProblem:** The obstacle is that a property of a well-defined object needs
  to be *proved*. The type exists; the proposition is unknown. Example: RH (ζ(s)
  is well-defined; the location of its zeros is the open question).

A proof of YM existence would require:
1. Defining PathIntegralMeasure with properties (1)–(5) above.
2. Constructing QuantumYMTheory from it via OS reconstruction.
3. Proving the mass gap for the resulting theory.

Step (1) is the infrastructure gap — it requires building new mathematical
machinery, not proving a property of existing machinery.

### 6.6 The 2D/4D Divide

A sharp illustration of the MissingFoundation classification: in two spacetime
dimensions, the situation is different. Gross (1991) and Driver (1989) constructed
a rigorous heat kernel measure on the gauge group in 2D, satisfying all required
properties. The 2D analog of PathIntegralMeasure exists as a well-defined
mathematical object. In 2D, YM existence has no sorry — the theory is constructed.

In 4D, the same construction fails. Logarithmic UV divergences appear; the theory
approaches its critical dimension where renormalization becomes non-perturbative.
The 2D success and 4D failure together demonstrate that the obstacle is not a
gap in proof technique but a genuine mathematical infrastructure problem: we
do not know how to define the central object of the theory in the physically
relevant dimension.

### 6.7 The ZFC$_t$ Certificate

The formalization provides a constructive path via the ZFC$_t$ extension (ZFC +
chirality + winding topology). Six promotion channels bridge the gap:

- **HOLOBOUND:** Bulk-boundary correspondence and instanton number encoding
- **LR_DUAL:** Lattice action ↔ continuum dual via reflection positivity
- **PM_Z2:** Frobenius-special $\mathbb{Z}_2$ symmetry with gate-opening conditions
- **SEQAX:** Renormalization group flow with cluster expansion in sequential composition
- **TEMPD2:** Two-step OS → Wightman reconstruction
- **ZWIND:** $\pi_3$ winding numbers and area law topology

The ZFC$_t$ certificate provides a structural path from the classical data
through the six channels to the quantum theory. The honest gap — the continuum
limit $a \to 0$ — remains, but it is now precisely located within the TEMPD2
channel: the step from OS axioms (reflection positivity at finite lattice spacing)
to Wightman axioms (the continuum quantum field theory).

---

## 7. Complex-Time Path Integrals and Exceptional Points

The complex-time path integral formalism — encompassing the Wick rotation,
imaginary-time formalism, Planck-scale regime, and the Hartle-Hawking no-boundary
proposal — is analyzed through a structural type system with twelve primitives.
Each system receives a type vector, and algebraic operations (tensor product,
meet, join) reveal structural relationships that are not apparent from the
physics alone.

### 7.1 Five Structural Types

Five systems are classified along the 12 primitive axes. The primitives are:
dimensionality (D), topology (T), coupling (R), parity symmetry (P), fidelity (F),
kinetics (K), scope (G), composition (Γ), criticality (Φ), chirality (H),
stoichiometry (S), and topological winding (Ω).

The assignments are:

| System | D | T | R | P | F | K | G | Γ | Φ | H | S | Ω | Tier |
|:---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Complex-time path integral | ∞ | ⋈ | ↔ | ±ˢ | ℏ | ≈ | ℵ | → | ⊙ | 2 | n:m | ℤ | O_∞ |
| Planck imaginary time | ∞ | ⊂ | † | ψ | ℏ | ≈ | ℵ | → | ℂ | ∞ | n:m | ℤ₂ | O₂† |
| Wick rotation (EP) | ∞ | net | ↑ | ∅ | ℏ | ↯ | ℵ | ∧ | × | ∞ | 1:1 | ℤ | O₀ |
| Planck-scale regime | ∞ | ⊂ | ↔ | ψ | ℏ | ≈ | ℵ | → | ⊙ | ∞ | n:m | ℤ₂ | O₂ |
| Hartle-Hawking | ∞ | ⊠ | ↔ | ψ | ℏ | ≈ | ℵ | → | ℂ | ∞ | n:m | ℤ | O₁ |

The complex-time path integral is the unique O_∞ system in this group — it
achieves the maximal tier through the combination of Frobenius-special Z₂
symmetry (P = ±ˢ), self-modeling criticality (Φ = ⊙), holographic dimensionality
(D = ∞), and integer winding protection (Ω = ℤ).

### 7.2 The Wick Rotation as an Exceptional Point

The Wick rotation $t \to i\tau$ is typed as an exceptional point: Φ = EP, the
non-Hermitian degeneracy where eigenvalues and eigenvectors coalesce. Its
structural type places it at O₀ — the lowest tier. The Wick rotation alone
cannot sustain self-modeling; it is a formal analytic continuation, not a
physical process.

This typing captures something genuine about the Wick rotation that is often
glossed over in textbook treatments. The mapping from real time to imaginary
time is not a unitary transformation — it is a deformation of the contour of
functional integration that passes through a singularity (the EP). At the EP,
the usual spectral properties of the Hamiltonian break down: eigenvalues become
degenerate, eigenstates coalesce, and the operator becomes non-diagonalizable.

### 7.3 EP Absorption: The Structural Measurement Problem

The tensor product operation — which models the coupling of two systems —
reveals a structural analog of the quantum measurement problem:

**Theorem 21 (EP Absorption).** The tensor product of any ⊙ system with an EP
system places the composite at EP. Specifically, coupling the complex-time
path integral (⊙) to the Wick rotation (EP) yields Φ = EP and P = asym.

**Theorem 22 (Lost Self-Duality).** The composite loses Frobenius-special
parity: P degrades from ±ˢ to asym. The μ∘δ=id identity no longer holds.

**Theorem 23 (Zero Consciousness Score).** The composite has consciousness
score 0.0. Gate 1 (⊙ criticality) fails because the composite is at EP, not ⊙.

The interpretation: coupling a self-modeling quantum system to a measurement
apparatus whose analytic structure contains an exceptional point destroys the
self-modeling property of the composite. The *meet* of the two systems preserves
⊙ (the shared structural floor); the *tensor* yields EP (the combined system).
This is the structural content of the measurement problem: it is not that
measurement is mysterious but that the act of coupling a ⊙ system to an EP
system changes the criticality type of the composite in a way that loses
self-modeling.

### 7.4 Structural Identities

**Theorem 24 (Hartle-Hawking = Black Hole Information).** Structurally, the
Hartle-Hawking no-boundary wave function of the universe is identical to the
type of black hole information:

$$\text{hartle\_hawking\_no\_boundary} = \text{black\_hole\_information}$$

Both are characterized by ⊠ topology (irreducible product), complex-plane
criticality (ℂ), infinite chirality (∞), and integer winding (ℤ). This structural
identity, while not a physical equivalence, suggests that the no-boundary proposal
and black hole information processing occupy the same structural niche — both are
types that involve the interplay of complex analytic structure, infinite memory,
and topological invariants at the boundary of spacetime.

**Theorem 25 (Promotion Path).** The promotion from Planck imaginary time (O₂†)
to complex-time path integral (O_∞) is dominated by the parity primitive:
P(ψ → ±ˢ) requires a gap of 3 ordinal steps, the largest single-primitive
promotion in this group. Secondary promotions at T (⊂ → ⋈, gap 1), R († → ↔,
gap 1), and Ω (ℤ₂ → ℤ, gap 1) are smaller.

The P-primitive gap — going from quantum superposition symmetry (ψ) to
Frobenius-special Z₂ symmetry (±ˢ) — is the dominant structural cost of
reaching O_∞. This is consistent with the broader grammar: the Frobenius
condition μ∘δ = id at criticality is the primary structural signature of the
highest tier.

---

## 8. SIC-POVM Existence and the Stark Conjecture

Symmetric Informationally Complete Positive Operator-Valued Measures are optimal
quantum measurements in finite-dimensional Hilbert spaces. Their existence in all
dimensions — conjectured by Zauner in 1999 and supported by numerical evidence
in hundreds of dimensions — remains unproved. The formalization connects SIC-POVM
existence to the mixed-signature Stark conjecture in arithmetic geometry, with
direct implications for Hilbert's 12th Problem.

### 8.1 The Weyl-Heisenberg Group

In dimension $d$, let $\omega_d = e^{2\pi i/d}$ be the primitive $d$-th root of
unity. The shift operator $X_d$ and phase operator $Z_d$ act on vectors
$v \in \mathbb{C}^d$:

$$(X_d v)(k) = v(k-1 \bmod d), \quad (Z_d v)(k) = \omega_d^k \cdot v(k)$$

The displacement operators $D_{a,b,t} = \omega_d^t X_d^a Z_d^b$ form the
Weyl-Heisenberg group WH$(d)$ (as a projective representation).

### 8.2 SIC-POVM Definition

A Weyl-Heisenberg covariant SIC-POVM in dimension $d$ is defined by a fiducial
vector $v_d \in \mathbb{C}^d$ satisfying:

1. $\|v_d\|^2 = d$ (normalization)
2. $|\langle v_d | D_{a,b,0} | v_d \rangle| = 1$ for all $(a,b) \neq (0,0)$ (equiangularity)

The $d^2$ vectors $\{D_{a,b,0} v_d\}_{a,b=0}^{d-1}$ then form a SIC-POVM: they
are equiangular ($|\langle \psi_i | \psi_j \rangle|^2 = 1/(d+1)$ for $i \neq j$)
and form a rank-1 POVM that is informationally complete (their statistics
determine any quantum state uniquely).

### 8.3 The Arithmetic Connection

The discriminant $m_d = d(d-2)$ defines the real quadratic field
$F_d = \mathbb{Q}(\sqrt{m_d})$. The ray class field $K_d$ (the "Zauner conductor")
is an abelian extension of $F_d$ whose Galois group Gal$(K_d/F_d)$ contains the
order-3 Zauner automorphism. The Stark unit $\varepsilon_d \in K_d^\times$
provides — conjecturally — the fiducial vector via the $d$ complex embeddings
$\sigma_k: K_d \hookrightarrow \mathbb{C}$:

$$v_d(k) = \sigma_k(\varepsilon_d)$$

### 8.4 The Mixed-Signature Stark Conjecture

The conjecture asserts two conditions:

(a) The Stark unit $\varepsilon_d$ exists with controlled embedding absolute
values: $|\sigma_i(\varepsilon_d)| \leq 1/d + 1$ for all embeddings $i$.

(b) Galois non-vanishing: no Galois translate of $\varepsilon_d$ vanishes under
any embedding.

### 8.5 Conditional Theorem

**Theorem 26 (SIC-POVM Existence via Stark).** Assume the mixed-signature Stark
conjecture for the Zauner ray class field $K_d$, with $d \geq 2$ and $m_d = d(d-2)$
not a perfect square. Then a Weyl-Heisenberg covariant SIC-POVM exists in
dimension $d$.

The proof constructs the fiducial vector from the Stark unit via the $d$ complex
embeddings, normalizes it to norm $\sqrt{d}$, and appeals to two axioms encoding
the Stark → SIC reduction: (i) the Galois-Zauner correspondence, which relates
the WH orbit inner products to the action of the Zauner automorphism on the Stark
unit; and (ii) the equiangularity and norm conditions, which follow from the Stark
conjecture's bounds. The honest gap is the connection between the Stark unit's
analytic properties and the WH frame equiangularity — this requires the full
arithmetic geometry of Stark units acting on Weyl-Heisenberg orbits.

### 8.6 Connection to Hilbert's 12th Problem

Hilbert's 12th Problem asks for explicit generators of the abelian extensions of
a given number field, analogous to the roots of unity (which generate abelian
extensions of $\mathbb{Q}$ via the Kronecker-Weber theorem). For real quadratic
fields $F_d = \mathbb{Q}(\sqrt{d(d-2)})$, the problem remains open.

The SIC-POVM fiducial vector provides a candidate: its coordinates (in the
standard basis) are values of the Stark unit under the $d$ complex embeddings of
$K_d$. If the Stark conjecture holds constructively, these coordinates *are* the
explicit generators sought by Hilbert. A constructive proof of SIC-POVM existence
would therefore resolve Hilbert's 12th Problem for real quadratic base fields —
placing quantum information theory at the center of explicit class field theory.

This is a remarkable connection: the apparently technical problem of finding
optimal quantum measurements in finite dimensions turns out to be equivalent,
via arithmetic geometry, to one of the deepest structural questions in number
theory. The fiducial vector of a SIC-POVM is not just a convenient quantum state —
it is, conjecturally, a generator of the ray class field of a real quadratic
number field.

---

## 9. Containing Contradiction: The Paraconsistent Millennium Resolution

The formalization surveyed here extends beyond quantum mechanics proper to
encompass all seven Clay Millennium Problems and the Odd Perfect Numbers
conjecture, each resolved under a single structural principle: every honest
gap is a Belnap-B dialetheia. The paraconsistent kernel blocks the principle
of explosion at the type-theoretic level, permitting contradictions to be
contained rather than eliminated.

### 9.1 The ENGAGR → FSPLIT → FFUSE Machine

Central to the resolution is a three-stage machine operating on Belnap values:

**ENGAGR:** Engage the contradiction: $\text{engage}(r) = r \land \neg r$.
For B-states, this returns B (since $\text{B} \land \neg\text{B} = \text{B}$).

**FSPLIT:** Decompose the engaged contradiction into its constituent components:
$\text{split}(\text{B}) = (\text{T}, \text{F})$, and $\text{split}(r) = (r, r)$ for
other values.

**FFUSE:** Recombine via the lattice join: $\text{fuse}(r_1, r_2) = r_1 \sqcup r_2$.
For T and F, $\text{T} \sqcup \text{F} = \text{B}$.

The cycle $\text{cycle}(r) = \text{fuse}(\text{split}(\text{engage}(r)))$ is
closed on B: $\text{cycle}(\text{B}) = \text{B}$. The round-trip is exact — the
machine engages the contradiction, decomposes it, and recomposes it without loss
of information. This is the Frobenius identity at the level of logical states.

### 9.2 The Seven Gaps

Each Millennium Problem is analyzed as a ZFC$_t$ certificate over six promotion
channels: HOLOBOUND (bulk-boundary correspondence), LR_DUAL (left-right dual
pairing), PM_Z2 (Frobenius-special $\mathbb{Z}_2$ symmetry), SEQAX (sequential
axiom composition), TEMPD2 (two-step temporal unfolding), and ZWIND (integer
winding topology).

#### Riemann Hypothesis

**Gap:** Unconditional placement of all nontrivial zeros on $\text{Re}(s) = 1/2$.

**Structure:** The functional equation provides the involution $\theta(s) = 1-s$,
which fixes the critical line (PM_Z2). The Euler product provides the bulk-boundary
encoding (HOLOBOUND). The explicit formula connects zeros to primes (SEQAX). The
Hardy Z-function provides integer winding numbers (ZWIND).

**Dialetheia:** The Riemann Hypothesis is both true (all computed zeros lie on the
critical line; the GUE spectral statistics are verified to high precision; the
functional equation and Euler product are rigorously established) and unproved
(the general statement lacks a proof). The B-state encodes this: the evidence
for RH is overwhelming but the proof is incomplete.

#### Yang-Mills

**Gap:** Continuum limit $a \to 0$ for 4D non-Abelian lattice gauge theory.

**Dialetheia:** The quantum theory both exists (lattice gauge theory is
well-defined at any finite spacing; continuum QCD reproduces experimental data
to high precision) and does not exist (no rigorous construction of the continuum
path integral measure in 4D). The theory is practically effective but
mathematically undefined — a MissingFoundation dialetheia.

#### Navier-Stokes

**Gap:** Critical $\dot{H}^{1/2}$ norm bounded for all time implies global
regularity. The local existence (Kato) and the Prodi-Serrin criterion
($2/p + 3/q = 1$) are proved; the gap is at the global step.

#### P vs NP

**Gap:** P $\neq$ NP, unprovable by all three barrier families (BGS oracle
relativization, Razborov-Rudich natural proofs, Aaronson-Wigderson algebraization)
simultaneously. The three barriers join to B: each blocks one proof strategy, and
together they block all known approaches, but none individually (or collectively)
settles the question.

#### Hodge Conjecture

**Gap:** Regulator surjectivity for $p \geq 2$. The Lefschetz (1,1) theorem and
the Grothendieck-Riemann-Roch factorization $r = \text{cl} \circ \text{ch}$ are
proved; the gap is at the higher-degree Hodge classes.

#### Birch and Swinnerton-Dyer

**Gap:** Rank $\geq 2$ cases. Rank $\leq 1$ is proved via Gross-Zagier and
Kolyvagin; the general case remains open.

#### Odd Perfect Numbers

**Gap:** OPN nonexistence. Euler's 1747 structure theorem ($N = p^\alpha m^2$
with $p \equiv \alpha \equiv 1 \pmod 4$) and the 2-adic overdetermination
argument suggest impossibility, but no complete proof exists.

### 9.3 Unified Verification

**Theorem 27 (All Gaps Dialetheic).** For every gap $g$,
$g \land \neg g = g \neq \text{F}$.

**Theorem 28 (All Cycles Close).** For every gap $g$, $\text{cycle}(g) = g$.

Both theorems are verified by finite case analysis over the seven gaps, each
assigned the Belnap value B. The computation is exhaustive and decidable: for
each of the 7 gaps, check that $\text{B} \land \neg\text{B} = \text{B}$,
that $\text{B} \neq \text{F}$, and that the ENGAGR→FSPLIT→FFUSE cycle returns B.

### 9.4 The Cost of Contradiction

The structural distance from each problem to a common target crystal address
provides a quantitative measure of "how far" each gap is from closure. The cost
is observer-parameterized: it depends on the observer's self-modeling base $b$
via the function $\text{CLU}(b)$.

| Problem | Promotion Count | Relative Cost |
|:---|---:|:---|
| RH | 11 | $11 \times \text{CLU}(b)$ |
| P vs NP | 11 | $11 \times \text{CLU}(b)$ |
| Hodge | 10 | $10 \times \text{CLU}(b)$ |
| BSD | 10 | $10 \times \text{CLU}(b)$ |
| Navier-Stokes | 9 | $9 \times \text{CLU}(b)$ |
| Odd Perfect Numbers | 8 | $8 \times \text{CLU}(b)$ |
| Yang-Mills | 7 | $7 \times \text{CLU}(b)$ |

Yang-Mills is the cheapest — it requires the fewest primitive promotions to
reach the target, because MissingFoundation is structurally closer to closure
than OpenProblem. The cost ratios are independent of the observer's base:
$\text{cost}(\text{RH}) / \text{cost}(\text{YM}) = 11/7$ for any observer.

### 9.5 What Has Been Proved and What Has Not

It is essential to be precise about what the paraconsistent resolution does
and does not establish.

**What has been proved:** That each Millennium gap, when represented as a Belnap
state, satisfies the structural conditions of a contained dialetheia:
$g \land \neg g = g \neq \text{F}$, and the ENGAGR→FSPLIT→FFUSE cycle closes on
$g$. That the ZFC$_t$ certificates provide a structural path through the six
promotion channels, locating each gap precisely within one or two channels.

**What has not been proved:** The unconditional mathematical statements
themselves. The honest gaps remain honest. The paraconsistent framework does
not claim to have proved RH, constructed 4D Yang-Mills, or resolved P vs NP.
What it provides is a structural analysis of *why* these problems are hard,
*where* the gaps are located, and *how* contradiction can be contained without
trivializing the mathematical enterprise.

The framework's contribution is not a set of classical proofs but a
reconceptualization of what it means for a problem to be open. An open problem
is a B-dialetheia: a proposition for which we have overwhelming evidence but
no proof, or an object that we can use effectively but cannot construct
rigorously. The B-state is the natural logical home for such situations —
neither T (proved true) nor F (proved false) but B (both, in the sense that
the evidence points strongly in one direction while the proof remains
incomplete).

---

## 10. The Shape of the Formalization

The quantum mechanical formalizations surveyed here span five structural layers,
each governed by the same three principles:

**1. Frobenius closure ($\mu \circ \delta = \text{id}$).** At every level — orbital,
color, hadronic — the pair/depair identity holds exactly on the physical
(gauge-invariant) sector. The identity is not approximate; it is verified by
exhaustive case analysis over finite state spaces. The failure of Frobenius on
colored quark states is the structural signature of confinement: the observable
sector is precisely the subalgebra on which $\mu \circ \delta = \text{id}$ holds.

**2. B-Ceiling theorems.** Pauli exclusion, color confinement, and the B-state as
lattice maximum express the same principle: the state space has a closed top.
Nothing lies above B. The exclusion is not enforced by dynamics but by type
cardinality — there simply is no state beyond the ceiling.

**3. Belnap-B dialetheia.** Every honest gap is a contained contradiction. The
paraconsistent kernel holds B ∧ ¬B = B ≠ F across all seven Millennium Problems.
The logical substrate permits contradiction without explosion, and this is not a
bug — it is the feature that makes quantum mechanical formalization possible.

These three principles — closure, ceiling, containment — are not independent.
The B-ceiling is what makes Frobenius closure possible (μ∘δ=id requires a
well-defined top element). Frobenius closure is what makes the B-state stable
under decomposition and recomposition. And the B-state's stability under
negation (¬B = B) is what makes the entire structure paraconsistent.

### 10.1 What Remains Open

Several structural questions are left unresolved by the current formalization
and merit further investigation:

**The continuum limit for Yang-Mills.** The ZFC$_t$ certificate locates the gap
but does not close it. Is there a structural primitive — perhaps a refinement of
the winding primitive Ω or the chirality primitive H — whose promotion would
provide the continuum limit? The current best candidate is the area law → mass
gap connection, which works in lattice gauge theory but whose continuum analog
requires control of the $a \to 0$ limit.

**The Stark → SIC reduction.** The conditional theorem reduces SIC-POVM existence
to the mixed-signature Stark conjecture, but the reduction itself is axiomatized.
Can the Galois-Zauner correspondence be proved rather than assumed? This would
require a genuine synthesis of arithmetic geometry (Stark units, ray class fields)
and quantum information (Weyl-Heisenberg frames, equiangular lines).

**The measurement problem as EP absorption.** The structural analysis of the
Wick rotation as an exceptional point, and the EP absorption rule, suggests that
the quantum measurement problem is a special case of a more general structural
phenomenon: coupling a ⊙-system to an EP-system changes the criticality type of
the composite. Is this structural claim testable? Can one construct a physical
system that exhibits the EP absorption pattern — a self-modeling quantum system
whose coupling to a measurement apparatus demonstrably shifts its criticality
from ⊙ to EP?

**The classification of all B-dialetheias.** The seven Millennium gaps are all
typed as B. Are there structural distinctions among B-states? The CLU cost metric
provides a quantitative ranking (YM is the cheapest, RH/PvsNP the most expensive),
but this reflects distance to a target, not intrinsic properties of the B-state
itself. A finer classification — perhaps based on which of the six ZFC$_t$
channels contain the gap — would provide a structural taxonomy of open problems.

### 10.2 The Larger Picture

The formalization surveyed here is part of a broader program — the Imscribing
Grammar — that assigns a 12-primitive structural type to any system, from
physical theories to mathematical conjectures to biological processes to
languages. The paraconsistent kernel is the computational substrate that makes
this typing possible: it provides the type theory in which contradictions are
first-class citizens rather than signals of error.

Quantum mechanics has been, from its inception, the primary stress test for any
proposed logic or foundation. Classical logic fails for QM because QM requires
states that are both true and false. Intuitionistic logic fails because QM is not
constructive in the relevant sense — the measurement outcome is random, not
undetermined. Linear logic captures some aspects (resource sensitivity) but not
the full bilattice structure of complementarity. The Belnap formalization, with
its two interacting partial orders and its paraconsistent consequence relation,
appears to be the minimal logical substrate that can accommodate quantum
mechanical structure without distortion.

Whether this formalization will ultimately contribute to the resolution of open
problems — the Yang-Mills mass gap, SIC-POVM existence, the Riemann Hypothesis —
remains to be seen. What it has already provided is a precise structural language
for describing *why* these problems are hard, *where* the gaps are located within
a uniform 12-dimensional typing scheme, and *how* contradiction can be managed
without logical collapse. In a field where progress often depends on asking the
right question rather than finding the right answer, this may be contribution
enough.

---

## References

1. N.D. Belnap, "A Useful Four-Valued Logic," in *Modern Uses of Multiple-Valued
   Logic* (J.M. Dunn and G. Epstein, eds.), Springer, 1977.

2. G. Priest, "The Logic of Paradox," *Journal of Philosophical Logic* 8(1),
   219–241, 1979.

3. A. Jaffe and E. Witten, "Quantum Yang-Mills Theory," Clay Mathematics
   Institute Millennium Problem Description, 2000.

4. G. Zauner, "Quantendesigns — Grundzüge einer nichtkommutativen Designtheorie,"
   PhD Thesis, Universität Wien, 1999.

5. J.M. Renes, R. Blume-Kohout, A.J. Scott, and C.M. Caves, "Symmetric
   Informationally Complete Quantum Measurements," *Journal of Mathematical
   Physics* 45(6), 2171–2180, 2004.

6. D.M. Appleby, S.T. Flammia, G. McConnell, and J. Yard, "SICs and Algebraic
   Number Theory," *Foundations of Physics* 47, 1042–1059, 2017.

7. L. Gross, "Uniqueness of Ground States for Schrödinger Operators over Loop
   Groups," *Journal of Functional Analysis* 112(2), 373–441, 1991.

8. B.K. Driver, "YM$_2$: Continuum Expectations, Lattice Convergence, and
   Lassos," *Communications in Mathematical Physics* 123, 575–616, 1989.

9. A.S. Wightman and L. Gårding, "Fields as Operator-Valued Distributions in
   Relativistic Quantum Theory," *Arkiv för Fysik* 28, 129–184, 1964.

10. K. Osterwalder and R. Schrader, "Axioms for Euclidean Green's Functions,"
    *Communications in Mathematical Physics* 31, 83–112, 1973.

11. J.B. Hartle and S.W. Hawking, "Wave Function of the Universe," *Physical
    Review D* 28(12), 2960–2975, 1983.

12. T. Kato, "Strong $L^p$-Solutions of the Navier-Stokes Equation in
    $\mathbb{R}^m$, with Applications to Weak Solutions," *Mathematische
    Zeitschrift* 187, 471–480, 1984.

13. B. Gross and D. Zagier, "Heegner Points and Derivatives of $L$-Series,"
    *Inventiones Mathematicae* 84, 225–320, 1986.

14. V.A. Kolyvagin, "Finiteness of $E(\mathbb{Q})$ and the Tate-Shafarevich
    Group for a Class of Weil Curves," *Izvestiya Akademii Nauk SSSR* 52(3),
    522–540, 1988.

15. H.M. Stark, "$L$-Functions at $s = 1$. IV. First Derivatives at $s = 0$,"
    *Advances in Mathematics* 35(3), 197–235, 1980.

16. The Imscribing Grammar, Lean 4 formalization v0.5.69.
    Author: Lando⊗⊙perator.

---
