[Duality in Domain Theory](https://alyata.github.io/documents/duality_domain_theory.pdf) 
Complete Proof of Proposition 3.5.3 on page 42. With all the prerequisite lemmas. We prove that Algebraic DCPOs 
(directed complete partial orders) are Sober.

The classical reference in this area of Computer Science is [Domain Theory Handbook](https://achimjungbham.github.io/pub/papers/handy1.pdf).
I believe that though the proof itself cannot be found here, the statement can be (TODO provide this)

Link to zulip discussion:
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/.3E.20Algebraic.20complete.20partial.20order.20and.20domain.20theory/with/536359313

## super brief background:
DCPOs are a standard construction in Domain theory. They are sets with some structure where each element (hereafter referred to as **point**)
is some (possible approximate) semantics of some program. We impose an additional structure of the DCPO being Algebraic (please see reference).
Algebraic DCPO's have some nice properties and my formalisation is of one such property.

Now lets talk about topologies. We introduce a Topology strucutre on an Algebraic DCPO (Called the Scott Topology). The open sets of a topology are intended to describe
*properties extensionally*. You may foresee how we are moving towards an axiomatic Hoare triple style semantics. Since we start talking
about sets of **points** rather than points directly. That's like an assertion, and certain **points** (programs) satisfy that assertion.

In axiomatic semantics we define a programs semantics by giving a set of assertions. So a set of **open sets** (these are called Locale
**elements**, cause of course the open sets actaully have a richer structure of a Locale which is a lattice + some more stuff). The whole
point of this work is to be able to smoothly transition between this denotational semantics (where we think explicitly of each **point**)
and axiomatic semantics (where we think instead of a conjunction of assertion, ie, properties). We need to be able to move smoothly between
the two worlds and that's what the Adjoint Functors below achieve.

We talk about 2 Functors between the category of Topologies and category of Locales. A Topological space is sober when these functors
create an adjunction. This is the content of my proof.

Further the reference goes on to prove equivalence between the two categories.

## Structure
Prerequisiste Proposition 3.5.2 is proven in `TopologicalBasis.lean`. Main result: `scott_is_upset`
Proposition 3.5.3 proven in `SoberLemma.lean`. Main result: `scottIsSober`

## Warning
Though this proof is correct and sorry free. It is at point very unreadable and I myself am not happy with its current state.
I will clean it up when I find time.

