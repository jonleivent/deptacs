# deptacs
Dependent decide equality and other dependent tactics for Coq

A first attempt at a `dependent` version of the `decide equality` (and its sibling `compare`) tactic that can handle dependent types.  Written entirely in Ltac.  Tested in Coq version 8.5pl2.

Some features are:

- Users can choose whether or not to use axioms (`proof_irrelevance`, `eq_rect_eq`).
- Can interface with typeclasses.
- Can handle cases of "green slime": non-injective function-based type index arguments.
- Can handle both eqdec (`{a=b} + {a≠b}`) and eqem (`a=b ∨ a≠b`) goals.
- also: `sigT_generalize_eqs` tactic.

What it won't handle:

- Proofs that need decidable equality on universes.
- Proofs that need decidable equality on function types.
- Probably other things as well.

What it needs:

- More&better tests (examples.v).
- A built-into-Coq way to segregate type indexes from non-index parameters (to avoid the hacks in paramth.v).
- A better way to detect which of `Eqdep`|`Eqdep_dec`|`Eqdec_em` are `Require`d by the user, as well as whether proof-irrelevance is `Require`d.

