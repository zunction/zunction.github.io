---
layout: post
title: Reading Casper CBC proofs - Part 4
date: 2021-06-10 11:59:00-0400
description: defining LightNode instance and completing the reading of Binary.v
comments: true
---

In this last part, we will be completing the reading of `Binary.v`.
Our previous reading ended with an inductive definition `protocol_state` which validates if a given `sigma : state` satisfies the requirements of a protocol state, followed by establishing some properties of the terms of `protocol_state sigma` for some given `sigma`.

Let's begin.

The first declaration is an `Instance` [`CBC_protocol_eq`](https://github.com/runtimeverification/casper-cbc-proofs/blob/master/CBC/Protocol.v#L27), a *class of consensus values with reflexive and transitive comparisons*.
The `CBC_protocol_eq` is a `Class` is defined in [`Protocol.v`](https://github.com/runtimeverification/casper-cbc-proofs/blob/master/CBC/Protocol.v) thus in the preamble of `Binary.v`, [`CBC.Protocol`](https://github.com/runtimeverification/casper-cbc-proofs/blob/master/CBC/Binary.v#L4) is imported for us to be able to call on it.

```coq
Instance LightNode_seteq : CBC_protocol_eq :=
   { (* >> *) consensus_values := C;
     (* >> *) about_consensus_values := about_C;
     validators := V;
     about_validators := about_V;
     weight := weight;
     t := t_full;
     suff_val := suff_val_full;
     state := state;
     about_state := about_state;
     state0 := state0;
     state_eq := state_eq;
     state_union := state_union;
     state_union_comm := state_union_comm;
     reach := reach;
     reach_refl := reach_refl;
     reach_trans := reach_trans;
     reach_union := reach_union;
     reach_morphism := reach_morphism;
     (* >> *) E := binEstimator;
     estimator_total := estimator_total;
     prot_state := protocol_state;
     about_state0 := protocol_state_nil;
     equivocation_weight := fault_weight_state;
     equivocation_weight_compat := equivocation_weight_compat;
     about_prot_state := about_prot_state;
   }.
```

**Slight digression.** The notion of `Class` and `Instance` in Coq is similar to the [concept of a class in Python and objects of a Python class is instantiated by a function notation](https://docs.python.org/3/tutorial/classes.html).
The equivalent functionality in Coq is called [*typeclasses*](https://coq.inria.fr/refman/addendum/type-classes.html).
An introductory tutorial of Coq's typeclasses can be found [here](https://softwarefoundations.cis.upenn.edu/draft/qc-current/Typeclasses.html) and [here](https://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf).
It bears some similarities to Coq's dependent record types; refer to stackoverflow discussion [here](https://stackoverflow.com/questions/29872260/coq-typeclasses-vs-dependent-records) which seems to suggest typeclasses are more suitable for defining mathematical objects.
My personal understanding is that by bundling dependent record types with canonical declarations which is better known as [*canonical structures*](https://hal.inria.fr/hal-00816703v1/document), they provide better utility than typeclasses due to the programmable type inferencing.

With the end of my digression, we move on to understand what this chunk of `LightNode_seteq` is all about.
What forms a class of consensus values with with reflexive and transitive comparisons?
The answer is found from the [`Class` declaration of `CBC_protocol_eq` defined in `Protocol.v`](https://github.com/runtimeverification/casper-cbc-proofs/blob/master/CBC/Protocol.v#L25).  

```coq
Class CBC_protocol_eq :=
   {
      (** Consensus values equipped with reflexive transitive comparison **)
      consensus_values : Type;
      about_consensus_values : StrictlyComparable consensus_values;
      (** Validators equipped with reflexive transitive comparison **)
      validators : Type;
      about_validators : StrictlyComparable validators;
      (** Weights are positive reals **)
      weight : validators -> {r | (r > 0)%R};
      (** Threshold is a non-negative real **)
      t : {r | (r >= 0)%R};
      suff_val : exists vs, NoDup vs /\ ((fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R) vs > (proj1_sig t))%R;
      (** States with equality and union **)
      state : Type;
      about_state : StrictlyComparable state;
      state0 : state;
      state_eq : state -> state -> Prop;
      state_union : state -> state -> state;
      state_union_comm : forall s1 s2, state_eq (state_union s1 s2) (state_union s2 s1);
      (** Reachability relation **)
      reach : state -> state -> Prop;
      reach_refl : forall s, reach s s;
      reach_trans : forall s1 s2 s3, reach s1 s2 -> reach s2 s3 -> reach s1 s3;
      reach_union : forall s1 s2, reach s1 (state_union s1 s2);
      reach_morphism : forall s1 s2 s3, reach s1 s2 -> state_eq s2 s3 -> reach s1 s3;
      (** Total estimator **)
      E : state -> consensus_values -> Prop;
      estimator_total : forall s, exists c, E s c;
      (** Protocol state definition as predicate **)
      prot_state : state -> Prop;
      about_state0 : prot_state state0;
      (** Equivocation weights from states **)
      equivocation_weight : state -> R;
      equivocation_weight_compat : forall s1 s2, (equivocation_weight s1 <= equivocation_weight (state_union s2 s1))%R;
      about_prot_state : forall s1 s2, prot_state s1 -> prot_state s2 ->
                                  (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R -> prot_state (state_union s1 s2);
   }.
```

Thus we will go through the methods of the `CBC_protocol_eq` class (the declarations of the class) and we will then see that the terms provided to the methods for `LightNode_seteq` are taken from the various definitions defined earlier in `Binary.v`.

First we need a few data types: consensus values `C`, validators `V` and protocol states `state`, and also verification of these data types satisfying the `StrictlyComparable` property in the form of the terms `about_C`, `about_V`, and `about_state`.
Next we introduce the relevant operators which are then used to establish properties for two of these three data types.

For validators, we require a `weight` function which assigns each validator to a positive weight value, a Byzantine fault tolerance threshold `t_full`, and `suff_val_full` which says that there exists a set of validators where the sum of their weights are above the fault tolerance threshold.

For states, an initial protocol state $$\sigma_0$$ needs to be provided, `state_eq` checks if two states are equal,  and `state_union` to create a new state from the union of two states.
A proof that union of states is commutative, is proved to `state_union_comm`.

The notion of reachability over states is defined by the `reach` operator.
This `reach` operator is required to be reflexive (`reach_refl`), transitive (`reach_trans`), reachable to its union (`reach_union`), and starting from a state, if it can reach another state, its equivalent states are also reachable (`reach_morphism`).

With states and consensus values, we can talk about estimating a consensus value given a state. 
An estimator `E` is needed and we require this estimator to be total (`estimator_total`), which means a consensus value can be estimated for any given state.

A protocol state is a list of messages satisfying some property, and the properties are verified using the provided `prot_state`.
Using `prot_state`, `about_state0` verifies that the given `state0` is a valid protocol state.

The remaining three methods are related to equivocating weights.
The function `equivocation_weight` calculates the weight of equivocating senders, and other two are the properties of `equivocation_weight` which we went through in [Part 3](https://zunction.github.io/blog/2021/reading-casper-cbc-proofs-p3/).

The remaining three lines in `Binary.v` are defined on `locked_on` and `not_locked_off`, which are defined in [`Consistency` section](https://github.com/runtimeverification/casper-cbc-proofs/blob/e32e74997d8fd53b44e8e87add22e9ee1de5d175/CBC/Protocol.v#L239) of `Protocol.v`.

```coq
Definition bivalent : pstate -> Prop :=
  fun (s : pstate) => not_locked_off zero s /\ not_locked_off one s.

Definition stuck : pstate -> Prop :=
  fun (s : pstate) => locked_off zero s /\ locked_off one s.

Lemma locked_on_off : forall s, locked_on one s -> locked_off zero s.
```
As the definitions are build on other functions which we have not seen in `Binary.v`, we will defer their discussion for the time being, and return to update when those definitions make sense to me.

#### Conclusions

It has been a fun experience reading `Binary.v`, complemented with the material in [CBC Casper family of consensus protocol](https://github.com/cbc-casper/cbc-casper-paper/blob/master/cbc-casper-paper-draft.pdf).
Reading their formalisation in Coq has also allowed me to better understand the content in the paper; the implementations in Coq has allowed me to identify the parts which I did not really understand and gain increased understanding of the definitions in finer detail which would not have been possible by simply just reading.
Midway reading, I realised that the chronological order of the files mean that `Protocol.v` is the starting file, and thus has lead to some definitions which are not defined in `Binary.v`.

My next reading will be on [`Protocol.v`](https://github.com/runtimeverification/casper-cbc-proofs/blob/master/CBC/Protocol.v) and please stay tuned!
