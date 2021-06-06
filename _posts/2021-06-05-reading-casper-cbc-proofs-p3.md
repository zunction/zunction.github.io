---
layout: post
title: Reading Casper CBC proofs - Part 3
date: 2021-06-05 11:59:00-0400
description: learning how consensus protocols are formally verified
comments: true
---

Welcome to Part 3 of my reading of Casper CBC proofs and thanks for following along in my journey.
This is a continuation of my earlier [Part 1](https://zunction.github.io/blog/2021/reading-casper-cbc-proofs-p1/) and [Part 2](https://zunction.github.io/blog/2021/reading-casper-cbc-proofs-p2/).

In this episode, we look at protocol state transitions in Definition 2.8 which says:

$$
\to : \Sigma \times \Sigma \to \{True, False\}
$$

$$
\sigma_1 \to \sigma_2 \Leftrightarrow \sigma_1 \subseteq \sigma_2
$$

In Coq this is represented by `reach s1 s2`, a `Prop` statement which is inhabited iff `s1` is a subset of `s2`.
One can interpret `reach s1 s2` as saying `s2` is reachable or can transit from `s1`.

```coq
Definition reach (s1 s2 : state) := incl s1 s2.
```

The next few lemmas prove some basic properties of `reach`, like reflexivity, transitivity, and in `reach_union` how a state can `reach` a union of itself with another state.
In `reach_morphism` it says that if $$\sigma_1 \to \sigma_2$$ and $$\sigma_2 = \sigma_3$$, then $$\sigma_1 \to \sigma_3$$.

```coq
Lemma reach_refl : forall s, reach s s.

Lemma reach_trans : forall s1 s2 s3, reach s1 s2 -> reach s2 s3 -> reach s1 s3.

Lemma reach_union : forall s1 s2, reach s1 (state_union s1 s2).

Lemma reach_morphism : forall s1 s2 s3, reach s1 s2 -> state_eq s2 s3 -> reach s1 s3.
```

Next is the definition of a binary estimator defined using inductive types.
The `binEstimator` is estimates a binary consensus value for a given state `sigma`.
Instead of a function which returns a binary consensus given a state, a binary consensus value is estimated by the construction of a `binEstimator` term.
For example for a given `sigma`, the term `estimator_one` can be constructed  if we can construct a proof which says the weight of the validators estimating `one` is greater than the weight of the validators estimating `zero`, i.e. `((score zero sigma) < (score one sigma))%R`.
In the last two constructors of `binEstimator`, it says that if we have proof that `((score zero sigma) = (score one sigma))%R`, then the terms `estimator_both_zero` and `estimator_both_one` can be constructed.

```coq
Inductive binEstimator : state -> C -> Prop :=
  | estimator_one : forall sigma, ((score zero sigma) < (score one sigma))%R 
    -> binEstimator sigma one
  | estimator_zero : forall sigma, ((score zero sigma) > (score one sigma))%R 
    -> binEstimator sigma zero
  | estimator_both_zero : forall sigma, ((score zero sigma) = (score one sigma))%R 
    -> binEstimator sigma zero
  | estimator_both_one : forall sigma, ((score zero sigma) = (score one sigma))%R 
    -> binEstimator sigma one.
```

The `estimator_total` lemma then says that for any state `s`, we are able to find a binary consensus value `c` such that we can construct a term of type `binEstimator s c`.

```coq
Lemma estimator_total : forall s : state, exists c : C, binEstimator s c.
```

**Upshot**: *a binary consensus value can be estimated for every state.*

Definition 2.9 describes what it means for two messages to be equivocating, with the $$\perp$$ operator to check if two messages are equivocating.

$$
\cdot \perp \cdot : M \times M \to \{True,False\}
$$

$$
m_1 \perp m_2 \Leftrightarrow \left(Sender(m_1) = Sender(m_2)\right) \wedge (m_1 \neq m_2) \wedge \left(m_{3-i} \notin Justification(m_i)\right)~i=1,2
$$

The equivocation definition says that two messages are equivocating when the messages are not the same but have the same sender and each message do not include each other in their justifications.
Using the `equivocating_messages` function, it returns `true` (`false`) if the messages `m1` and `m2` are (not) equivocating.

```coq
Definition equivocating_messages (msg1 msg2 : message) : bool :=
  match compare_eq_dec msg1 msg2 with
    | left _  => false
    | _ => match msg1, msg2 with (c1,v1,j1), (c2,v2,j2) =>
      match compare_eq_dec v1 v2 with
        | left _  => negb (inb compare_eq_dec (hash msg1) j2) 
                     && negb (inb compare_eq_dec (hash msg2) j1)
        | right _ => false
      end
             end
  end.
```

To check if a message equivocates with some message in a protocol state, `equivocating_message_state` is a boolean predicate which checks if a given message equivocates with some message in a state.
The [`existsb`](https://coq.inria.fr/library/Coq.Lists.List.html#existsb) helps to check if there is any message in a given `sigma : state` which satisfies `equivocating_messages`.

```coq
Definition equivocating_message_state (msg : message) : state -> bool :=
  existsb (equivocating_messages msg).
```

Here we have a property of protocol states which says if $$\sigma \subseteq \sigma '$$ then if there is a message $$m$$ which equivocates with some message in $$\sigma$$, $$m$$ will also equivocate with some message in $$\sigma '$$.

```coq
Lemma equivocating_message_state_incl : forall sigma sigma', incl sigma sigma' 
  -> forall msg, equivocating_message_state msg sigma = true 
    -> equivocating_message_state msg sigma' = true.
```

The set of equivocating senders (or validators) can be obtained using `equivocating_senders`; built from `equivocating_messages`.
Note that the 

```coq
Definition equivocating_senders (sigma : state) : set V :=
  set_map compare_eq_dec sender (filter (fun msg => equivocating_message_state msg sigma) sigma).
```
The use of [`set_map`](https://coq.inria.fr/library/Coq.Lists.ListSet.html#set_map) on `set V` ensures that any element of a set occurs at most once.
Thus the fact that the list of equivocating sends has no duplicates (`NoDup`) is proved in `equivocating_senders_nodup` below.

```coq
Lemma equivocating_senders_nodup : forall sigma, NoDup (equivocating_senders sigma).
```

It also follows that if $$\sigma \subseteq \sigma '$$ then the set of equivocating senders in $$\sigma$$ are contained in the set of equivocating senders in $$\sigma '$$, proved in `equivocating_senders_incl`.

```coq
Lemma equivocating_senders_incl : forall sigma sigma', incl sigma sigma' 
  -> incl (equivocating_senders sigma) (equivocating_senders sigma').
```

It is important to identify the equivocating senders as the aim is for the protocol to guarantee consensus safety by being tolerant up to $$t$$ Byzantine faults, measured by weight of equivocating senders (validators).
Thus if the threshold is $$t$$, then consensus safety can be guaranteed when the weights do not cross the threshold.
The function `fault_weight_state` measures the sum of weights of equivocating senders to determine if it lies within the threshold.

```coq
Definition fault_weight_state (sigma : state) : R := 
  sum_weights (equivocating_senders sigma).
```

The next two lemmas provide results which are used in the proofs of other results below.
The first lemma `sum_weights_in` verifies that if for validator `v` and a list of validators `vs` such that `v` is in the list `vs`, the sum of weights of `vs` is equal to the weight of  `v` added to the sum of weights of `vs` without `v`.
The next lemma `sum_weights_incl` says that for two list of validators `vs` and `vs'` such that each list has no duplicates (is a legitimate set) with `vs` contained in `vs'`, then the sum of weights of `vs` is less than or equal to the sum of weights of `vs'`.

```coq
Lemma sum_weights_in : forall v vs, NoDup vs -> In v vs 
  -> sum_weights vs = (weight v + sum_weights (set_remove compare_eq_dec v vs))%R.

Lemma sum_weights_incl : forall vs vs', NoDup vs -> NoDup vs' 
  -> incl vs vs' -> (sum_weights vs <= sum_weights vs')%R.
```

Extending the result of `sum_weights_incl` to weights of equivocating validators, we have the `fault_weight_state_incl` result below.

```coq
Lemma fault_weight_state_incl : forall sigma sigma', incl sigma sigma' ->
  (fault_weight_state sigma <= fault_weight_state sigma')%R.
```

Following which `fault_weight_max` says that the weights of equivocating senders will be at most the sum of the weights of all the senders in a given state.
It is easy to see that equality occurs when all senders are equivocating.

```coq
Lemma fault_weight_max : forall sigma,
  (fault_weight_state sigma <= sum_weights (set_map compare_eq_dec sender sigma))%R.
```

Lastly, the `equivocation_weight_compat` result which says that the weights of equivocating senders in a state $$\sigma_1$$ is less than or equal to the weights of equivocating senders in a state formed by the union of $$\sigma_1$$ and another state $$\sigma_2$$, can be easily derived from the result `fault_weight_state_incl`:

```coq  
Lemma equivocation_weight_compat : forall s1 s2, (fault_weight_state s1 <= fault_weight_state (state_union s2 s1))%R.
```

The definition below says that a term of for some `sigma` and `c`, a term of `binEstimator sigma c` is a valid estimate condition.
A term of `fault_tolerance_condition sigma` for some `sigma` is used to indicate that the weights of the equivocating senders is less than or equal to the threshold `t_full`.
Both definitions will be used in the forming of an `Instance` declaration defined later.

```coq
Definition valid_estimate_condition (c : C) (sigma : state) : Prop :=
  binEstimator sigma c.
Definition fault_tolerance_condition (sigma : state) : Prop :=
  (fault_weight_state sigma <= proj1_sig t_full)%R.
```

The lemma below states the easy result that if $$\sigma \subseteq \sigma '$$, then if the `fault_tolerance_condition` property holds for $$\sigma '$$, it also holds for $$\sigma$$.

```coq
Lemma fault_tolerance_condition_subset : forall sigma sigma',
  incl sigma sigma' -> fault_tolerance_condition sigma' -> fault_tolerance_condition sigma.
```

The `hash_state` is a function that maps a state (which is a list of messages) to `justification_type` which is a list of hashes.

```coq
Definition hash_state (sigma : state) : justification_type := map hash sigma.
```

Now we reach the inductive definition of the `protocol_state` dependent type.
In the definition, we see that a `protocol_state` term is either a `protocol_state_nil` which has type `protocol_state state0` (recall that `state0` is an empty list), or a term formed from the `protocol_state_cons` constructor together with some other ingredients which ensure that some conditions are fulfilled before it can be valid protocol state.

```coq
Inductive protocol_state : state -> Prop :=
  | protocol_state_nil : protocol_state state0
  | protocol_state_cons : forall c v j sigma',
     protocol_state j ->
     valid_estimate_condition c j ->
     In (c, v, hash_state j) sigma' ->
     protocol_state (set_remove compare_eq_dec (c, v, hash_state j) sigma') ->
     NoDup sigma' ->
     fault_tolerance_condition sigma' ->
     protocol_state sigma'.
```

We now examine the ingredients required to form a term with `protocol_state_cons`.
It requires a consensus value `c`, a validator `v`, a justification `j` (list of messages), and lastly protocol state `sigma'` (list of messages).
Based on the ingredients above, it requires the proofs that:
- `protocol_state j`: protocol state `j` is valid
- `valid_estimate_condition`: for the given `j`, the binary estimator is able to estimate the consensus value `c`
- `In (c, v, hash_state j) sigma'`: the triple `(c, v, hash_state j)` is a element in the `sigma'` list
- `protocol_state (set_remove compare_eq_dec (c, v, hash_state j) sigma')`: the removal of `(c, v, hash_state j)` from `sigma'` is still a valid protocol state
- `NoDup sigma'`: the list of messages `sigma'` has no duplicates
- `fault_tolerance_condition sigma'`: the weight of equivocating senders in the protocol state `sigma'` is within the threshold (`t_full`)

Thus the `protocol_state_cons` recursively checks that all the elements of a given `sigma'` fulfils the requirements of a valid protocol state to construct a term of `protocol_state sigma'` from `sigma'`.
With `protocol_state` inductively defined, we can now reason on the properties of the terms of `protocol_state`.

Starting with a simple result, `protocol_state_nodup` proves that for all protocol states `sigma` which can be successfully constructed as a `protocol_state sigma`, does not have any duplicates in the list.
This result is trivial as `NoDup sigma` is required in the construction of `protocol_state sigma`.

```coq
 Lemma protocol_state_nodup : forall sigma,
  protocol_state sigma -> NoDup sigma.
```

We can also show that if two protocol states are equal as sets, then if one satisfies the `fault_tolerance_condition` property, so does the other.
This result is represented in `fault_tolerance_condition_set_eq`:

```coq
Lemma fault_tolerance_condition_set_eq : forall sigma sigma', set_eq sigma sigma' -> 
  fault_tolerance_condition sigma -> fault_tolerance_condition sigma'.
 ```
 
 Unsurprisingly, the `protocol_state` property is also `transferrable' between two protocol states which are equal as sets, presented as `set_eq_protocol_state` below.
 
 ```coq
 Lemma set_eq_protocol_state : forall sigma,
  protocol_state sigma -> forall sigma', set_eq sigma sigma' ->
    NoDup sigma' -> protocol_state sigma'.
```

The results of `about_prot_state` provides us another alternative way to validating protocol states.
With the proof that two protocol states have the `protocol_state` property, `about_prot_state` allows for the construction of their union having the `protocol_state` property if we have the weights of equivocating senders of their union below the threshold.
Thus this helps reduce the repetitive work of checking each element in the union of two valid protocol states to validate their union.

```coq
Lemma about_prot_state : forall (s1 s2 : state),
  protocol_state s1 -> protocol_state s2 ->
    (fault_weight_state (state_union s1 s2) <= proj1_sig t_full)%R ->
      protocol_state (state_union s1 s2).
```

We are now at line 418 of `Binary.v` out of the total 489 lines.
In the next and final part, we will look at the definition of light nodes and also introduce some other new definitions, and eventually complete the reading of `Binary.v`.