---
layout: post
title: Reading Casper CBC proofs - Part 2
date: 2021-05-27 11:59:00-0400
description: messages and protocol states 
comments: true
---


We continue from where we left off earlier in [Part 1](https://zunction.github.io/blog/2021/reading-casper-cbc-proofs/) and continue reading the [`Binary.v`](https://github.com/runtimeverification/casper-cbc-proofs/blob/master/CBC/Binary.v) code.
The code which we are covering today starts working on $$\S 2.2$$ of the paper.

**Some paper definitions.** We start by going through what are protocol states and messages.
As protocol states and messages both change over time as new blocks are mined or validated, a time step $$n$$ is used to index the time. 
For $$n = 0$$, the protocol states $$\Sigma$$ starts off empty:

$$
\Sigma^0 := \{\emptyset\}
$$

With this declared, we can then talk about messages, which are triples formed from consensus value $$\mathcal{C}$$, validators $$\mathcal{V}$$ and protocol states a time step $$\Sigma^n$$,

$$
M^n := \{m \in \mathcal{C} \times \mathcal{V} \times \Sigma^n \mid Estimate(m) \in \mathcal{E}(Justification(m)) \}
$$

such that the projection of the consensus value denoted by $$Estimate(m)$$ of each message in $$M^n$$ is in the set of consensus values $$\mathcal{E}(Justification(m))$$.
Let's go into details of the definition of $$M^n$$.
As messages are triples, it comes along with projection functions (the lack of the superscript $$n$$ for $$M$$ will be explained later) which we went through the code for it in Part 1:

$$
Estimate: M \to \mathcal{C}
$$

$$
Sender: M \to \mathcal{V}
$$

$$
Justification: M \to \Sigma
$$

Using the binary consensus as an example, we will have for any $$m \in M^0$$, $$Estimate(m)$$ will be either $$0$$ or $$1$$ and $$Justification(m) = \emptyset$$.
Next the $$\mathcal{E} : \Sigma \to \mathcal{P}(\mathcal{C})\backslash \emptyset$$ is an estimator function (different from the $$Estimate$$ projection function) which maps a protocol state to a non-empty subset of possible consensus value, denoted by $$\mathcal{P}(\mathcal{C})\backslash \emptyset$$.
Thus if $$M^0$$ is non-empty, it would require $$\mathcal{E}$$ to map the empty set to a set which contains $$Estimate(m)$$.


**Upshot**: *a triple is a message only if its consensus value is one of the possible values evaluated by $$\mathcal{E}$$ on the protocol state of the triple.*

Now we can talk about what protocol states are when $$n >0$$.

$$
\Sigma^n := \{\sigma \in \mathcal{P}_{finite}(M^{n-1}) \mid m \in \sigma \implies Justification(m) \subseteq \sigma\} ~~ \text{for } n >0
$$

Breaking down the definition, a protocol state $$\sigma \in \Sigma^n$$ is a finite subset of $$M^{n-1}$$ such that $$m \in \sigma$$ when the protocol state of $$m$$ ($$Justification(m)$$) is a subset of the protocol state $$\sigma$$.
This means not every subset of $$M^{n-1}$$ is a protocol state.
A subset of $$M^{n-1}$$ is a protocol state when the protocol state of each message in the subset is contained in the subset.

Let's work out an example: suppose $$\mathcal{E}(\emptyset) = \{0,1\}$$[^1] and assuming two validators $$v_1, v_2 \in \mathcal{V}$$, then we can have one possible $$M^0$$ like this:

[^1]: this is a valid estimator as all the consensus values are possible when no data is given.

$$
M^0 = \{(0,v_1,\emptyset), (1,v_2,\emptyset)\}
$$

$$
 \mathcal{P}_{finite}(M^0)= \mathcal{P}(M^0)= \{ \{\emptyset\}, \{(0,v_1,\emptyset)\}, \{(1,v_2,\emptyset)\}, \{(0,v_1,\emptyset), (1,v_2,\emptyset)\} \}
$$

and we see that

$$
\{(0,v_1,\emptyset)\}, \{(1,v_2,\emptyset)\}, \{(0,v_1,\emptyset), (1,v_2,\emptyset)\} \in \Sigma^1
$$

since for each $$\sigma \in \Sigma^1$$ and $$m \in \sigma$$ above, $$Justification(m) = \emptyset \in \sigma$$ trivially.
An example of a nontrivial protocol state is:

$$
\sigma := \{(0,v_1,\{(1,v_2,\emptyset)\}), (1,v_2,\emptyset)\}
$$

the justification of the message $$(0,v_1,\{(1,v_2,\emptyset)\})$$ is $$\{(1,v_2,\emptyset)\} \subseteq \sigma$$ 

**Upshot**: *an element $$\sigma$$ in $${P}_{finite}(M^{n-1})$$ (which is a subset $$M^{n-1}$$) is a protocol state if the protocol state of each message in $$\sigma$$ is a subset $$\sigma$$*

Lastly, the definition of protocol states and messages are completed by 

$$
M := \bigcup_{i=0}^{\infty}M^i
$$

$$
\Sigma := \bigcup_{i=0}^{\infty}\Sigma^i
$$

thus the notations without the superscript to denote the time is simply the union of all of them.

At this point, some thoughts that I have is about the representation of messages in Coq. 
The definitions in `Binary.v` which we went through previously (at least for now) does not enforce that the consensus value of a message be an element of the possible consensus value given by the estimator $$\mathcal{E}$$.
It is also mentioned in the paper that the domain of the estimator is yet to be defined, thus perhaps this constrain might be addressed later.

With the definitions established and understood, we are ready to head over to the code side.

#### To the code

Recall that protocol states are defined as `justification_type` which is a list of hashes `H`.

Using [`set`](https://coq.inria.fr/library/Coq.Lists.ListSet.html#set), which is a function which takes a type to a list of its type, i.e. 

```coq
fun A : Type => list A : Type -> Type
```

`state`s are list of `message`s, and we have the trivial state `state0` to be the empty list.
[`Parameter`](https://coq.inria.fr/refman/language/core/assumptions.html?highlight=parameters#coq:cmd.Parameters) declarations in Coq are used to declare an abstract object of the given type.
Below, the parameter `about_state` declares that we assume that we have a proof that `state` satisfies the strictly comparable property.

```coq
Definition state := set message.

Definition state0 : state := [].  

Parameter about_state : StrictlyComparable state.
```

To establish that two protocol states $$s1, s2$$ are equal, we need to construct a proof for the proposition `state_eq s1 s2` which checks that each state is the inclusion of the other.
The `state_union` function takes two protocol states and returns a union. 
This process is not similar to the concatenation two list of messages as a set which in this case is represented by a list of messages, can only have distinct elements.
Thus the `compare_eq_dec` is a proof that the comparison function `compare` has [decidable equality](https://ncatlab.org/nlab/show/decidable+equality#:~:text=1.-,Definitions,either%20equal%20or%20not%20equal.&text=More%20generally%2C%20X%20has%20stable,they%20are%20not%20not%20equal.) and is used in the `state_union` function.
The last line is a lemma which states an easy result that union of states is commutative.

```coq
Definition state_eq (s1 s2 : state) := incl s1 s2 /\ incl s2 s1.
Definition state_union (s1 s2 : state) : state := set_union compare_eq_dec s1 s2.
Lemma state_union_comm : forall s1 s2, state_eq (state_union s1 s2) (state_union s2 s1).
```

The next 40 plus lines is a haemorrhage of definitions, beginning with

```coq
Definition observed (sigma:state) : list V :=  set_map compare_eq_dec sender sigma.
```

The function `observed` takes in a protocol state (list of messages) and extracts a list of validators in each message using [`set_map`](https://coq.inria.fr/library/Coq.Lists.ListSet.html#set_map) and `sender` function defined earlier (cf. Part 1).
Although the explicit form of `V` is not described, the use of `set_map` suggests that we can take `V` to be a set of elements, perhaps strings which represent the validator's name.

Next two parameters are declared:

```coq
Parameters (hash : message -> H) (hash_injective : Inj eq eq hash). 
```

The next function `later` filters for messages in `sigma` such that the protocol state of every message, which we shall subsequently call it the *justification of the message*, in `sigma` contains the given message `msg`.
Recall early we saw that $$\Sigma^n$$ is formed from $$M^{n-1}$$.
Thus if `msg` is in the justification of `msg'` this implies that `msg'` is a later message compared to `msg`.

```coq
Definition later (msg : message) (sigma : state) : list message :=
    filter (fun msg' => inb compare_eq_dec (hash msg) (justification msg')) sigma. 
```

**Upshot** : `later` *returns messages from a list of message which occurs later than the given message.*

In the function `from_sender`, it filters for messages in `sigma` such that the validator of the message is the given validator `v`,

```coq
Definition from_sender (v:V) (sigma:state) : list message :=
    filter (fun msg' => compareb (sender msg') v) sigma.
```
Lastly, `later_from` is the composition of `later` and `from_sender`, which filters for messages in `sigma` such that its justification contains the given `msg` and is validated by validator `v`.

```coq
Definition later_from (msg : message) (v : V) (sigma : state) : list message :=
    filter (fun msg' => (inb compare_eq_dec (hash msg) (justification msg')) && (compareb (sender msg') v)) sigma.
```

**Upshot** : `later_from` *returns messages by the given validator, from a list of messages which occurs later than the given message.*

Just a though, is the observation `obs` stated below true?

```coq
Lemma obs : forall (msg : message) (v : V) (sigma : state), 
  state_eq (later_from msg v sigma) (from_sender v (later msg sigma)).
```

Leaving this as an exercise during my free time~.

The next definition is a boolean predicate which tests if a given list is the trivial empty list, defined to be used in `latest_messages`.

```coq
Definition is_nil_fn {A:Type} (l:list A) : bool :=
  match l with
    | nil => true
    | _ => false
  end.
```

In `latest_messages`, what is does is that over a list of messages by validator `v`, it filters for those messages that is **not** contained in another message's justification by the same validator `v`.
A message $$m_1$$ can only be contained in the justification of another message $$m_2$$ iff $$m_1$$ is earlier then $$m_2$$
Thus for a message to be not contained in the justification the another messages in a list of messages, it needs to be the latest, and hence the name of the function.

```coq
Definition latest_messages (sigma : state) : V -> list message :=
    fun v => filter (fun msg => is_nil_fn (later_from msg v sigma)) (from_sender v sigma).
```

**Upshot**: `latest_messages` *literally returns the latest messages by the given validator.*

What we have next is the statement `latest_messages_driven` that says that given an estimator  `estimator: state -> C -> Prop`, there exists a validator `validator: (V -> list message) -> C -> Prop` such that for all protocol states and consensus values `estimator sigma c` is inhabited iff `validator (latest_messages sigma) c` is inhabited, i.e. both the estimator and validator are in agreement given any protocol state and consensus value.
The `estimator` is referring to $$\mathcal{E}$$ which we saw above and `validator` can be thought of as a validator which makes use of his latest messages to decide on the consensus value.

```coq
Definition latest_messages_driven (estimator : state -> C -> Prop) : Prop :=
    exists validator : (V -> list message) -> C -> Prop,
      forall sigma c, estimator sigma c <-> validator (latest_messages sigma) c.
```

**Upshot**: `latest_messages_driven` *says that there is a validator with knowledge of the latest messages which is consistent with the estimator*

The following `latest_estimates` function provides another way to decide on possible consensus values.
Instead of using the latest messages, it extracts out the consensus component (which we shall call it by the *estimate of the message*) of those latest message and uses it to decide on the consensus value, and this function is applied in the definition of `latest_estimates_driven`

```coq
Definition latest_estimates (sigma : state) : V -> list C :=
    fun v => set_map compare_eq_dec estimate (latest_messages sigma v).
Definition latest_estimates_driven (estimator : state -> C -> Prop) : Prop :=
    exists validator : (V -> list C) -> C -> Prop,
      forall sigma c, estimator sigma c <-> validator (latest_estimates sigma) c.
```

**Upshot**: `latest_estimates_driven` *says there is a validator with knowledge of the latest estimates which is consistent with the estimator*

The `in_fn` stands for ``in function'' which simply checks if the term `a : A` is in the list `l : list A` and returns a boolean value.

```coq
Definition in_fn {A:Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (a:A) (l:list A) : bool :=
  match in_dec eq_dec a l with
  | left _ => true
  | right _ => false
  end.
```

The `validators_latest_estimate` function returns the list of validators from a state, whose last estimate contains the given consensus value `c`.

```coq
Definition validators_latest_estimates (c : C) (sigma : state) : list V :=
    filter (fun v => in_fn compare_eq_dec c (latest_estimates sigma v)) (observed sigma).
```

The `score` of a consensus value `c` over a state `sigma` computes for the weight of the validators who have `c` in their latest estimates of the consensus values.

```coq
Definition score (c : C) (sigma : state) : R :=
    fold_right Rplus R0 (map posR_proj1 (map weight (validators_latest_estimates c sigma))).
```

My thoughts about `score` is that it could have been defined using the `sum_weights` function defined earlier:

```coq
Definition score' (c : C) (sigma : state) : R :=
  sum_weights (validators_latest_estimates c sigma)
```

This leaves us at line 152 of `Binary.v` out of the total 489 lines.
In [Part 3](), we will be looking at `reach`, which are protocol state transitions.




