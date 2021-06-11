---
layout: post
title: Reading Casper CBC proofs - Part 1
date: 2021-05-16 11:59:00-0400
description: first post on understanding how consensus protocols are formally verified
comments: true
---

Recently I have been reading about the [CBC Casper family of consensus protocol](https://github.com/cbc-casper/cbc-casper-paper/blob/master/cbc-casper-paper-draft.pdf) where CBC means *correct-by-construction*.
The people at [runtime verification](https://runtimeverification.com/) have done the [protocol verification of Casper Correct-By-Construction in Coq](https://github.com/runtimeverification/casper-cbc-proofs).

Here, I will attempt to understand how the formal verification Casper is being done in Coq. 
In particular, I will be going through the code [`Binary.v`](https://github.com/runtimeverification/casper-cbc-proofs/blob/master/CBC/Binary.v) to inspect what is being done in it. 
The code in `Binary.v` follows closely the content in the paper: [Introducing the "Minimal CBC Casper" Family of Consensus Protocols](https://github.com/cbc-casper/cbc-casper-paper/blob/master/cbc-casper-paper-draft.pdf); I would recommend reading this paper first so you would be able to relate to the definitions and proofs in `Binary.v`.

Let's begin.

The first definition describes the possible decisions of a [binary consensus protocol](https://github.com/runtimeverification/casper-cbc-proofs/blob/master/CBC/Binary.v#L13). 
At the moment, it is not clear why `C_inhabited` is defined as the term `one : C`, but as we go progress further we might be able to make some sense of this definition.

```coq
Inductive C : Type :=
  | zero : C
  | one : C.

Definition C_inhabited : C := one.
```
The `C_compare` function is a comparison operator on the consensus. 
This operator returns a term of the [`comparison`](https://coq.inria.fr/library/Coq.Init.Datatypes.html#comparison) datatype provided in the default Coq library. 
Based on the usual semantics of `zero` and `one`, when any of these two terms are compared, the possible outputs are the comparison datatype has three terms, `Eq`, `Lt` and `Gt` which means equal, lesser than and greater than respectively.

```coq
Definition C_compare (c1 c2 : C) : comparison :=
  match c1 with
    | zero => match c2 with
      | zero => Eq
      | one => Lt
        end
    | one => match c2 with
      | zero => Gt
      | one => Eq
        end
  end.
```

The `C_compare` operator has some properties that come along with it based on its definition.
When performing formal verification, these properties have to be formally verified the paper and pen approach where we normally use these properties for free without explicitly proving them.
The reflexive and transitive properties of `C_compare` are formally proven with `C_compare_reflexive` and `C_compare_transitive` respectively, and `C_compare_strictorder` is a proof that an operator satisfies the [`CompareStrictOrder'](https://github.com/runtimeverification/casper-cbc-proofs/blob/e32e74997d8fd53b44e8e87add22e9ee1de5d175/Lib/Preamble.v#L291): an operator having the reflexive and transitive properties.

```coq
Lemma C_compare_reflexive : CompareReflexive C_compare.
Lemma C_compare_transitive : CompareTransitive C_compare.
Lemma C_compare_strictorder : CompareStrictOrder C_compare.
```

Here, we say the consensus protocol `C` is `StrictlyComparable` when it is nonempty (provided by the `C_inhabited` term defined earlier), has a comparison operator and has strict-orderedness property.
```coq
Instance about_C : StrictlyComparable C :=
  { inhabited := C_inhabited;
    compare := C_compare;
    compare_strictorder := C_compare_strictorder;
  }. 
```

Up to now, the work has been focused on establishing the properties of the binary consensus comparison operator.
We finally move towards defining some definitions that are found in $$\S 2$$ Description of CBC Casper.
Positive reals are first defined using [sigma types](https://coq.inria.fr/library/Coq.Init.Specif.html#sig), on the real numbers obtained through the package imported in the [preamble](https://github.com/runtimeverification/casper-cbc-proofs/blob/master/CBC/Binary.v#L1).
A coercion `posR_proj1` is declared, which allows functions defined on real numbers to also be usable for positive real numbers as it helps change the type of a term into another by automatically inserting a function, which in this case is `posR_proj1` to prevent type error.

```coq
Definition posR : Type := {r : R | (r > 0)%R}.
Definition posR_proj1 (r : posR) := proj1_sig r.
Coercion posR_proj1 : posR >-> R. 
```

We can now define validator weights as  `weight` which maps a given validator $$v \in \mathcal{V}$$ to a positive real number. 
The `sum_weights` builds upon `weight` to sum the weights of a list of validators given a list of validators `l`.
The parameter `t_full` denote the Byzantine-fault-tolerance threshold.
As for the parameter `suff_val_full`, it specifies the existence of a set of validators where the `sum_weights` is above the threshold `t_full`.

```coq
Parameter weight : V -> posR. 

Definition sum_weights (l : list V) : R 
  := fold_right (fun v r => ((weight v) + r)%R) 0%R l.

Parameter (t_full : {r | (r >= 0)%R}) 
Parameter (suff_val_full : exists vs, NoDup vs /\ ((fold_right (fun v r => ((weight v) + r)%R) 0%R) vs > (proj1_sig t_full))%R).
```

The next few definitions are about the protocol state which are called justification. 
In the definition, justification is a list of elements of type `H` suggesting a list of [hashes](https://en.wikipedia.org/wiki/Cryptographic_hash_function).
Similar to the binary consensus `C`, we also establish that `justification_type` is also `StrictlyComparable` on the definitions below.

```coq
Definition justification_type : Type := list H.

Definition justification_type_inhabited : justification_type := [].

Definition justification_compare : (justification_type -> justification_type -> comparison) := list_compare compare.

Instance about_justification_type : StrictlyComparable justification_type :=
  { inhabited := justification_type_inhabited;
    compare := list_compare compare;
    compare_strictorder := list_compare_strict_order;
  }.
```
The next few are protocol definitions which define what a message is and the auxiliary projection functions for messages which allows us to project out the various components of a message.
The [`TripleStrictlyComparable`](https://github.com/runtimeverification/casper-cbc-proofs/blob/e32e74997d8fd53b44e8e87add22e9ee1de5d175/Lib/Preamble.v#L699) is an instance which helps to establish that the triple `message_type` is strictly comparable, given that the types forming triple are also strictly comparable.

```coq
Definition message : Type := C * V * justification_type.

Definition message_type := TripleStrictlyComparable C V justification_type.

Definition estimate (msg : message) : C :=
  match msg with (c, _, _) => c end.

Definition sender (msg : message) : V :=
  match msg with (_, v, _) => v end.

Definition justification (msg : message) : justification_type :=
  match msg with (_, _, j) => j end.
```

I personally feel that a Coq record (presented below) would be a better way to represent the definition of `message` as it comes with projection functions, also the constructor `mkMsg` as compared to the triple definition above will help ensure that errant messages are not created by accident.

```coq
Record message : Type := mkMsg {  estimate : C;  
                                    sender : V;  
                             justification : justification_type }
```

This leaves us at line 88 of `Binary.v` out of the total 489 lines. 
In the subsequent few lines, the definitions starts working on the protocol states, thus it is a good time to end and in the next part we shall look at the treatment of the protocol states.
I hope this write-up provides a clear, readable way of understanding the code.
Comments and questions are very welcomed :)