---
layout: post
title: A flavour of type theory
date: 2016-09-12 10:29
description: a quick taste of types
---

For the past one month, I have been burying myself in reading the [Homotopy Type Theory (HoTT) book](https://github.com/HoTT/book/wiki); which has been an nothing
short of interesting. The idea of HoTT suggested as the new foundations of
mathematics (the current foundation is based on
[Zermelo Fraenkel set theory with axiom of choice](https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory)) is
so intriguing which is probably why it has generated much interest. The HoTT
book is by no means an easy read; references are being made to topics in
topology and category theory which most people do not have a deep
understanding or familiarity with (including me). Thankfully the first chapter
on type theory was still manageable after spending much time to digest the
material and referencing other sources.

Type theory was first created by Bertrand Russell so as to avoid Russell's
Paradox that says:

$$
R = \{x ~|~ x \notin x\}  \text{, then, } R \in R \Leftrightarrow R \notin R
$$

Over time, type theory was further worked on by other people and type theory
that is introduced in the first chapter is better known as
*Martin-Löf’s intensional type theory*.

To begin, let's understand what is meant by a *type*. The basic concept of type
theory is that we have *terms* and *types* as compared to elements and sets in
set theory. The term $a$ that is of type $$A$$ is written as
$$a :A$$
we can also say that $a$ is an inhabitant of $$A$$. The only visible difference
is just a change in symbol from $$\in$$ to $$:$$ but its interpretation is of
another kind. There are two ways of interpreting a type:

- when $$A$$ is used to represent a proposition, then the $$a$$ in $$a:A$$ may be
seen as a witness to the provability of $$A$$ or evidence to the truth of $$A$$.
This important concept of *proposition as types* is how it is used to formalize mathematics and verify the correctness of proofs.

We can represent the proposition, '$$A$$ is isomorphic to $$B$$' using the type in
the way below, where we treat $$\Pi$$ and $$\Sigma$$  as the existential quantifiers
*for all* and *there exists* respectively

$$
\text{Iso($A,B$)}:\equiv \sum_{f:A\to B}\sum_{g:B\to A}\left(\left(\prod_{x:A}g(f(x))=x\right)\times \left(\prod_{y:B}f(g(y))=y\right)\right)
$$

then if no term inhabits Iso($A,B$), it translates to there is no
evidence to show the isomorphism between $$A$$ and $$B$$. But if
$$p:\text{Iso}(A,B)$$, then the isomorphism holds and $$p$$ is one such isomorphism.
Hence we see that proofs are treated like mathematical objects (think sets,
functions etc) instead of how we see them in classical mathematics.

-  the type $$A$$ can also be treated more like a set than a proposition, then
'$$a : A$$' is analogous to '$$a \in A$$' but they differ in the the former is
a *judgment* whereas the latter is *proposition*.

Here, the use of the words judgment and proposition can be quite confusing if
we interpret the meaning of these words as how we understand usually. We
should understand the judgment as that the term $$a$$ is judged to be of type
$$A$$ (it is by construction constructed to be of type $$A$$!) and $$a \in A$$
is a proposition as the membership of $$a$$ in $$A$$ may or may not be true. The
proposition ,there exists two irrational numbers such that its sum is rational
can be represented in mathematically in the following way:

$$ 
\exists~ x, y \in \mathbb{R}\setminus\mathbb{Q} \text{  such that  } x + y \in \mathbb{Q}
$$

if we were to consider the symbol $$\in$$ in the representation above, the first
$$\in$$ is saying that $$x, y$$ are irrationals by definition, but the second $$\in$$
is questioning of $$x+y$$ is really a rational number. This is the nature of set
theory which does not exists in types, in fact, the type has to be formed
before we can construct its terms but for set theory, we can just take any
element and throw them into the sets we want them to belong to.

Another interesting aspect of type theory is its treatment of equality. Again
we have two different types of equalities (which at the point of typing,
I have some intuition that it is related to the dual interpretation of types
discussed above).

- *Judgmental equality* or *Definitional equality* is equality of the syntax 	
and is denote by $$:\equiv$$. For example,

$$
(x+1)^2  :\equiv x^2+2x+1
$$

since it is easily obtained by algebraic expansion. From the HoTT book, it says
that it is helpful to think of this meaning "equality by definition" which is
really exactly what it says.

- *Propositional equality* on the other hand is though of as a type since we
treat propositions as types. For terms $$a, b : A$$, we have the type '$$a =_Ab$$'
 which can also be written as $$\text{Id}(a,b)$$. Only when $$\text{Id}(a,b)$$
 is inhabited can we say that $$a$$ and $$b$$ are (propositionally) equal, and this inhabitation comes in the form of a term for the type $$\text{Id}(a,b)$$,
 i.e. $$p:\text{Id}(a,b)$$ and $$p$$ should be viewed as evidence for
 the equality to hold.

 As mentioned earlier, a type has to be formed before we can construct
 a term of a type. For all types, it follows a set of type forming rules:

1. **Formation** Tells us how to form new types.
2. **Introduction.** Also known as a *constructor*, which specifies how to construct terms of a newly formed type.
3. **Elimination.** How to use the terms of that type.
4. **Computation.** Expresses how an eliminator acts on a constructor.
5. **Uniqueness Principle.** Expresses the uniqueness of maps into or out of that type.

Here is an example of the formation rules for *function types*, which is
the usual functions that we know.
### Inference Rules

$$
\frac{\vdash X: Type\qquad \vdash A:Type}{\vdash (X \to A): Type}\tag{Type Formation}
$$

$$
\frac{x:X\vdash a(x):A}{\vdash (x \mapsto a(x)):X \to A} \tag{Type Introduction}
$$

$$
\frac{\vdash f:(X \to A) \qquad \vdash x:X}{x:X \vdash f(x):A}\tag{Type Elimination}
$$

$$
\frac{x:X\vdash a(x):A \qquad \vdash x:X}{\vdash (\lambda(x:X).a)(y)\equiv a[y\,/\, x]:A[y\,/\, x]}\tag{Type Computation}
$$

$$
\frac{\vdash f: (X \to A)}{\vdash f \equiv (\lambda x.f(x)):X \to A} \tag{Uniqueness}
$$

the $$\vdash$$ symbol is called the turnstile and for $$x:A\vdash a(x):A$$, it should be understood as 'In the context of variable $$x$$ of type $$X$$, the expression $$a(x)$$ has type $$A$$.' (Normally there is the $\Gamma$ symbol on the left hand side of
$$\vdash$$ which denotes the context which I have chosen to leave out to
reduce the clutter.)

Although in the first chapter of the HoTT book it does not show the formation
rules like the above but instead 'talks' its way through the type formation,
I personally like to understand the type formation written in the inference
rules way which is clearer and easier to understand. There are much more that
I would have liked to discuss but due to my lack of deep understanding in this
topic, I'll have to end it off here. I would like to give credit to Mike
Shulman as almost every other reference that have helped in my understanding
is linked to him in one way or another, be it the [From Set Theory to Type Theory](https://golem.ph.utexas.edu/category/2013/01/from_set_theory_to_type_theory.html) post in The n-Category Café, to replying [my question in mathoverflow](http://mathoverflow.net/questions/247685/uniqueness-principle-for-function-types), the list goes on. I hope to find time to explore and learn more about
HoTT but oh wells, tomorrow is the first day of the semester.

Good luck to me.
