---
layout: post
title: Isomorphism theorems
date: 2021-04-29 11:12:00-0400
description: Looking at some isomorphism theorems for rings
comments: true
---


Today we shall look and proof the isomorphism theorems for [rings](https://en.wikipedia.org/wiki/Ring_(mathematics)) today.

Let's begin.

####  First isomorphism theorem

Let $$R$$ and $$S$$ be rings and let $$\phi: R \to S$$ be a ring homomorphism. Then,
1. $$ker(\phi)$$ is an ideal of $$R$$
2. The image of $$R$$ is a subring of $$S$$
3. The image of $$\phi$$ is isomorphic to the quotient ring $$R/ker(\phi)$$, which we write $$R/ker(\phi) \cong \phi(R)$$

In particular, if $$\phi$$ is surjective, then $$S$$ is isomorphic to $$R/ker(\phi)$$

**Proof.** We will only consider the case where a subset of $$R$$ is a left ideal and leave the case of right ideal and two-sided idea to the reader.


(1) $$ker(\phi)$$ is a subring: for $$k_1, k_2 \in ker(\phi)$$

$$
\phi(k_1 - k_2) = \phi(k_1) + \phi(-k_2) = 0_S
$$

$$
\phi(k_1 k_2) = \phi(k_1) \cdot \phi(-k_2) = 0_S
$$


Next, $$rk \in ker(\phi)$$ for $$k \in ker(\phi)$$, $$r \in R$$, since

$$
\phi(rk) = \phi(r)\cdot\phi(k) = \phi(r) \cdot 0_{S} = 0_{S}
$$

(2) Let $$r_1, r_2 \in R$$, so $$\phi(r_1), \phi(r_2) \in \phi(R)$$,

$$
\phi(r_1) - \phi(r_2) = \phi(r_1 - r_2) \in \phi(R)
$$

$$
\phi(r_1)\phi(r_2) = \phi(r_1 r_2) \in \phi(R)
$$

(3) Let $$\psi : R/ker(\phi) \to \phi(R)$$ be defined by $$\psi(r + ker(\phi)) = \phi(r)$$, and it is clear that $$\psi$$ is surjective. It suffices to show that $$\psi$$ is well-defined and injective. Let $$r_1, r_2 \in R$$ be given

$$
r_1 + ker(\phi) = r_2 + ker(\phi)\Leftrightarrow r_1 - r_2 \in ker(\phi) \Leftrightarrow \phi(r_1 - r_2) = 0_S 
$$

$$
\phi(r_1 - r_2) = 0_S \Leftrightarrow \phi(r_1) = \phi(r_2) \Leftrightarrow \psi(r_1 + ker(\phi)) = \psi(r_2+ker(\phi))
$$

The forward direction shows well-defined: any two equivalent different expressions of the equivalence class in $$R/ker(\phi)$$ will evaluate to the same value on $$\psi$$. The converse shows $$\psi$$ is injective.


####  Second isomorphism theorem
Let $$R$$ be a ring, $$S$$ be a subring of $$R$$ and $$I$$ be an ideal of $$R$$.
1. The sum $$S+I:=\{s+i \mid s \in S, i \in I\}$$ is a subring of $$R$$
2. The intersection $$S \cap I$$ is an ideal of $$S$$
3. The quotient rings $$(S+I)/I$$ and $$S/(S \cap I)$$ are isomorphic

**Proof.**

(1) Let $$s_1+ i_1, s_2+i_2 \in S + I$$ where $$s_k \in S, i_K \in I$$ for $$i = 1,2$$. It suffices to show that $$S+I$$ is closed under $$-$$ and $$\cdot$$. 

$$
(s_1+ i_1) - (s_2+i_2) = (s_1 - s_2) + (i_1 - i_2) \in S + I
$$

$$
(s_1+ i_1) \cdot (s_2+i_2) = s_1s_2 + (s_1i_2 + i_1s_2 + i_1i_2) \in S + I 
$$

since $$s_1s_2 \in S$$ and $$s_1i_2 + i_1s_2 + i_1i_2 \in I$$

(2) Let $$x_1, x_2 \in S \cap I$$.  First, $$S \cap I$$ is an subring: By considering the membership of $$x_1, x_2$$ in $$S$$ and $$I$$ respective we see that $$x_1 - x_2$$ and $$x_1 \cdot x_2$$ are contained in $$S \cap I$$, thus $$S \cap I$$ is a subring. Next we consider the left ideal case and leave the right to the reader. For $$x \in S \cap I$$ and $$s \in S$$, we have $$s \cdot x \in S$$ since $$x \in S$$. $$s \cdot x \in I$$ since $$I$$ is an ideal of $$R$$ and $$s \in S \subseteq R$$. Thus $$S \cap I$$ is an ideal of $$S$$.


(3) With the earlier parts proven, it is then meaningful to consider $$(S+I)/I$$ and $$S/(S \cap I)$$.

[//]: # (i.e. $$I \subseteq S+I$$ and $$S+I$$ is a subring, $$S \cap I$$ is an ideal.)

Let $$\phi : R \to R/I$$ and the inclusion map $$\iota : S \to R$$, then define $$\psi = \phi \circ \iota : S \to (S+I)/I$$ by  $$s \mapsto s + I$$. The $$ker(\psi) = \{s \in S \mid s \in I\} = S \cap I$$ and $$\psi(S) = (S+I)/I $$. Note that $$\psi (S) \neq S/I$$ since it is not necessary that $$I \subseteq S$$. For $$s_1, s_2 \in S$$, 

$$
\psi(s_1 + s_2) = (s_1 + s_2) + I = (s_1 + I) + (s_2 + I) = \psi(s_1) + \psi(s_2)
$$

$$
\psi(s_1s_2) = (s_1s_2) + I = (s_1 + I) \cdot (s_2 + I) = \psi(s_1) \cdot \psi(s_2)
$$

thus $$\psi$$ is a ring homomorphism, and the first isomorphism theorem says that $$S/(S \cap I)\cong (S+I)/I$$. 
####  Third isomorphism theorem

Let $$R$$ be a ring, and $$I$$ an ideal of $$R$$. Then if $$J$$ is an ideal of $$R$$ such that $$I \subseteq J \subseteq R$$, then the quotient ring $$(R/I)/(J/I)$$ is isomorphic to $$R/J$$

**Proof.** Let $$\phi : R/I \to R/J$$ defined by $$r + I \to r + J$$ for $$r \in R$$. Then $$ker(\phi) = \{r + I \mid r \in J\}$$ which is $$J/I$$. The image $$\phi(R/I) = R/J$$. We now verify that $$\phi$$ is well-defined and a ring homomorphism. For $$r_1, r_2 \in R$$,

$$
r_1 + I = r_2 +I \Leftrightarrow r_1 - r_2 \in I \subseteq J \Leftrightarrow r_1 + J = r_2 + J \Leftrightarrow \phi(r_1 + I) = \phi(r_2 + I)
$$

therefore $$\phi$$ is well-defined. Next,

$$
\phi(r_1 + r_2) = (r_1 + r_2) + J = (r_1 + J) + (r_2 + J) = \phi(r_1) + \phi(r_2)
$$

$$
\phi(r_1r_2) = (r_1r_2) + J = (r_1 + J) \cdot (r_2 + J) = \phi(r_1) \cdot \phi(r_2)
$$

thus by the first isomorphism theorem we get $$(R/I)/(J/I)\cong R/J$$.

####  Fourth isomorphism theorem (Lattice isomorphism theorem for rings)
Let $$I$$ be an ideal of $$R$$. The correspondence $$S \leftrightarrow S/I$$ is an inclusion preserving bijection between the set of subrings $$S$$ of $$R$$ that contain $$I$$ and the set of subrings of $$R/I$$. Furthermore, $$S$$ (a subring containing $$I$$) is an ideal of $$R$$ if and only if $$S/I$$ is an ideal of $$R/I$$.

**Proof.** Take the *natural quotient map*, $$p : R \to R/I$$ defined by $$r \mapsto r + I$$. It is easy to see that $$p$$ is a bijective ring homomorphism. Let $$s_1, s_2 \in S \supseteq I$$  be a given subring, then observe

$$
s_1 - s_2 \in S \Leftrightarrow p(s_1) - p(s_2)  \in S/I
$$

$$
s_1s_2 \in S \Leftrightarrow p(s_1)p(s_2) \in S/I
$$

which shows that $$S/I$$ is a subring of $$R/I$$. If $$S \supseteq I$$ is an ideal, for $$r \in R$$

$$
rs \in S \Leftrightarrow p(rs) \in S/I
$$

Lastly to show the bijection between the set of subrings(ideals) of $$R$$ containing $$I$$ and the set of subrings(ideals) of $$R/I$$, let $$S_1, S_2 \supseteq I$$ be subrings(ideals) such that $$p(S_1) = p(S_2)$$. Then there exists  $$s_1 \in S_1, s_2 \in S_2$$ such that for $$i=1,2$$

$$
\phi(s_i) = \phi(s_{3-i}) \Leftrightarrow s_i - s_{3-i} \in I \subseteq S_{3-i} \Leftrightarrow s_i \in S_{3-i}
$$

Therefore $$S_1 = S_2$$. Now for surjectivity of $$p$$, let $$S/I$$ be a subring(ideal), then $$p^{-1}(S/I) = S\supseteq I$$, since $$0_{S/I} \in S/I$$ and $$ker(p) = I$$. Thus the inclusion preserving bijection is shown.



