# Generalized Bulletproofs

Notation from https://doc-internal.dalek.rs/bulletproofs/notes/r1cs_proof/index.html

## The Relation ("Extended R1CS")

Bulletproofs provide a proof for the following relation:

$$
W_L \cdot \vec{a_L} + 
W_R \cdot \vec{a_R} +
W_O \cdot \vec{a_O} = 
W_V \cdot \vec{v} + \vec{c}
\ \land \ \vec{a_L} \circ \vec{a_R} = \vec{a_O}
$$

Where $\vec{a_L}, \vec{a_R}, \vec{a_O}, \vec{v}$ are the witnesses, with $\vec{v}$ being the opening of a number of (dimension 1) Pedersen commitments. It is not quite the standard def. of R1CS, but clearly equivalent.

Because we are going to have a "pre-committed" vectors $\vec{a_C}$ (a Pedersen commiment of some high dimension), we instead consider a generalization i.e.

$$
W_L \cdot \vec{a_L} + 
W_R \cdot \vec{a_R} +
W_O \cdot \vec{a_O} +
W_C \cdot \vec{a_C} = W_V \cdot \vec{v} + \vec{c} \\
\ \land \ \\
\vec{a_L} \circ \vec{a_R} = \vec{a_O}
$$

Of course, we could have even more of these committed "linear" terms $\vec{a_C}$, but for simplicity in this explaination let us keep it at 1 -- generalizating it further is an easy exercise left to the reader.

## R1CS $\rightarrow$ Sum of Inner Products

Rewrite:

$$
\vec{a_L} \circ \vec{a_R} - \vec{a_O} = \vec{0}
$$

We can sample $\vec{y} = (1, \ldots, y^{n-1})$ to reduce it to a single field element:

$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R} - \vec{a_O}
\rangle
= 0
$$

The same trick can be applied to every row of $W_L, W_R, W_V, W_C, W_O$ by sampling $\vec{z} = (1, \ldots, z^{n-1})$ and noting:

$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R} - \vec{a_O}
\rangle
= 0
\land
W_L \cdot \vec{a_L} + 
W_R \cdot \vec{a_R} +
W_O \cdot \vec{a_O} +
W_C \cdot \vec{a_C} -
W_V \cdot \vec{v} - 
\vec{c}
= \vec{0}
$$

If and only if (with overhelming probability over $z$):

$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R} - \vec{a_O}
\rangle
+
z \cdot
\langle \vec{z},
W_L \cdot \vec{a_L} + 
W_R \cdot \vec{a_R} +
W_O \cdot \vec{a_O} +
W_C \cdot \vec{a_C} -
W_v \cdot \vec{v} -
\vec{c}
\rangle
= 0
$$

(we went from an equation over vectors to single field elements using a challenge $z$)
    
Moving stuff around and seperating the inner products, rewrite the second part of the expression:

$$
\langle z \vec{z} \cdot W_L, \vec{a_L} \rangle + 
\langle z \vec{z} \cdot W_R, \vec{a_R} \rangle +
\langle z \vec{z} \cdot W_O, \vec{a_O} \rangle +
\langle z \vec{z} \cdot W_C, \vec{a_C} \rangle -
\langle z \vec{z} \cdot W_V, \vec{v} \rangle -
\langle z \vec{z}, \vec{c} \rangle
= 0
$$

Let us define:

$$
\vec{w_L} = z \cdot \vec{z} \cdot W_L \in \mathbb{F}^n \\
\vec{w_R} = z \cdot \vec{z} \cdot W_R \in \mathbb{F}^n \\
\vec{w_V} = z \cdot \vec{z} \cdot W_V \in \mathbb{F}^n \\
\vec{w_C} = z \cdot \vec{z} \cdot W_C \in \mathbb{F}^n \\
\vec{w_O} = z \cdot \vec{z} \cdot W_O \in \mathbb{F}^n  \\
w_c = \langle z \cdot \vec{z}, \vec{c} \rangle \in \mathbb{F} 
$$

Note that the verifier can just compute these vectors by himself (since the matrixes, the circuit relation, is public). We are now left with:

$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R} - \vec{a_O}
\rangle
+
\langle \vec{w_L}, \vec{a_L} \rangle + 
\langle \vec{w_R}, \vec{a_R} \rangle +
\langle \vec{w_O}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$


$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R}
\rangle -
\langle
\vec{y},
\vec{a_O}
\rangle+
\langle \vec{w_L}, \vec{a_L} \rangle + 
\langle \vec{w_R}, \vec{a_R} \rangle +
\langle \vec{w_O}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

Which enforces sat. of the extended R1CS.

However, the expression above has *many* inner products. Since we need to do a folding argument for every inner product we would like to avoid this, so, how do we reduce these to a single inner product? First an intermezzo.

## Intermezzo: Vector Polynomials

### Definition

An "$n$" dimensional "vector polynomial" consists of $n$ polynomials "in parallel":
$$
\vec{f}(X) = (f_1(X), \ldots, f_n(X)) = \sum_{i=0}^d \vec{a_i} \cdot  X^i \in \mathbb{F}[X]^n
$$

A polynomial over the $\mathbb{F}$-module $\mathbb{F}^n$. Note that for $x \in \mathbb{F}$ we get $\vec{f}(x) \in \mathbb{F}^n$

This notion is useful, because Pedersen commitments allow us to commit to a vector polynomial efficiently (independently of the dimension) and homomorphically evaluate every coordinate of the vector polynomial:

$$
\mathsf{Com}(\vec{f}(X)) = (\mathsf{PedersenVec}(\vec{a_0}), \ldots, \mathsf{PedersenVec}(\vec{a_d}))
$$

($d$ commitments to $n$-dimensional vectors)

### Inner Product of Vector Polyomials

The "inner product" between two vector polynomials is defined in the inutitive way (for any module over any ring):  taking the coordinate-wise product of polynomials and summing:
$$
\langle
\vec{f}(X), \vec{g}(X)
\rangle = \sum_i f_i(X) \cdot g_i(X) 
\in \mathbb{F}[X]
$$

Note that $\forall x. \langle
\vec{f}, \vec{g}
\rangle(x) = \langle \vec{f}(x), \vec{g}(x)\rangle$ and $\deg(\langle \vec{f}, \vec{g} \rangle) = \deg(\vec{f}) + \deg(\vec{g})$.

This already hints at the approach to check correctness of an inner product between vector polynomials, since we can homomorphically compute commitments to $\vec{f}(x) \in \mathbb{F}$ and $\vec{g}(x) \in \mathbb{F}$ at any public $x$ efficiently by operating on the commitments to the coefficients, to check $\langle \vec{f}, \vec{g} \rangle = \vec{h}$ at a random point $x$

## Sum of Inner Products $\rightarrow$ Single Inner Product

Let us now see why inner products between vector polynomials are useful to us. 

Suppose we have two inner products:

$$
\Delta = \langle \vec{a}, \vec{b} \rangle + \langle \vec{c}, \vec{d} \rangle
$$

If I define the vector polynomials (left/right):

$$
\vec{f_L}(X) = \vec{a} \cdot X + \vec{c} \cdot X^2
$$

$$
\vec{f_R}(X) = \vec{b} \cdot X + \vec{d}
$$

And consider the inner product, then $\Delta$ lands in the square term:

$$
\langle \vec{f_L}, \vec{f_R} \rangle(X) = \delta_0 + \delta_1 \cdot X + \Delta \cdot X^2 + \delta_3 \cdot X^3
\in \mathbb{F}[X]$$

Where $\delta_0, \delta_1, \delta_3$ are some cross-term garbage.

More generally: we define a "left polynomial" where powers *increase* for every left term in the series of inner products and a "right polynomial" where the powers *decrease* for every right term, then the terms will "align" at the "middle power". i.e. in general, suppose we have:

$$
\Delta = \sum_{i=1}^t \langle \vec{L_i}, \vec{R_i} \rangle
$$

Then we define:

$$
\vec{f_L}(X) = \sum_{i=1}^t \vec{L_i} \cdot X^i \\
\vec{f_R}(X) = \sum_{i=1}^{t} \vec{R_i} \cdot X^{t - i} 
$$

In which case, the $t$'th coeficient of $\langle \vec{f_L}, \vec{f_R} \rangle(X)$ is $\Delta$, neato!

This observation suggest the following approach to reduce a sum of multiple inner products, given commitments to every vector, to a single inner product as follows:

1. Prover sends commitments to $\{ \delta_i \}_{i \in 0, \ldots, 2 \cdot t - 1}$ the coefficients, were we are intrested in $\delta_t = \Delta$, which is usually implicit (e.g. fixed to $0$). Then both parties locally define:
$$
\vec{f_L}(X) = \sum_{i=1}^t \vec{L_i} \cdot X^i \in \mathbb{F}[X]^n \\
\vec{f_R}(X) = \sum_{i=1}^{t} \vec{R_i} \cdot X^{t - i} \in \mathbb{F}[X]^n \\
g(X) = \sum_{i = 0}^{2 \cdot t - 1} \delta_i \cdot X^i \in \mathbb{F}[X]
$$
1. Verifier samples $x \gets \mathbb{F}$
1. Both sides compute commitments to the vectors:
$$
\vec{f_L}(x), \vec{f_R}(x)\in \mathbb{F}^n
$$

And a commitment to the field element $g(x) \in \mathbb{F}$, using the homomorphic property of the Pedersen commitments. We now have just a single inner product claim about Pedersen commitments:

$$
\langle \vec{f_L}(x), \vec{f_R}(x) \rangle = g(x)
$$

## Hadamard Products between Secrets and Public Values

Given $\mathsf{PedersenVec}_{\vec{G}}(\vec{V})$ we can simply define 
$$
\mathsf{PedersenVec}_{[\vec{C}^{-1}] \ \circ \ \vec{G}}(\vec{V} \circ \vec{C}) =
\mathsf{PedersenVec}_{\vec{G}}(\vec{V})
$$
In other words, we can homomorphically compute a Hadamard product, where one side is public, simply by a change of basis: rather than a commitment to $\vec{V}$ in bais $\vec{G}$ it is a commitment to $\vec{V} \circ \vec{C}$ in basis $\left[\vec{C}^{-1}\right] \circ \vec{G}$, in other words: if the commitment was opened you would check the correctness by re-commiting using $\left[\vec{C}^{-1}\right] \circ \vec{G}$.

## What Inner Products?

Now that we have the components let us massage our expression from before:

$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R}
\rangle -
\langle
\vec{y},
\vec{a_O}
\rangle+
\langle \vec{w_L}, \vec{a_L} \rangle + 
\langle \vec{w_R}, \vec{a_R} \rangle +
\langle \vec{w_O}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

We are going to massage this so that it is on a form where our newly dicussed techniques apply, we have two goals:

1. Reduce the number of inner products (for efficiency) by collecting common terms.
2. Get rid of the Hadamard product betwen two secrets: $\vec{a_L} \circ \vec{a_R}$.

Start by combining $\vec{a_O}$ terms:

$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R}
\rangle -
\color{brown}{\langle
\vec{y},
\vec{a_O}
\rangle} +
\langle \vec{w_L}, \vec{a_L} \rangle + 
\langle \vec{w_R}, \vec{a_R} \rangle +
\color{brown}{\langle \vec{w_O}, \vec{a_O} \rangle} +
\langle \vec{w_C}, \vec{a_C} \rangle =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

<center><b>Becomes</b></center>

$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R}
\rangle +
\langle \vec{w_L}, \vec{a_L} \rangle + 
\langle \vec{w_R}, \vec{a_R} \rangle +
\color{brown}{\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle} +
\langle \vec{w_C}, \vec{a_C} \rangle =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

Note that the left size of the inner product $\langle \vec{y}, \vec{a_L} \circ \vec{a_R} \rangle$ is public, so lets move one secret two each side, using $\langle \vec{y}, \vec{a_L} \circ \vec{a_R} \rangle = \langle \vec{a_L}, \vec{y} \circ \vec{a_R} \rangle$ get rid of the Hadamard product between secret values:

$$
\color{magenta}{
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R}
\rangle} +
\langle \vec{w_L}, \vec{a_L} \rangle + 
\langle \vec{w_R}, \vec{a_R} \rangle +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

<center><b>Becomes</b></center>

$$
\color{magenta}{ \langle \vec{a_L}, \vec{y} \circ \vec{a_R} \rangle } +
\langle \vec{w_L}, \vec{a_L} \rangle + 
\langle \vec{w_R}, \vec{a_R} \rangle +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

Note that we *know* how to deal with a Hadamard product between a secret and a public value.

Using $\color{blue}{\langle \vec{a_R}, \vec{w_R} \rangle = \langle  \vec{w_R} \circ (\vec{y})^{-1}, \vec{a_R} \circ \vec{y} \rangle}$ rewrite:

$$
\langle
\vec{a_L}, \vec{y} \circ \vec{a_R}
\rangle +
\langle \vec{w_L}, \vec{a_L} \rangle + 
\color{blue}{\langle \vec{w_R}, \vec{a_R} \rangle} +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle \\ =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$


<center><b>Becomes</b></center>

$$
\langle
\vec{a_L}, \vec{y} \circ \vec{a_R}
\rangle +
\langle \vec{w_L}, \vec{a_L} \rangle + 
\color{blue}{\langle  \vec{w_R} \circ (\vec{y})^{-1}, \vec{a_R} \circ \vec{y} \rangle} +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle \\ =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

Collect $\vec{y} \circ \vec{a_R}$ terms (our motivation for the previous step):

$$
\color{green}{ \langle
\vec{a_L}, \vec{y} \circ \vec{a_R}
\rangle } +
\langle \vec{w_L}, \vec{a_L} \rangle + 
 \color{green}{ \langle  \vec{w_R} \circ (\vec{y})^{-1}, \vec{a_R} \circ \vec{y} \rangle} +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle = \\
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$


<center><b>Becomes</b></center>

$$
\color{green}{ \langle
\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1},\vec{y} \circ \vec{a_R}
\rangle } +
\langle \vec{w_L}, \vec{a_L} \rangle +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle = \\
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

Add $\color{red}{\delta(y, z) = \langle (\vec{y})^{-1} \circ \vec{w_R}, \vec{w_L} \rangle}$ to both sides:

$$
\langle
\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1}, \vec{y} \circ \vec{a_R}
\rangle +
\langle \vec{w_L}, \vec{a_L} \rangle +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle \\ =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

<center><b>Becomes</b></center>

$$
\langle
\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1}, \vec{y} \circ \vec{a_R}
\rangle +
\langle \vec{w_L}, \vec{a_L} \rangle +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle +
\color{red}{\langle (\vec{y})^{-1} \circ \vec{w_R}, \vec{w_L} \rangle} \\ = 
\langle \vec{w_V}, \vec{v} \rangle +
w_c +
\color{red}{\delta(y, z)}
\in \mathbb{F}
$$

Note that $\delta(y, z)$ does not depend on the witness! (the verifier can compute it)

Combine $\vec{w_L}$ terms:

$$
\langle
\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1}, \vec{y} \circ \vec{a_R}
\rangle +
\color{orange}{\langle \vec{w_L}, \vec{a_L} \rangle} + 
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle \\ + 
\langle \vec{w_C}, \vec{a_C} \rangle +
\color{orange}{\langle (\vec{y})^{-1} \circ \vec{w_R}, \vec{w_L} \rangle} =
\langle \vec{w_V}, \vec{v} \rangle +
w_c +
\delta(y, z)
\in \mathbb{F}
$$

<center><b>Becomes</b></center>

$$
\langle
\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1}, \vec{y} \circ \vec{a_R}
\rangle +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle \\ + 
\langle \vec{w_C}, \vec{a_C} \rangle +
\color{orange}{\langle (\vec{y})^{-1} \circ \vec{w_R} + \vec{a_L}, \vec{w_L} \rangle} =
\langle \vec{w_V}, \vec{v} \rangle +
w_c +
\delta(y, z)
\in \mathbb{F}
$$

Combine $\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1}$ terms:

$$
\color{purple}{
\langle
\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1}, \vec{y} \circ \vec{a_R}
\rangle } +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle \\ + 
\langle \vec{w_C}, \vec{a_C} \rangle +
\color{purple}{\langle (\vec{y})^{-1} \circ \vec{w_R} + \vec{a_L}, \vec{w_L} \rangle} =
\langle \vec{w_V}, \vec{v} \rangle +
w_c +
\delta(y, z)
\in \mathbb{F}
$$

<center><b>Becomes</b></center>

$$
\color{purple}{
\langle
\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1}, \vec{y} \circ \vec{a_R} +\vec{w_L}
\rangle } +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle + 
\langle \vec{w_C}, \vec{a_C} \rangle \\ =
\langle \vec{w_V}, \vec{v} \rangle +
w_c +
\delta(y, z)
\in \mathbb{F}
$$

So in the end we have 3 inner products on the left: in general we would be left with $2 + m$ inner products of $m$ vector Pedersen commitments. All these are combined into a single inner product using the previous technique based on vector polynomials.

Note that during verification the right side is a commitment to a single field element!

## The Folding Argument: Just Regular Bulletproofs from Here.

At this point we have a single inner product to verify.

The folding argument (not covered here) proves:

$$
\left\{
    (
    \vec{a} \in \mathbb{F}^{n},
    \vec{b} \in \mathbb{F}^{n}
    )
    : P = \langle \vec{a}, \vec{G} \rangle + \langle \vec{b}, \vec{H} \rangle \land c = \langle \vec{a}, \vec{b} \rangle
\right\}
$$