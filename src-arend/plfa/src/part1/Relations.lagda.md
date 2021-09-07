---
title     : "Relations: Inductive definition of relations"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
---

```
module plfa.part1.Relations where
```

After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.

## Imports

<details><summary>Agda</summary>

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)
```
</details>

```tex
\import Paths (pmap)
\open Nat (+)
\import Arith.Nat (NatSemiring)
\open NatSemiring (+-comm)
```


## Defining relations

The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
<details><summary>Agda</summary>

```agda
data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n
```
</details>

```tex
-- Note that each constructor has `m` and `n` as implicit parameters.

\data \infix 4 <= Nat Nat \with
  | 0, _ => z<=n
  | suc m, suc n => s<=s (m <= n)
```
Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.

Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`:

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof:
<details><summary>Agda</summary>

```agda
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)
```
</details>

```tex
\func [2<=4] : 2 <= 4 => s<=s (s<=s z<=n)
```




## Implicit arguments

This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit:
<details><summary>Agda</summary>

```agda
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))
```
</details>

```tex
\func [2<=4]' : 2 <= 4 => s<=s {1} {3} (s<=s {0} {2} (z<=n {2}))
```
One may also identify implicit arguments by name:
<details><summary>Agda</summary>

```agda
_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))
```
</details>

```tex
-- Arend doesn't have this.
```
In the latter format, you can choose to only supply some implicit arguments:
<details><summary>Agda</summary>

```agda
_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)
```
</details>

```tex
-- Arend doesn't have this.
```
It is not permitted to swap implicit arguments, even when named.

We can ask Agda to use the same inference to try and infer an _explicit_ term,
by writing `_`. For instance, we can define a variant of the proposition
`+-identityʳ` with implicit arguments:
<details><summary>Agda</summary>

```agda
+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _
```
</details>

```tex
\import part1.Induction (+-identity-left)

\func +-identity-left' {m : Nat} : 0 + m = m => +-identity-left _
```
We use `_` to ask Agda to infer the value of the _explicit_ argument from
context. There is only one value which gives us the correct proof, `m`, so Agda
happily fills it in.
If Agda fails to infer the value, it reports an error.


## Precedence

We declare the precedence for comparison as follows:
<details><summary>Agda</summary>

```agda
infix 4 _≤_
```
</details>

```tex
-- As we have seen above, precedence is declared as a part of the data declaration in Arend.
```
We set the precedence of `_≤_` at level 4, so it binds less tightly
than `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable](/Decidable/).


## Inversion

In our definitions, we go from smaller things to larger things.
For instance, from `m ≤ n` we can conclude `suc m ≤ suc n`,
where `suc m` is bigger than `m` (that is, the former contains
the latter), and `suc n` is bigger than `n`. But sometimes we
want to go from bigger things to smaller things.

There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  This lets us invert our previous rule.
<details><summary>Agda</summary>

```agda
inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n
```
</details>

```tex
\func inv-s<=s {m n : Nat} (p : suc m <= suc n) : m <= n \elim p
  | s<=s m<=n => m<=n
```
Here `m≤n` (with no spaces) is a variable name while
`m ≤ n` (with spaces) is a type, and the latter
is the type of the former.  It is a common convention
in Agda to derive a variable name by removing
spaces from its type.

Not every rule is invertible; indeed, the rule for `z≤n` has
no non-implicit hypotheses, so there is nothing to invert.
But often inversions of this kind hold.

Another example of inversion is showing that there is
only one way a number can be less than or equal to zero.
<details><summary>Agda</summary>

```agda
inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl
```
</details>

```tex
-- TODO Agda seems to be a bit smarter here.

\func inv-z<=n {m : Nat} (p : m <= 0) : m = 0 \elim m
  | 0 => idp
```

## Properties of ordering relations

Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
partial order but not a total order.


#### Exercise `orderings` (practice) {name=orderings}

Give an example of a preorder that is not a partial order.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
-- Your code goes here
```

Give an example of a partial order that is not a total order.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
-- Your code goes here
```

## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
<details><summary>Agda</summary>

```agda
≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl
```
</details>

```tex
\func <=-refl {n : Nat} : n <= n
  | {0} => z<=n
  | {suc n} => s<=s <=-refl
```
The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
<details><summary>Agda</summary>

```agda
≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)
```
</details>

```tex
-- TODO Agda can pattern match on constructors directly here, Arend cannot.
-- See: https://github.com/JetBrains/Arend/issues/286

\func <=-trans {m n p : Nat} (m<=n : m <= n) (n<=p : n <= p) : m <= p
  | {0}, _, _ => z<=n
  | {suc m}, {suc n}, {suc p}, s<=s m<=n, s<=s n<=p => s<=s (<=-trans m<=n n<=p)
```
Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤ p`,
which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.

Alternatively, we could make the implicit parameters explicit:
<details><summary>Agda</summary>

```agda
≤-trans′ : ∀ (m n p : ℕ)
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans′ zero    _       _       z≤n       _          =  z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans′ m n p m≤n n≤p)
```
</details>

```tex
\func <=-trans' (m n p : Nat) (m<=n : m <= n) (n<=p : n <= p) : m <= p
  | 0 , _, _, _, _ => z<=n
  | suc m, suc n, suc p, s<=s m<=n, s<=s n<=p => s<=s (<=-trans m<=n n<=p)
```
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Anti-symmetry

The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds:
<details><summary>Agda</summary>

```agda
≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)
```
</details>

```tex
\func <=-antisym {m n : Nat} (m<=n : m <= n) (n<=m : n <= m) : m = n
  | {0}, {0}, z<=n, z<=n => idp
  | {suc n}, {suc m}, s<=s m<=n, s<=s n<=m => pmap suc (<=-antisym m<=n n<=m)
```
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.

In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.

#### Exercise `≤-antisym-cases` (practice) {name=leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
-- Your code goes here
```


## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total:
<details><summary>Agda</summary>

```agda
data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n
```
</details>

```tex
\data Total (m n : Nat)
  | forward (m <= n)
  | flipped (n <= m)
```
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives](/Connectives/).)

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
<details><summary>Agda</summary>

```agda
data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ----------
    → Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ----------
    → Total′ m n
```
</details>

```tex
-- Arend doesn't actually have a distinction between indices and parameters.
```
Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality:
<details><summary>Agda</summary>

```agda
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)
```
</details>

```tex
\func <=-total (m n : Nat) : Total m n
  | 0, n => forward z<=n
  | suc m, 0 => flipped z<=n
  | suc m, suc n => \case <=-total m n \with {
    | forward m<=n => forward (s<=s m<=n)
    | flipped n<=m => flipped (s<=s n<=m)
  }
```
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
<details><summary>Agda</summary>

```agda
≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)
```
</details>

```tex
\func <=-total' (m n : Nat) : Total m n
  | 0, n => forward z<=n
  | suc m, 0 => flipped z<=n
  | suc m, suc n => helper (<=-total' m n)
  \where {
    \func helper {m n : Nat} (t : Total m n) : Total (suc m) (suc n) \elim t
      | forward m<=n => forward (s<=s m<=n)
      | flipped n<=m => flipped (s<=s n<=m)
  }
```
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
<details><summary>Agda</summary>

```agda
≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m       zero                      =  flipped z≤n
≤-total″ zero    (suc n)                   =  forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
...                        | forward m≤n   =  forward (s≤s m≤n)
...                        | flipped n≤m   =  flipped (s≤s n≤m)
```
</details>

```tex
\func <=-total'' (m n : Nat) : Total m n
  | m, 0 => flipped z<=n
  | 0, suc n => forward z<=n
  | suc m, suc n => \case <=-total'' m n \with {
    | forward m<=n => forward (s<=s m<=n)
    | flipped n<=m => flipped (s<=s n<=m)
  }
```
It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
<details><summary>Agda</summary>

```agda
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)
```
</details>

```tex
\func +-mono-right-<= (n p q : Nat) (p<=q : p <= q) : n + p <= n + q \elim n
  | 0 => p<=q
  | suc n => s<=s (+-mono-right-<= n p q p<=q)
```
The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc n`, in which case
  `suc n + p ≤ suc n + q` simplifies to `suc (n + p) ≤ suc (n + q)`.
  The inductive hypothesis `+-monoʳ-≤ n p q p≤q` establishes that
  `n + p ≤ n + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
<details><summary>Agda</summary>

```agda
+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n
```
</details>

```tex
\import Function.Meta ($)
\import Paths.Meta (rewrite)

\func +-mono-left-<= (m n p : Nat) (m<=n : m <= n) : m + p <= n + p =>
  rewrite (+-comm {m} {p}) $ rewrite (+-comm {n} {p}) $ +-mono-right-<= p m n m<=n
```
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results:
<details><summary>Agda</summary>

```agda
+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)
```
</details>

```tex
\func +-mono-<= (m n p q : Nat) (m<=n : m <= n) (p<=q : p <= q) : m + p <= n + q =>
  <=-trans (+-mono-left-<= m n p m<=n) (+-mono-right-<= n p q p<=q)
```
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\open Nat (*)
\open NatSemiring (*-comm)

\func *-mono-<= (m n p q : Nat) (m<=n : m <= n) (p<=q : p <= q) : m * p <= n * q =>
  <=-trans (*-mono-left-<= m n p m<=n) (*-mono-right-<= n p q p<=q)
  \where {
    \func *-mono-right-<= (n p q : Nat) (p<=q : p <= q) : n * p <= n * q \elim p, q, p<=q
      | 0, _, _ => z<=n
      | suc p, suc q, s<=s p<=q => +-mono-left-<= (n * p) (n * q) n (*-mono-right-<= n p q p<=q)

    \func *-mono-left-<= (m n p : Nat) (m<=n : m <= n) : m * p <= n * p =>
      rewrite (*-comm {m} {p}) $ rewrite (*-comm {n} {p}) $ *-mono-right-<= p m n m<=n
  }
```


## Strict inequality {name=strict-inequality}

We can define strict inequality similarly to inequality:
<details><summary>Agda</summary>

```agda
infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n
```
</details>

```tex
\data \infix 4 < Nat Nat \with
  | 0, suc n => z<s
  | suc m, suc n => s<s (m<n : m < n)
```
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation](/Negation/).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.

#### Exercise `<-trans` (recommended) {name=less-trans}

Show that strict inequality is transitive.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func <-trans {m n p : Nat} (m<n : m < n) (n<p : n < p) : m < p
  | {0}, {suc n}, {suc p}, _, _ => z<s
  | {suc m}, {suc n}, {suc p}, s<s m<n, s<s n<p => s<s (<-trans m<n n<p)
```

#### Exercise `trichotomy` (practice) {name=trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation](/Negation/).)

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\data Trichotomy (m n : Nat)
  | less (m < n)
  | eq (m = n)
  | greater (n < m)

\func <-trichotomy (m n : Nat) : Trichotomy m n
  | 0, 0 => eq idp
  | 0, suc n => less z<s
  | suc m, 0 => greater z<s
  | suc m, suc n => \case <-trichotomy m n \with {
    | less m<n => less (s<s m<n)
    | eq m=n => eq $ pmap suc m=n
    | greater m>n => greater (s<s m>n)
  }
```

#### Exercise `+-mono-<` (practice) {name=plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func +-mono-< (m n p q : Nat) (m<n : m < n) (p<q : p < q) : m + p < n + q =>
  <-trans (+-mono-left-< m n p m<n) (+-mono-right-< n p q p<q)
  \where {
    \func +-mono-right-< (n p q : Nat) (p<q : p < q) : n + p < n + q \elim n
      | 0 => p<q
      | suc n => s<s (+-mono-right-< n p q p<q)

    \func +-mono-left-< (m n p : Nat) (m<n : m < n) : m + p < n + p =>
      rewrite (+-comm {m} {p}) $ rewrite (+-comm {n} {p}) $ +-mono-right-< p m n m<n
  }
```

#### Exercise `≤-iff-<` (recommended) {name=leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func <=-implies-< {m n : Nat} (sm<=n : suc m <= n) : m < n
  | {0}, {suc n}, _ => z<s
  | {suc m}, {suc n}, s<=s sm<=n => s<s $ <=-implies-< sm<=n

\func <-implies-<= {m n : Nat} (m<n : m < n) : suc m <= n
  | {0}, {suc n}, z<s => s<=s z<=n
  | {suc m}, {suc n}, s<s m<n => s<=s $ <-implies-<= m<n
```

#### Exercise `<-trans-revisited` (practice) {name=less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func <-trans-revisited {m n p : Nat} (m<n : m < n) (n<p : n < p) : m < p =>
  \let
    | ssm<=n => s<=s $ <-implies-<= m<n
    | sn<=p => <-implies-<= n<p
    | ssm<=p => <=-trans ssm<=n sn<=p
    | sm<p => <=-implies-< ssm<=p
  \in <-decr-left sm<p
  \where {
    \func <-decr-left {m n : Nat} (sm<n : suc m < n) : m < n
      | {0}, {suc n}, _ => z<s
      | {suc m}, {suc n}, s<s sm<n => s<s $ <-decr-left sm<n
  }
```


## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
<details><summary>Agda</summary>

```agda
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
```
</details>

```tex
-- (!) Arend does not support overloaded constructors. If we used `suc` instead of `suc-odd` and `suc-even`,
-- we would need to refer to them as `even.suc` and `even.odd`.

\data even Nat : \Type \with
  | 0 => zero-even
  | suc n => suc-even (odd n)

\data odd Nat : \Type \with
  | suc n => suc-odd (even n)
```
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even:
<details><summary>Agda</summary>

```agda
e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)
```
</details>

```tex
\func e+e=e {m n : Nat} (em : even m) (en : even n) : even (m + n) \elim m, em
  | 0, zero-even => en
  | suc m, suc-even om => suc-even $ o+e=o om en

\func o+e=o {m n : Nat} (om : odd m) (en : even n) : odd (m + n) \elim m, om
  | suc m, suc-odd em => suc-odd $ e+e=e em en
```
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.

To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.

#### Exercise `o+o≡e` (stretch) {name=odd-plus-odd}

Show that the sum of two odd numbers is even.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func o+o=e {m n : Nat} (om : odd m) (on : odd n) : even (m + n)
  | {suc m}, {suc n}, suc-odd em, suc-odd en => suc-even $ suc-odd $ e+e=e em en
```

#### Exercise `Bin-predicates` (stretch) {name=Bin-predicates}

Recall that
Exercise [Bin](/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    ⟨⟩ I O I I
    ⟨⟩ O O I O I I

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can b
    ------------
    Can (inc b)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can b
    ---------------
    to (from b) ≡ b

(Hint: For each of these, you may first need to prove related
properties of `One`. Also, you may need to prove that
if `One b` then `1` is less or equal to the result of `from b`.)

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\import util.Arith.Bin
\open Bin
\import Function (o)
\import Paths (inv)

\data Can Bin \with
  | O <> => zero-can
  | b => one-can (One b)

\data One Bin \with
  | I <> => one
  | O b => O-one (One b)
  | I b => I-one (One b)

\func inc-Can {b : Bin} (cn : Can b) : Can (inc b)
  | {O <>}, zero-can => one-can one
  | one-can ob => one-can $ inc-One ob

\func inc-One {b : Bin} (ob : One b) : One $ inc b
  | {I <>}, one => O-one one
  | {O b}, O-one ob => I-one ob
  | {I b}, I-one ob => O-one $ inc-One ob

\func to-Can {n : Nat} : Can (to n)
  | {0} => zero-can
  | {suc n} => inc-Can to-Can

\func to-from-id-Can {b : Bin} (cb : Can b) : to (from b) = b
  | {O <>}, zero-can => idp
  | one-can ob => to-from-id-One ob

\func to-from-id-One {b : Bin} (ob : One b) : to (from b) = b
  | {I <>}, one => idp
  | {O b}, O-one ob => \case from b \as from-b, [1<=from-b] ob : 1 <= from-b, idp : from b = from-b \with {
    | suc n, s<=s _, from-b=suc-n =>
      rewrite from-b=suc-n $
      rewrite (inv $ to-from-id-One ob) $
      rewrite from-b=suc-n $
      lemma0
  }
  | {I b}, I-one ob => \case from b \as from-b, [1<=from-b] ob : 1 <= from-b, idp : from b = from-b \with {
    | suc n, s<=s _, from-b=suc-n =>
      rewrite from-b=suc-n $
      rewrite (inv $ to-from-id-One ob) $
      rewrite from-b=suc-n $
      lemma1
  }

  \where {
    \func [1<=from-b] {b : Bin} (ob : One b) : 1 <= from b
      | {I <>}, one => s<=s z<=n
      | {O b}, O-one ob => *-mono-<= 1 2 _ _ (s<=s z<=n) ([1<=from-b] ob)
      | {I b}, I-one ob => +-mono-<= 0 1 _ _ z<=n (*-mono-<= 1 2 _ _ (s<=s z<=n) ([1<=from-b] ob))

    \func lemma0 {n : Nat} : inc (inc (to (2 * n))) = O (inc (to n))
      | {0} => idp
      | {suc n} => pmap (inc o inc) lemma0

    \func lemma1 {n : Nat} : inc (inc (inc (to (2 * n)))) = I (inc (to n))
      | {0} => idp
      | {suc n} => pmap (inc o inc) lemma1
  }
```

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
<details><summary>Agda</summary>

```agda
import Data.Nat using (_≤_; z≤n; s≤s)
import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
                                  +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
```
</details>

```tex
\import Order.PartialOrder (<=, <=-reflexive, <=-transitive, <=-antisymmetric)
\import Order.LinearOrder (TotalOrder)
\open TotalOrder (totality)
\import Algebra.Ordered (LinearlyOrderedSemiring)
\open LinearlyOrderedSemiring (<=_+)
\import Arith.Nat (zero<=_, suc<=suc, NatSemiring)
```
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives](/Connectives/)),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.


## Unicode

This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
