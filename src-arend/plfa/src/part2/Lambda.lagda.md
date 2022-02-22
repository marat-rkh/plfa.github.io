---
title     : "Lambda: Introduction to Lambda Calculus"
layout    : page
prev      : /Lists/
permalink : /Lambda/
next      : /Properties/
---

```
module plfa.part2.Lambda where
```

The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It captures the key concept of
_functional abstraction_, which appears in pretty much every programming
language, in the form of either functions, procedures, or methods.
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations.
We will instead echo Plotkin's _Programmable Computable
Functions_ (PCF), and add operations on natural numbers and
recursive function definitions.

This chapter formalises the simply-typed lambda calculus, giving its
syntax, small-step semantics, and typing rules.  The next chapter
[Properties](/Properties/)
proves its main properties, including
progress and preservation.  Following chapters will look at a number
of variants of lambda calculus.

Be aware that the approach we take here is _not_ our recommended
approach to formalisation.  Using de Bruijn indices and
intrinsically-typed terms, as we will do in
Chapter [DeBruijn](/DeBruijn/),
leads to a more compact formulation.  Nonetheless, we begin with named
variables and extrinsically-typed terms,
partly because names are easier than indices to read,
and partly because the development is more traditional.

The development in this chapter was inspired by the corresponding
development in Chapter _Stlc_ of _Software Foundations_
(_Programming Language Foundations_).  We differ by
representing contexts explicitly (as lists pairing identifiers with
types) rather than as partial maps (which take identifiers to types),
which corresponds better to our subsequent development of DeBruijn
notation. We also differ by taking natural numbers as the base type
rather than booleans, allowing more sophisticated examples. In
particular, we will be able to show (twice!) that two plus two is
four.

## Imports

<details><summary>Agda</summary>

```agda
open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
```
</details>

```tex
\import Arith.Nat
\import Data.List
\import Equiv
\import Function.Meta ($)
\import Logic
\import Logic.Meta
\import Meta
\import Paths
\import Paths.Meta
\import Set
```

## Syntax of terms

Terms have seven constructs. Three are for the core lambda calculus:

  * Variables `` ` x ``
  * Abstractions `ƛ x ⇒ N`
  * Applications `L · M`

Three are for the naturals:

  * Zero `` `zero ``
  * Successor `` `suc M ``
  * Case `` case L [zero⇒ M |suc x ⇒ N ] ``

And one is for recursion:

  * Fixpoint `μ x ⇒ M`

Abstraction is also called _lambda abstraction_, and is the construct
from which the calculus takes its name.

With the exception of variables and fixpoints, each term
form either constructs a value of a given type (abstractions yield functions,
zero and successor yield natural numbers) or deconstructs it (applications use functions,
case terms use naturals). We will see this again when we come
to the rules for assigning types to terms, where constructors
correspond to introduction rules and deconstructors to eliminators.

Here is the syntax of terms in Backus-Naur Form (BNF):

    L, M, N  ::=
      ` x  |  ƛ x ⇒ N  |  L · M  |
      `zero  |  `suc M  |  case L [zero⇒ M |suc x ⇒ N ]  |
      μ x ⇒ M

And here it is formalised in Agda:
<details><summary>Agda</summary>

```agda
Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term
```
</details>

```tex
-- There is no String data type in Arend, so we will use natural numbers as identifiers.

\func Id => Nat

-- Here we import all identifiers that will be used in this chapter.

\import util.LambdaIdentifiers

\data Term
  | ref Id
  | lam Id Term
  | app \alias \infixl 7 ∙ Term Term
  | zero'
  | suc' Term
  | case (num : Term) (zeroCase : Term) (sucId : Id) (sucCase : Term)
  | fixpoint Id Term
```
We represent identifiers by strings.  We choose precedence so that
lambda abstraction and fixpoint bind least tightly, then application,
then successor, and tightest of all is the constructor for variables.
Case expressions are self-bracketing.


### Example terms

Here are some example terms: the natural number two,
a function that adds naturals,
and a term that computes two plus two:
<details><summary>Agda</summary>

```agda
two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]
```
</details>

```tex
\func two => suc' (suc' zero')

\func plus => fixpoint PLUS (lam M (lam N
    (case (ref M)
        (ref N)
        M (suc' (ref PLUS ∙ ref M ∙ ref N))
    )
))
```
The recursive definition of addition is similar to our original
definition of `_+_` for naturals, as given in
Chapter [Naturals](/Naturals/#plus).
Here variable "m" is bound twice, once in a lambda abstraction and once in
the successor branch of the case; the first use of "m" refers to
the former and the second to the latter.  Any use of "m" in the successor branch
must refer to the latter binding, and so we say that the latter binding _shadows_
the former.  Later we will confirm that two plus two is four, in other words that
the term

    plus · two · two

reduces to `` `suc `suc `suc `suc `zero ``.

As a second example, we use higher-order functions to represent
natural numbers.  In particular, the number _n_ is represented by a
function that accepts two arguments and applies the first _n_ times to the
second.  This is called the _Church representation_ of the
naturals.  Here are some example terms: the Church numeral two, a
function that adds Church numerals, a function to compute successor,
and a term that computes two plus two:
<details><summary>Agda</summary>

```agda
twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")
```
</details>

```tex
\func two-c => lam S (lam Z (ref S ∙ (ref S ∙ ref Z)))

\func plus-c => lam M (lam N (lam S (lam Z (ref M ∙ ref S ∙ (ref N ∙ ref S ∙ ref Z)))))

\func suc-c => lam N (suc' (ref N))
```
The Church numeral for two takes two arguments `s` and `z`
and applies `s` twice to `z`.
Addition takes two numerals `m` and `n`, a
function `s` and an argument `z`, and it uses `m` to apply `s` to the
result of using `n` to apply `s` to `z`; hence `s` is applied `m` plus
`n` times to `z`, yielding the Church numeral for the sum of `m` and
`n`.  For convenience, we define a function that computes successor.
To convert a Church numeral to the corresponding natural, we apply
it to the `sucᶜ` function and the natural number zero.
Again, later we will confirm that two plus two is four,
in other words that the term

    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

reduces to `` `suc `suc `suc `suc `zero ``.


#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.  Your definition may use `plus` as
defined earlier.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func mul => fixpoint MUL (lam M (lam N
    (case (ref M)
        zero'
        M (plus ∙ ref N ∙ (ref MUL ∙ ref M ∙ ref N))
    )
))
```


#### Exercise `mulᶜ` (practice)

Write out the definition of a lambda term that multiplies
two natural numbers represented as Church numerals. Your
definition may use `plusᶜ` as defined earlier (or may not
— there are nice definitions both ways).

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func zero-c => lam S (lam Z (ref Z))

\func mul-c1 => lam M (lam N (ref M ∙ (plus-c ∙ ref N) ∙ zero-c))

\func mul-c2 => lam M (lam N (lam S (lam Z (ref M ∙ (ref N ∙ ref S) ∙ ref Z))))
```


#### Exercise `primed` (stretch) {name=primed}

Some people find it annoying to write `` ` "x" `` instead of `x`.
We can make examples with lambda terms slightly easier to write
by adding the following definitions:
<details><summary>Agda</summary>

```agda
ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N  =  ƛ x ⇒ N
ƛ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]      =  ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N
μ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥
```
</details>

```tex
-- TODO
```
We intend to apply the function only when the first term is a variable, which we
indicate by postulating a term `impossible` of the empty type `⊥`.  If we use
C-c C-n to normalise the term

    ƛ′ two ⇒ two

Agda will return an answer warning us that the impossible has occurred:

    ⊥-elim (plfa.part2.Lambda.impossible (`` `suc (`suc `zero)) (`suc (`suc `zero)) ``)

While postulating the impossible is a useful technique, it must be
used with care, since such postulation could allow us to provide
evidence of _any_ proposition whatsoever, regardless of its truth.

The definition of `plus` can now be written as follows:
<details><summary>Agda</summary>

```agda
plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"
```
</details>

```tex
-- TODO
```
Write out the definition of multiplication in the same style.


### Formal vs informal

In informal presentation of formal semantics, one uses choice of
variable name to disambiguate and writes `x` rather than `` ` x ``
for a term that is a variable. Agda requires we distinguish.

Similarly, informal presentation often use the same notation for
function types, lambda abstraction, and function application in both
the _object language_ (the language one is describing) and the
_meta-language_ (the language in which the description is written),
trusting readers can use context to distinguish the two.  Agda is
not quite so forgiving, so here we use `ƛ x ⇒ N` and `L · M` for the
object language, as compared to `λ x → N` and `L M` in our
meta-language, Agda.


### Bound and free variables

In an abstraction `ƛ x ⇒ N` we call `x` the _bound_ variable
and `N` the _body_ of the abstraction.  A central feature
of lambda calculus is that consistent renaming of bound variables
leaves the meaning of a term unchanged.  Thus the five terms

* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
* `` ƛ "f" ⇒ ƛ "x" ⇒ ` "f" · (` "f" · ` "x") ``
* `` ƛ "sam" ⇒ ƛ "zelda" ⇒ ` "sam" · (` "sam" · ` "zelda") ``
* `` ƛ "z" ⇒ ƛ "s" ⇒ ` "z" · (` "z" · ` "s") ``
* `` ƛ "😇" ⇒ ƛ "😈" ⇒ ` "😇" · (` "😇" · ` "😈" ) ``

are all considered equivalent.  Following the convention introduced
by Haskell Curry, who used the Greek letter `α` (_alpha_) to label such rules,
this equivalence relation is called _alpha renaming_.

As we descend from a term into its subterms, variables
that are bound may become free.  Consider the following terms:

* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  has both `s` and `z` as bound variables.

* `` ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  has `z` bound and `s` free.

* `` ` "s" · (` "s" · ` "z") ``
  has both `s` and `z` as free variables.

We say that a term with no free variables is _closed_; otherwise it is
_open_.  Of the three terms above, the first is closed and the other
two are open.  We will focus on reduction of closed terms.

Different occurrences of a variable may be bound and free.
In the term

    (ƛ "x" ⇒ ` "x") · ` "x"

the inner occurrence of `x` is bound while the outer occurrence is free.
By alpha renaming, the term above is equivalent to

    (ƛ "y" ⇒ ` "y") · ` "x"

in which `y` is bound and `x` is free.  A common convention, called the
_Barendregt convention_, is to use alpha renaming to ensure that the bound
variables in a term are distinct from the free variables, which can
avoid confusions that may arise if bound and free variables have the
same names.

Case and recursion also introduce bound variables, which are also subject
to alpha renaming. In the term

    μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

notice that there are two binding occurrences of `m`, one in the first
line and one in the last line.  It is equivalent to the following term,

    μ "plus" ⇒ ƛ "x" ⇒ ƛ "y" ⇒
      case ` "x"
        [zero⇒ ` "y"
        |suc "x′" ⇒ `suc (` "plus" · ` "x′" · ` "y") ]

where the two binding occurrences corresponding to `m` now have distinct
names, `x` and `x′`.


## Values

A _value_ is a term that corresponds to an answer.
Thus, `` `suc `suc `suc `suc `zero `` is a value,
while `` plus · two · two `` is not.
Following convention, we treat all function abstractions
as values; thus, `` plus `` by itself is considered a value.

The predicate `Value M` holds if term `M` is a value:

<details><summary>Agda</summary>

```agda
data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)
```
</details>

```tex
\data Value (t : Term) \with
  | lam x N => V-lam
  | zero' => V-zero'
  | suc' V => V-suc' (Value V)
```

In what follows, we let `V` and `W` range over values.


### Formal vs informal

In informal presentations of formal semantics, using
`V` as the name of a metavariable is sufficient to
indicate that it is a value. In Agda, we must explicitly
invoke the `Value` predicate.

### Other approaches

An alternative is not to focus on closed terms,
to treat variables as values, and to treat
`ƛ x ⇒ N` as a value only if `N` is a value.
Indeed, this is how Agda normalises terms.
We consider this approach in
Chapter [Untyped](/Untyped/).


## Substitution

The heart of lambda calculus is the operation of
substituting one term for a variable in another term.
Substitution plays a key role in defining the
operational semantics of function application.
For instance, we have

      (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) · sucᶜ · `zero
    —→
      (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
    —→
      sucᶜ · (sucᶜ · `zero)

where we substitute `sucᶜ` for `` ` "s" `` and `` `zero `` for `` ` "z" ``
in the body of the function abstraction.

We write substitution as `N [ x := V ]`, meaning
"substitute term `V` for free occurrences of variable `x` in term `N`",
or, more compactly, "substitute `V` for `x` in `N`",
or equivalently, "in `N` replace `x` by `V`".
Substitution works if `V` is any closed term;
it need not be a value, but we use `V` since in fact we
usually substitute values.

Here are some examples:

* `` (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] `` yields
  `` ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z") ``.
* `` (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] `` yields
  `` sucᶜ · (sucᶜ · `zero) ``.
* `` (ƛ "x" ⇒ ` "y") [ "y" := `zero ] `` yields `` ƛ "x" ⇒ `zero ``.
* `` (ƛ "x" ⇒ ` "x") [ "x" := `zero ] `` yields `` ƛ "x" ⇒ ` "x" ``.
* `` (ƛ "y" ⇒ ` "y") [ "x" := `zero ] `` yields `` ƛ "y" ⇒ ` "y" ``.

In the last but one example, substituting `` `zero `` for `x` in
`` ƛ "x" ⇒ ` "x" `` does _not_ yield `` ƛ "x" ⇒ `zero ``,
since `x` is bound in the lambda abstraction.
The choice of bound names is irrelevant: both
`` ƛ "x" ⇒ ` "x" `` and `` ƛ "y" ⇒ ` "y" `` stand for the
identity function.  One way to think of this is that `x` within
the body of the abstraction stands for a _different_ variable than
`x` outside the abstraction, they just happen to have the same name.

We will give a definition of substitution that is only valid
when term substituted for the variable is closed. This is because
substitution by terms that are _not_ closed may require renaming
of bound variables. For example:

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero] `` should not yield <br/>
  `` (ƛ "x" ⇒ ` "x" · (` "x" · `zero)) ``.

Instead, we should rename the bound variable to avoid capture:

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ] `` should yield <br/>
  `` ƛ "x′" ⇒ ` "x′" · (` "x" · `zero) ``.

Here `x′` is a fresh variable distinct from `x`.
Formal definition of substitution with suitable renaming is considerably
more complex, so we avoid it by restricting to substitution by closed terms,
which will be adequate for our purposes.

Here is the formal definition of substitution by closed terms in Agda:

<details><summary>Agda</summary>

```agda
infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _          =  V
... | no  _          =  ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  ƛ x ⇒ N
... | no  _          =  ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]   =  L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]   =  `zero
(`suc M) [ y := V ]  =  `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  μ x ⇒ N
... | no  _          =  μ x ⇒ N [ y := V ]
```
</details>

```tex
\func subst \alias \infix 9 <<= (N : Term) (s : \Sigma Id Term) : Term
  | ref x, (y, V) => \case decideEq x y \with {
    | yes _ => V
    | no _ => ref x
  }
  | lam x N, (y, V) => \case decideEq x y \with {
    | yes _ => lam x N
    | no _ => lam x $ N <<= (y, V)
  }
  | ∙ L M, (y, V) => L <<= (y, V) ∙ M <<= (y, V)
  | zero', (y, V) => zero'
  | suc' M, (y, V) => suc' $ M <<= (y, V)
  | case L M x N, (y, V) => \case decideEq x y \with {
    | yes _ => case (L <<= (y, V)) (M <<= (y, V)) x N
    | no _ => case (L <<= (y, V)) (M <<= (y, V)) x (N <<= (y, V))
  }
  | fixpoint x N, (y, V) => \case decideEq x y \with {
    | yes _ => fixpoint x N
    | no _ => fixpoint x $ N <<= (y, V)
  }
```

Let's unpack the first three cases:

* For variables, we compare `y`, the substituted variable,
with `x`, the variable in the term. If they are the same,
we yield `V`, otherwise we yield `x` unchanged.

* For abstractions, we compare `y`, the substituted variable,
with `x`, the variable bound in the abstraction. If they are the same,
we yield the abstraction unchanged, otherwise we substitute inside the body.

* For application, we recursively substitute in the function
and the argument.

Case expressions and recursion also have bound variables that are
treated similarly to those in lambda abstractions.  Otherwise we
simply push substitution recursively into the subterms.


### Examples

Here is confirmation that the examples above are correct:

<details><summary>Agda</summary>

```agda
_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl
```
</details>

```tex
\func example-subst1 : lam Z (ref S ∙ (ref S ∙ ref Z)) <<= (S, suc-c) = lam Z (suc-c ∙ (suc-c ∙ ref Z)) => idp

\func example-subst2 : suc-c ∙ (suc-c ∙ ref Z) <<= (Z, zero') = suc-c ∙ (suc-c ∙ zero') => idp

\func example-subst3 : lam X (ref Y) <<= (Y, zero') = lam X zero' => idp

\func example-subst4 : lam X (ref X) <<= (X, zero') = lam X (ref X) => idp

\func example-subst5 : lam Y (ref Y) <<= (X, zero') = lam Y (ref Y) => idp
```


#### Quiz

What is the result of the following substitution?

    (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ]

1. `` (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) ``
2. `` (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ `zero)) ``
3. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x")) ``
4. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ `zero)) ``


#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a `with` clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\module SubstRefactoring \where {
  \func subst \alias \infix 9 <<= (N : Term) (s : \Sigma Id Term) : Term
    | ref x, (y, V) => \case decideEq x y \with {
      | yes _ => V
      | no _ => ref x
    }
    | lam x N, (y, V) => lam x $ N <<=-≠ (x, y, V)
    | ∙ L M, (y, V) => L <<= (y, V) ∙ M <<= (y, V)
    | zero', (y, V) => zero'
    | suc' M, (y, V) => suc' $ M <<= (y, V)
    | case L M x N, (y, V) => case (L <<= (y, V)) (M <<= (y, V)) x (N <<=-≠ (x, y, V))
    | fixpoint x N, (y, V) => fixpoint x $ N <<=-≠ (x, y, V)

  \func subst-if-not-equal \alias \infix 9 <<=-≠ (N : Term) (s : \Sigma Id Id Term) : Term \elim s
    | (x, y, V) => \case decideEq x y \with {
      | yes _ => N
      | no _ => N <<= (y, V)
    }
}
```


## Reduction

We give the reduction rules for call-by-value lambda calculus.  To
reduce an application, first we reduce the left-hand side until it
becomes a value (which must be an abstraction); then we reduce the
right-hand side until it becomes a value; and finally we substitute
the argument for the variable in the abstraction.

In an informal presentation of the operational semantics,
the rules for reduction of applications are written as follows:

    L —→ L′
    --------------- ξ-·₁
    L · M —→ L′ · M

    M —→ M′
    --------------- ξ-·₂
    V · M —→ V · M′

    ----------------------------- β-ƛ
    (ƛ x ⇒ N) · V —→ N [ x := V ]

The Agda version of the rules below will be similar, except that universal
quantifications are made explicit, and so are the predicates that indicate
which terms are values.

The rules break into two sorts. Compatibility rules direct us to
reduce some part of a term.  We give them names starting with the
Greek letter `ξ` (_xi_).  Once a term is sufficiently reduced, it will
consist of a constructor and a deconstructor, in our case `ƛ` and `·`,
which reduces directly.  We give them names starting with the Greek
letter `β` (_beta_) and such rules are traditionally called _beta rules_.

A bit of terminology: A term that matches the left-hand side of a
reduction rule is called a _redex_. In the redex `(ƛ x ⇒ N) · V`, we
may refer to `x` as the _formal parameter_ of the function, and `V`
as the _actual parameter_ of the function application.  Beta reduction
replaces the formal parameter by the actual parameter.

If a term is a value, then no reduction applies; conversely,
if a reduction applies to a term then it is not a value.
We will show in the next chapter that
this exhausts the possibilities: every well-typed term
either reduces or is a value.

For numbers, zero does not reduce and successor reduces the subterm.
A case expression reduces its argument to a number, and then chooses
the zero or successor branch as appropriate.  A fixpoint replaces
the bound variable by the entire fixpoint term; this is the one
case where we substitute by a term that is not a value.

Here are the rules formalised in Agda:

<details><summary>Agda</summary>

```agda
infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      ------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]
```
</details>

```tex
\data \infix 4 ~~> Term Term \with
  | app L M, app L' M' => xi-app-1 (L ~~> L') (M = M')
  | app V M, app V' M' => xi-app-2 (V = V') (Value V) (M ~~> M')
  | app (lam x N) V, S => beta-lam (Value V) (S = N <<= (x, V))
  | suc' M, suc' M' => xi-suc (M ~~> M')
  | case L M x N, case L' M' x' N' => xi-case (L ~~> L') (M = M') (x = x') (N = N')
  | case zero' M x N, M' => beta-zero (M = M')
  | case (suc' V) M x N, S => beta-suc (Value V) (S = N <<= (x, V))
  | fixpoint x M, S => beta-fixpoint (S = M <<= (x, fixpoint x M))
```

The reduction rules are carefully designed to ensure that subterms
of a term are reduced to values before the whole term is reduced.
This is referred to as _call-by-value_ reduction.

Further, we have arranged that subterms are reduced in a
left-to-right order.  This means that reduction is _deterministic_:
for any term, there is at most one other term to which it reduces.
Put another way, our reduction relation `—→` is in fact a function.

This style of explaining the meaning of terms is called
a _small-step operational semantics_.  If `M —→ N`, we say that
term `M` _reduces_ to term `N`, or equivalently,
term `M` _steps_ to term `N`.  Each compatibility rule has
another reduction rule in its premise; so a step always consists
of a beta rule, possibly adjusted by zero or more compatibility rules.


#### Quiz

What does the following term step to?

    (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???

1.  `` (ƛ "x" ⇒ ` "x") ``
2.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``
3.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``

What does the following term step to?

    (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???

1.  `` (ƛ "x" ⇒ ` "x") ``
2.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``
3.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``

What does the following term step to?  (Where `twoᶜ` and `sucᶜ` are as
defined above.)

    twoᶜ · sucᶜ · `zero  —→  ???

1.  `` sucᶜ · (sucᶜ · `zero) ``
2.  `` (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero ``
3.  `` `zero ``


## Reflexive and transitive closure

A single step is only part of the story. In general, we wish to repeatedly
step a closed term until it reduces to a value.  We do this by defining
the reflexive and transitive closure `—↠` of the step relation `—→`.

We define reflexive and transitive closure as a sequence of zero or
more steps of the underlying relation, along lines similar to that for
reasoning about chains of equalities in
Chapter [Equality](/Equality/):
<details><summary>Agda</summary>

```agda
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```
</details>

```tex
\data \infix 2 ~~>> (L : Term) (N : Term)
  | red-refl (L = N)
  | red-trans {M : Term} (L ~~> M) (M ~~>> N)

\func \fix 2 qed (a : Term) : a ~~>> a => red-refl idp

\func \infix 2 ==< (a : Term) {a' : Term} (p : a ~~> a') : a ~~> a' => p

\func \infixr 1 >== {a a' a'' : Term} (p : a ~~> a') (q : a' ~~>> a'') : a ~~>> a'' => red-trans p q
```
We can read this as follows:

* From term `M`, we can take no steps, giving a step of type `M —↠ M`.
  It is written `M ∎`.

* From term `L` we can take a single step of type `L —→ M` followed by zero
  or more steps of type `M —↠ N`, giving a step of type `L —↠ N`. It is
  written `L —→⟨ L—→M ⟩ M—↠N`, where `L—→M` and `M—↠N` are steps of the
  appropriate type.

The notation is chosen to allow us to lay out example reductions in an
appealing way, as we will see in the next section.

An alternative is to define reflexive and transitive closure directly,
as the smallest relation that includes `—→` and is also reflexive
and transitive.  We could do so as follows:
<details><summary>Agda</summary>

```agda
data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N
```
</details>

```tex
\data \infix 2 ~~>>' (L : Term) (N : Term)
  | red-step (L ~~> N)
  | red-refl' (L = N)
  | red-trans' {M : Term} (L ~~>>' M) (M ~~>>' N)
```
The three constructors specify, respectively, that `—↠′` includes `—→`
and is reflexive and transitive.  A good exercise is to show that
the two definitions are equivalent (indeed, one embeds in the other).

#### Exercise `—↠≲—↠′` (practice)

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
-- TODO
```

## Confluence

One important property a reduction relation might satisfy is
to be _confluent_.  If term `L` reduces to two other terms,
`M` and `N`, then both of these reduce to a common term `P`.
It can be illustrated as follows:

               L
              / \
             /   \
            /     \
           M       N
            \     /
             \   /
              \ /
               P

Here `L`, `M`, `N` are universally quantified while `P`
is existentially quantified.  If each line stands for zero
or more reduction steps, this is called confluence,
while if the top two lines stand for a single reduction
step and the bottom two stand for zero or more reduction
steps it is called the diamond property. In symbols:

<details><summary>Agda</summary>

```agda
postulate
  confluence : ∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

  diamond : ∀ {L M N}
    → ((L —→ M) × (L —→ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))
```
</details>

```tex
\func confluence {L M N : Term} (_ : L ~~>> M) (_ : L ~~>> N) : ∃ {P} (M ~~>> P) (N ~~>> P) => {?}

\func dimond {L M N : Term} (_ : L ~~> M) (_ : L ~~> N) : ∃ {P} (M ~~>> P) (N ~~>> P) => {?}
```

The reduction system studied in this chapter is deterministic.
In symbols:

<details><summary>Agda</summary>

```agda
postulate
  deterministic : ∀ {L M N}
    → L —→ M
    → L —→ N
      ------
    → M ≡ N
```
</details>

```tex
\func deterministics {L M N : Term} (_ : L ~~> M) (_ : L ~~> N) : M = N => {?}
```

It is easy to show that every deterministic relation satisfies
the diamond and confluence properties. Hence, all the reduction
systems studied in this text are trivially confluent.


## Examples

We start with a simple example. The Church numeral two applied to the
successor function and zero yields the natural number two:
<details><summary>Agda</summary>

```agda
_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
  ∎
```
</details>

```tex
\func example-two-suc-zero : two-c ∙ suc-c ∙ zero' ~~>> suc' (suc' zero') =>
  two-c ∙ suc-c ∙ zero' ==< xi-app-1 (beta-lam V-lam idp) idp >==
  lam Z (suc-c ∙ (suc-c ∙ ref Z)) ∙ zero' ==< beta-lam V-zero' idp >==
  suc-c ∙ (suc-c ∙ zero')  ==< xi-app-2 idp V-lam (beta-lam V-zero' idp) >==
  suc-c ∙ suc' zero'  ==< beta-lam (V-suc' V-zero') idp >==
  suc' (suc' zero') `qed
```

Here is a sample reduction demonstrating that two plus two is four:
<details><summary>Agda</summary>

```agda
_ : plus · two · two —↠ `suc `suc `suc `suc `zero
_ =
  begin
    plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
      case two [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
         · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ]
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ "n" ⇒
      case `suc `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (case `suc `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc `suc (plus · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc `suc ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc `suc (case `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎
```
</details>

```tex
-- TODO
```

And here is a similar sample reduction for Church numerals:
<details><summary>Agda</summary>

```agda
_ : plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero —↠ `suc `suc `suc `suc `zero
_ =
  begin
    (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (twoᶜ · ` "s" · ` "z")) · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (sucᶜ · `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (`suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc `suc `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · (`suc `suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎
```
</details>

```tex
-- TODO
```

In the next chapter, we will see how to compute such reduction sequences.


#### Exercise `plus-example` (practice)

Write out the reduction sequence demonstrating that one plus one is two.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func one => suc' zero'

-- TODO is there a tactic that fills in all these constructor chains?
--   Currently, everything between ==< and >== can be filled by calling "Replace with constructor" repeatedly.
--   And this is tedious.

\func example-one-plus-one : plus ∙ one ∙ one ~~>> suc' (suc' zero') =>
  plus ∙ one ∙ one ==< xi-app-1 (xi-app-1 (beta-fixpoint idp) idp) idp >==
  lam M (lam N
      (case (ref M)
          (ref N)
          M (suc' (plus ∙ ref M ∙ ref N))
      )
  ) ∙ one ∙ one ==< xi-app-1 (beta-lam (V-suc' V-zero') idp) idp >==
  lam N (case one
      (ref N)
      M (suc' (plus ∙ ref M ∙ ref N))
  ) ∙ one ==< beta-lam (V-suc' V-zero') idp >==
  case one
      one
      M (suc' (plus ∙ ref M ∙ one)) ==< beta-suc V-zero' idp >==
  suc' (plus ∙ zero' ∙ one) ==< xi-suc (xi-app-1 (xi-app-1 (beta-fixpoint idp) idp) idp) >==
  suc' (lam M (lam N
      (case (ref M)
          (ref N)
          M (suc' (plus ∙ ref M ∙ ref N))
      )
  ) ∙ zero' ∙ one) ==< xi-suc (xi-app-1 (beta-lam V-zero' idp) idp) >==
  suc' (lam N (case zero'
      (ref N)
      M (suc' (plus ∙ ref M ∙ ref N))
  ) ∙ one) ==< xi-suc (beta-lam (V-suc' V-zero') idp) >==
  suc' (case zero'
      one
      M (suc' (plus ∙ ref M ∙ one))) ==< xi-suc (beta-zero idp) >==
  suc' (suc' zero') `qed

\func one-c => lam S (lam Z (ref S ∙ ref Z))

\func example-one-plus-one-c : plus-c ∙ one-c ∙ one-c ∙ suc-c ∙ zero' ~~>> suc' (suc' zero') =>
  plus-c ∙ one-c ∙ one-c ∙ suc-c ∙ zero'
    ==< xi-app-1 (xi-app-1 (xi-app-1 (beta-lam V-lam idp) idp) idp) idp >==
  lam N (lam S (lam Z (one-c ∙ ref S ∙ (ref N ∙ ref S ∙ ref Z)))) ∙ one-c ∙ suc-c ∙ zero'
    ==< xi-app-1 (xi-app-1 (beta-lam V-lam idp) idp) idp >==
  lam S (lam Z (one-c ∙ ref S ∙ (one-c ∙ ref S ∙ ref Z))) ∙ suc-c ∙ zero'
    ==< xi-app-1 (beta-lam V-lam idp) idp >==
  lam Z (one-c ∙ suc-c ∙ (one-c ∙ suc-c ∙ ref Z)) ∙ zero'
    ==< beta-lam V-zero' idp >==
  one-c ∙ suc-c ∙ (one-c ∙ suc-c ∙ zero')
    ==< xi-app-1 (beta-lam V-lam idp) idp >==
  lam Z (suc-c ∙ ref Z) ∙ (one-c ∙ suc-c ∙ zero')
    ==< xi-app-2 idp V-lam (xi-app-1 (beta-lam V-lam idp) idp) >==
  lam Z (suc-c ∙ ref Z) ∙ (lam Z (suc-c ∙ ref Z) ∙ zero')
    ==< xi-app-2 idp V-lam (beta-lam V-zero' idp) >==
  lam Z (suc-c ∙ ref Z) ∙ (suc-c ∙ zero')
    ==< xi-app-2 idp V-lam (beta-lam V-zero' idp) >==
  lam Z (suc-c ∙ ref Z) ∙ suc' zero'
    ==< beta-lam (V-suc' V-zero') idp >==
  suc-c ∙ suc' zero'
    ==< beta-lam (V-suc' V-zero') idp >==
  suc' (suc' zero') `qed
```


## Syntax of types

We have just two types:

  * Functions, `A ⇒ B`
  * Naturals, `` `ℕ ``

As before, to avoid overlap we use variants of the names used by Agda.

Here is the syntax of types in BNF:

    A, B, C  ::=  A ⇒ B | `ℕ

And here it is formalised in Agda:

<details><summary>Agda</summary>

```agda
infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type
```
</details>

```tex
\data Type
  | arr \alias \infixr 7 ==> Type Type
  | Nat'
```

### Precedence

As in Agda, functions of two or more arguments are represented via
currying. This is made more convenient by declaring `_⇒_` to
associate to the right and `_·_` to associate to the left.
Thus:

* ``(`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ`` stands for ``((`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ))``.
* `plus · two · two` stands for `(plus · two) · two`.

### Quiz

* What is the type of the following term?

    `` ƛ "s" ⇒ ` "s" · (` "s"  · `zero) ``

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.

* What is the type of the following term?

    `` (ƛ "s" ⇒ ` "s" · (` "s"  · `zero)) · sucᶜ ``

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.


## Typing

### Contexts

While reduction considers only closed terms, typing must
consider terms with free variables.  To type a term,
we must first type its subterms, and in particular in the
body of an abstraction its bound variable may appear free.

A _context_ associates variables with types.  We let `Γ` and `Δ` range
over contexts.  We write `∅` for the empty context, and `Γ , x ⦂ A`
for the context that extends `Γ` by mapping variable `x` to type `A`.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ``

is the context that associates variable `` "s" `` with type `` `ℕ ⇒ `ℕ ``,
and variable `` "z" `` with type `` `ℕ ``.

Contexts are formalised as follows:

<details><summary>Agda</summary>

```agda
infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context
```
</details>

```tex
\data Context
  | nil-ctx \alias ∅
  | cons-ctx \alias \infixl 5 |: Context (\Sigma Id Type)
```


#### Exercise `Context-≃` (practice)

Show that `Context` is isomorphic to `List (Id × Type)`.
For instance, the isomorphism relates the context

    ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ

to the list

    [ ⟨ "z" , `ℕ ⟩ , ⟨ "s" , `ℕ ⇒ `ℕ ⟩ ]

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func Context-equiv-List : QEquiv {Context} {List (\Sigma Id Type)} \cowith
  | f (ctx : Context) : List (\Sigma Id Type) \with {
    | ∅ => nil
    | |: ctx b => b :: f ctx
  }
  | ret (xs : List (\Sigma Id Type)) : Context \with {
    | nil => ∅
    | :: x xs => ret xs |: x
  }
  | ret_f (ctx : Context) : ret (f ctx) = ctx \with {
    | ∅ => idp
    | |: ctx b => rewrite (ret_f ctx) idp
  }
  | f_sec (xs : List (\Sigma Id Type)) : f (ret xs) = xs \with {
    | nil => idp
    | :: x xs => rewrite (f_sec xs) idp
  }
```

### Lookup judgment

We have two forms of _judgment_.  The first is written

    Γ ∋ x ⦂ A

and indicates in context `Γ` that variable `x` has type `A`.
It is called _lookup_.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ ``

give us the types associated with variables `` "z" `` and `` "s" ``,
respectively.  The symbol `∋` (pronounced "ni", for "in"
backwards) is chosen because checking that `Γ ∋ x ⦂ A` is analogous to
checking whether `x ⦂ A` appears in a list corresponding to `Γ`.

If two variables in a context have the same name, then lookup
should return the most recently bound variable, which _shadows_
the other variables.  For example,

* `` ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ∋ "x" ⦂ `ℕ ``.

Here `` "x" ⦂ `ℕ ⇒ `ℕ `` is shadowed by `` "x" ⦂ `ℕ ``.

Lookup is formalised as follows:
<details><summary>Agda</summary>

```agda
infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A
```
</details>

```tex
\data InContext \alias \infix 4 ∋ Context (\Sigma Id Type) \with
  | |: G (x, A), (x', A') => Here (x' = x) (A' = A)
  | |: G (y, B), (x, A) => There (x /= y) (G ∋ (x, A))
```

The constructors `Z` and `S` correspond roughly to the constructors
`here` and `there` for the element-of relation `_∈_` on lists.
Constructor `S` takes an additional parameter, which ensures that
when we look up a variable that it is not _shadowed_ by another
variable with the same name to its left in the list.

It can be rather tedious to use the `S` constructor, as you have to provide
proofs that `x ≢ y` each time. For example:

<details><summary>Agda</summary>

```agda
_ : ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "y" ⦂ `ℕ , "z" ⦂ `ℕ ∋ "x" ⦂ `ℕ ⇒ `ℕ
_ = S (λ()) (S (λ()) Z)
```
</details>

```tex
\func example-InContext : ∅ |: (X, Nat' ==> Nat') |: (Y, Nat') |: (Z, Nat') ∋ (X, Nat' ==> Nat') =>
  There (\case __) (There (\case __) (Here idp idp))
```

Instead, we'll use a "smart constructor", which uses [proof by reflection](/Decidable/#proof-by-reflection) to check the inequality while type checking:

<details><summary>Agda</summary>

```agda
S′ : ∀ {Γ x y A B}
   → {x≢y : False (x ≟ y)}
   → Γ ∋ x ⦂ A
     ------------------
   → Γ , y ⦂ B ∋ x ⦂ A

S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x
```
</details>

```tex
\meta here => Here idp idp

\meta there p => There (\case __) p
```

### Typing judgment

The second judgment is written

    Γ ⊢ M ⦂ A

and indicates in context `Γ` that term `M` has type `A`.
Context `Γ` provides types for all the free variables in `M`.
For example:

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" ⦂ `ℕ ⇒ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · ` "z" ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · (` "s" · ` "z") ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  `ℕ ⇒ `ℕ ``
* `` ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ``

Typing is formalised as follows:
<details><summary>Agda</summary>

```agda
infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ M ⦂ A
```
</details>

```tex
\data HasType \alias \infix 4 ⊢ Context (\Sigma Term Type) \with
  | G, (ref x, A) => in-ctx-axiom (G ∋ (x, A))
  | G, (lam x N, arr A B) => arr-intro (G |: (x, A) ⊢ (N, B))
  | G, (app L M, B) => arr-elim {A : Type} (G ⊢ (L, A ==> B)) (G ⊢ (M, A))
  | G, (zero', Nat') => nat-intro1
  | G, (suc' M, Nat') => nat-intro2 (G ⊢ (M, Nat'))
  | G, (case L M x N, A) => nat-elim (G ⊢ (L, Nat')) (G ⊢ (M, A)) (G |: (x, Nat') ⊢ (N, A))
  | G, (fixpoint x M, A) => fixpoint-axiom (G |: (x, A) ⊢ (M, A))
```

Each type rule is named after the constructor for the
corresponding term.

Most of the rules have a second name, derived from a convention in
logic, whereby the rule is named after the type connective that it
concerns; rules to introduce and to eliminate each connective are
labeled `-I` and `-E`, respectively. As we read the rules from top to
bottom, introduction and elimination rules do what they say on the
tin: the first _introduces_ a formula for the connective, which
appears in the conclusion but not in the premises; while the second
_eliminates_ a formula for the connective, which appears in a premise
but not in the conclusion. An introduction rule describes how to
construct a value of the type (abstractions yield functions, successor
and zero yield naturals), while an elimination rule describes how to
deconstruct a value of the given type (applications use functions,
case expressions use naturals).

Note also the three places (in `⊢ƛ`, `⊢case`, and `⊢μ`) where the
context is extended with `x` and an appropriate type, corresponding to
the three places where a bound variable is introduced.

The rules are deterministic, in that at most one rule applies to every term.


### Example type derivations {name=derivation}

Type derivations correspond to trees. In informal notation, here
is a type derivation for the Church numeral two,

                            ∋s                     ∋z
                            ------------------ ⊢`  -------------- ⊢`
    ∋s                      Γ₂ ⊢ ` "s" ⦂ A ⇒ A     Γ₂ ⊢ ` "z" ⦂ A
    ------------------ ⊢`   ------------------------------------- _·_
    Γ₂ ⊢ ` "s" ⦂ A ⇒ A      Γ₂ ⊢ ` "s" · ` "z" ⦂ A
    ---------------------------------------------- _·_
    Γ₂ ⊢ ` "s" · (` "s" · ` "z") ⦂ A
    -------------------------------------------- ⊢ƛ
    Γ₁ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ A ⇒ A
    ------------------------------------------------------------- ⊢ƛ
    Γ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ (A ⇒ A) ⇒ A ⇒ A

where `∋s` and `∋z` abbreviate the two derivations,

                 ---------------- Z
    "s" ≢ "z"    Γ₁ ∋ "s" ⦂ A ⇒ A
    ----------------------------- S       ------------- Z
    Γ₂ ∋ "s" ⦂ A ⇒ A                       Γ₂ ∋ "z" ⦂ A

and where `Γ₁ = Γ , "s" ⦂ A ⇒ A` and `Γ₂ = Γ , "s" ⦂ A ⇒ A , "z" ⦂ A`.
The typing derivation is valid for any `Γ` and `A`, for instance,
we might take `Γ` to be `∅` and `A` to be `` `ℕ ``.

Here is the above typing derivation formalised in Agda:
<details><summary>Agda</summary>

```agda
Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋s · (⊢` ∋s · ⊢` ∋z)))
  where
  ∋s = S′ Z
  ∋z = Z
```
</details>

```tex
\func Ch (A : Type) : Type => (A ==> A) ==> A ==> A

\func has-type-two-c {G : Context} {A : Type} : G ⊢ (two-c, Ch A) =>
  run {
    arr-intro,
    arr-intro,
    arr-elim (in-ctx-axiom (there here)) (arr-elim (in-ctx-axiom (there here)) (in-ctx-axiom here))
  }
```

Here are the typings corresponding to computing two plus two:
<details><summary>Agda</summary>

```agda
⊢two : ∀ {Γ} → Γ ⊢ two ⦂ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢` ∋n)
         (⊢suc (⊢` ∋+ · ⊢` ∋m′ · ⊢` ∋n′)))))
  where
  ∋+  = S′ (S′ (S′ Z))
  ∋m  = S′ Z
  ∋n  = Z
  ∋m′ = Z
  ∋n′ = S′ Z

⊢2+2 : ∅ ⊢ plus · two · two ⦂ `ℕ
⊢2+2 = ⊢plus · ⊢two · ⊢two
```
</details>

```tex
\func has-type-two {G : Context} : G ⊢ (two, Nat') => nat-intro2 (nat-intro2 nat-intro1)

\func has-type-plus {G : Context} : G ⊢ (plus, Nat' ==> Nat' ==> Nat') =>
  run {
    fixpoint-axiom,
    arr-intro,
    arr-intro,
    nat-elim
        (in-ctx-axiom (there here))
        (in-ctx-axiom here)
        (nat-intro2 (arr-elim
            (arr-elim
                (in-ctx-axiom (there $ there $ there here))
                (in-ctx-axiom here))
            (in-ctx-axiom (there here))
        ))
  }

\func has-type-2+2 : ∅ ⊢ (plus ∙ two ∙ two, Nat') =>
  arr-elim (arr-elim has-type-plus has-type-two) has-type-two
```
In contrast to our earlier examples, here we have typed `two` and `plus`
in an arbitrary context rather than the empty context; this makes it easy
to use them inside other binding contexts as well as at the top level.
Here the two lookup judgments `∋m` and `∋m′` refer to two different
bindings of variables named `"m"`.  In contrast, the two judgments `∋n` and
`∋n′` both refer to the same binding of `"n"` but accessed in different
contexts, the first where `"n"` is the last binding in the context, and
the second after `"m"` is bound in the successor branch of the case.

And here are typings for the remainder of the Church example:
<details><summary>Agda</summary>

```agda
⊢plusᶜ : ∀ {Γ A} → Γ  ⊢ plusᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢plusᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢` ∋m · ⊢` ∋s · (⊢` ∋n · ⊢` ∋s · ⊢` ∋z)))))
  where
  ∋m = S′ (S′ (S′ Z))
  ∋n = S′ (S′ Z)
  ∋s = S′ Z
  ∋z = Z

⊢sucᶜ : ∀ {Γ} → Γ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` ∋n))
  where
  ∋n = Z

⊢2+2ᶜ : ∅ ⊢ plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ⦂ `ℕ
⊢2+2ᶜ = ⊢plusᶜ · ⊢twoᶜ · ⊢twoᶜ · ⊢sucᶜ · ⊢zero
```
</details>

```tex
\func has-type-plus-c {G : Context} {A : Type} : G ⊢ (plus-c, Ch A ==> Ch A ==> Ch A) =>
  run {
    arr-intro,
    arr-intro,
    arr-intro,
    arr-intro,
    arr-elim
        (arr-elim
            (in-ctx-axiom (there (there (there here))))
            (in-ctx-axiom (there here)))
        (arr-elim
            (arr-elim
                (in-ctx-axiom (there (there here)))
                (in-ctx-axiom (there here)))
            (in-ctx-axiom here))
  }

\func has-type-suc-c {G : Context} : G ⊢ (suc-c, Nat' ==> Nat') =>
  run {
    arr-intro,
    nat-intro2,
    in-ctx-axiom here
  }

\func has-type-2+2-c : ∅ ⊢ (plus-c ∙ two-c ∙ two-c ∙ suc-c ∙ zero', Nat') =>
  arr-elim (arr-elim (arr-elim (arr-elim has-type-plus-c has-type-two-c) has-type-two-c) has-type-suc-c) nat-intro1
```

### Interaction with Agda

Construction of a type derivation may be done interactively.
Start with the declaration:

    ⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
    ⊢sucᶜ = ?

Typing C-c C-l causes Agda to create a hole and tell us its expected type:

    ⊢sucᶜ = { }0
    ?0 : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `sucᶜ` is `ƛ`, which is typed using `⊢ƛ`. The
`⊢ƛ` rule in turn takes one argument, which Agda leaves as a hole:

    ⊢sucᶜ = ⊢ƛ { }1
    ?1 : ∅ , "n" ⦂ `ℕ ⊢ `suc ` "n" ⦂ `ℕ

We can fill in the hole by typing C-c C-r again:

    ⊢sucᶜ = ⊢ƛ (⊢suc { }2)
    ?2 : ∅ , "n" ⦂ `ℕ ⊢ ` "n" ⦂ `ℕ

And again:

    ⊢sucᶜ = ⊢ƛ (⊢suc (⊢` { }3))
    ?3 : ∅ , "n" ⦂ `ℕ ∋ "n" ⦂ `ℕ

A further attempt with C-c C-r yields the message:

    Don't know which constructor to introduce of Z or S

We can fill in `Z` by hand. If we type C-c C-space, Agda will confirm we are done:

    ⊢sucᶜ = ⊢ƛ (⊢suc (⊢` Z))

The entire process can be automated using Agsy, invoked with C-c C-a.

Chapter [Inference](/Inference/)
will show how to use Agda to compute type derivations directly.


### Lookup is injective

The lookup relation `Γ ∋ x ⦂ A` is injective, in that for each `Γ` and `x`
there is at most one `A` such that the judgment holds:
<details><summary>Agda</summary>

```agda
∋-injective : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-injective Z        Z          =  refl
∋-injective Z        (S x≢ _)   =  ⊥-elim (x≢ refl)
∋-injective (S x≢ _) Z          =  ⊥-elim (x≢ refl)
∋-injective (S _ ∋x) (S _ ∋x′)  =  ∋-injective ∋x ∋x′
```
</details>

```tex
\func InContext-injective {G : Context} {x : Id} {A B : Type} (_ : G ∋ (x, A)) (_ : G ∋ (x, B)) : A = B
  | {cons-ctx G ((_, C))}, Here _ A=C, Here _ B=C => A=C *> inv B=C
  | {cons-ctx G ((y, _))}, Here x=y _, There x/=y _ => contradiction
  | {cons-ctx G ((y, _))}, There x/=y _, Here x=y _ => contradiction
  | {cons-ctx G ((y, C))}, There _ p1, There _ p2 => InContext-injective p1 p2
```

The typing relation `Γ ⊢ M ⦂ A` is not injective. For example, in any `Γ`
the term `` ƛ "x" ⇒ ` "x" `` has type `A ⇒ A` for any type `A`.

### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term
`` `zero · `suc `zero ``.  It cannot be typed, because doing so
requires that the first term in the application is both a natural and
a function:

<details><summary>Agda</summary>

```agda
nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ⦂ A)
nope₁ (() · _)
```
</details>

```tex
\func nope1 {A : Type} : Not (∅ ⊢ (zero' ∙ suc' zero', A)) => \case __ \with {
  | arr-elim () _
}
```

As a second example, here is a formal proof that it is not possible to
type `` ƛ "x" ⇒ ` "x" · ` "x" ``. It cannot be typed, because
doing so requires types `A` and `B` such that `A ⇒ B ≡ A`:

<details><summary>Agda</summary>

```agda
nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ⦂ A)
nope₂ (⊢ƛ (⊢` ∋x · ⊢` ∋x′))  =  contradiction (∋-injective ∋x ∋x′)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()
```
</details>

```tex
\func nope2 {A : Type} (_ : ∅ ⊢ (lam X (ref X ∙ ref X), A)) : Empty
  | {arr A1 A2}, arr-intro (arr-elim (in-ctx-axiom h1) (in-ctx-axiom h2)) =>
    arr-type-/=-type $ InContext-injective h1 h2
  \where {
    -- TODO Arend cannot infer this
    \func arr-type-/=-type {A B : Type} (p : A ==> B = A) : Empty => {?}
  }
```


#### Quiz

For each of the following, give a type `A` for which it is derivable,
or explain why there is no such `A`.

1. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "y" · ` "x" ⦂ A ``
2. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "x" · ` "y" ⦂ A ``
3. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ⦂ A ``

For each of the following, give types `A`, `B`, and `C` for which it is derivable,
or explain why there are no such types.

1. `` ∅ , "x" ⦂ A ⊢ ` "x" · ` "x" ⦂ B ``
2. `` ∅ , "x" ⦂ A , "y" ⦂ B ⊢ ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ⦂ C ``


#### Exercise `⊢mul` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well typed.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func has-type-mul {G : Context} : G ⊢ (mul, Nat' ==> Nat' ==> Nat') =>
  run {
    fixpoint-axiom,
    arr-intro,
    arr-intro,
    nat-elim
        (in-ctx-axiom (there here))
        nat-intro1
        (arr-elim
            (arr-elim has-type-plus (in-ctx-axiom (there here)))
            (arr-elim
                (arr-elim
                    (in-ctx-axiom (there (there (there here))))
                    (in-ctx-axiom here))
                (in-ctx-axiom (there here))))
  }
```


#### Exercise `⊢mulᶜ` (practice)

Using the term `mulᶜ` you defined earlier, write out the derivation
showing that it is well typed.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func has-type-mul-c {G : Context} {A : Type} : G ⊢ (mul-c2, Ch A ==> Ch A ==> Ch A) =>
  run {
    arr-intro,
    arr-intro,
    arr-intro,
    arr-intro,
    arr-elim
        (arr-elim
            (in-ctx-axiom (there $ there $ there here))
            (arr-elim
                (in-ctx-axiom (there $ there here))
                (in-ctx-axiom (there here))))
        (in-ctx-axiom here)
  }
```



## Unicode

This chapter uses the following unicode:

    ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
    ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    ·  U+00B7  MIDDLE DOT (\cdot)
    ≟  U+225F  QUESTIONED EQUAL TO (\?=)
    —  U+2014  EM DASH (\em)
    ↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
    ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
    β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
    Γ  U+0393  GREEK CAPITAL LETTER GAMMA (\GG or \Gamma)
    ≠  U+2260  NOT EQUAL TO (\=n or \ne)
    ∋  U+220B  CONTAINS AS MEMBER (\ni)
    ∅  U+2205  EMPTY SET (\0)
    ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
    ⦂  U+2982  Z NOTATION TYPE COLON (\:)
    😇  U+1F607  SMILING FACE WITH HALO
    😈  U+1F608  SMILING FACE WITH HORNS

We compose reduction `—→` from an em dash `—` and an arrow `→`.
Similarly for reflexive and transitive closure `—↠`.
