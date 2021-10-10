---
title     : "Lists: Lists and higher-order functions"
layout    : page
prev      : /Decidable/
permalink : /Lists/
next      : /Lambda/
---

```
module plfa.part1.Lists where
```

This chapter discusses the list data type.  It gives further examples
of many of the techniques we have developed so far, and provides
examples of polymorphic types and higher-order functions.

## Imports

<details><summary>Agda</summary>

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_)
```
</details>

```tex
\import Paths (inv, *>, pmap, ==<, >==, qed)
\import part1.Connectives (prod)
\import util.Paths (=<>=)
\import Data.Bool (Bool, true, false, So, and, or, not)
\open Nat (+, *)
\import Order.PartialOrder (<=)
\import Arith.Nat (-', NatSemiring, suc<=suc, zero<=_)
\import Set (Dec, yes, no)
\import util.Logic (~, &&)
\import Function (o)
\import util.Equiv (=~)
\import Logic (TruncP, absurd, inP, propExt, truncP)
```


## Lists

Lists are defined in Agda as follows:
<details><summary>Agda</summary>

```agda
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_
```
</details>

```tex
\data List (A : \Type)
  | []
  | \infixr 5 :: A (List A)
```
Let's unpack this definition. If `A` is a set, then `List A` is a set.
The next two lines tell us that `[]` (pronounced _nil_) is a list of
type `A` (often called the _empty_ list), and that `_∷_` (pronounced
_cons_, short for _constructor_) takes a value of type `A` and a value
of type `List A` and returns a value of type `List A`.  Operator `_∷_`
has precedence level 5 and associates to the right.

For example,
<details><summary>Agda</summary>

```agda
_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []
```
</details>

```tex
\func example-list : List Nat => 0 :: 1 :: 2 :: []
```
denotes the list of the first three natural numbers.  Since `_∷_`
associates to the right, the term parses as `0 ∷ (1 ∷ (2 ∷ []))`.
Here `0` is the first element of the list, called the _head_,
and `1 ∷ (2 ∷ [])` is a list of the remaining elements, called the
_tail_. A list is a strange beast: it has a head and a tail,
nothing in between, and the tail is itself another list!

As we've seen, parameterised types can be translated to
indexed types. The definition above is equivalent to the following:
<details><summary>Agda</summary>

```agda
data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A
```
</details>

```tex
-- Same in Arend.
```
Each constructor takes the parameter as an implicit argument.
Thus, our example list could also be written:
<details><summary>Agda</summary>

```agda
_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))
```
</details>

```tex
\func example-list' : List Nat => (::) {Nat} 0 ((::) {Nat} 1 ((::) {Nat} 2 ([] {Nat})))
```
where here we have provided the implicit parameters explicitly.

Including the pragma:

    {-# BUILTIN LIST List #-}

tells Agda that the type `List` corresponds to the Haskell type
list, and the constructors `[]` and `_∷_` correspond to nil and
cons respectively, allowing a more efficient representation of lists.


## List syntax

We can write lists more conveniently by introducing the following definitions:
<details><summary>Agda</summary>

```agda
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
```
</details>

```tex
-- There is no such thing in Arend.
```
This is our first use of pattern declarations.  For instance,
the third line tells us that `[ x , y , z ]` is equivalent to
`x ∷ y ∷ z ∷ []`, and permits the former to appear either in
a pattern on the left-hand side of an equation, or a term
on the right-hand side of an equation.


## Append

Our first function on lists is written `_++_` and pronounced
_append_:

<details><summary>Agda</summary>

```agda
infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)
```
</details>

```tex
\func \infixr 5 ++ {A : \Type} (xs ys : List A) : List A \elim xs
  | [] => ys
  | :: x xs => x :: (xs ++ ys)
```
The type `A` is an implicit argument to append, making it a _polymorphic_
function (one that can be used at many types). A list appended to the empty list
yields the list itself. A list appended to a non-empty list yields a list with
the head the same as the head of the non-empty list, and a tail the same as the
other list appended to tail of the non-empty list.

Here is an example, showing how to compute the result
of appending two lists:
<details><summary>Agda</summary>

```agda
_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎
```
</details>

```tex
\func example-append : 0 :: 1 :: 2 :: [] ++ 3 :: 4 :: [] = 0 :: 1 :: 2 :: 3 :: 4 :: [] =>
  0 :: 1 :: 2 :: [] ++ 3 :: 4 :: [] =<>=
  0 :: (1 :: 2 :: [] ++ 3 :: 4 :: []) =<>=
  0 :: 1 :: (2 :: [] ++ 3 :: 4 :: []) =<>=
  0 :: 1 :: 2 :: ([] ++ 3 :: 4 :: []) =<>=
  0 :: 1 :: 2 :: 3 :: 4 :: [] `qed
```
Appending two lists requires time linear in the
number of elements in the first list.


## Reasoning about append

We can reason about lists in much the same way that we reason
about numbers.  Here is the proof that append is associative:
<details><summary>Agda</summary>

```agda
++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎
```
</details>

```tex
\func ++-assoc {A : \Type} (xs ys zs : List A) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) \elim xs
  | [] =>
    ([] ++ ys) ++ zs =<>=
    ys ++ zs =<>=
    [] ++ (ys ++ zs) `qed
  | :: x xs =>
    (x :: xs ++ ys) ++ zs =<>=
    x :: (xs ++ ys) ++ zs =<>=
    x :: ((xs ++ ys) ++ zs) ==< pmap (x ::) (++-assoc xs ys zs) >==
    x :: xs ++ (ys ++ zs) `qed
```
The proof is by induction on the first argument. The base case instantiates
to `[]`, and follows by straightforward computation.
The inductive case instantiates to `x ∷ xs`,
and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated by a recursive
invocation of the proof, in this case `++-assoc xs ys zs`.

Recall that Agda supports [sections](/Induction/#sections).
Applying `cong (x ∷_)` promotes the inductive hypothesis:

    (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

to the equality:

    x ∷ ((xs ++ ys) ++ zs) ≡ x ∷ (xs ++ (ys ++ zs))

which is needed in the proof.

It is also easy to show that `[]` is a left and right identity for `_++_`.
That it is a left identity is immediate from the definition:
<details><summary>Agda</summary>

```agda
++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎
```
</details>

```tex
\func ++-identity-l {A : \Type} (xs : List A) : [] ++ xs = xs =>
  [] ++ xs =<>= xs `qed
```
That it is a right identity follows by simple induction:
<details><summary>Agda</summary>

```agda
++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎
```
</details>

```tex
\func ++-identity-r {A : \Type} (xs : List A) : xs ++ [] = xs
  | [] => [] ++ [] =<>= [] `qed
  | :: x xs =>
    (x :: xs) ++ [] =<>=
    x :: (xs ++ []) ==< pmap (x ::) (++-identity-r xs) >==
    x :: xs `qed
```
As we will see later,
these three properties establish that `_++_` and `[]` form
a _monoid_ over lists.

## Length

Our next function finds the length of a list:
<details><summary>Agda</summary>

```agda
length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  suc (length xs)
```
</details>

```tex
\func length {A : \Type} (_ : List A) : Nat
  | [] => 0
  | :: x xs => suc (length xs)
```
Again, it takes an implicit parameter `A`.
The length of the empty list is zero.
The length of a non-empty list
is one greater than the length of the tail of the list.

Here is an example showing how to compute the length of a list:
<details><summary>Agda</summary>

```agda
_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎
```
</details>

```tex
\func example-length : length (0 :: 1 :: 2 :: []) = 3 =>
  length (0 :: 1 :: 2 :: []) =<>=
  suc (length (1 :: 2 :: [])) =<>=
  suc (suc (length (2 :: []))) =<>=
  suc (suc (suc (length {Nat} []))) =<>=
  suc (suc (suc 0)) `qed
```
Computing the length of a list requires time
linear in the number of elements in the list.

In the second-to-last line, we cannot write simply `length []` but
must instead write `length {ℕ} []`.  Since `[]` has no elements, Agda
has insufficient information to infer the implicit parameter.


## Reasoning about length

The length of one list appended to another is the
sum of the lengths of the lists:
<details><summary>Agda</summary>

```agda
length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎
```
</details>

```tex
\func length-++ {A : \Type} (xs ys : List A) : length (xs ++ ys) = length xs + length ys \elim xs
  | [] =>
    length ([] ++ ys) =<>=
    length ys =<>=
    (length {Nat} []) + length ys `qed
  | :: x xs =>
    length ((x :: xs) ++ ys) =<>=
    suc (length (xs ++ ys)) ==< pmap suc (length-++ xs ys) >==
    suc (length xs + length ys) =<>=
    length (x :: xs) + length ys `qed
```
The proof is by induction on the first argument. The base case
instantiates to `[]`, and follows by straightforward computation.  As
before, Agda cannot infer the implicit type parameter to `length`, and
it must be given explicitly.  The inductive case instantiates to
`x ∷ xs`, and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated
by a recursive invocation of the proof, in this case `length-++ xs ys`,
and it is promoted by the congruence `cong suc`.


## Reverse

Using append, it is easy to formulate a function to reverse a list:
<details><summary>Agda</summary>

```agda
reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]
```
</details>

```tex
\func reverse {A : \Type} (_ : List A) : List A
  | [] => []
  | :: x xs => reverse xs ++ x :: []
```
The reverse of the empty list is the empty list.
The reverse of a non-empty list
is the reverse of its tail appended to a unit list
containing its head.

Here is an example showing how to reverse a list:
<details><summary>Agda</summary>

```agda
_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎
```
</details>

```tex
\func example-reverse : reverse (0 :: 1 :: 2 :: []) = 2 :: 1 :: 0 :: [] =>
  reverse (0 :: 1 :: 2 :: []) =<>=
  reverse (1 :: 2 :: []) ++ 0 :: [] =<>=
  (reverse (2 :: []) ++ 1 :: []) ++ 0 :: [] =<>=
  ((reverse [] ++ 2 :: []) ++ 1 :: []) ++ 0 :: [] =<>=
  (([] ++ 2 :: []) ++ 1 :: []) ++ 0 :: [] =<>=
  (([] ++ 2 :: []) ++ 1 :: []) ++ 0 :: [] =<>=
  (2 :: [] ++ 1 :: []) ++ 0 :: [] =<>=
  2 :: ([] ++ 1 :: []) ++ 0 :: [] =<>=
  (2 :: 1 :: []) ++ 0 :: [] =<>=
  2 :: (1 :: [] ++ 0 :: []) =<>=
  2 :: 1 :: ([] ++ 0 :: []) =<>=
  2 :: 1 :: 0 :: [] =<>=
  2 :: 1 :: 0 :: [] `qed

\import Paths.Meta (rewrite)
\import Meta (later)

\func reverse-++-distrib {A : \Type} (xs ys : List A) : reverse (xs ++ ys) = reverse ys ++ reverse xs \elim xs
  | [] => rewrite (++-identity-r (reverse ys)) idp
  | :: x xs =>
    reverse (xs ++ ys) ++ x :: [] ==< later rewrite (reverse-++-distrib xs ys) idp >==
    (reverse ys ++ reverse xs) ++ x :: [] ==< ++-assoc _ _ _ >==
    reverse ys ++ reverse xs ++ x :: [] `qed

\func reverse-involutive {A : \Type} (xs : List A)  : reverse (reverse xs) = xs
  | [] => idp
  | :: x xs =>
    reverse (reverse xs ++ x :: []) ==< reverse-++-distrib _ _ >==
    reverse (x :: []) ++ reverse (reverse xs) =<>=
    x :: reverse (reverse xs) ==< later rewrite (reverse-involutive _) idp >==
    x :: xs `qed
```
Reversing a list in this way takes time _quadratic_ in the length of
the list. This is because reverse ends up appending lists of lengths
`1`, `2`, up to `n - 1`, where `n` is the length of the list being
reversed, append takes time linear in the length of the first
list, and the sum of the numbers up to `n - 1` is `n * (n - 1) / 2`.
(We will validate that last fact in an exercise later in this chapter.)

#### Exercise `reverse-++-distrib` (recommended)

Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first:

    reverse (xs ++ ys) ≡ reverse ys ++ reverse xs


#### Exercise `reverse-involutive` (recommended)

A function is an _involution_ if when applied twice it acts
as the identity function.  Show that reverse is an involution:

    reverse (reverse xs) ≡ xs


## Faster reverse

The definition above, while easy to reason about, is less efficient than
one might expect since it takes time quadratic in the length of the list.
The idea is that we generalise reverse to take an additional argument:
<details><summary>Agda</summary>

```agda
shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)
```
</details>

```tex
\func shunt {A : \Type} (xs ys : List A) : List A \elim xs
  | [] => ys
  | :: x xs => shunt xs (x :: ys)
```
The definition is by recursion on the first argument. The second argument
actually becomes _larger_, but this is not a problem because the argument
on which we recurse becomes _smaller_.

Shunt is related to reverse as follows:
<details><summary>Agda</summary>

```agda
shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎
```
</details>

```tex
\func shunt-reverse {A : \Type} (xs ys : List A) : shunt xs ys = reverse xs ++ ys \elim xs
  | [] =>
    shunt [] ys =<>=
    ys =<>=
    reverse [] ++ ys `qed
  | :: x xs =>
    shunt (x :: xs) ys =<>=
    shunt xs (x :: ys) ==< shunt-reverse _ _ >==
    reverse xs ++ (x :: ys) =<>=
    reverse xs ++ (x :: [] ++ ys) ==< inv (++-assoc _ _ _) >==
    (reverse xs ++ x :: []) ++ ys =<>=
    reverse (x :: xs) ++ ys `qed
```
The proof is by induction on the first argument.
The base case instantiates to `[]`, and follows by straightforward computation.
The inductive case instantiates to `x ∷ xs` and follows by the inductive
hypothesis and associativity of append.  When we invoke the inductive hypothesis,
the second argument actually becomes *larger*, but this is not a problem because
the argument on which we induct becomes *smaller*.

Generalising on an auxiliary argument, which becomes larger as the argument on
which we recurse or induct becomes smaller, is a common trick. It belongs in
your quiver of arrows, ready to slay the right problem.

Having defined shunt be generalisation, it is now easy to respecialise to
give a more efficient definition of reverse:
<details><summary>Agda</summary>

```agda
reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []
```
</details>

```tex
\func reverse' {A : \Type} (xs : List A) : List A => shunt xs []
```

Given our previous lemma, it is straightforward to show
the two definitions equivalent:
<details><summary>Agda</summary>

```agda
reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎
```
</details>

```tex
\func reverses {A : \Type} (xs : List A) : reverse' xs = reverse xs =>
  reverse' xs =<>=
  shunt xs [] ==< shunt-reverse xs [] >==
  reverse xs ++ [] ==< ++-identity-r _ >==
  reverse xs `qed
```

Here is an example showing fast reverse of the list `[ 0 , 1 , 2 ]`:
<details><summary>Agda</summary>

```agda
_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎
```
</details>

```tex
\func example-reverse' : reverse' (0 :: 1 :: 2 :: []) = 2 :: 1 :: 0 :: [] =>
  reverse' (0 :: 1 :: 2 :: []) =<>=
  shunt (0 :: 1 :: 2 :: []) [] =<>=
  shunt (1 :: 2 :: []) (0 :: []) =<>=
  shunt (2 :: []) (1 :: 0 :: []) =<>=
  shunt [] (2 :: 1 :: 0 :: []) =<>=
  2 :: 1 :: 0 :: [] `qed
```
Now the time to reverse a list is linear in the length of the list.

## Map {name=Map}

Map applies a function to every element of a list to generate a corresponding list.
Map is an example of a _higher-order function_, one which takes a function as an
argument or returns a function as a result:
<details><summary>Agda</summary>

```agda
map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs
```
</details>

```tex
\func map {A B : \Type} (f : A -> B) (xs : List A) : List B \elim xs
  | [] => []
  | :: x xs => f x :: map f xs
```
Map of the empty list is the empty list.
Map of a non-empty list yields a list
with head the same as the function applied to the head of the given list,
and tail the same as map of the function applied to the tail of the given list.

Here is an example showing how to use map to increment every element of a list:
<details><summary>Agda</summary>

```agda
_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ map suc (1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ≡⟨⟩
    1 ∷ 2 ∷ 3 ∷ []
  ∎
```
</details>

```tex
\func example-map-suc : map suc (0 :: 1 :: 2 :: []) = 1 :: 2 :: 3 :: [] =>
  map suc (0 :: 1 :: 2 :: []) =<>=
  suc 0 :: map suc (1 :: 2 :: []) =<>=
  suc 0 :: suc 1 :: map suc (2 :: []) =<>=
  suc 0 :: suc 1 :: suc 2 :: map suc [] =<>=
  suc 0 :: suc 1 :: suc 2 :: [] =<>=
  1 :: 2 :: 3 :: [] `qed
```
Map requires time linear in the length of the list.

It is often convenient to exploit currying by applying
map to a function to yield a new function, and at a later
point applying the resulting function:
<details><summary>Agda</summary>

```agda
sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎
```
</details>

```tex
\func sucs => map suc

\func example-sucs : sucs (0 :: 1 :: 2 :: []) = 1 :: 2 :: 3 :: [] =>
  sucs (0 :: 1 :: 2 :: []) =<>=
  map suc (0 :: 1 :: 2 :: []) =<>=
  1 :: 2 :: 3 :: [] `qed
```

Any type that is parameterised on another type, such as lists, has a
corresponding map, which accepts a function and returns a function
from the type parameterised on the domain of the function to the type
parameterised on the range of the function. Further, a type that is
parameterised on _n_ types will have a map that is parameterised on
_n_ functions.


#### Exercise `map-compose` (practice)

Prove that the map of a composition is equal to the composition of two maps:

    map (g ∘ f) ≡ map g ∘ map f

The last step of the proof requires extensionality.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\import util.Function (extensionality)

\func map-compose {A B C : \Type} (f : A -> B) (g : B -> C) : map (g o f) = map g o map f =>
  extensionality {_} {_} {map (g o f)} {map g o map f} (lemma1 _ _ __)
  \where {
    \func lemma1 {A B C : \Type} (f : A -> B) (g : B -> C) (xs : List A) : map (g o f) xs = (map g o map f) xs \elim xs
      | [] => idp
      | :: x xs =>
        (g o f) x :: map (g o f) xs ==< later rewrite lemma1 idp >==
        (g o f) x :: (map g o map f) xs =<>=
        map g (f x :: map f xs) =<>=
        map g ((map f) (x :: xs)) =<>=
        (map g o map f) (x :: xs) `qed
  }
```

#### Exercise `map-++-distribute` (practice)

Prove the following relationship between map and append:

    map f (xs ++ ys) ≡ map f xs ++ map f ys

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func map-++-distribute {A B : \Type} (f : A -> B) (xs ys : List A) : map f (xs ++ ys) = map f xs ++ map f ys \elim xs
  | [] => idp
  | :: x xs => pmap (f x ::) (map-++-distribute _ _ _)
```

#### Exercise `map-Tree` (practice)

Define a type of trees with leaves of type `A` and internal
nodes of type `B`:
<details><summary>Agda</summary>

```agda
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B
```
</details>

```tex
\data Tree (A B : \Type)
  | leaf A
  | node (Tree A B) B (Tree A B)
```
Define a suitable map operator over trees:

    map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func map-Tree {A B C D : \Type} (f : A -> C) (g : B -> D) (tr : Tree A B) : Tree C D \elim tr
  | leaf a => leaf (f a)
  | node tr1 b tr2 => node (map-Tree f g tr1) (g b) (map-Tree f g tr2)
```

## Fold {name=Fold}

Fold takes an operator and a value, and uses the operator to combine
each of the elements of the list, taking the given value as the result
for the empty list:
<details><summary>Agda</summary>

```agda
foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs
```
</details>

```tex
\func foldr {A B : \Type} (** : A -> B -> B) (e : B) (xs : List A) : B \elim xs
  | [] => e
  | :: x xs => x `**` foldr ** e xs
```
Fold of the empty list is the given value.
Fold of a non-empty list uses the operator to combine
the head of the list and the fold of the tail of the list.

Here is an example showing how to use fold to find the sum of a list:
<details><summary>Agda</summary>

```agda
_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎
```
</details>

```tex
\func example-foldr : foldr (+) 0 (1 :: 2 :: 3 :: 4 :: []) = 10 =>
  foldr (+) 0 (1 :: 2 :: 3 :: 4 :: []) =<>=
  1 + foldr (+) 0 (2 :: 3 :: 4 :: []) =<>=
  1 + (2 + foldr (+) 0 (3 :: 4 :: [])) =<>=
  1 + (2 + (3 + foldr (+) 0 (4 :: []))) =<>=
  1 + (2 + (3 + (4 + foldr (+) 0 []))) =<>=
  1 + (2 + (3 + (4 + 0))) `qed
```
Here we have an instance of `foldr` where `A` and `B` are both `ℕ`.
Fold requires time linear in the length of the list.

It is often convenient to exploit currying by applying
fold to an operator and a value to yield a new function,
and at a later point applying the resulting function:
<details><summary>Agda</summary>

```agda
sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎
```
</details>

```tex
\func sum : List Nat -> Nat => foldr (+) 0

\func example-sum : sum (1 :: 2 :: 3 :: 4 :: []) = 10 =>
  sum (1 :: 2 :: 3 :: 4 :: []) =<>=
  foldr (+) 0 (1 :: 2 :: 3 :: 4 :: []) =<>=
  10 `qed
```

Just as the list type has two constructors, `[]` and `_∷_`,
so the fold function takes two arguments, `e` and `_⊗_`
(in addition to the list argument).
In general, a data type with _n_ constructors will have
a corresponding fold function that takes _n_ arguments.

As another example, observe that

    foldr _∷_ [] xs ≡ xs

Here, if `xs` is of type `List A`, then we see we have an instance of
`foldr` where `A` is `A` and `B` is `List A`.  It follows that

    xs ++ ys ≡ foldr _∷_ ys xs

Demonstrating both these equations is left as an exercise.


#### Exercise `product` (recommended)

Use fold to define a function to find the product of a list of numbers.
For example:

    product [ 1 , 2 , 3 , 4 ] ≡ 24

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func product : List Nat -> Nat => foldr (*) 1
```

#### Exercise `foldr-++` (recommended)

Show that fold and append are related as follows:

    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func foldr-++ {A B : \Type} (** : A -> B -> B) (e : B) (xs ys : List A)
  : foldr ** e (xs ++ ys) = foldr ** (foldr ** e ys) xs \elim xs
  | [] => idp
  | :: x xs => pmap (x `**`) (foldr-++ _ _ _ _)
```

#### Exercise `foldr-∷` (practice)

Show

    foldr _∷_ [] xs ≡ xs

Show as a consequence of `foldr-++` above that

    xs ++ ys ≡ foldr _∷_ ys xs


<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func foldr-:: {A : \Type} (xs ys : List A) : xs ++ ys = foldr (::) ys xs \elim xs
  | [] => idp
  | :: x xs => pmap (x `::`) (foldr-:: _ _)
```

#### Exercise `map-is-foldr` (practice)

Show that map can be defined using fold:

    map f ≡ foldr (λ x xs → f x ∷ xs) []

The proof requires extensionality.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func map-is-foldr {A B : \Type} (f : A -> B) (xs : List A) : map f = foldr (\lam x xs => f x :: xs) [] =>
  extensionality (lemma _ xs __)
  \where {
    \func lemma {A B : \Type} (f : A -> B) (xs : List A) (ys : List A)
      : map f ys = (foldr (\lam x xs => f x :: xs) []) ys \elim ys
      | [] => idp
      | :: y ys => pmap (f y ::) (lemma _ xs _)
  }
```

#### Exercise `fold-Tree` (practice)

Define a suitable fold function for the type of trees given earlier:

    fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C


<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func fold-Tree {A B C : \Type} (f : A -> C) (g : C -> B -> C -> C) (tr : Tree A B) : C \elim tr
  | leaf a => f a
  | node tr1 b tr2 => g (fold-Tree f g tr1) b (fold-Tree f g tr2)
```

#### Exercise `map-is-fold-Tree` (practice)

Demonstrate an analogue of `map-is-foldr` for the type of trees.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\import Paths (pmap2)

\func map-is-foldr-Tree {A B C D : \Type} (f : A -> C) (g : B -> D)
  : map-Tree f g = fold-Tree (\lam a => leaf (f a)) (\lam tr1 b tr2 => node tr1 (g b) tr2) =>
  extensionality (lemma _ _)
  \where {
    \func lemma {A B C D : \Type} (f : A -> C) (g : B -> D) (tr : Tree A B)
      : map-Tree f g tr = fold-Tree (\lam a => leaf (f a)) (\lam tr1 b tr2 => node tr1 (g b) tr2) tr \elim tr
      | leaf a => idp
      | node tr1 b tr2 => pmap2 (\lam tr1 tr2 => node tr1 (g b) tr2) (lemma _ _ _) (lemma _ _ _)
  }
```

#### Exercise `sum-downFrom` (stretch)

Define a function that counts down as follows:
<details><summary>Agda</summary>

```agda
downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n
```
</details>

```tex
\func downFrom (_ : Nat) : List Nat
  | 0 => []
  | suc n => n :: downFrom n
```
For example:
<details><summary>Agda</summary>

```agda
_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl
```
</details>

```tex
\func example-downFrom : downFrom 3 = 2 :: 1 :: 0 :: [] => idp

\import part1.Induction (-'+assoc)
\open -'+assoc ([n-'0=n])
\import Function.Meta ($)
\import Arith.Nat (-'id)
\import Algebra.Meta (equation)

\func sum-downFrom (n : Nat) : sum (downFrom n) * 2 = n * (n -' 1)
  | 0 => idp
  | suc n =>
    (n + sum (downFrom n)) + (n + sum (downFrom n)) =<>=
    (n + sum (downFrom n)) * 2 ==< NatSemiring.rdistr {n} {_} {2} >==
    n * 2 + sum (downFrom n) * 2 ==< pmap (n * 2 +) (sum-downFrom n) >==
    n * 2 + n * (n -' 1) ==< pmap (n * 2 +) NatSemiring.*-comm >==
    n * 2 + (n -' 1) * n ==< lemma >==
    suc n * n ==< pmap (suc n *) (inv $ [n-'0=n] _) >==
    suc n * (n -' 0) `qed
  \where {
    \func lemma {n : Nat} : n + n + (n -' 1) * n = (n + 1) * n
      | {0} => idp
      | {suc n} =>
        n + n + ((n -' 0) * n + (n -' 0)) + 2 ==< later rewrite ([n-'0=n] n) idp >==
        n + n + (n * n + (n -' 0)) + 2 ==< later rewrite ([n-'0=n] n) idp >==
        (n + n) + (n * n + n) + 2 ==< equation >==
        (n + 2) * n + n + 2 `qed
  }
```
Prove that the sum of the numbers `(n - 1) + ⋯ + 0` is
equal to `n * (n ∸ 1) / 2`:

    sum (downFrom n) * 2 ≡ n * (n ∸ 1)


## Monoids

Typically when we use a fold the operator is associative and the
value is a left and right identity for the operator, meaning that the
operator and the value form a _monoid_.

We can define a monoid as a suitable record type:
<details><summary>Agda</summary>

```agda
record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid
```
</details>

```tex
\class IsMonoid (A : \Type)
  | \infixl 7 ** \alias \infixl 7 ⊗ : A -> A -> A
  | e : A
  | assoc (x y z : A) : (x ⊗ y) ** z = x ⊗ (y ⊗ z)
  | identity-left (x : A) : e ⊗ x = x
  | identity-right (x : A) : x ⊗ e = x
```

As examples, sum and zero, multiplication and one, and append and the empty
list, are all examples of monoids:
<details><summary>Agda</summary>

```agda
+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }
```
</details>

```tex
\func +-monoid : IsMonoid _ (+) 0 \cowith
  | assoc => NatSemiring.+-assoc {__} {__} {__}
  | identity-left => NatSemiring.zro-left {__}
  | identity-right => NatSemiring.zro-right {__}

\func *-monoid : IsMonoid _ (*) 1 \cowith
  | assoc => NatSemiring.*-assoc {__} {__} {__}
  | identity-left => NatSemiring.ide-left {__}
  | identity-right => NatSemiring.ide-right {__}

\func ++-monoid {A : \Type} : IsMonoid (List A) (++) [] \cowith
  | assoc => ++-assoc
  | identity-left => ++-identity-l
  | identity-right => ++-identity-r
```

If `_⊗_` and `e` form a monoid, then we can re-express fold on the
same operator and an arbitrary value:
<details><summary>Agda</summary>

```agda
foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎
```
</details>

```tex
\func foldr-monoid {M : IsMonoid} (xs : List M) (y : M) : foldr (⊗) y xs = foldr (⊗) e xs `⊗` y \elim xs
  | [] =>
    foldr (⊗) y [] =<>=
    y ==< inv (identity-left y) >==
    e ⊗ y =<>=
    foldr (⊗) e [] ⊗ y `qed
  | :: x xs =>
    foldr (⊗) y (x :: xs) =<>=
    x ⊗ (foldr (⊗) y xs) ==< pmap (x ⊗) (foldr-monoid xs y) >==
    x ⊗ (foldr (⊗) e xs ⊗ y) ==< inv (assoc x (foldr (⊗) e xs) y) >==
    (x ⊗ foldr (⊗) e xs) ⊗ y =<>=
    foldr (⊗) e (x :: xs) ⊗ y `qed
```

In a previous exercise we showed the following.
```
postulate
  foldr-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) (xs ys : List A) →
    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
```

As a consequence, using a previous exercise, we have the following:
<details><summary>Agda</summary>

```agda
foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎
```
</details>

```tex
\func foldr-monoid-++ {M : IsMonoid} (xs ys : List M) : foldr (⊗) e (xs ++ ys) = foldr (⊗) e xs ⊗ foldr (⊗) e ys =>
  foldr (⊗) e (xs ++ ys) ==< foldr-++ (⊗) e xs ys >==
  foldr (⊗) (foldr (⊗) e ys) xs ==< foldr-monoid xs (foldr (⊗) e ys) >==
  foldr (⊗) e xs ⊗ foldr (⊗) e ys `qed
```

#### Exercise `foldl` (practice)

Define a function `foldl` which is analogous to `foldr`, but where
operations associate to the left rather than the right.  For example:

    foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
    foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func foldl {A B : \Type} (** : B -> A -> B) (e : B) (xs : List A) : B \elim xs
  | [] => e
  | :: x xs => foldl (**) (e `**` x) xs

\func example-foldl : foldl (+) 0 (1 :: 2 :: 3 :: 4 :: []) = 10 =>
  foldl (+) 0 (1 :: 2 :: 3 :: 4 :: []) =<>=
  foldl (+) (0 + 1) (2 :: 3 :: 4 :: []) =<>=
  foldl (+) ((0 + 1) + 2) (3 :: 4 :: []) =<>=
  foldl (+) (((0 + 1) + 2) + 3) (4 :: []) =<>=
  foldl (+) ((((0 + 1) + 2) + 3) + 4) [] =<>=
  (((0 + 1) + 2) + 3) + 4 `qed
```


#### Exercise `foldr-monoid-foldl` (practice)

Show that if `_⊗_` and `e` form a monoid, then `foldr _⊗_ e` and
`foldl _⊗_ e` always compute the same result.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func foldr-monoid-foldl {M : IsMonoid} (xs : List M) : foldr (⊗) e xs = foldl (⊗) e xs
  | [] => idp
  | :: x xs =>
    x ⊗ foldr (⊗) e xs ==< pmap (x ⊗) (foldr-monoid-foldl xs) >==
    x ⊗ foldl (⊗) e xs ==< inv (foldl-monoid xs x) >==
    foldl (⊗) x xs ==< later rewrite {1} (inv (identity-left x)) idp >==
    foldl (⊗) (e ⊗ x) xs `qed
  \where {
    \func foldl-monoid {M : IsMonoid} (xs : List M) (y : M) : foldl (**) y xs = y ** foldl (**) e xs \elim xs
      | [] => inv $ identity-right y
      | :: x xs =>
        foldl (⊗) (y ⊗ x) xs ==< foldl-monoid _ _ >==
        (y ⊗ x) ⊗ foldl (⊗) e xs ==< assoc y x _ >==
        y ⊗ (x ⊗ foldl (⊗) e xs) ==< pmap (y ⊗) (inv $ foldl-monoid _ _) >==
        y ⊗ foldl (⊗) x xs ==< later rewrite {1} (inv $ identity-left x) idp >==
        y ⊗ foldl (⊗) (e ⊗ x) xs `qed
  }
```


## All {name=All}

We can also define predicates over lists. Two of the most important
are `All` and `Any`.

Predicate `All P` holds if predicate `P` is satisfied by every element of a list:
<details><summary>Agda</summary>

```agda
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)
```
</details>

```tex
\data All {A : \Type} (P : A -> \Prop) (xs : List A) \elim xs
  | [] => []all \alias []∀
  | :: x xs => \infixr 7 ::all \alias \infixr 7 ::∀ (P x) (All P xs)
```
The type has two constructors, reusing the names of the same constructors for lists.
The first asserts that `P` holds for every element of the empty list.
The second asserts that if `P` holds of the head of a list and for every
element of the tail of a list, then `P` holds for every element of the list.
Agda uses types to disambiguate whether the constructor is building
a list or evidence that `All P` holds.

For example, `All (_≤ 2)` holds of a list where every element is less
than or equal to two.  Recall that `z≤n` proves `zero ≤ n` for any
`n`, and that if `m≤n` proves `m ≤ n` then `s≤s m≤n` proves `suc m ≤
suc n`, for any `m` and `n`:
<details><summary>Agda</summary>

```agda
_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []
```
</details>

```tex
\func example-all : All (__ <= 2) (0 :: 1 :: 2 :: []) =>
  zero<=_ ::∀ suc<=suc zero<=_ ::∀ suc<=suc (suc<=suc zero<=_) ::∀ []∀
```
Here `_∷_` and `[]` are the constructors of `All P` rather than of `List A`.
The three items are proofs of `0 ≤ 2`, `1 ≤ 2`, and `2 ≤ 2`, respectively.

(One might wonder whether a pattern such as `[_,_,_]` can be used to
construct values of type `All` as well as type `List`, since both use
the same constructors. Indeed it can, so long as both types are in
scope when the pattern is declared.  That's not the case here, since
`List` is defined before `[_,_,_]`, but `All` is defined later.)


## Any

Predicate `Any P` holds if predicate `P` is satisfied by some element of a list:
<details><summary>Agda</summary>

```agda
data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)
```
</details>

```tex
\truncated \data Any {A : \Type} (P : A -> \Prop) (xs : List A) : \Prop \elim xs
  | :: x xs => here (P x)
  | :: x xs => there (Any P xs)
```
The first constructor provides evidence that the head of the list
satisfies `P`, while the second provides evidence that some element of
the tail of the list satisfies `P`.  For example, we can define list
membership as follows:
<details><summary>Agda</summary>

```agda
infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)
```
</details>

```tex
\func in-list \alias \infix 4 ∈ {A : \Type} (x : A) (xs : List A) : \Prop => Any (\lam a => TruncP (x = a)) xs

\func not-in-list \alias \infix 4 ∉ {A : \Type} (x : A) (xs : List A) : \Prop => ~ (x ∈ xs)
```
For example, zero is an element of the list `[ 0 , 1 , 0 , 2 ]`.  Indeed, we can demonstrate
this fact in two different ways, corresponding to the two different
occurrences of zero in the list, as the first element and as the third element:
<details><summary>Agda</summary>

```agda
_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))
```
</details>

```tex
\func example-in-list1 : 0 ∈ (0 :: 1 :: 0 :: 2 :: []) => here (inP idp)

\func example-in-list2 : 0 ∈ (0 :: 1 :: 0 :: 2 :: []) => there (there (here (inP idp)))
```
Further, we can demonstrate that three is not in the list, because
any possible proof that it is in the list leads to contradiction:
<details><summary>Agda</summary>

```agda
not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))
```
</details>

```tex
\func example-not-in-list : 3 ∉ (0 :: 1 :: 0 :: 2 :: []) => \lam p => \case p \with {
  | here (inP ())
  | there (here (inP ()))
  | there (there (here (inP ())))
  | there (there (there (here (inP ()))))
  | there (there (there (there ())))
}
```
The five occurrences of `()` attest to the fact that there is no
possible evidence for `3 ≡ 0`, `3 ≡ 1`, `3 ≡ 0`, `3 ≡ 2`, and
`3 ∈ []`, respectively.

## All and append

A predicate holds for every element of one list appended to another if and
only if it holds for every element of both lists:
<details><summary>Agda</summary>

```agda
All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩
```
</details>

```tex
\func All-++-= {A : \Type} {P : A -> \Prop} (xs ys : List A) : All P (xs ++ ys) = All P xs && All P ys =>
  propExt ([=>] xs ys) ([<=] xs ys)
  \where {
    \func [=>] {A : \Type} {P : A -> \Prop} (xs ys : List A) (all : All P (xs ++ ys)) : All P xs && All P ys \elim xs, all
      | [], Pys => prod []∀ Pys
      | :: x xs, ::∀ Px Pxs++ys => \case [=>] xs ys Pxs++ys \with {
        | prod Pxs Pys => prod (Px ::∀ Pxs) Pys
      }

    \func [<=] {A : \Type} {P : A -> \Prop} (xs ys : List A) (both : All P xs && All P ys) : All P (xs ++ ys) \elim xs, both
      | [], prod []∀ Pys => Pys
      | :: x xs, prod (::∀ Px Pxs) Pys => Px ::∀ [<=] xs ys (prod Pxs Pys)
  }
```

#### Exercise `Any-++-⇔` (recommended)

Prove a result similar to `All-++-⇔`, but with `Any` in place of `All`, and a suitable
replacement for `_×_`.  As a consequence, demonstrate an equivalence relating
`_∈_` and `_++_`.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\import Logic (||, byLeft, byRight)

\func Any-++-= {A : \Type} {P : A -> \Prop} (xs ys : List A) : Any P (xs ++ ys) = Any P xs || Any P ys =>
  propExt ([=>] xs ys) ([<=] xs ys)
  \where {
    \func [=>] {A : \Type} {P : A -> \Prop} (xs ys : List A) (any : Any P (xs ++ ys)) : Any P xs || Any P ys \elim xs, any
      | [], Pys => byRight Pys
      | :: _ xs, here Px => byLeft (here Px)
      | :: _ xs, there any => \case [=>] xs ys any \with {
        | byLeft Pxs => byLeft (there Pxs)
        | byRight Pys => byRight Pys
      }

    \func [<=] {A : \Type} {P : A -> \Prop} (xs ys : List A) (or : Any P xs || Any P ys) : Any P (xs ++ ys) \elim xs, or
      | [], byLeft ()
      | [], byRight Pys => Pys
      | :: _ xs, byLeft (here Px) => here Px
      | :: _ xs, byLeft (there Pxs) => there ([<=] xs ys (byLeft Pxs))
      | :: _ xs, byRight Pys => there ([<=] xs ys (byRight Pys))
  }

\func in-list-++-= {A : \Type} (a : A) (xs ys : List A) : a ∈ (xs ++ ys) = a ∈ xs || a ∈ ys => Any-++-= xs ys
```

#### Exercise `All-++-≃` (stretch)

Show that the equivalence `All-++-⇔` can be extended to an isomorphism.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
-- (!) We have already proven a more general case (equality) because our All is a proposition.
```

#### Exercise `¬Any⇔All¬` (recommended)

Show that `Any` and `All` satisfy a version of De Morgan's Law:

    (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs

(Can you see why it is important that here `_∘_` is generalised
to arbitrary levels, as described in the section on
[universe polymorphism](/Equality/#unipoly)?)

Do we also have the following?

    (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs

If so, prove; if not, explain why.


<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\import Logic.Meta (contradiction)

\func ~Any=All~ {A : \Type} {P : A -> \Prop} (xs : List A) : (~ o Any P) xs = All (~ o P) xs =>
  propExt ([=>] xs) ([<=] xs)
  \where {
    \func [=>] {A : \Type} {P : A -> \Prop} (xs : List A) (not-any : ~ (Any P xs)) : All (~ o P) xs \elim xs
      | [] => []∀
      | :: x xs => (\lam Px => not-any (here Px)) ::∀ ([=>] xs (\lam Pxs => not-any (there Pxs)))

    \func [<=] {A : \Type} {P : A -> \Prop} (xs : List A) (all-not : All (~ o P) xs) : ~ (Any P xs)
      | [], []∀ => contradiction
      | :: x xs, ::∀ ~Px all-not => \lam any => \case any \with {
        | here Px => ~Px Px
        | there any => [<=] xs all-not any
      }
  }

-- `(~ o All P) xs = Any (~ o P) xs` doesn't hold as we need a double negation elimination to prove it.
-- If we attempted to prove it constructively, we would need to construct `(x, p : (P x -> Empty))` at some point.
-- But we only have `(All P xs -> Empty)`, and it is unclear how to get a requied proof out of is without DNE.
```

#### Exercise `¬Any≃All¬` (stretch)

Show that the equivalence `¬Any⇔All¬` can be extended to an isomorphism.
You will need to use extensionality.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
-- (!) We have already proven a more general case (equality) because our All and Any are propositions.
```

#### Exercise `All-∀` (practice)

Show that `All P xs` is isomorphic to `∀ {x} → x ∈ xs → P x`.

<details><summary>Agda</summary>

```agda
-- You code goes here
```
</details>

```tex
\func All-ForAll \alias All-∀ {A : \Type} {P : A -> \Prop} (xs : List A) : All P xs = (\Pi {x : A} (x ∈ xs) -> P x) =>
  propExt ([=>] xs) ([<=] xs)
  \where {
    \func [=>] {A : \Type} {P : A -> \Prop} (xs : List A) (all : All P xs) {x : A} (in : x ∈ xs) : P x
      | :: a xs, ::∀ Pa all, here (inP x=a) => rewrite x=a Pa
      | :: a xs, ::∀ Pa all, there in => [=>] xs all in

    \func [<=] {A : \Type} {P : A -> \Prop} (xs : List A) (p : \Pi {x : A} -> x ∈ xs -> P x) : All P xs \elim xs
      | [] => []∀
      | :: a xs => p (here (inP idp)) ::∀ ([<=] xs (\lam {x} x-in-xs => p (there x-in-xs)))
  }
```


#### Exercise `Any-∃` (practice)

Show that `Any P xs` is isomorphic to `∃[ x ] (x ∈ xs × P x)`.

<details><summary>Agda</summary>

```agda
-- You code goes here
```
</details>

```tex
\import Logic.Meta (∃)

\func Any-Exists \alias Any-∃ {A : \Type} {P : A -> \Prop} (xs : List A) : Any P xs = ∃ {x} (x ∈ xs && P x) =>
  propExt ([=>] xs) ([<=] xs)
  \where {
    \func [=>] {A : \Type} {P : A -> \Prop} (xs : List A) (any : Any P xs) : ∃ {x} (x ∈ xs && P x)
      | :: x xs, here Px => inP (x, prod (here (inP idp)) Px)
      | :: x xs, there any =>
        \let (inP (y, prod y-in-xs Py)) => [=>] xs any
        \in inP (y, prod (there y-in-xs) Py)

    \func [<=] {A : \Type} {P : A -> \Prop} (xs : List A) (p : ∃ {x} (x ∈ xs && P x)) : Any P xs
      | [], inP (x, prod () b)
      | :: x xs, inP (y, prod (here (inP y=x)) Py) => rewrite (inv y=x) (here Py)
      | :: x xs, inP (y, prod (there any) Py) => there ([<=] xs (inP (y, prod any Py)))
  }
```


## Decidability of All

If we consider a predicate as a function that yields a boolean,
it is easy to define an analogue of `All`, which returns true if
a given predicate returns true for every element of a list:
<details><summary>Agda</summary>

```agda
all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p
```
</details>

```tex
\func all {A : \Type} (p : A -> Bool) : List A -> Bool => (foldr (and) true) o (map p)
```
The function can be written in a particularly compact style by
using the higher-order functions `map` and `foldr`.

As one would hope, if we replace booleans by decidables there is again
an analogue of `All`.  First, return to the notion of a predicate `P` as
a function of type `A → Set`, taking a value `x` of type `A` into evidence
`P x` that a property holds for `x`.  Say that a predicate `P` is _decidable_
if we have a function that for a given `x` can decide `P x`:
<details><summary>Agda</summary>

```agda
Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)
```
</details>

```tex
\func Decidable {A : \Type} (P : A -> \Prop) : \Prop => \Pi (x : A) -> Dec (P x)
```
Then if predicate `P` is decidable, it is also decidable whether every
element of a list satisfies the predicate:
<details><summary>Agda</summary>

```agda
All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }
```
</details>

```tex
\func All? {A : \Type} {P : A -> \Prop} (P? : Decidable P) (xs : List A) : Dec (All P xs) \elim xs
  | [] => yes []∀
  | :: x xs => \case P? x, All? P? xs \with {
    | yes Px, yes Pxs => yes (Px ::∀ Pxs)
    | no ~Px, _ => no (\lam (::∀ Px Pxs) => ~Px Px)
    | _, no ~Pxs => no (\lam (::∀ Px Pxs) => ~Pxs Pxs)
  }
```
If the list is empty, then trivially `P` holds for every element of
the list.  Otherwise, the structure of the proof is similar to that
showing that the conjunction of two decidable propositions is itself
decidable, using `_∷_` rather than `⟨_,_⟩` to combine the evidence for
the head and tail of the list.


#### Exercise `Any?` (stretch)

Just as `All` has analogues `all` and `All?` which determine whether a
predicate holds for every element of a list, so does `Any` have
analogues `any` and `Any?` which determine whether a predicate holds
for some element of a list.  Give their definitions.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func any {A : \Type} (p : A -> Bool) : List A -> Bool => (foldr (or) false) o (map p)

\func Any? {A : \Type} {P : A -> \Prop} (P? : Decidable P) (xs : List A) : Dec (Any P xs) \elim xs
  | [] => no (\case __ \with {})
  | :: x xs => \case P? x, Any? P? xs \with {
    | yes Px, _ => yes (here Px)
    | _, yes Pxs => yes (there Pxs)
    | no ~Px, no ~Pxs => no (\case __ \with {
      | here Px => ~Px Px
      | there Pxs => ~Pxs Pxs
    })
  }
```


#### Exercise `split` (stretch)

The relation `merge` holds when two lists merge to give a third list.
<details><summary>Agda</summary>

```agda
data merge {A : Set} : (xs ys zs : List A) → Set where

  [] :
      --------------
      merge [] [] []

  left-∷ : ∀ {x xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge (x ∷ xs) ys (x ∷ zs)

  right-∷ : ∀ {y xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge xs (y ∷ ys) (y ∷ zs)
```
</details>

```tex
\data merge {A : \Type} (_ _ _ : List A) \with
  | [], [], [] => []m
  | :: x xs, ys, :: z zs => left-:: (x = z) (merge xs ys zs)
  | xs, :: y ys, :: z zs => right-:: (y = z) (merge xs ys zs)
```

For example,
<details><summary>Agda</summary>

```agda
_ : merge [ 1 , 4 ] [ 2 , 3 ] [ 1 , 2 , 3 , 4 ]
_ = left-∷ (right-∷ (right-∷ (left-∷ [])))
```
</details>

```tex
\func example-merge : merge (1 :: 4 :: []) (2 :: 3 :: []) (1 :: 2 :: 3 :: 4 :: []) =>
  left-:: idp (right-:: idp (right-:: idp (left-:: idp []m)))
```

Given a decidable predicate and a list, we can split the list
into two lists that merge to give the original list, where all
elements of one list satisfy the predicate, and all elements of
the other do not satisfy the predicate.

Define the following variant of the traditional `filter` function on
lists, which given a decidable predicate and a list returns a list of
elements that satisfy the predicate and a list of elements that don't,
with their corresponding proofs.

    split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
      → ∃[ xs ] ∃[ ys ] ( merge xs ys zs × All P xs × All (¬_ ∘ P) ys )

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func split {A : \Type} {P : A -> \Prop} (P? : Decidable P) (zs : List A)
  : \Sigma (xs ys : List A) (merge xs ys zs) (All P xs) (All (~ o P) ys) \elim zs
  | [] => ([], [], []m, []∀, []∀)
  | :: z zs =>
    \let (xs, ys, merge-xs-ys-zs, Pxs, ~Pys) => split P? zs
    \in \case P? z \with {
      | yes Pz => (z :: xs, ys, left-:: idp merge-xs-ys-zs, Pz ::∀ Pxs, ~Pys)
      | no ~Pz => (xs, z :: ys, right-:: idp merge-xs-ys-zs, Pxs, ~Pz ::∀ ~Pys)
    }
```

## Standard Library

Definitions similar to those in this chapter can be found in the standard library:
<details><summary>Agda</summary>

```agda
import Data.List using (List; _++_; length; reverse; map; foldr; downFrom)
import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Membership.Propositional using (_∈_)
import Data.List.Properties
  using (reverse-++-commute; map-compose; map-++-commute; foldr-++)
  renaming (mapIsFold to map-is-foldr)
import Algebra.Structures using (IsMonoid)
import Relation.Unary using (Decidable)
import Relation.Binary using (Decidable)
```
</details>

```tex
\import Data.List (++, length, map, map_comp, ListMonoid)
```
The standard library version of `IsMonoid` differs from the
one given here, in that it is also parameterised on an equivalence relation.

Both `Relation.Unary` and `Relation.Binary` define a version of `Decidable`,
one for unary relations (as used in this chapter where `P` ranges over
unary predicates) and one for binary relations (as used earlier, where `_≤_`
ranges over a binary relation).

## Unicode

This chapter uses the following unicode:

    ∷  U+2237  PROPORTION  (\::)
    ⊗  U+2297  CIRCLED TIMES  (\otimes, \ox)
    ∈  U+2208  ELEMENT OF  (\in)
    ∉  U+2209  NOT AN ELEMENT OF  (\inn, \notin)
