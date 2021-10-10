---
title     : "Decidable: Booleans and decision procedures"
layout    : page
prev      : /Quantifiers/
permalink : /Decidable/
next      : /Lists/
---

```
module plfa.part1.Decidable where
```

We have a choice as to how to represent relations:
as an inductive data type of _evidence_ that the relation holds,
or as a function that _computes_ whether the relation holds.
Here we explore the relation between these choices.
We first explore the familiar notion of _booleans_,
but later discover that these are best avoided in favour
of a new notion of _decidable_.


## Imports

<details><summary>Agda</summary>

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.part1.Relations using (_<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_⇔_)
```
</details>

```tex
\import Paths (==<, >==, qed)
\import util.Paths (=<>=)
\import util.Logic (&&)
\import Logic (||, byLeft, byRight)
\import util.Logic (~)
\import part1.Negation (Not-Not-intro)
\import part1.Connectives (T \as Unit, tt)
\import Logic (Empty, absurd)
\import part1.Relations (<, z<s, s<s)
\import part1.Isomorphism (<=>)
```

## Evidence vs Computation

Recall that Chapter [Relations](/Relations/)
defined comparison as an inductive datatype,
which provides _evidence_ that one number
is less than or equal to another:
<details><summary>Agda</summary>

```agda
infix 4 _≤_

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
\data \infix 4 <= Nat Nat \with
  | 0, _ => z<=n
  | suc m, suc n => s<=s (m <= n)
```
For example, we can provide evidence that `2 ≤ 4`,
and show there is no possible evidence that `4 ≤ 2`:
<details><summary>Agda</summary>

```agda
2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))
```
</details>

```tex
\func [2<=4] : 2 <= 4 => s<=s (s<=s z<=n)

\func ~[4<=2] : ~ (4 <= 2) => \lam [4<=2] => \case [4<=2] \with {
  | s<=s (s<=s ())
}
```
The occurrence of `()` attests to the fact that there is
no possible evidence for `2 ≤ 0`, which `z≤n` cannot match
(because `2` is not `zero`) and `s≤s` cannot match
(because `0` cannot match `suc n`).

An alternative, which may seem more familiar, is to define a
type of booleans:
<details><summary>Agda</summary>

```agda
data Bool : Set where
  true  : Bool
  false : Bool
```
</details>

```tex
\data Bool | true | false
```
Given booleans, we can define a function of two numbers that
_computes_ to `true` if the comparison holds and to `false` otherwise:
<details><summary>Agda</summary>

```agda
infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n       =  true
suc m ≤ᵇ zero   =  false
suc m ≤ᵇ suc n  =  m ≤ᵇ n
```
</details>

```tex
\func \infix 4 <=b (m n : Nat) : Bool
  | 0, n => true
  | suc m, 0 => false
  | suc m, suc n => m <=b n
```
The first and last clauses of this definition resemble the two
constructors of the corresponding inductive datatype, while the
middle clause arises because there is no possible evidence that
`suc m ≤ zero` for any `m`.
For example, we can compute that `2 ≤ᵇ 4` holds,
and we can compute that `4 ≤ᵇ 2` does not hold:
<details><summary>Agda</summary>

```agda
_ : (2 ≤ᵇ 4) ≡ true
_ =
  begin
    2 ≤ᵇ 4
  ≡⟨⟩
    1 ≤ᵇ 3
  ≡⟨⟩
    0 ≤ᵇ 2
  ≡⟨⟩
    true
  ∎

_ : (4 ≤ᵇ 2) ≡ false
_ =
  begin
    4 ≤ᵇ 2
  ≡⟨⟩
    3 ≤ᵇ 1
  ≡⟨⟩
    2 ≤ᵇ 0
  ≡⟨⟩
    false
  ∎
```
</details>

```tex
\func [2<=b4] : (2 <=b 4) = true =>
  2 <=b 4 =<>=
  1 <=b 3 =<>=
  0 <=b 2 =<>=
  true `qed

\func ~[4<=b2] : (4 <=b 2) = false =>
  4 <=b 2 =<>=
  3 <=b 1 =<>=
  2 <=b 0 =<>=
  false `qed
```
In the first case, it takes two steps to reduce the first argument to zero,
and one more step to compute true, corresponding to the two uses of `s≤s`
and the one use of `z≤n` when providing evidence that `2 ≤ 4`.
In the second case, it takes two steps to reduce the second argument to zero,
and one more step to compute false, corresponding to the two uses of `s≤s`
and the one use of `()` when showing there can be no evidence that `4 ≤ 2`.

## Relating evidence and computation

We would hope to be able to show these two approaches are related, and
indeed we can.  First, we define a function that lets us map from the
computation world to the evidence world:
<details><summary>Agda</summary>

```agda
T : Bool → Set
T true   =  ⊤
T false  =  ⊥
```
</details>

```tex
\func T (b : Bool) : \Type
  | true => Unit
  | false => Empty
```
Recall that `⊤` is the unit type which contains the single element `tt`,
and the `⊥` is the empty type which contains no values.  (Also note that
`T` is a capital letter t, and distinct from `⊤`.)  If `b` is of type `Bool`,
then `tt` provides evidence that `T b` holds if `b` is true, while there is
no possible evidence that `T b` holds if `b` is false.

Another way to put this is that `T b` is inhabited exactly when `b ≡ true`
is inhabited.
In the forward direction, we need to do a case analysis on the boolean `b`:
<details><summary>Agda</summary>

```agda
T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt   =  refl
T→≡ false ()
```
</details>

```tex
\func T->= (b : Bool) (t : T b) : b = true
  | true, tt => idp
```
If `b` is true then `T b` is inhabited by `tt` and `b ≡ true` is inhabited
by `refl`, while if `b` is false then `T b` in uninhabited.

In the reverse direction, there is no need for a case analysis on the boolean `b`:
<details><summary>Agda</summary>

```agda
≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl  =  tt
```
</details>

```tex
\func =->T {b : Bool} (p : b = true) : T b \elim p
  | idp => tt
```
If `b ≡ true` is inhabited by `refl` we know that `b` is `true` and
hence `T b` is inhabited by `tt`.

Now we can show that `T (m ≤ᵇ n)` is inhabited exactly when `m ≤ n` is inhabited.

In the forward direction, we consider the three clauses in the definition
of `_≤ᵇ_`:
<details><summary>Agda</summary>

```agda
≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero    n       tt  =  z≤n
≤ᵇ→≤ (suc m) zero    ()
≤ᵇ→≤ (suc m) (suc n) t   =  s≤s (≤ᵇ→≤ m n t)
```
</details>

```tex
\func leq-b->leq \alias ≤b->≤ (m n : Nat) (_ : T (m <=b n)) : m <= n
  | 0, n, tt => z<=n
  | suc m, suc n, t => s<=s (≤b->≤ m n t)
```
In the first clause, we immediately have that `zero ≤ᵇ n` is
true, so `T (m ≤ᵇ n)` is evidenced by `tt`, and correspondingly `m ≤ n` is
evidenced by `z≤n`. In the middle clause, we immediately have that
`suc m ≤ᵇ zero` is false, and hence `T (m ≤ᵇ n)` is empty, so we need
not provide evidence that `m ≤ n`, which is just as well since there is no
such evidence.  In the last clause, we have that `suc m ≤ᵇ suc n` recurses
to `m ≤ᵇ n`.  We let `t` be the evidence of `T (suc m ≤ᵇ suc n)` if it exists,
which, by definition of `_≤ᵇ_`, will also be evidence of `T (m ≤ᵇ n)`.
We recursively invoke the function to get evidence that `m ≤ n`, which
`s≤s` converts to evidence that `suc m ≤ suc n`.

In the reverse direction, we consider the possible forms of evidence
that `m ≤ n`:
<details><summary>Agda</summary>

```agda
≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n        =  tt
≤→≤ᵇ (s≤s m≤n)  =  ≤→≤ᵇ m≤n
```
</details>

```tex
\func leq->leq-b \alias ≤->≤b {m n : Nat} (_ : m <= n) : T (m <=b n)
  | {0}, z<=n => tt
  | {suc m}, {suc n}, s<=s m<=n => ≤->≤b m<=n
```
If the evidence is `z≤n` then we immediately have that `zero ≤ᵇ n` is
true, so `T (m ≤ᵇ n)` is evidenced by `tt`. If the evidence is `s≤s`
applied to `m≤n`, then `suc m ≤ᵇ suc n` reduces to `m ≤ᵇ n`, and we
may recursively invoke the function to produce evidence that `T (m ≤ᵇ n)`.

The forward proof has one more clause than the reverse proof,
precisely because in the forward proof we need clauses corresponding to
the comparison yielding both true and false, while in the reverse proof
we only need clauses corresponding to the case where there is evidence
that the comparison holds.  This is exactly why we tend to prefer the
evidence formulation to the computation formulation, because it allows
us to do less work: we consider only cases where the relation holds,
and can ignore those where it does not.

On the other hand, sometimes the computation formulation may be just what
we want.  Given a non-obvious relation over large values, it might be
handy to have the computer work out the answer for us.  Fortunately,
rather than choosing between _evidence_ and _computation_,
there is a way to get the benefits of both.

## The best of both worlds

A function that returns a boolean returns exactly a single bit of information:
does the relation hold or does it not? Conversely, the evidence approach tells
us exactly why the relation holds, but we are responsible for generating the
evidence.  But it is easy to define a type that combines the benefits of
both approaches.  It is called `Dec A`, where `Dec` is short for _decidable_:
<details><summary>Agda</summary>

```agda
data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A
```
</details>

```tex
\data Dec (A : \Type)
  | yes A
  | no (~ A)
```
Like booleans, the type has two constructors.  A value of type `Dec A`
is either of the form `yes x`, where `x` provides evidence that `A` holds,
or of the form `no ¬x`, where `¬x` provides evidence that `A` cannot hold
(that is, `¬x` is a function which given evidence of `A` yields a contradiction).

For example, we define a function `_≤?_` which given two numbers decides whether one
is less than or equal to the other, and provides evidence to justify its conclusion.

First, we introduce two functions useful for constructing evidence that
an inequality does not hold:
<details><summary>Agda</summary>

```agda
¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n
```
</details>

```tex
\func ~s<=z {m : Nat} : ~ (suc m <= zero) => \case __ \with {}

\func ~s<=s {m n : Nat} (~m<=n : ~ (m <= n)) : ~ (suc m <= suc n) => \lam sm<=sn => \case sm<=sn \with {
  | s<=s m<=n => ~m<=n m<=n
}
```
The first of these asserts that `¬ (suc m ≤ zero)`, and follows by
absurdity, since any evidence of inequality has the form `zero ≤ n`
or `suc m ≤ suc n`, neither of which match `suc m ≤ zero`. The second
of these takes evidence `¬m≤n` of `¬ (m ≤ n)` and returns a proof of
`¬ (suc m ≤ suc n)`.  Any evidence of `suc m ≤ suc n` must have the
form `s≤s m≤n` where `m≤n` is evidence that `m ≤ n`.  Hence, we have
a contradiction, evidenced by `¬m≤n m≤n`.

Using these, it is straightforward to decide an inequality:
<details><summary>Agda</summary>

```agda
_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero  ≤? n                   =  yes z≤n
suc m ≤? zero                =  no ¬s≤z
suc m ≤? suc n with m ≤? n
...               | yes m≤n  =  yes (s≤s m≤n)
...               | no ¬m≤n  =  no (¬s≤s ¬m≤n)
```
</details>

```tex
\func \infix 4 <=? (m n : Nat) : Dec (m <= n)
  | 0, n => yes z<=n
  | suc m, 0 => no ~s<=z
  | suc m, suc n => \case m <=? n \with {
    | yes m<=n => yes (s<=s m<=n)
    | no ~m<=n => no (~s<=s ~m<=n)
  }
```
As with `_≤ᵇ_`, the definition has three clauses.  In the first
clause, it is immediate that `zero ≤ n` holds, and it is evidenced by
`z≤n`.  In the second clause, it is immediate that `suc m ≤ zero` does
not hold, and it is evidenced by `¬s≤z`.
In the third clause, to decide whether `suc m ≤ suc n` holds we
recursively invoke `m ≤? n`.  There are two possibilities.  In the
`yes` case it returns evidence `m≤n` that `m ≤ n`, and `s≤s m≤n`
provides evidence that `suc m ≤ suc n`.  In the `no` case it returns
evidence `¬m≤n` that `¬ (m ≤ n)`, and `¬s≤s ¬m≤n` provides evidence
that `¬ (suc m ≤ suc n)`.

When we wrote `_≤ᵇ_`, we had to write two other functions, `≤ᵇ→≤` and `≤→≤ᵇ`,
in order to show that it was correct.  In contrast, the definition of `_≤?_`
proves itself correct, as attested to by its type.  The code of `_≤?_`
is far more compact than the combined code of `_≤ᵇ_`, `≤ᵇ→≤`, and `≤→≤ᵇ`.
As we will later show, if you really want the latter three, it is easy
to derive them from `_≤?_`.

We can use our new function to _compute_ the _evidence_ that earlier we had to
think up on our own:
<details><summary>Agda</summary>

```agda
_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl
```
</details>

```tex
\func [2<=?4] : 2 <=? 4 = yes (s<=s (s<=s z<=n)) => idp

\func [4<=?2] : 4 <=? 2 = no (~s<=s (~s<=s ~s<=z)) => idp
```
You can check that Agda will indeed compute these values.  Typing
`C-c C-n` and providing `2 ≤? 4` or `4 ≤? 2` as the requested expression
causes Agda to print the values given above.

(A subtlety: if we do not define `¬s≤z` and `¬s≤s` as top-level functions,
but instead use inline anonymous functions then Agda may have
trouble normalising evidence of negation.)


#### Exercise `_<?_` (recommended)

Analogous to the function above, define a function to decide strict inequality:
```
postulate
  _<?_ : ∀ (m n : ℕ) → Dec (m < n)
```

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\import part1.Relations (<, z<s, s<s)
\import Logic.Meta (contradiction)

\func \infix 4 <? (m n : Nat) : Dec (m < n)
  | 0, 0 => no contradiction
  | 0, suc n => yes z<s
  | suc m, 0 => no contradiction
  | suc m, suc n => \case m <? n \with {
    | yes m<n => yes (s<s m<n)
    | no ~m<n => no (\lam sm<sn => \case sm<sn \with {
      | s<s m<n => ~m<n m<n
    })
  }
```

#### Exercise `_≡ℕ?_` (practice)

Define a function to decide whether two naturals are equal:
```
postulate
  _≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
```

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\import Paths (pmap)
\import Arith.Nat (pred)

\func \infix 4 =N? (m n : Nat) : Dec (m = n)
  | 0, 0 => yes idp
  | 0, suc n => no contradiction
  | suc m, 0 => no contradiction
  | suc m, suc n => \case m =N? n \with {
    | yes m=n => yes (pmap suc m=n)
    | no m/=n => no (\lam sm=sn => m/=n (pmap pred sm=sn))
  }
```


## Decidables from booleans, and booleans from decidables

Curious readers might wonder if we could reuse the definition of
`m ≤ᵇ n`, together with the proofs that it is equivalent to `m ≤ n`, to show
decidability.  Indeed, we can do so as follows:
<details><summary>Agda</summary>

```agda
_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = yes (p tt)
...        | false  | _        | ¬p           = no ¬p
```
</details>

```tex
\import Meta (cases)

\func \infix 4 <=?' (m n : Nat) : Dec (m <= n) => cases (m <=b n, ≤b->≤ m n, ≤->≤b {m} {n}) \with {
  | true, p, _ => yes (p tt)
  | false, _, ~p => no ~p
}
```
If `m ≤ᵇ n` is true then `≤ᵇ→≤` yields a proof that `m ≤ n` holds,
while if it is false then `≤→≤ᵇ` takes a proof that `m ≤ n` holds into a contradiction.

The triple binding of the `with` clause in this proof is essential.
If instead we wrote:

    _≤?″_ : ∀ (m n : ℕ) → Dec (m ≤ n)
    m ≤?″ n with m ≤ᵇ n
    ... | true   =  yes (≤ᵇ→≤ m n tt)
    ... | false  =  no (≤→≤ᵇ {m} {n})

then Agda would make two complaints, one for each clause:

    ⊤ !=< (T (m ≤ᵇ n)) of type Set
    when checking that the expression tt has type T (m ≤ᵇ n)

    T (m ≤ᵇ n) !=< ⊥ of type Set
    when checking that the expression ≤→≤ᵇ {m} {n} has type ¬ m ≤ n

Putting the expressions into the `with` clause permits Agda to exploit
the fact that `T (m ≤ᵇ n)` is `⊤` when `m ≤ᵇ n` is true, and that
`T (m ≤ᵇ n)` is `⊥` when `m ≤ᵇ n` is false.

However, overall it is simpler to just define `_≤?_` directly, as in the previous
section.  If one really wants `_≤ᵇ_`, then it and its properties are easily derived
from `_≤?_`, as we will now show.

Erasure takes a decidable value to a boolean:
<details><summary>Agda</summary>

```agda
⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋  =  true
⌊ no ¬x ⌋  =  false
```
</details>

```tex
\func toBool {A : \Type} (d : Dec A) : Bool
  | yes x => true
  | no ~x => false
```
Using erasure, we can easily derive `_≤ᵇ_` from `_≤?_`:
<details><summary>Agda</summary>

```agda
_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n  =  ⌊ m ≤? n ⌋
```
</details>

```tex
\func \infix 4 <=b' (m n : Nat) : Bool => toBool (m <=? n)
```

Further, if `D` is a value of type `Dec A`, then `T ⌊ D ⌋` is
inhabited exactly when `A` is inhabited:
<details><summary>Agda</summary>

```agda
toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt  =  x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _  =  tt
fromWitness {A} {no ¬x} x  =  ¬x x
```
</details>

```tex
\func toWitness {A : \Type} {D : Dec A} (td : T (toBool D)) : A
  | {A}, {yes x}, tt => x

\func fromWitness {A : \Type} {D : Dec A} (x : A) : T (toBool D)
  | {A}, {yes x}, _ => tt
  | {A}, {no ~x}, x => ~x x
```
Using these, we can easily derive that `T (m ≤ᵇ′ n)` is inhabited
exactly when `m ≤ n` is inhabited:
<details><summary>Agda</summary>

```agda
≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤  =  toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness
```
</details>

```tex
\func leq-b->leq' \alias ≤b->≤' {m n : Nat} (td : T (m <=b' n)) : m <= n => toWitness td

\func leq->leq-b' \alias ≤->≤b' {m n : Nat} (p : m <= n) : T (m <=b' n) => fromWitness p
```

In summary, it is usually best to eschew booleans and rely on decidables.
If you need booleans, they and their properties are easily derived from the
corresponding decidables.


## Logical connectives

Most readers will be familiar with the logical connectives for booleans.
Each of these extends to decidables.

The conjunction of two booleans is true if both are true,
and false if either is false:
<details><summary>Agda</summary>

```agda
infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false
```
</details>

```tex
\func \infixr 6 ^ (_ _ : Bool) : Bool
  | true, true => true
  | false, _ => false
  | _, false => false
```
In Emacs, the left-hand side of the third equation displays in grey,
indicating that the order of the equations determines which of the
second or the third can match.  However, regardless of which matches
the answer is the same.

Correspondingly, given two decidable propositions, we can
decide their conjunction:
<details><summary>Agda</summary>

```agda
infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }
```
</details>

```tex
\func \infixr 6 &&-dec {A B : \Prop} (da : Dec A) (db : Dec B) : Dec (A && B)
  | yes x, yes y => yes (&&.prod x y)
  | no ~x, _ => no (\lam a&&b => ~x (&&.proj1 a&&b))
  | _, no ~y => no (\lam a&&b => ~y (&&.proj2 a&&b))
```
The conjunction of two propositions holds if they both hold,
and its negation holds if the negation of either holds.
If both hold, then we pair the evidence for each to yield
evidence of the conjunct.  If the negation of either holds,
assuming the conjunct will lead to a contradiction.

Again in Emacs, the left-hand side of the third equation displays in grey,
indicating that the order of the equations determines which of the
second or the third can match.  This time the answer is different depending
on which matches; if both conjuncts fail to hold we pick the first to
yield the contradiction, but it would be equally valid to pick the second.

The disjunction of two booleans is true if either is true,
and false if both are false:
<details><summary>Agda</summary>

```agda
infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _      = true
_     ∨ true   = true
false ∨ false  = false
```
</details>

```tex
\func \infixr 5 or \alias \infixr 5 ∨ (_ _ : Bool) : Bool
  | true, _ => true
  | _, true => true
  | false, false => false
```
In Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  However, regardless of which matches
the answer is the same.

Correspondingly, given two decidable propositions, we can
decide their disjunction:
<details><summary>Agda</summary>

```agda
infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }
```
</details>

```tex
\func \infixr 5 ||-dec {A B : \Prop} (da : Dec A) (db : Dec B) : Dec (A || B)
  | yes x, _ => yes (byLeft x)
  | _, yes y => yes (byRight y)
  | no ~x, no ~y => no (\lam a||b => \case a||b \with {
    | byLeft x => ~x x
    | byRight y => ~y y
  })
```
The disjunction of two propositions holds if either holds,
and its negation holds if the negation of both hold.
If either holds, we inject the evidence to yield
evidence of the disjunct.  If the negation of both hold,
assuming either disjunct will lead to a contradiction.

Again in Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  This time the answer is different depending
on which matches; if both disjuncts hold we pick the first,
but it would be equally valid to pick the second.

The negation of a boolean is false if its argument is true,
and vice versa:
<details><summary>Agda</summary>

```agda
not : Bool → Bool
not true  = false
not false = true
```
</details>

```tex
\func not (_ : Bool) : Bool
  | true => false
  | false => true
```
Correspondingly, given a decidable proposition, we
can decide its negation:
<details><summary>Agda</summary>

```agda
¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x)  =  no (¬¬-intro x)
¬? (no ¬x)  =  yes ¬x
```
</details>

```tex
\func ~? {A : \Type} (d : Dec A) : Dec (~ A)
  | yes x => no (Not-Not-intro x)
  | no ~x => yes ~x
```
We simply swap yes and no.  In the first equation,
the right-hand side asserts that the negation of `¬ A` holds,
in other words, that `¬ ¬ A` holds, which is an easy consequence
of the fact that `A` holds.

There is also a slightly less familiar connective,
corresponding to implication:
<details><summary>Agda</summary>

```agda
_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false
```
</details>

```tex
\func implication \alias ⊃ (_ _ : Bool) : Bool
  | _, true => true
  | false, _ => true
  | true, false => false
```
One boolean implies another if
whenever the first is true then the second is true.
Hence, the implication of two booleans is true if
the second is true or the first is false,
and false if the first is true and the second is false.
In Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  However, regardless of which matches
the answer is the same.

Correspondingly, given two decidable propositions,
we can decide if the first implies the second:
<details><summary>Agda</summary>

```agda
_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y  =  yes (λ _ → y)
no ¬x →-dec _      =  yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y  =  no (λ f → ¬y (f x))
```
</details>

```tex
\func ->-dec {A B : \Type} (_ : Dec A) (_ : Dec B) : Dec (A -> B)
  | _, yes y => yes (\lam _ => y)
  | no ~x, _ => yes (\lam x => absurd (~x x))
  | yes x, no ~y => no (\lam a->b => ~y (a->b x))
```
The implication holds if either the second holds or
the negation of the first holds, and its negation
holds if the first holds and the negation of the second holds.
Evidence for the implication is a function from evidence
of the first to evidence of the second.
If the second holds, the function returns the evidence for it.
If the negation of the first holds, the function takes the
evidence of the first and derives a contradiction.
If the first holds and the negation of the second holds,
given evidence of the implication we must derive a contradiction;
we apply the evidence of the implication `f` to the evidence of the
first `x`, yielding a contradiction with the evidence `¬y` of
the negation of the second.

Again in Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  This time the answer is different depending
on which matches; but either is equally valid.

#### Exercise `erasure` (practice)

Show that erasure relates corresponding boolean and decidable operations:
<details><summary>Agda</summary>

```agda
postulate
  ∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
  ∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
  not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
```
</details>

```tex
\func ^-&& {A B : \Prop} (x : Dec A) (y : Dec B) : (toBool x) ^ (toBool y) = toBool (x &&-dec y)
  | yes _, yes _ => idp
  | yes _, no _ => idp
  | no _, yes _ => idp
  | no _, no _ => idp

\func or-|| \alias ∨-|| {A B : \Prop} (x : Dec A) (y : Dec B) : (toBool x) ∨ (toBool y) = toBool (x ||-dec y)
  | yes _, yes _ => idp
  | yes _, no _ => idp
  | no _, yes _ => idp
  | no _, no _ => idp

\func not-~ {A : \Type} (x : Dec A) : not (toBool x) = toBool (~? x)
  | yes _ => idp
  | no _ => idp
```

#### Exercise `iff-erasure` (recommended)

Give analogues of the `_⇔_` operation from
Chapter [Isomorphism](/Isomorphism/#iff),
operation on booleans and decidables, and also show the corresponding erasure:
```
postulate
  _iff_ : Bool → Bool → Bool
  _⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
  iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
```

```
-- Your code goes here
```

## Proof by reflection {name=proof-by-reflection}

Let's revisit our definition of monus from
Chapter [Naturals](/Naturals/).
If we subtract a larger number from a smaller number, we take the result to be
zero. We had to do something, after all. What could we have done differently? We
could have defined a *guarded* version of minus, a function which subtracts `n`
from `m` only if `n ≤ m`:

<details><summary>Agda</summary>

```agda
minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m       zero    _         = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m
```
</details>

```tex
\func minus (m n : Nat) (n<=m : n <= m) : Nat
  | m, 0, _ => m
  | suc m, suc n, s<=s n<=m => minus m n n<=m
```

Unfortunately, it is painful to use, since we have to explicitly provide
the proof that `n ≤ m`:

<details><summary>Agda</summary>

```agda
_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl
```
</details>

```tex
\func [5-3] : minus 5 3 (s<=s (s<=s (s<=s z<=n))) = 2 => idp
```

We cannot solve this problem in general, but in the scenario above, we happen to
know the two numbers *statically*. In that case, we can use a technique called
*proof by reflection*. Essentially, we can ask Agda to run the decidable
equality `n ≤? m` while type checking, and make sure that `n ≤ m`!

We do this by using a feature of implicits. Agda will fill in an implicit of a
record type if it can fill in all its fields. So Agda will *always* manage to
fill in an implicit of an *empty* record type, since there aren't any fields
after all. This is why `⊤` is defined as an empty record.

The trick is to have an implicit argument of the type `T ⌊ n ≤? m ⌋`. Let's go
through what this means step-by-step. First, we run the decision procedure,
`n ≤? m`. This provides us with evidence whether `n ≤ m` holds or not. We erase the
evidence to a boolean. Finally, we apply `T`. Recall that `T` maps booleans into
the world of evidence: `true` becomes the unit type `⊤`, and `false` becomes the
empty type `⊥`. Operationally, an implicit argument of this type works as a
guard.

- If `n ≤ m` holds, the type of the implicit value reduces to `⊤`. Agda then
  happily provides the implicit value.
- Otherwise, the type reduces to `⊥`, which Agda has no chance of providing, so
  it will throw an error. For instance, if we call `3 - 5` we get `_n≤m_254 : ⊥`.

We obtain the witness for `n ≤ m` using `toWitness`, which we defined earlier:

<details><summary>Agda</summary>

```agda
_-_ : (m n : ℕ) {n≤m : T ⌊ n ≤? m ⌋} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)
```
</details>

```tex
\func \infix 6 - (m n : Nat) {n<=m : T (toBool (n <=? m))} => minus m n (toWitness n<=m)
```

We can safely use `_-_` as long as we statically know the two numbers:

<details><summary>Agda</summary>

```agda
_ : 5 - 3 ≡ 2
_ = refl
```
</details>

```tex
-- TODO doesn't work, Arend cannot infer the implicit argument
-- Will be partially available in Arend 1.8
-- \func [5-3]' : (5 - 3) = 2 => idp
```

It turns out that this idiom is very common. The standard library defines a
synonym for `T ⌊ ? ⌋` called `True`:

<details><summary>Agda</summary>

```agda
True : ∀ {Q} → Dec Q → Set
True Q = T ⌊ Q ⌋
```
</details>

```tex
-- TODO
```

#### Exercise `False`

Give analogues of `True`, `toWitness`, and `fromWitness` which work with *negated* properties. Call these `False`, `toWitnessFalse`, and `fromWitnessFalse`.


## Standard Library

<details><summary>Agda</summary>

```agda
import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
import Data.Nat using (_≤?_)
import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)
```
</details>

```tex
\import Data.Bool (Bool, true, false, So, and, or, not)
\import Set (Dec, yes, no, decToBool)
```


## Unicode

    ∧  U+2227  LOGICAL AND (\and, \wedge)
    ∨  U+2228  LOGICAL OR (\or, \vee)
    ⊃  U+2283  SUPERSET OF (\sup)
    ᵇ  U+1D47  MODIFIER LETTER SMALL B  (\^b)
    ⌊  U+230A  LEFT FLOOR (\clL)
    ⌋  U+230B  RIGHT FLOOR (\clR)
