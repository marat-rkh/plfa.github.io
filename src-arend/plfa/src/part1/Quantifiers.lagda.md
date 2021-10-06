---
title     : "Quantifiers: Universals and existentials"
layout    : page
prev      : /Negation/
permalink : /Quantifiers/
next      : /Decidable/
---

```
module plfa.part1.Quantifiers where
```

This chapter introduces universal and existential quantification.

## Imports

<details><summary>Agda</summary>

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
```
</details>

```tex
\open Nat (+, *)
\import Logic (Empty, absurd, ||)
\import util.Logic (~)
\open || (byLeft, byRight)
\import util.Logic (&&)
\open && (prod, proj1, proj2)
\import util.Equiv (=~)
\import part1.Isomorphism (extensionality)
```


## Universals

We formalise universal quantification using the dependent function
type, which has appeared throughout this book.  For instance, in
Chapter Induction we showed addition is associative:

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

which asserts for all natural numbers `m`, `n`, and `p`
that `(m + n) + p ≡ m + (n + p)` holds.  It is a dependent
function, which given values for `m`, `n`, and `p` returns
evidence for the corresponding equation.

In general, given a variable `x` of type `A` and a proposition `B x`
which contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B x` holds if for every term `M` of type `A`
the proposition `B M` holds.  Here `B M` stands for the proposition
`B x` with each free occurrence of `x` replaced by `M`.  Variable `x`
appears free in `B x` but bound in `∀ (x : A) → B x`.

Evidence that `∀ (x : A) → B x` holds is of the form

    λ (x : A) → N x

where `N x` is a term of type `B x`, and `N x` and `B x` both contain
a free variable `x` of type `A`.  Given a term `L` providing evidence
that `∀ (x : A) → B x` holds, and a term `M` of type `A`, the term `L M`
provides evidence that `B M` holds.  In other words, evidence that
`∀ (x : A) → B x` holds is a function that converts a term `M` of type
`A` into evidence that `B M` holds.

Put another way, if we know that `∀ (x : A) → B x` holds and that `M`
is a term of type `A` then we may conclude that `B M` holds:
<details><summary>Agda</summary>

```agda
∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M
```
</details>

```tex
\func Pi-elim {A : \Type} {B : A -> \Type} (L : \Pi (a : A) -> B a) (M : A) : B M => L M
```
As with `→-elim`, the rule corresponds to function application.

Functions arise as a special case of dependent functions,
where the range does not depend on a variable drawn from the domain.
When a function is viewed as evidence of implication, both its
argument and result are viewed as evidence, whereas when a dependent
function is viewed as evidence of a universal, its argument is viewed
as an element of a data type and its result is viewed as evidence of
a proposition that depends on the argument. This difference is largely
a matter of interpretation, since in Agda a value of a type and
evidence of a proposition are indistinguishable.

Dependent function types are sometimes referred to as dependent
products, because if `A` is a finite type with values `x₁ , ⋯ , xₙ`,
and if each of the types `B x₁ , ⋯ , B xₙ` has `m₁ , ⋯ , mₙ` distinct
members, then `∀ (x : A) → B x` has `m₁ * ⋯ * mₙ` members.  Indeed,
sometimes the notation `∀ (x : A) → B x` is replaced by a notation
such as `Π[ x ∈ A ] (B x)`, where `Π` stands for product.  However, we
will stick with the name dependent function, because (as we will see)
dependent product is ambiguous.


#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction:
<details><summary>Agda</summary>

```agda
postulate
  ∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
```
</details>

```tex
\import Logic (propExt)

\func Pi-distrib-&& {A : \Type} {B C : A -> \Prop} :
  (\Pi (a : A) -> B a && C a) = (\Pi (a : A) -> B a) && (\Pi (a : A) -> C a) =>
  propExt ([=>] {A} {B} {C}) ([<=] {A} {B} {C})
  \where {
    \func [=>] {A : \Type} {B C : A -> \Prop} (p : \Pi (a : A) -> B a && C a) :
      (\Pi (a : A) -> B a) && (\Pi (a : A) -> C a) =>
      prod (\lam a => proj1 (p a)) (\lam a => (proj2 (p a)))

    \func [<=] {A : \Type} {B C : A -> \Prop} (p : (\Pi (a : A) -> B a) && (\Pi (a : A) -> C a)) :
      \Pi (a : A) -> B a && C a =>
      \lam a => prod ((proj1 p) a) ((proj2 p) a)
  }
```
Compare this with the result (`→-distrib-×`) in
Chapter [Connectives](/Connectives/).

#### Exercise `⊎∀-implies-∀⊎` (practice)

Show that a disjunction of universals implies a universal of disjunctions:
<details><summary>Agda</summary>

```agda
postulate
  ⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
```
</details>

```tex
\func ||-Pi->Pi-|| {A : \Type} {B C : A -> \Prop} (p : (\Pi (a : A) -> B a) || (\Pi (a : A) -> C a)) :
  \Pi (a : A) -> B a || C a \elim p
  | byLeft a=>Ba => \lam a => byLeft (a=>Ba a)
  | byRight a=>Ca => \lam a => byRight (a=>Ca a)

\func Pi-||->||-Pi =>
  \Pi {A : \Type} {B C : A -> \Prop} -> (\Pi (a : A) -> B a || C a) -> (\Pi (a : A) -> B a) || (\Pi (a : A) -> C a)

\import Data.Bool

\func Pi-||->||-Pi-is-false : ~ (Pi-||->||-Pi) =>
  \lam p => \case p {Bool} {__ = true} {__ = false} bool-is-true-or-false \with {
    | byLeft any-bool-is-true => \case any-bool-is-true false \with {}
    | byRight any-bool-is-false => \case any-bool-is-false true \with {}
  }

  \where {
    \func bool-is-true-or-false (b : Bool) : (b = true) || (b = false) \elim b
      | true => byLeft idp
      | false => byRight idp
  }
```
Does the converse hold? If so, prove; if not, explain why.


#### Exercise `∀-×` (practice)

Consider the following type.
<details><summary>Agda</summary>

```agda
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
```
</details>

```tex
\import part1.Connectives (Tri, x)
\open Tri
\import part1.Connectives (x, proj1 \as x-proj1, proj2 \as x-proj2)
\import part1.Isomorphism (Pi-extensionality)

\func Pi-x {B : Tri -> \Type} : (\Pi (t : Tri) -> B t) =~ B aa x B bb x B cc \cowith
  | f => \lam p => x.prod (p aa) (x.prod (p bb) (p cc))
  | ret => \lam p t => \case \elim t \with {
    | aa => x-proj1 p
    | bb => x-proj1 (x-proj2 p)
    | cc => x-proj2 (x-proj2 p)
  }
  | ret_f => \lam p => Pi-extensionality {Tri} {B} (\lam x => \case \elim x \with {
    | aa => idp
    | bb => idp
    | cc => idp
  })
  | f_sec => \lam (x.prod a (x.prod b c)) => idp
```
Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.
Hint: you will need to postulate a version of extensionality that
works for dependent functions.


## Existentials

Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `Σ[ x ∈ A ] B x` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`Σ[ x ∈ A ] B x`.

We formalise existential quantification by declaring a suitable
inductive type:
<details><summary>Agda</summary>

```agda
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B
```
</details>

```tex
\data Sigma (A : \Type) (B : A -> \Prop)
  | pair (x : A) (B x)

-- (!) Note that `Sigma` is not generally in `\Prop`. We can fix this using truncation as we did for disjunction
-- in `part1.Connectives`. This time, we will use `TruncP` from the standard library, it allows truncating any type
-- to `\Prop`. `TruncP` has 2 contructors:
-- 1. `inP` - constructs values of `TruncP` from any type.
-- 2. `truncP` - states that any 2 values of `TruncP` are identical.
-- Note that `truncP` is special. It doesn't construct values of `TruncP`, but rather constructs values
-- of identity type on `TruncP`. This is a feature of higher inductive types. `TruncP` is an example of such type.
-- See: https://arend-lang.github.io/documentation/language-reference/definitions/hits

\import Logic (TruncP, inP)

\func Exists-example (A : \Type) (B : A -> \Prop) (a : A) (b : B a) : TruncP (Sigma A B) => inP (pair a b)
```
We define a convenient syntax for existentials as follows:
<details><summary>Agda</summary>

```agda
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
```
</details>

```tex
-- Arend has a special builtin type `\Sigma` for dependent tuples:

\func Sigma-syntax-example (A : \Type) (B : A -> \Prop) (a : A) (b : B a) : \Sigma (a : A) (B a) => (a, b)

-- For `TruncP (\Sigma ...)` convenient syntax is provided by the meta definition `∃`.
-- See: https://arend-lang.github.io/about/arend-features#language-extensions

\import Logic.Meta (∃)

\func Exists-syntax-example (A : \Type) (B : A -> \Prop) (a : A) (b : B a) : ∃ (a : A) (B a) => inP (a, b)
```
This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.

Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`⟨ M , N ⟩` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.

Equivalently, we could also declare existentials as a record type:
<details><summary>Agda</summary>

```agda
record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′
```
</details>

```tex
\record Sigma' (A : \Type) (B : A -> \Prop)
  | proj1' : A
  | proj2' : B proj1'
```
Here record construction

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

corresponds to the term

    ⟨ M , N ⟩

where `M` is a term of type `A` and `N` is a term of type `B M`.

Products arise as a special case of existentials, where the second
component does not depend on a variable drawn from the first
component.  When a product is viewed as evidence of a conjunction,
both of its components are viewed as evidence, whereas when it is
viewed as evidence of an existential, the first component is viewed as
an element of a datatype and the second component is viewed as
evidence of a proposition that depends on the first component.  This
difference is largely a matter of interpretation, since in Agda a value
of a type and evidence of a proposition are indistinguishable.

Existentials are sometimes referred to as dependent sums,
because if `A` is a finite type with values `x₁ , ⋯ , xₙ`, and if
each of the types `B x₁ , ⋯ B xₙ` has `m₁ , ⋯ , mₙ` distinct members,
then `Σ[ x ∈ A ] B x` has `m₁ + ⋯ + mₙ` members, which explains the
choice of notation for existentials, since `Σ` stands for sum.

Existentials are sometimes referred to as dependent products, since
products arise as a special case.  However, that choice of names is
doubly confusing, since universals also have a claim to the name dependent
product and since existentials also have a claim to the name dependent sum.

A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
<details><summary>Agda</summary>

```agda
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B
```
</details>

```tex
\func Exists-syntax-example' (A : \Type) (B : A -> \Type) (a : A) (b : B a) : ∃ {a} (B a) => inP (a, b)
```
The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.

Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
<details><summary>Agda</summary>

```agda
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y
```
</details>

```tex
\func Exists-elim {A : \Type} {B : A -> \Prop} {C : \Prop}
                  (f : \Pi (x : A) -> B x -> C)
                  (e : ∃ {x} (B x)) : C \elim e
  | inP (x, y) => f x y
```
In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.

Indeed, the converse also holds, and the two together form an isomorphism:
<details><summary>Agda</summary>

```agda
∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
```
</details>

```tex
\func Pi-Sigma-currying {A : \Type} {B : A -> \Type} {C : \Type} :
  (\Pi (x : A) -> B x -> C) =~ (\Sigma (x : A) (B x) -> C) \cowith
  | f => \lam f' (x, y) => f' x y
  | ret => \lam g x y => g (x, y)
  | ret_f => \lam f => idp
  | f_sec => \lam g => extensionality (\lam (x, y) => idp)
```
The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication](/Connectives/#implication).

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
<details><summary>Agda</summary>

```agda
postulate
  ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
```
</details>

```tex
\func Exists-distrib-|| {A : \Type} {B C : A -> \Prop} : ∃ {a} (B a || C a) = (∃ {a} (B a) || ∃ {a} (C a)) =>
  propExt ([=>] {A} {B} {C}) ([<=] {A} {B} {C})
  \where {
    \func [=>] {A : \Type} {B C : A -> \Prop} (p : ∃ {a} (B a || C a)) : ∃ {a} (B a) || ∃ {a} (C a)
      | inP (a, b||c) => \case b||c \with {
        | byLeft b => byLeft (inP (a, b))
        | byRight c => byRight (inP (a, c))
      }

    \func [<=] {A : \Type} {B C : A -> \Prop} (p : ∃ {a} (B a) || ∃ {a} (C a)) : ∃ {a} (B a || C a)
      | byLeft (inP (a, b)) => inP (a, byLeft b)
      | byRight (inP (a, c)) => inP (a, byRight c)
  }
```

#### Exercise `∃×-implies-×∃` (practice)

Show that an existential of conjunctions implies a conjunction of existentials:
<details><summary>Agda</summary>

```agda
postulate
  ∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
```
</details>

```tex
\func Exists-&&->&&-Exists {A : \Type} {B C : A -> \Prop} (p : ∃ {a} (B a && C a)) : (∃ {a} (B a)) && (∃ {a} (C a))
  | inP (a, x.prod b c) => x.prod (inP (a, b)) (inP (a, c))

\func &&-Exists->Exists-&& => \Pi {A : \Type} {B C : A -> \Prop} -> (∃ {a} (B a)) && (∃ {a} (C a)) -> ∃ {a} (B a && C a)

\import Paths (inv, *>)

\func &&-Exists->Exists-&&-is-false : ~ (&&-Exists->Exists-&&) =>
  \lam p => \case p {Bool} {\lam b => b = true} {\lam b => b = false} (x.prod (inP (true, idp)) (inP (false, idp))) \with {
    | inP (b, x.prod b=true b=false) => \case (inv b=true) *> b=false \with {}
  }

-- TODO ∃-||
```
Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-⊎` (practice)

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.


## An existential example

Recall the definitions of `even` and `odd` from
Chapter [Relations](/Relations/):
<details><summary>Agda</summary>

```agda
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
```
</details>

```tex
\import part1.Relations (even, odd, suc-even, suc-odd, zero-even)
```
A number is even if it is zero or the successor of an odd number, and
odd if it is the successor of an even number.

We will show that a number is even if and only if it is twice some
other number, and odd if and only if it is one more than twice
some other number.  In other words, we will show:

`even n`   iff   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   iff   `∃[ m ] (1 + m * 2 ≡ n)`

By convention, one tends to write constant factors first and to put
the constant term in a sum last. Here we've reversed each of those
conventions, because doing so eases the proof.

Here is the proof in the forward direction:
<details><summary>Agda</summary>

```agda
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩
```
</details>

```tex
\import Paths (pmap)

\func even-Exists {n : Nat} (en : even n) : ∃ {m} (m * 2 = n)
  | {0}, zero-even => inP (0, idp)
  | {suc n}, suc-even o => \case odd-Exists o \with {
    | inP (m, p) => inP (suc m, pmap suc p)
  }

\func odd-Exists {n : Nat} (on : odd n) : ∃ {m} (1 + m * 2 = n)
  | {suc n}, suc-odd e => \case even-Exists e \with {
    | inP (m, p) => inP (m, pmap suc p)
  }
```
We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `m * 2 ≡ n` or `1 + m * 2 ≡ n`.
We induct over the evidence that `n` is even or odd:

* If the number is even because it is zero, then we return a pair
consisting of zero and the evidence that twice zero is zero.

* If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + m * 2 ≡ n`. We return a pair consisting of `suc m`
and evidence that `suc m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

* If the number is odd because it is the successor of an even number,
then we apply the induction hypothesis to give a number `m` and
evidence that `m * 2 ≡ n`. We return a pair consisting of `suc m` and
evidence that `1 + m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

This completes the proof in the forward direction.

Here is the proof in the reverse direction:
<details><summary>Agda</summary>

```agda
∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)
```
</details>

```tex
\import Arith.Nat (pred)

\func Exists-even {n : Nat} (e : ∃ {m} (m * 2 = n)) : even n \elim n
  | 0 => zero-even
  | suc n => suc-even (Exists-odd (lemma1 e))
  \where {
    \func lemma1 {n : Nat} (e : ∃ {m} (m * 2 = suc n)) : ∃ {k} (suc (k * 2) = n)
      | {0}, inP (0, ())
      | {0}, inP (suc n, ())
      | {suc n}, inP ((0, ()))
      | {suc n}, inP (suc m, p) => inP (m, pmap pred p)
  }

\func Exists-odd {n : Nat} (e : ∃ {m} (suc (m * 2) = n)) : odd n \elim n
  | 0 =>
    \let empty => TruncP.map e (\case __.2 \with {})
    \in absurd (TruncP.remove Path.inProp empty)
  | suc n =>
    \let e' : ∃ {m} (m * 2 = n) => TruncP.map e (\lam p => (p.1, pmap pred p.2))
    \in suc-odd (Exists-even e')
```
Given a number that is twice some other number we must show it is
even, and a number that is one more than twice some other number we
must show it is odd.  We induct over the evidence of the existential,
and in the even case consider the two possibilities for the number
that is doubled:

- In the even case for `zero`, we must show `zero * 2` is even, which
follows by `even-zero`.

- In the even case for `suc n`, we must show `suc m * 2` is even.  The
inductive hypothesis tells us that `1 + m * 2` is odd, from which the
desired result follows by `even-suc`.

- In the odd case, we must show `1 + m * 2` is odd.  The inductive
hypothesis tell us that `m * 2` is even, from which the desired result
follows by `odd-suc`.

This completes the proof in the backward direction.

#### Exercise `∃-even-odd` (practice)

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
-- TODO ∃-even-odd
```

#### Exercise `∃-|-≤` (practice)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\import Order.PartialOrder (<=)
\import Arith.Nat (NatSemiring, suc<=suc, zero<=_)
\import Paths.Meta (rewrite)

\func LEQ-lemma {y z : Nat} : TruncP (y <= z) = ∃ {x} (x + y = z) => propExt [=>] [<=]
  \where {
    -- TODO can we rewrite `TruncP.map p (\lam p' => (p'.1, pmap suc p'.2))` using `Data.Sigma (tupleMapRight)`?
    \func [=>] {y z : Nat} (leq : TruncP (y <= z)) : ∃ {x} (x + y = z)
      | {0}, {z}, _ => inP (z, idp)
      | {suc y}, {0}, inP suc<=0 => absurd (suc<=0 NatSemiring.zero<suc)
      | {suc y}, {suc z}, inP suc-y<=suc-z =>
        \let p : ∃ {x} (x + y = z) => [=>] (inP (suc<=suc.conv suc-y<=suc-z))
        \in TruncP.map p (\lam p' => (p'.1, pmap suc p'.2))

    \func [<=] {y z : Nat} (p :  ∃ {x} (x + y = z)) : TruncP (y <= z)
      | {y}, {z}, inP (0, y=z) => inP (rewrite y=z NatSemiring.<=-reflexive)
      | {y}, {0}, inP (suc x, ())
      | {y}, {suc z}, inP (suc x, suc[x+y]=suc[z]) =>
        \let
          | p : TruncP (y <= z) => [<=] (inP (x, pmap pred suc[x+y]=suc[z]))
          | q : z <= suc z => NatSemiring.<=_+ (NatSemiring.<=-reflexive {z}) (zero<=_ {1})
        \in TruncP.map p (NatSemiring.<=-transitive __ q)
  }
```


## Existentials, Universals, and Negation

Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
<details><summary>Agda</summary>

```agda
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }
```
</details>

```tex
\func NotExists=ForAllNot \alias ~∃=∀~ {A : \Type} {B : A -> \Prop} : ~ (∃ {x} (B x)) = (\Pi (x : A) -> ~ (B x)) =>
  propExt ([=>] {A} {B}) ([<=] {A} {B})
  \where {
    \func [=>] {A : \Type} {B : A -> \Prop} (p : ~ (∃ {x} (B x))) : \Pi (x : A) -> ~ (B x) =>
      \lam x bx => p (inP (x, bx))

    \func [<=] {A : \Type} {B : A -> \Prop} (p : \Pi (x : A) -> ~ (B x)) : ~ (∃ {x} (B x)) =>
      \lam q => \case q \with {
        | inP (x, bx) => p x bx
      }
  }
```
In the `to` direction, we are given a value `¬∃xy` of type
`¬ ∃[ x ] B x`, and need to show that given a value
`x` that `¬ B x` follows, in other words, from
a value `y` of type `B x` we can derive false.  Combining
`x` and `y` gives us a value `⟨ x , y ⟩` of type `∃[ x ] B x`,
and applying `¬∃xy` to that yields a contradiction.

In the `from` direction, we are given a value `∀¬xy` of type
`∀ x → ¬ B x`, and need to show that from a value `⟨ x , y ⟩`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.

The two inverse proofs are straightforward, where one direction
requires extensionality.


#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal:
<details><summary>Agda</summary>

```agda
postulate
  ∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
    → ∃[ x ] (¬ B x)
      --------------
    → ¬ (∀ x → B x)
```
</details>

```tex
\func ExistsNot-implies-NotForAll \alias ∃~-implies-~∀
  {A : \Type} {B : A -> \Prop} (p : ∃ {x} (~ (B x))) : ~ (\Pi (x : A) -> B x) \elim p
  | inP (x, not-bx) => \lam x=>bx => not-bx (x=>bx x)

-- The inverse doesn't hold as we need a double negation elimination to prove it.
```
Does the converse hold? If so, prove; if not, explain why.


#### Exercise `Bin-isomorphism` (stretch) {name=Bin-isomorphism}

Recall that Exercises
[Bin](/Naturals/#Bin),
[Bin-laws](/Induction/#Bin-laws), and
[Bin-predicates](/Relations/#Bin-predicates)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties:

    from (to n) ≡ n

    ----------
    Can (to n)

    Can b
    ---------------
    to (from b) ≡ b

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ b ](Can b)`.

We recommend proving the following lemmas which show that, for a given
binary number `b`, there is only one proof of `One b` and similarly
for `Can b`.

    ≡One : ∀{b : Bin} (o o' : One b) → o ≡ o'

    ≡Can : ∀{b : Bin} (cb : Can b) (cb' : Can b) → cb ≡ cb'

Many of the alternatives for proving `to∘from` turn out to be tricky.
However, the proof can be straightforward if you use the following lemma,
which is a corollary of `≡Can`.

    proj₁≡→Can≡ : {cb cb′ : ∃[ b ](Can b)} → proj₁ cb ≡ proj₁ cb′ → cb ≡ cb′

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\import util.Arith.Bin
\open Bin (to, from, from-to-id)
\import part1.Relations (Can, to-Can, to-from-id-Can, zero-can, one-can, One, one, O-one, I-one)

\func Nat=~Can-Bin : Nat =~ (\Sigma (b : Bin) (Can b)) \cowith
  | f (n : Nat) => (to n, to-Can)
  | ret (cb : \Sigma (b : Bin) (Can b)) => from cb.1
  | ret_f => from-to-id
  | f_sec (cb : \Sigma (b : Bin) (Can b)) : (to (from cb.1), to-Can) = {\Sigma (b : Bin) (Can b)} cb \elim cb {
    | (b, c) => sigmaExt to-Can c (to-from-id-Can c)
  }
  \where {
    \func sigmaExt {b b' : Bin} (cb : Can b) (cb' : Can b') (p : b = b')
      : (b, cb) = {\Sigma (d : Bin) (Can d)} (b', cb') \elim p
      | idp => rewrite (Can-b-isProp cb cb') idp

    \func Can-b-isProp {b : Bin} (cb cb' : Can b) : cb = cb'
      | {O <>}, zero-can, zero-can => idp
      | {O <>}, _, one-can (O-one ())
      | {O <>}, one-can (O-one ()), _
      | one-can ob, one-can ob' => pmap one-can (One-b-isProp ob ob')

    \func One-b-isProp {b : Bin} (ob ob' : One b) : ob = ob'
      | {I <>}, one, one => idp
      | {I <>}, _, I-one ()
      | {O b}, O-one ob, O-one ob' => pmap O-one (One-b-isProp ob ob')
      | {I <>}, I-one (), _
      | {I b}, I-one ob, I-one ob' => pmap I-one (One-b-isProp ob ob')
  }
```


## Standard library

Definitions similar to those in this chapter can be found in the standard library:
```
import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
```


## Unicode

This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)
