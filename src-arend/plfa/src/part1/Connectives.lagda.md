---
title     : "Connectives: Conjunction, disjunction, and implication"
layout    : page
prev      : /Isomorphism/
permalink : /Connectives/
next      : /Negation/
---

<details><summary>Agda</summary>

```agda
module plfa.part1.Connectives where
```
</details>

```tex
-- Arend uses a "propositions as some types" approach to encode logic. There is as a special universe `\Prop`
-- of types that has at most one element. Empty types correspond to false propositions,
-- one element types correspond to true propositions.
-- See: https://arend-lang.github.io/documentation/language-reference/expressions/universes
-- See: https://ncatlab.org/nlab/show/propositions+as+types#PropositionsAsSomeTypes
```

<!-- The ⊥ ⊎ A ≅ A exercise requires a (inj₁ ()) pattern,
     which the reader will not have seen. Restore this
     exercise, and possibly also associativity? Take the
     exercises from the final sections on distributivity
     and exponentials? -->

This chapter introduces the basic logical connectives, by observing a
correspondence between connectives of logic and data types, a
principle known as _Propositions as Types_:

* _conjunction_ is _product_,
* _disjunction_ is _sum_,
* _true_ is _unit type_,
* _false_ is _empty type_,
* _implication_ is _function space_.


## Imports

<details><summary>Agda</summary>

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality)
open plfa.part1.Isomorphism.≃-Reasoning
```
</details>

```tex
\import Paths (==<, >==, qed)
\import Function (o)
\import util.Equiv (=~, =~-Reasoning)
\open =~-Reasoning
\import part1.Isomorphism (<~, extensionality)
```


## Conjunction is product

Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable record type:
<details><summary>Agda</summary>

```agda
data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B
```
</details>

```tex
\data \infixr 2 x (A B : \Type)
  | prod A B

-- Conjunction is a product over `\Prop`

\func \infixr 2 && (A B : \Prop) : \Prop => A x B
```
Evidence that `A × B` holds is of the form `⟨ M , N ⟩`, where `M`
provides evidence that `A` holds and `N` provides evidence that `B`
holds.

Given evidence that `A × B` holds, we can conclude that either
`A` holds or `B` holds:
<details><summary>Agda</summary>

```agda
proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y
```
</details>

```tex
\func proj1 {A B : \Type} (w : A x B) : A
  | prod a b => a

\func proj2 {A B : \Type} (w : A x B) : B
  | prod a b => b
```
If `L` provides evidence that `A × B` holds, then `proj₁ L` provides evidence
that `A` holds, and `proj₂ L` provides evidence that `B` holds.

When `⟨_,_⟩` appears in a term on the right-hand side of an equation
we refer to it as a _constructor_, and when it appears in a pattern on
the left-hand side of an equation we refer to it as a _destructor_.
We may also refer to `proj₁` and `proj₂` as destructors, since they
play a similar role.

Other terminology refers to `⟨_,_⟩` as _introducing_ a conjunction, and
to `proj₁` and `proj₂` as _eliminating_ a conjunction; indeed, the
former is sometimes given the name `×-I` and the latter two the names
`×-E₁` and `×-E₂`.  As we read the rules from top to bottom,
introduction and elimination do what they say on the tin: the first
_introduces_ a formula for the connective, which appears in the
conclusion but not in the hypotheses; the second _eliminates_ a
formula for the connective, which appears in a hypothesis but not in
the conclusion. An introduction rule describes under what conditions
we say the connective holds---how to _define_ the connective. An
elimination rule describes what we may conclude when the connective
holds---how to _use_ the connective.[^from-wadler-2015]

In this case, applying each destructor and reassembling the results with the
constructor is the identity over products:
<details><summary>Agda</summary>

```agda
η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl
```
</details>

```tex
\func eta-x {A B : \Type} (w : A x B) : prod (proj1 w) (proj2 w) = w
  | prod a b => idp
```
The pattern matching on the left-hand side is essential, since
replacing `w` by `⟨ x , y ⟩` allows both sides of the
propositional equality to simplify to the same term.

We set the precedence of conjunction so that it binds less
tightly than anything save disjunction:
```
infixr 2 _×_
```
Thus, `m ≤ n × n ≤ p` parses as `(m ≤ n) × (n ≤ p)`.

Alternatively, we can declare conjunction as a record type:
<details><summary>Agda</summary>

```agda
record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_
```
</details>

```tex
\record \infixr 2 x' (A B : \Type)
  | proj1' : A
  | proj2' : B

\func \infixr 2 prod' {A B : \Type} (a : A) (b : B) : A x' B \cowith
  | proj1' => a
  | proj2' => b
```
The record construction `record { proj₁′ = M ; proj₂′ = N }` corresponds to the
term `⟨ M , N ⟩` where `M` is a term of type `A` and `N` is a term of type `B`.
The constructor declaration allows us to write `⟨ M , N ⟩′` in place of the
record construction.

The data type `_x_` and the record type `_×′_` behave similarly. One
difference is that for data types we have to prove η-equality, but for record
types, η-equality holds *by definition*. While proving `η-×′`, we do not have to
pattern match on `w` to know that η-equality holds:
<details><summary>Agda</summary>

```agda
η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl
```
</details>

```tex
\func eta-x' {A B : \Type} (w : A x' B) : w.proj1' prod' w.proj2' = w => idp
```
It can be very convenient to have η-equality *definitionally*, and so the
standard library defines `_×_` as a record type. We use the definition from the
standard library in later chapters.


Given two types `A` and `B`, we refer to `A × B` as the
_product_ of `A` and `B`.  In set theory, it is also sometimes
called the _Cartesian product_, and in computing it corresponds
to a _record_ type. Among other reasons for
calling it the product, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A × B` has `m * n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members:
<details><summary>Agda</summary>

```agda
data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
```
</details>

```tex
\data Bool | true | false

\data Tri | aa | bb | cc
```
Then the type `Bool × Tri` has six members:

    ⟨ true  , aa ⟩    ⟨ true  , bb ⟩    ⟨ true ,  cc ⟩
    ⟨ false , aa ⟩    ⟨ false , bb ⟩    ⟨ false , cc ⟩

For example, the following function enumerates all
possible arguments of type `Bool × Tri`:
<details><summary>Agda</summary>

```agda
×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6
```
</details>

```tex
\func x-count (bt : Bool x Tri) : Nat
  | prod true aa => 1
  | prod true bb => 2
  | prod true cc => 3
  | prod false aa => 4
  | prod false bb => 5
  | prod false cc => 6
```

Product on types also shares a property with product on numbers in
that there is a sense in which it is commutative and associative.  In
particular, product is commutative and associative _up to
isomorphism_.

For commutativity, the `to` function swaps a pair, taking `⟨ x , y ⟩` to
`⟨ y , x ⟩`, and the `from` function does the same (up to renaming).
Instantiating the patterns correctly in `from∘to` and `to∘from` is essential.
Replacing the definition of `from∘to` by `λ w → refl` will not work;
and similarly for `to∘from`:
<details><summary>Agda</summary>

```agda
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
    ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
    }
```
</details>

```tex
\func x-comm {A B : \Type} : A x B =~ B x A \cowith
  | f (p : A x B) : B x A \with {
    | prod x y => prod y x
  }
  | ret (p : B x A) : A x B \with {
    | prod y x => prod x y
  }
  | ret_f (p : A x B) : ret (f p) = p \with {
    | prod x y => idp
  }
  | f_sec (p : B x A) : f (ret p) = p \with {
    | prod y x => idp
  }

-- (!) In Arend, we can prove that product is purely commutative (without isomorphism).
-- The proof uses builtin function `iso`, which basically states that isomorphism implies equality
-- (or, better read, equivalence implies identity). This is called the univalence principle.

\func x-comm' {A B : \Type} : A x B = B x A =>
  path (iso x-comm.f x-comm.ret x-comm.ret_f x-comm.f_sec)

-- The same using a library function `equiv=`

\import Equiv.Sigma (equiv=)

\func x-comm'' {A B : \Type} : A x B = B x A => equiv= x-comm
```

Being _commutative_ is different from being _commutative up to
isomorphism_.  Compare the two statements:

    m * n ≡ n * m
    A × B ≃ B × A

In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m * n` and `n * m` are equal to `6`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool × Tri` is
_not_ the same as `Tri × Bool`.  But there is an isomorphism between
the two types.  For instance, `⟨ true , aa ⟩`, which is a member of the
former, corresponds to `⟨ aa , true ⟩`, which is a member of the latter.

For associativity, the `to` function reassociates two uses of pairing,
taking `⟨ ⟨ x , y ⟩ , z ⟩` to `⟨ x , ⟨ y , z ⟩ ⟩`, and the `from` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplification:
<details><summary>Agda</summary>

```agda
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }
```
</details>

```tex
\func x-assoc {A B C : \Type} : (A x B) x C =~ A x (B x C) \cowith
  | f (p : (A x B) x C) : A x (B x C) \with {
    | prod (prod a b) c => prod a (prod b c)
  }
  | ret (p : A x (B x C)) : (A x B) x C \with {
    | prod a (prod b c) => prod (prod a b) c
  }
  | ret_f (p : (A x B) x C) : ret (f p) = p \with {
    | prod (prod a b) c => idp
  }
  | f_sec (p : A x (B x C)) : f (ret p) = p \with {
    | prod a (prod b c) => idp
  }

\func x-assoc' {A B C : \Type} : (A x B) x C = A x (B x C) => equiv= x-assoc
```

Being _associative_ is not the same as being _associative
up to isomorphism_.  Compare the two statements:

    (m * n) * p ≡ m * (n * p)
    (A × B) × C ≃ A × (B × C)

For example, the type `(ℕ × Bool) × Tri` is _not_ the same as `ℕ ×
(Bool × Tri)`. But there is an isomorphism between the two types. For
instance `⟨ ⟨ 1 , true ⟩ , aa ⟩`, which is a member of the former,
corresponds to `⟨ 1 , ⟨ true , aa ⟩ ⟩`, which is a member of the latter.

#### Exercise `⇔≃×` (recommended)

Show that `A ⇔ B` as defined [earlier](/Isomorphism/#iff)
is isomorphic to `(A → B) × (B → A)`.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\import part1.Isomorphism (<=>)

\func <=>=~x {A B : \Type} : (A <=> B) =~ (A -> B) x (B -> A) \cowith
  | f (A<=>B : A <=> B) : (A -> B) x (B -> A) => prod A<=>B.to A<=>B.from
  | ret (AxB : (A -> B) x (B -> A)) : A <=> B \cowith {
    | to => proj1 AxB
    | from => proj2 AxB
  }
  | ret_f (A<=>B : A <=> B) => idp
  | f_sec (AxB : (A -> B) x (B -> A)) : f (ret AxB) = AxB \with {
    | prod AB BA => idp
  }
```


## Truth is unit

Truth `⊤` always holds. We formalise this idea by
declaring a suitable record type:
<details><summary>Agda</summary>

```agda
data ⊤ : Set where

  tt :
    --
    ⊤
```
</details>

```tex
\data T | tt
```
Evidence that `⊤` holds is of the form `tt`.

There is an introduction rule, but no elimination rule.
Given evidence that `⊤` holds, there is nothing more of interest we
can conclude.  Since truth always holds, knowing that it holds tells
us nothing new.

The nullary case of `η-×` is `η-⊤`, which asserts that any
value of type `⊤` must be equal to `tt`:
<details><summary>Agda</summary>

```agda
η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl
```
</details>

```tex
\func eta-T (w : T) : tt = w
  | tt => idp
```
The pattern matching on the left-hand side is essential. Replacing
`w` by `tt` allows both sides of the propositional equality to
simplify to the same term.

Alternatively, we can declare truth as an empty record:
<details><summary>Agda</summary>

```agda
record ⊤′ : Set where
  constructor tt′
```
</details>

```tex
\record T'

\func tt' : T' \cowith
```
The record construction `record {}` corresponds to the term `tt`. The
constructor declaration allows us to write `tt′`.

As with the product, the data type `⊤` and the record type `⊤′` behave
similarly, but η-equality holds *by definition* for the record type. While
proving `η-⊤′`, we do not have to pattern match on `w`---Agda *knows* it is
equal to `tt′`:
<details><summary>Agda</summary>

```agda
η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl
```
</details>

```tex
\func eta-T' (w : T') : tt' = w => idp
```
Agda knows that *any* value of type `⊤′` must be `tt′`, so any time we need a
value of type `⊤′`, we can tell Agda to figure it out:
<details><summary>Agda</summary>

```agda
truth′ : ⊤′
truth′ = _
```
</details>

```tex
-- Arend doesn't have this.
```

We refer to `⊤` as the _unit_ type. And, indeed,
type `⊤` has exactly one member, `tt`.  For example, the following
function enumerates all possible arguments of type `⊤`:
<details><summary>Agda</summary>

```agda
⊤-count : ⊤ → ℕ
⊤-count tt = 1
```
</details>

```tex
\func T-count (w : T) : Nat
  | tt => 1
```

For numbers, one is the identity of multiplication. Correspondingly,
unit is the identity of product _up to isomorphism_.  For left
identity, the `to` function takes `⟨ tt , x ⟩` to `x`, and the `from`
function does the inverse.  The evidence of left inverse requires
matching against a suitable pattern to enable simplification:
<details><summary>Agda</summary>

```agda
⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }
```
</details>

```tex
\func T-identity-left {A : \Type} : T x A =~ A \cowith
  | f => \lam p => proj2 p
  | ret => \lam a => prod tt a
  | ret_f (p : T x A) : prod tt (proj2 p) = p \with {
    | prod tt a => idp
  }
  | f_sec => \lam a => idp
```

Having an _identity_ is different from having an identity
_up to isomorphism_.  Compare the two statements:

    1 * m ≡ m
    ⊤ × A ≃ A

In the first case, we might have that `m` is `2`, and both
`1 * m` and `m` are equal to `2`.  In the second
case, we might have that `A` is `Bool`, and `⊤ × Bool` is _not_ the
same as `Bool`.  But there is an isomorphism between the two types.
For instance, `⟨ tt , true ⟩`, which is a member of the former,
corresponds to `true`, which is a member of the latter.

Right identity follows from commutativity of product and left identity:
<details><summary>Agda</summary>

```agda
⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎
```
</details>

```tex
\func T-identity-right {A : \Type} : A x T =~ A =>
  (A x T) =~< x-comm >=~
  (T x A) =~< T-identity-left >=~
  A `=~-qed
```
Here we have used a chain of isomorphisms, analogous to that used for
equality.


## Disjunction is sum

Given two propositions `A` and `B`, the disjunction `A ⊎ B` holds
if either `A` holds or `B` holds.  We formalise this idea by
declaring a suitable inductive type:
<details><summary>Agda</summary>

```agda
data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B
```
</details>

```tex
\data \infixr 1 u (A B : \Type)
  | inj1 A
  | inj2 B

-- (!) Note that `u` is not in `\Prop`: even if `A` and `B` are in `\Prop`, `A u B` can have
-- more than one element. So, we cannot use `u` to encode disjunction in Arend. To fix this,
-- we can enforce a data definition to be in `\Prop` by using `\truncated` keyword
-- and explicit `: \Prop` annotation:

\truncated \data \infixr 1 || (A B : \Prop) : \Prop
  | byLeft A
  | byRight B

-- Truncating a data has one crucial consequence: any function defined by recursion over a truncated data
-- must have the codomain lying in the universe of the data. In our case, functions over `A || B`
-- can only return types in `\Prop`.
-- See: https://arend-lang.github.io/documentation/language-reference/definitions/data#truncation
```
Evidence that `A ⊎ B` holds is either of the form `inj₁ M`, where `M`
provides evidence that `A` holds, or `inj₂ N`, where `N` provides
evidence that `B` holds.

Given evidence that `A → C` and `B → C` both hold, then given
evidence that `A ⊎ B` holds we can conclude that `C` holds:
<details><summary>Agda</summary>

```agda
case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y
```
</details>

```tex
\func case-u {A B C : \Type} (f : A -> C) (g : B -> C) (w : A u B) : C \elim w
  | inj1 x => f x
  | inj2 y => g y
```
Pattern matching against `inj₁` and `inj₂` is typical of how we exploit
evidence that a disjunction holds.

When `inj₁` and `inj₂` appear on the right-hand side of an equation we
refer to them as _constructors_, and when they appear on the
left-hand side we refer to them as _destructors_.  We also refer to
`case-⊎` as a destructor, since it plays a similar role.  Other
terminology refers to `inj₁` and `inj₂` as _introducing_ a
disjunction, and to `case-⊎` as _eliminating_ a disjunction; indeed
the former are sometimes given the names `⊎-I₁` and `⊎-I₂` and the
latter the name `⊎-E`.

Applying the destructor to each of the constructors is the identity:
<details><summary>Agda</summary>

```agda
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl
```
</details>

```tex
\func eta-u {A B : \Type} (w : A u B) : case-u inj1 inj2 w = w
  | inj1 x => idp
  | inj2 y => idp
```
More generally, we can also throw in an arbitrary function from a disjunction:
<details><summary>Agda</summary>

```agda
uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl
```
</details>

```tex
\func uniq-u {A B C : \Type} (h : A u B -> C) (w : A u B) : case-u (h o inj1) (h o inj2) w = h w \elim w
  | inj1 x => idp
  | inj2 y => idp
```
The pattern matching on the left-hand side is essential.  Replacing
`w` by `inj₁ x` allows both sides of the propositional equality to
simplify to the same term, and similarly for `inj₂ y`.

We set the precedence of disjunction so that it binds less tightly
than any other declared operator:
```
infixr 1 _⊎_
```
Thus, `A × C ⊎ B × C` parses as `(A × C) ⊎ (B × C)`.

Given two types `A` and `B`, we refer to `A ⊎ B` as the
_sum_ of `A` and `B`.  In set theory, it is also sometimes
called the _disjoint union_, and in computing it corresponds
to a _variant record_ type. Among other reasons for
calling it the sum, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A ⊎ B` has `m + n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members, as defined earlier.
Then the type `Bool ⊎ Tri` has five
members:

    inj₁ true     inj₂ aa
    inj₁ false    inj₂ bb
                  inj₂ cc

For example, the following function enumerates all
possible arguments of type `Bool ⊎ Tri`:
<details><summary>Agda</summary>

```agda
⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5
```
</details>

```tex
\func u-count (w : Bool u Tri) : Nat
  | inj1 true => 1
  | inj1 false => 2
  | inj2 aa => 3
  | inj2 bb => 4
  | inj2 cc => 5
```

Sum on types also shares a property with sum on numbers in that it is
commutative and associative _up to isomorphism_.

#### Exercise `⊎-comm` (recommended)

Show sum is commutative up to isomorphism.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func u-comm {A B : \Type} : (A u B) =~ (B u A) \cowith
  | f => \lam w => case-u inj2 inj1 w
  | ret => \lam w => case-u inj2 inj1 w
  | ret_f (w : A u B) : case-u inj2 inj1 (case-u inj2 inj1 w) = w \with {
    | inj1 a => idp
    | inj2 b => idp
  }
  | f_sec (w : B u A) : case-u inj2 inj1 (case-u inj2 inj1 w) = w \with {
    | inj1 a => idp
    | inj2 b => idp
  }
```

#### Exercise `⊎-assoc` (practice)

Show sum is associative up to isomorphism.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func u-assoc {A B C : \Type} : ((A u B) u C) =~ (A u (B u C)) \cowith
  | f (w : (A u B) u C) : A u B u C \with {
    | inj1 (inj1 a) => inj1 a
    | inj1 (inj2 b) => inj2 (inj1 b)
    | inj2 c => inj2 (inj2 c)
  }
  | ret (w : A u B u C) : (A u B) u C \with {
    | inj1 a => inj1 (inj1 a)
    | inj2 (inj1 b) => inj1 (inj2 b)
    | inj2 (inj2 c) => inj2 c
  }
  | ret_f (w : (A u B) u C) : ret (f w) = w \with {
    | inj1 (inj1 a) => idp
    | inj1 (inj2 b) => idp
    | inj2 c => idp
  }
  | f_sec (w : A u B u C) : f (ret w) = w \with {
    | inj1 a => idp
    | inj2 (inj1 b) => idp
    | inj2 (inj2 c) => idp
  }
```

## False is empty

False `⊥` never holds.  We formalise this idea by declaring
a suitable inductive type:
<details><summary>Agda</summary>

```agda
data ⊥ : Set where
  -- no clauses!
```
</details>

```tex
\data _|_
```
There is no possible evidence that `⊥` holds.

Dual to `⊤`, for `⊥` there is no introduction rule but an elimination rule.
Since false never holds, knowing that it holds tells us we are in a
paradoxical situation.  Given evidence that `⊥` holds, we might
conclude anything!  This is a basic principle of logic, known in
medieval times by the Latin phrase _ex falso_, and known to children
through phrases such as "if pigs had wings, then I'd be the Queen of
Sheba".  We formalise it as follows:
<details><summary>Agda</summary>

```agda
⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()
```
</details>

```tex
\func _|_-elim {A : \Type} (e : _|_) : A
```
This is our first use of the _absurd pattern_ `()`.
Here since `⊥` is a type with no members, we indicate that it is
_never_ possible to match against a value of this type by using
the pattern `()`.

The nullary case of `case-⊎` is `⊥-elim`.  By analogy,
we might have called it `case-⊥`, but chose to stick with the name
in the standard library.

The nullary case of `uniq-⊎` is `uniq-⊥`, which asserts that `⊥-elim`
is equal to any arbitrary function from `⊥`:
<details><summary>Agda</summary>

```agda
uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()
```
</details>

```tex
\func uniq-_|_ {C : \Type} (h : _|_ -> C) (w : _|_) : _|_-elim w = h w
```
Using the absurd pattern asserts there are no possible values for `w`,
so the equation holds trivially.

We refer to `⊥` as the _empty_ type. And, indeed,
type `⊥` has no members. For example, the following function
enumerates all possible arguments of type `⊥`:
<details><summary>Agda</summary>

```agda
⊥-count : ⊥ → ℕ
⊥-count ()
```
</details>

```tex
\func _|_-count (e : _|_) : Nat
```
Here again the absurd pattern `()` indicates that no value can match
type `⊥`.

For numbers, zero is the identity of addition. Correspondingly, empty
is the identity of sums _up to isomorphism_.

#### Exercise `⊥-identityˡ` (recommended)

Show empty is the left identity of sums up to isomorphism.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func _|_-identity-left {A : \Type} : (_|_ u A) =~ A \cowith
  | f (w : _|_ u A) : A \with {
    | inj1 e => _|_-elim e
    | inj2 a => a
  }
  | ret => inj2
  | ret_f (w : _|_ u A) : inj2 (f w) = w \with {
    | inj1 e => _|_-elim e
    | inj2 a => idp
  }
  | f_sec => \lam a => idp
```

#### Exercise `⊥-identityʳ` (practice)

Show empty is the right identity of sums up to isomorphism.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func _|_-identity-right {A : \Type} : (A u _|_) =~ A =>
  (A u _|_) =~< u-comm >=~
  (_|_ u A) =~< _|_-identity-left >=~
  A `=~-qed
```

## Implication is function {name=implication}

Given two propositions `A` and `B`, the implication `A → B` holds if
whenever `A` holds then `B` must also hold.  We formalise implication using
the function type, which has appeared throughout this book.

Evidence that `A → B` holds is of the form

    λ (x : A) → N

where `N` is a term of type `B` containing as a free variable `x` of type `A`.
Given a term `L` providing evidence that `A → B` holds, and a term `M`
providing evidence that `A` holds, the term `L M` provides evidence that
`B` holds.  In other words, evidence that `A → B` holds is a function that
converts evidence that `A` holds into evidence that `B` holds.

Put another way, if we know that `A → B` and `A` both hold,
then we may conclude that `B` holds:
<details><summary>Agda</summary>

```agda
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M
```
</details>

```tex
\func ->-elim {A B : \Type} (f : A -> B) (a : A) : B => f a

-- In Arend, implication is a function over `\Prop`:

\func ->-elim' {A B : \Prop} (imp : A -> B) (a : A) : B => imp a
```
In medieval times, this rule was known by the name _modus ponens_.
It corresponds to function application.

Defining a function, with a named definition or a lambda abstraction,
is referred to as _introducing_ a function,
while applying a function is referred to as _eliminating_ the function.

Elimination followed by introduction is the identity:
<details><summary>Agda</summary>

```agda
η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl
```
</details>

```tex
\func eta--> {A B : \Type} (f : A -> B) : (\lam x => f x) = f => idp
```

Implication binds less tightly than any other operator. Thus, `A ⊎ B →
B ⊎ A` parses as `(A ⊎ B) → (B ⊎ A)`.

Given two types `A` and `B`, we refer to `A → B` as the _function_
space from `A` to `B`.  It is also sometimes called the _exponential_,
with `B` raised to the `A` power.  Among other reasons for calling
it the exponential, note that if type `A` has `m` distinct
members, and type `B` has `n` distinct members, then the type
`A → B` has `nᵐ` distinct members.  For instance, consider a
type `Bool` with two members and a type `Tri` with three members,
as defined earlier. Then the type `Bool → Tri` has nine (that is,
three squared) members:

    λ{true → aa; false → aa}  λ{true → aa; false → bb}  λ{true → aa; false → cc}
    λ{true → bb; false → aa}  λ{true → bb; false → bb}  λ{true → bb; false → cc}
    λ{true → cc; false → aa}  λ{true → cc; false → bb}  λ{true → cc; false → cc}

For example, the following function enumerates all possible
arguments of the type `Bool → Tri`:
<details><summary>Agda</summary>

```agda
→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9
```
</details>

```tex
\func ->-count (f : Bool -> Tri) : Nat => \case f true, f false \with {
  | aa, aa => 1
  | aa, bb => 2
  | aa, cc => 3
  | bb, aa => 4
  | bb, bb => 5
  | bb, cc => 6
  | cc, aa => 7
  | cc, bb => 8
  | cc, cc => 9
}
```

Exponential on types also share a property with exponential on
numbers in that many of the standard identities for numbers carry
over to the types.

Corresponding to the law

    (p ^ n) ^ m  ≡  p ^ (n * m)

we have the isomorphism

    A → (B → C)  ≃  (A × B) → C

Both types can be viewed as functions that given evidence that `A` holds
and evidence that `B` holds can return evidence that `C` holds.
This isomorphism sometimes goes by the name *currying*.
The proof of the right inverse requires extensionality:
<details><summary>Agda</summary>

```agda
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
```
</details>

```tex
\func currying {A B C : \Type} : (A -> B -> C) =~ (A x B -> C) \cowith
  | f => \lam f' (prod a b) => f' a b
  | ret => \lam g a b => g (prod a b)
  | ret_f => \lam f => idp
  | f_sec => \lam g => extensionality (\lam (prod a b) => idp)
```

Currying tells us that instead of a function that takes a pair of arguments,
we can have a function that takes the first argument and returns a function that
expects the second argument.  Thus, for instance, our way of writing addition

    _+_ : ℕ → ℕ → ℕ

is isomorphic to a function that accepts a pair of arguments:

    _+′_ : (ℕ × ℕ) → ℕ

Agda is optimised for currying, so `2 + 3` abbreviates `_+_ 2 3`.
In a language optimised for pairing, we would instead take `2 +′ 3` as
an abbreviation for `_+′_ ⟨ 2 , 3 ⟩`.

Corresponding to the law

    p ^ (n + m) = (p ^ n) * (p ^ m)

we have the isomorphism:

    (A ⊎ B) → C  ≃  (A → C) × (B → C)

That is, the assertion that if either `A` holds or `B` holds then `C` holds
is the same as the assertion that if `A` holds then `C` holds and if
`B` holds then `C` holds.  The proof of the left inverse requires extensionality:
<details><summary>Agda</summary>

```agda
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }
```
</details>

```tex
\func ->-distrib-u {A B C : \Type} : (A u B -> C) =~ ((A -> C) x (B -> C)) \cowith
  | f => \lam f' => prod (f' o inj1) (f' o inj2)
  | ret => \lam (prod g h) ab => \case ab \with {
    | inj1 x => g x
    | inj2 y => h y
  }
  | ret_f => \lam f => extensionality (\lam ab => \case \elim ab \with {
    | inj1 x => idp
    | inj2 y => idp
  })
  | f_sec => \lam (prod g h) => idp
```

Corresponding to the law

    (p * n) ^ m = (p ^ m) * (n ^ m)

we have the isomorphism:

    A → B × C  ≃  (A → B) × (A → C)

That is, the assertion that if `A` holds then `B` holds and `C` holds
is the same as the assertion that if `A` holds then `B` holds and if
`A` holds then `C` holds.  The proof of left inverse requires both extensionality
and the rule `η-×` for products:
<details><summary>Agda</summary>

```agda
→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }
```
</details>

```tex
\func ->-distrib-x {A B C : \Type} : (A -> B x C) =~ ((A -> B) x (A -> C)) \cowith
  | f => \lam f' => prod (proj1 o f') (proj2 o f')
  | ret (gh : (A -> B) x (A -> C)) : A -> B x C \elim gh {
    | prod g h => \lam x => prod (g x) (h x)
  }
  | ret_f => \lam f => extensionality (\lam x => eta-x (f x))
  | f_sec (gh : (A -> B) x (A -> C)) : prod (proj1 o ret gh) (proj2 o ret gh) = gh \with {
    | prod g h => idp
  }
```


## Distribution

Products distribute over sum, up to isomorphism.  The code to validate
this fact is similar in structure to our previous results:
<details><summary>Agda</summary>

```agda
×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
                 ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
                 }
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
                 }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
    }
```
</details>

```tex
\func x-distrib-u {A B C : \Type} : (A u B) x C =~ (A x C u B x C) \cowith
  | f (p : (A u B) x C) : A x C u B x C \with {
    | prod (inj1 x) z => inj1 (prod x z)
    | prod (inj2 y) z => inj2 (prod y z)
  }
  | ret (p : A x C u B x C) : (A u B) x C \with {
    | inj1 (prod x z) => prod (inj1 x) z
    | inj2 (prod y z) => prod (inj2 y) z
  }
  | ret_f (p : (A u B) x C) : ret (f p) = p \with {
    | prod (inj1 x) z => idp
    | prod (inj2 y) z => idp
  }
  | f_sec (p : A x C u B x C) : f (ret p) = p \with {
    | inj1 (prod x z) => idp
    | inj2 (prod y z) => idp
  }
```

Sums do not distribute over products up to isomorphism, but it is an embedding:
<details><summary>Agda</summary>

```agda
⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                 ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
                 }
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
                 ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
                 ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
                 }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z)         → refl
                 }
    }
```
</details>

```tex
\func u-distrib-x {A B C : \Type} : (A x B u C) <~ (A u C) x (B u C) \cowith
  | to (p : A x B u C) : (A u C) x (B u C) \with {
    | inj1 (prod x y) => prod (inj1 x) (inj1 y)
    | inj2 z => prod (inj2 z) (inj2 z)
  }
  | from (p : (A u C) x (B u C)) : A x B u C \with {
    | prod (inj1 x) (inj1 y) => inj1 (prod x y)
    | prod (inj1 x) (inj2 z) => inj2 z
    | prod (inj2 z) _ => inj2 z
  }
  | from-to (p : A x B u C) : from (to p) = p \with {
    | inj1 (prod x y) => idp
    | inj2 z => idp
  }

-- (!) In Arend, we can prove (A && B || C) = (A || C) && (B || C).
-- We use `propExt` which is a convenient wrapper around `iso` that we used for `x-comm'` before.

\import Logic (propExt)

\func &&-distrib-|| {A B C : \Prop} : (A && B || C) = (A || C) && (B || C) =>
  propExt &&-distrib-||-right &&-distrib-||-left

  \where {
    \func &&-distrib-||-right {A B C : \Prop} (p : A && B || C) : (A || C) && (B || C)
      | byLeft (prod a b) => prod (byLeft a) (byLeft b)
      | byRight c => prod (byRight c) (byRight c)

    \func &&-distrib-||-left {A B C : \Prop} (p : (A || C) && (B || C)) : A && B || C
      | prod (byLeft a) (byLeft b) => byLeft (prod a b)
      | prod (byLeft a) (byRight c) => byRight c
      | prod (byRight c) _ => byRight c
  }
```
Note that there is a choice in how we write the `from` function.
As given, it takes `⟨ inj₂ z , inj₂ z′ ⟩` to `inj₂ z`, but it is
easy to write a variant that instead returns `inj₂ z′`.  We have
an embedding rather than an isomorphism because the
`from` function must discard either `z` or `z′` in this case.

In the usual approach to logic, both of the distribution laws
are given as equivalences, where each side implies the other:

    A × (B ⊎ C) ⇔ (A × B) ⊎ (A × C)
    A ⊎ (B × C) ⇔ (A ⊎ B) × (A ⊎ C)

But when we consider the functions that provide evidence for these
implications, then the first corresponds to an isomorphism while the
second only corresponds to an embedding, revealing a sense in which
one of these laws is "more true" than the other.


#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds:
```
postulate
  ⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
```
This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
-- (A u B) x C =~ A x C u B x C
-- A x C u B x C -> A + B * C

\func u-weak-x {A B C : \Type} (p : (A u B) x C) : A u (B x C)
  | prod (inj1 a) _ => inj1 a
  | prod (inj2 b) c => inj2 (prod b c)
```


#### Exercise `⊎×-implies-×⊎` (practice)

Show that a disjunct of conjuncts implies a conjunct of disjuncts:
```
postulate
  ⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
```
Does the converse hold? If so, prove; if not, give a counterexample.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func ux-implies-xu {A B C D : \Type} (p : A x B u C x D) : (A u C) x (B u D)
  | inj1 (prod a b) => prod (inj1 a) (inj1 b)
  | inj2 (prod c d) => prod (inj2 c) (inj2 d)

-- The converse doesn't hold. Counterexample:
-- Let A = T, B = _|_, C = _|_, D = T.
-- Then (T u _|_) x (_|_ u T) = T,
-- but   T x _|_  u  _|_ x T  = _|_
```


## Standard library

Definitions similar to those in this chapter can be found in the standard library:
<details><summary>Agda</summary>

```agda
import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Data.Unit using (⊤; tt)
import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Data.Empty using (⊥; ⊥-elim)
import Function.Equivalence using (_⇔_)
```
</details>

```tex
-- \import Logic (||, Empty, absurd)
-- \import Relation.Equivalence (Equivalence)
```
The standard library constructs pairs with `_,_` whereas we use `⟨_,_⟩`.
The former makes it convenient to build triples or larger tuples from pairs,
permitting `a , b , c` to stand for `(a , (b , c))`.  But it conflicts with
other useful notations, such as `[_,_]` to construct a list of two elements in
Chapter [Lists](/Lists/)
and `Γ , A` to extend environments in
Chapter [DeBruijn](/DeBruijn/).
The standard library `_⇔_` is similar to ours, but the one in the
standard library is less convenient, since it is parameterised with
respect to an arbitrary notion of equivalence.


## Unicode

This chapter uses the following unicode:

    ×  U+00D7  MULTIPLICATION SIGN (\x)
    ⊎  U+228E  MULTISET UNION (\u+)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊥  U+22A5  UP TACK (\bot)
    η  U+03B7  GREEK SMALL LETTER ETA (\eta)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)


[^from-wadler-2015]: This paragraph was adopted from "Propositions as Types", Philip Wadler, _Communications of the ACM_, December 2015.
