---
title     : "Isomorphism: Isomorphism and Embedding"
layout    : page
prev      : /Equality/
permalink : /Isomorphism/
next      : /Connectives/
---

```
module plfa.part1.Isomorphism where
```

This section introduces isomorphism as a way of asserting that two
types are equal, and embedding as a way of asserting that one type is
smaller than another.  We apply isomorphisms in the next chapter
to demonstrate that operations on types such as product and sum
satisfy properties akin to associativity, commutativity, and
distributivity.

## Imports

<details><summary>Agda</summary>

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
```
</details>

```tex
\import Paths (pmap, ==<, >==, qed)
\import util.Paths (=<>=, pmap-app)
\open Nat (+)
\import Arith.Nat (NatSemiring)
\open NatSemiring (+-comm)
```


## Lambda expressions

The chapter begins with a few preliminaries that will be useful
here and elsewhere: lambda expressions, function composition, and
extensionality.

_Lambda expressions_ provide a compact way to define functions without
naming them.  A term of the form

    λ{ P₁ → N₁; ⋯ ; Pₙ → Nₙ }

is equivalent to a function `f` defined by the equations

    f P₁ = N₁
    ⋯
    f Pₙ = Nₙ

where the `Pₙ` are patterns (left-hand sides of an equation) and the
`Nₙ` are expressions (right-hand side of an equation).

In the case that there is one equation and the pattern is a variable,
we may also use the syntax

    λ x → N

or

    λ (x : A) → N

both of which are equivalent to `λ{x → N}`. The latter allows one to
specify the domain of the function.

Often using an anonymous lambda expression is more convenient than
using a named function: it avoids a lengthy type declaration; and the
definition appears exactly where the function is used, so there is no
need for the writer to remember to declare it in advance, or for the
reader to search for the definition in the code.


## Function composition

In what follows, we will make use of function composition:
<details><summary>Agda</summary>

```agda
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)
```
</details>

```tex
\func \infixr 8 o {A B C : \Type} (g : B -> C) (f : A -> B) (x : A) : C =>
  g (f x)

\func \infixr 8 o' {A B C : \Type} (g : B -> C) (f : A -> B) : A -> C =>
  \lam x => g (f x)
```
Thus, `g ∘ f` is the function that first applies `f` and
then applies `g`.  An equivalent definition, exploiting lambda
expressions, is as follows:
```
_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)
```


## Extensionality {name=extensionality}

Extensionality asserts that the only way to distinguish functions is
by applying them; if two functions applied to the same argument always
yield the same result, then they are the same function.  It is the
converse of `cong-app`, as introduced
[earlier](/Equality/#cong).

Agda does not presume extensionality, but we can postulate that it holds:
<details><summary>Agda</summary>

```agda
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```
</details>

```tex
-- (!) In Arend, we can prove functional extensionality. Informally, it works like this:
-- 1. `=` is a special case of a type `Path` that has a `path` constructor.
-- `=` can be viewed as a path between values considered equal.
-- 2. `path` accepts a function from a special type `I` to the type of values considered equal.
-- In our case this is `I -> (A -> B)`. The type `I` is an interval that has `left` and `right` contructors.
-- When we prove equality, we need to provide a function that computes to `f` on the `left`,
-- and to `g` on the `right`.
-- 3. Operator `@` computes a path on `I`. For `f x = g x` it computes to `f x` on the `left`,
-- and to `g x` on the `right`. As a result, `\lam x => (eq x) @ i` is `\lam x => f x` on the `left`,
-- and `\lam x => g x` on the `right`.

\func extensionality {A B : \Type} {f g : A -> B} (eq : \Pi (x : A) -> f x = g x) : f = g =>
  path (\lam i => \lam x => (eq x) @ i)
```
Postulating extensionality does not lead to difficulties, as it is
known to be consistent with the theory that underlies Agda.

As an example, consider that we need results from two libraries,
one where addition is defined, as in
Chapter [Naturals](/Naturals/),
and one where it is defined the other way around.
<details><summary>Agda</summary>

```agda
_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)
```
</details>

```tex
-- Builtin `+` is defined by eliminatng the second parameter, so we eliminate the first here.

\func \infixl 6 +' (m n : Nat) : Nat \elim m
  | 0 => n
  | suc m => suc (m +' n)
```
Applying commutativity, it is easy to show that both operators always
return the same result given the same arguments:
<details><summary>Agda</summary>

```agda
same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero    = refl
  helper m (suc n) = cong suc (helper m n)
```
</details>

```tex
\import Paths.Meta (rewrite)

\func same-app (m n : Nat) : m +' n = m + n => rewrite +-comm (helper m n)
  \where {
    \func helper (m n : Nat) : m +' n = n + m \elim m
      | 0 => idp
      | suc m => pmap suc (helper m n)
  }
```
However, it might be convenient to assert that the two operators are
actually indistinguishable. This we can do via two applications of
extensionality:
<details><summary>Agda</summary>

```agda
same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))
```
</details>

```tex
\func same : (+') = (+) => extensionality (\lam m => extensionality (\lam n => same-app m n))
```
We occasionally need to postulate extensionality in what follows.

More generally, we may wish to postulate extensionality for
dependent functions.
<details><summary>Agda</summary>

```agda
postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```
</details>

```tex
\func Pi-extensionality {A : \Type} {B : A -> \Type} {f g : \Pi (x : A) -> B x}
                        (eq : \Pi (x : A) -> f x = g x) : f = g =>
  path (\lam i => \lam x => (eq x) @ i)
```
Here the type of `f` and `g` has changed from `A → B` to
`∀ (x : A) → B x`, generalising ordinary functions to
dependent functions.


## Isomorphism

Two sets are isomorphic if they are in one-to-one correspondence.
Here is a formal definition of isomorphism:
<details><summary>Agda</summary>

```agda
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_
```
</details>

```tex
\record \infix 1 =~ (A B : \Type)
  | to : A -> B
  | from : B -> A
  | from-to : \Pi (x : A) -> from (to x) = x
  | to-from : \Pi (y : B) -> to (from y) = y
```
Let's unpack the definition. An isomorphism between sets `A` and `B` consists
of four things:
+ A function `to` from `A` to `B`,
+ A function `from` from `B` back to `A`,
+ Evidence `from∘to` asserting that `from` is a *left-inverse* for `to`,
+ Evidence `to∘from` asserting that `from` is a *right-inverse* for `to`.

In particular, the third asserts that `from ∘ to` is the identity, and
the fourth that `to ∘ from` is the identity, hence the names.
The declaration `open _≃_` makes available the names `to`, `from`,
`from∘to`, and `to∘from`, otherwise we would need to write `_≃_.to` and so on.

The above is our first use of records. A record declaration behaves similar to a single-constructor data declaration (there are minor differences, which we discuss in [Connectives](/Connectives/)):
<details><summary>Agda</summary>

```agda
data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g
```
</details>

```tex
-- TODO
```

We construct values of the record type with the syntax

    record
      { to    = f
      ; from  = g
      ; from∘to = g∘f
      ; to∘from = f∘g
      }

which corresponds to using the constructor of the corresponding
inductive type

    mk-≃′ f g g∘f f∘g

where `f`, `g`, `g∘f`, and `f∘g` are values of suitable types.


## Isomorphism is an equivalence

Isomorphism is an equivalence, meaning that it is reflexive, symmetric,
and transitive.  To show isomorphism is reflexive, we take both `to`
and `from` to be the identity function:
<details><summary>Agda</summary>

```agda
≃-refl : ∀ {A : Set}
    -----
  → A ≃ A
≃-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{y → refl}
    }
```
</details>

```tex
\func =~-refl {A : \Type} : A =~ A \cowith
  | to x => x
  | from x => x
  | from-to x => idp
  | to-from x => idp

-- Alternative syntax with \new:

\func =~-refl' {A : \Type} : A =~ A => \new =~ {
  | to x => x
  | from x => x
  | from-to x => idp
  | to-from x => idp
}
```
In the above, `to` and `from` are both bound to identity functions,
and `from∘to` and `to∘from` are both bound to functions that discard
their argument and return `refl`.  In this case, `refl` alone is an
adequate proof since for the left inverse, `from (to x)`
simplifies to `x`, and similarly for the right inverse.

To show isomorphism is symmetric, we simply swap the roles of `to`
and `from`, and `from∘to` and `to∘from`:
<details><summary>Agda</summary>

```agda
≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A
≃-sym A≃B =
  record
    { to      = from A≃B
    ; from    = to   A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }
```
</details>

```tex
\func =~-sym {A B : \Type} (A=~B : A =~ B) : B =~ A \cowith
  | to => A=~B.from
  | from => A=~B.to
  | from-to => A=~B.to-from
  | to-from => A=~B.from-to
```

To show isomorphism is transitive, we compose the `to` and `from`
functions, and use equational reasoning to combine the inverses:
<details><summary>Agda</summary>

```agda
≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans A≃B B≃C =
  record
    { to       = to   B≃C ∘ to   A≃B
    ; from     = from A≃B ∘ from B≃C
    ; from∘to  = λ{x →
        begin
          (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
        ≡⟨⟩
          from A≃B (from B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          from A≃B (to A≃B x)
        ≡⟨ from∘to A≃B x ⟩
          x
        ∎}
    ; to∘from = λ{y →
        begin
          (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
        ≡⟨⟩
          to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          to B≃C (from B≃C y)
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎}
     }
```
</details>

```tex
\func =~-trans {A B C : \Type} (A=~B : A =~ B) (B=~C : B =~ C) : A =~ C \cowith
  | to => B=~C.to o A=~B.to
  | from => A=~B.from o B=~C.from
  | from-to x =>
    (A=~B.from o B=~C.from) ((B=~C.to o A=~B.to) x) =<>=
    A=~B.from (B=~C.from (B=~C.to (A=~B.to x))) ==< pmap A=~B.from (B=~C.from-to (A=~B.to x)) >==
    A=~B.from (A=~B.to x) ==< A=~B.from-to x >==
    x `qed
  | to-from x =>
    (B=~C.to o A=~B.to) ((A=~B.from o B=~C.from) x) =<>=
    B=~C.to (A=~B.to (A=~B.from (B=~C.from x))) ==< pmap B=~C.to (A=~B.to-from (B=~C.from x)) >==
    B=~C.to (B=~C.from x) ==< B=~C.to-from x >==
    x `qed
```


## Equational reasoning for isomorphism

It is straightforward to support a variant of equational reasoning for
isomorphism.  We essentially copy the previous definition
of equality for isomorphism.  We omit the form that corresponds to `_≡⟨⟩_`, since
trivial isomorphisms arise far less often than trivial equalities:

<details><summary>Agda</summary>

```agda
module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning
```
</details>

```tex
\module =~-Reasoning \where {
  \func \infix 3 =~< (A : \Type) {B : \Type} (A=~B : A =~ B) : A =~ B => A=~B

  \func \infixr 2 >=~ {A B C : \Type} (A=~B : A =~ B) (B=~C : B =~ C) : A =~ C => =~-trans A=~B B=~C

  \func \fix 3 =~-qed (A : \Type) : A =~ A => =~-refl
}

\open =~-Reasoning
```


## Embedding

We also need the notion of _embedding_, which is a weakening of
isomorphism.  While an isomorphism shows that two types are in
one-to-one correspondence, an embedding shows that the first type is
included in the second; or, equivalently, that there is a many-to-one
correspondence between the second type and the first.

Here is the formal definition of embedding:
<details><summary>Agda</summary>

```agda
infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_
```
</details>

```tex
\record \infix 1 <~ (A B : \Type)
  | to : A -> B
  | from : B -> A
  | from-to : \Pi (x : A) -> from (to x) = x
```
It is the same as an isomorphism, save that it lacks the `to∘from` field.
Hence, we know that `from` is left-inverse to `to`, but not that `from`
is right-inverse to `to`.

Embedding is reflexive and transitive, but not symmetric.  The proofs
are cut down versions of the similar proofs for isomorphism:
<details><summary>Agda</summary>

```agda
≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to      = λ{x → to   B≲C (to   A≲B x)}
    ; from    = λ{y → from A≲B (from B≲C y)}
    ; from∘to = λ{x →
        begin
          from A≲B (from B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
          from A≲B (to A≲B x)
        ≡⟨ from∘to A≲B x ⟩
          x
        ∎}
     }
```
</details>

```tex
\func <~-refl {A : \Type} : A <~ A \cowith
  | to x => x
  | from x => x
  | from-to x => idp

\func <~-trans {A B C : \Type} (A<~B : A <~ B) (B<~C : B <~ C) : A <~ C \cowith
  | to => B<~C.to o A<~B.to
  | from => A<~B.from o B<~C.from
  | from-to x =>
    (A<~B.from o B<~C.from) ((B<~C.to o A<~B.to) x) =<>=
    A<~B.from (B<~C.from (B<~C.to (A<~B.to x))) ==< pmap A<~B.from (B<~C.from-to (A<~B.to x)) >==
    A<~B.from (A<~B.to x) ==< A<~B.from-to x >==
    x `qed
```

It is also easy to see that if two types embed in each other, and the
embedding functions correspond, then they are isomorphic.  This is a
weak form of anti-symmetry:
<details><summary>Agda</summary>

```agda
≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
    -------------------
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to      = to A≲B
    ; from    = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = λ{y →
        begin
          to A≲B (from A≲B y)
        ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
          to A≲B (to B≲A y)
        ≡⟨ cong-app to≡from (to B≲A y) ⟩
          from B≲A (to B≲A y)
        ≡⟨ from∘to B≲A y ⟩
          y
        ∎}
    }
```
</details>

```tex
\func <~-antisym {A B : \Type}
                 (A<~B : A <~ B)
                 (B<~A : B <~ A)
                 (to=from : A<~B.to = B<~A.from)
                 (from=to : A<~B.from = B<~A.to)
  : A =~ B \cowith
  | to => A<~B.to
  | from => A<~B.from
  | from-to => A<~B.from-to
  | to-from => \lam y =>
      A<~B.to (A<~B.from y) ==< pmap A<~B.to (pmap-app from=to y) >==
      A<~B.to (B<~A.to y) ==< pmap-app to=from (B<~A.to y) >==
      B<~A.from (B<~A.to y) ==< B<~A.from-to y >==
      y `qed
```
The first three components are copied from the embedding, while the
last combines the left inverse of `B ≲ A` with the equivalences of
the `to` and `from` components from the two embeddings to obtain
the right inverse of the isomorphism.

## Equational reasoning for embedding

We can also support tabular reasoning for embedding,
analogous to that used for isomorphism:

<details><summary>Agda</summary>

```agda
module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning
```
</details>

```tex
\module <~-Reasoning \where {
  \func \infix 3 <~[ (A : \Type) {B : \Type} (A<~B : A <~ B) : A <~ B => A<~B

  \func \infixr 2 ]<~ {A B C : \Type} (A<~B : A <~ B) (B<~C : B <~ C) : A <~ C => <~-trans A<~B B<~C

  \func \fix 3 <~-qed (A : \Type) : A <~ A => <~-refl
}

\open <~-Reasoning
```

#### Exercise `≃-implies-≲` (practice)

Show that every isomorphism implies an embedding.
```
postulate
  ≃-implies-≲ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≲ B
```

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func =~-implies-<~ {A B : \Type} (A=~B : A =~ B) : A <~ B \cowith
  | to => A=~B.to
  | from => A=~B.from
  | from-to => A=~B.from-to
```

#### Exercise `_⇔_` (practice) {name=iff}

Define equivalence of propositions (also known as "if and only if") as follows:
<details><summary>Agda</summary>

```agda
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
```
</details>

```tex
\record \infix 1 <=> (A B : \Type)
  | to : A -> B
  | from : B -> A
```
Show that equivalence is reflexive, symmetric, and transitive.

<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\func <=>-refl {A : \Type} : A <=> A \cowith
  | to a => a
  | from a => a

\func <=>-sym {A B : \Type} (A<=>B : A <=> B) : B <=> A \cowith
  | to => A<=>B.from
  | from => A<=>B.to

\func <=>-trans {A B C : \Type} (A<=>B : A <=> B) (B<=>C : B <=> C) : A <=> C \cowith
  | to => B<=>C.to o A<=>B.to
  | from => A<=>B.from o B<=>C.from
```

#### Exercise `Bin-embedding` (stretch) {name=Bin-embedding}

Recall that Exercises
[Bin](/Naturals/#Bin) and
[Bin-laws](/Induction/#Bin-laws)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to : ℕ → Bin
    from : Bin → ℕ

which satisfy the following property:

    from (to n) ≡ n

Using the above, establish that there is an embedding of `ℕ` into `Bin`.
<details><summary>Agda</summary>

```agda
-- Your code goes here
```
</details>

```tex
\import util.Arith.Bin

\func Bin-embeds-Nat : Nat <~ Bin \cowith
  | to => Bin.to
  | from => Bin.from
  | from-to => Bin.from-to-id
```

Why do `to` and `from` not form an isomorphism?

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
<details><summary>Agda</summary>

```agda
import Function using (_∘_)
import Function.Inverse using (_↔_)
import Function.LeftInverse using (_↞_)
```
</details>

```tex
-- \import Function (o)
-- \import Equiv (QEquiv, >->)
```
The standard library `_↔_` and `_↞_` correspond to our `_≃_` and
`_≲_`, respectively, but those in the standard library are less
convenient, since they depend on a nested record structure and are
parameterised with regard to an arbitrary notion of equivalence.

## Unicode

This chapter uses the following unicode:

    ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\lambda, \Gl)
    ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~-)
    ≲  U+2272  LESS-THAN OR EQUIVALENT TO (\<~)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
