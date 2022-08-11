{---
title = "The Kavvos-Sojakova proof of Syllepsis in Agda";
---}

In this file we work through the Kavvos-Sojakova proof of the syllepsis as given in [this paper](https://dl.acm.org/doi/10.1145/3531130.3533347).

<details>
<summary> Module header </summary>

```agda
module Syllepsis where

open import Agda.Builtin.Equality

variable
  X Y Z : Set
  x y z w : X
  p q r s t u v : x ≡ y
```

</details>

We start by defining composition of paths. Note that the one below is the weakest form of equality we can give with the J rule, and does not give us the definitional equality `refl ∙ p = p′. This was done to see if any of the paper proof relied on this property, and it was found that this was used in two places, which were both easily fixable. After this we give the horizontal composition of 2-paths, and both whiskering operations, as in the paper.

```agda
infixr 5 _∙_
_∙_ : x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl

infixl 6 _⋆_
_⋆_ : (α : p ≡ q) → (β : r ≡ s) → p ∙ r ≡ q ∙ s
refl ⋆ refl = refl

lwhisk : (p : x ≡ y) → (α : q ≡ r) → p ∙ q ≡ p ∙ r
lwhisk p refl = refl

rwhisk : (α : p ≡ q) → (r : y ≡ z) → p ∙ r ≡ q ∙ r
rwhisk refl r = refl
```

We next give some standard properties of equality.
<details>
<summary>Standard properties of equality</summary>

```agda
sym : x ≡ y → y ≡ x
sym refl = refl

linv : (p : x ≡ y) → sym p ∙ p ≡ refl
linv refl = refl

rinv : (p : x ≡ y) → p ∙ sym p ≡ refl
rinv refl = refl

cong : (f : X → Y) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : (f : X → Y → Z) → x ≡ y → z ≡ w → f x z ≡ f y w
cong₂ f refl refl = refl

lunit : (p : x ≡ y) → refl ∙ p ≡ p
lunit refl = refl

runit : (p : x ≡ y) → p ∙ refl ≡ p
runit refl = refl

assoc : (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc refl refl refl = refl
```

</details>

Using these we can set up equational reasoning, as in the [standard library](https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#2708). We set this up slightly differently to normal, so that no extra reflexivity is added to the end of the proof. This is necessary as we are trying to reason about the paths we define with equational reasoning. Equational reasoning does not allow us to do anything tha could not be done with path composition, but it increases the readability of proofs considerably.

<details>
<summary>Equational Reasoning</summary>

```agda
module ≡-Reasoning {A : Set} where

  infixr 3 step-end step-end˘
  infixr 2 _≡⟨⟩_ step-≡ step-≡˘
  infix  1 begin_

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ y≡z x≡y = x≡y ∙ y≡z

  step-≡˘ : ∀ (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
  step-≡˘ _ y≡z y≡x = (sym y≡x) ∙ y≡z

  step-end : ∀ (x y : A) → x ≡ y → x ≡ y
  step-end _ _ x≡y = x≡y

  step-end˘ : ∀ (x y : A) → y ≡ x → x ≡ y
  step-end˘ _ _ y≡x = sym y≡x

  syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
  syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
  syntax step-end  x y x≡y = x ≡⟨  x≡y ⟩′ y ∎
  syntax step-end˘ x y y≡x = x ≡˘⟨ y≡x ⟩′ y ∎
```

</details>

## Squares
We next formalise the various lemmas about squares that appear in section 5. This is a change in order from the paper, but allows us to keep all square related lemmas in the same place, at the cost of delaying the definition of Eckmann-Hilton. We start with the definition of a square.

```agda
Square : (p : x ≡ y) → (q : x ≡ z) → (r : y ≡ w) → (s : z ≡ w) → Set
Square p q r s = p ∙ r ≡ q ∙ s
```

We now show Lemma 3.1, that degenerate squares are equivalent to paths. We rename ⇉ and ⇊ to cancel→ and cancel↓ as ⇉ and ⇊ are hard to read.

```agda
cancel→ : Square p refl refl q → p ≡ q
cancel→ {p = p} {q = q} α = begin
  p
    ≡˘⟨ runit p ⟩
  p ∙ refl
    ≡⟨ α ⟩
  refl ∙ q
    ≡⟨ lunit q ⟩′
  q ∎
  where open ≡-Reasoning

cancel→′ : p ≡ q → Square p refl refl q
cancel→′ {p = p} {q = q} α = begin
  p ∙ refl
    ≡⟨ runit p ⟩
  p
    ≡⟨ α ⟩
  q
    ≡˘⟨ lunit q ⟩′
  refl ∙ q ∎
  where open ≡-Reasoning

cancel→linv : {p q : x ≡ y} → (α : Square p refl refl q) → cancel→′ (cancel→ α) ≡ α
cancel→linv {p = p} {q = q} α = begin
  runit p ∙ (sym (runit p) ∙ α ∙ lunit q) ∙ sym (lunit q)
    ≡⟨ lwhisk (runit p) (assoc _ _ _) ⟩
  runit p ∙ sym (runit p) ∙ (α ∙ lunit q) ∙ sym (lunit q)
    ≡˘⟨ assoc _ _ _ ⟩
  (runit p ∙ sym (runit p)) ∙ (α ∙ lunit q) ∙ sym (lunit q)
    ≡⟨ (rinv (runit p)) ⋆ (assoc _ _ _ ∙ (refl ⋆ rinv (lunit q))) ⟩
  refl ∙ α ∙ refl
    ≡⟨ lunit (α ∙ refl) ⟩
  α ∙ refl
    ≡⟨ runit α ⟩′
  α ∎
  where open ≡-Reasoning

cancel→rinv : (α : p ≡ q) → cancel→ (cancel→′ α) ≡ α
cancel→rinv {p = refl} refl = refl

cancel↓ : Square refl q p refl → p ≡ q
cancel↓ {q = q} {p = p} α = begin
  p
    ≡˘⟨ lunit p ⟩
  refl ∙ p
    ≡⟨ α ⟩
  q ∙ refl
    ≡⟨ runit q ⟩′
  q ∎
  where open ≡-Reasoning

cancel↓′ : p ≡ q → Square refl q p refl
cancel↓′ {p = p} {q = q} α = begin
  refl ∙ p
    ≡⟨ lunit p ⟩
  p
    ≡⟨ α ⟩
  q
    ≡˘⟨ runit q ⟩′
  q ∙ refl ∎
  where open ≡-Reasoning

cancel↓linv : {p q : x ≡ y} → (α : Square refl p q refl) → cancel↓′ (cancel↓ α) ≡ α
cancel↓linv {p = p} {q = q} α = begin
  lunit q ∙ (sym (lunit q) ∙ α ∙ runit p) ∙ sym (runit p)
    ≡⟨ lwhisk (lunit q) (assoc _ _ _) ⟩
  lunit q ∙ sym (lunit q) ∙ (α ∙ runit p) ∙ sym (runit p)
    ≡˘⟨ assoc _ _ _ ⟩
  (lunit q ∙ sym (lunit q)) ∙ (α ∙ runit p) ∙ sym (runit p)
    ≡⟨ rinv (lunit q) ⋆ (assoc _ _ _ ∙ (refl ⋆ rinv (runit p))) ⟩
  refl ∙ α ∙ refl
    ≡⟨ lunit (α ∙ refl) ⟩
  α ∙ refl
    ≡⟨ runit α ⟩′
  α ∎
  where open ≡-Reasoning
```

We can define the horizontal and vertical composition of squares.

```agda
horiz : Square p q r s → Square s t u v → Square p (q ∙ t) (r ∙ u) v
horiz {p = p} {q = q} {r = r} {s = s} {t = t} {u = u} {v = v} α β = begin
  p ∙ (r ∙ u)
    ≡˘⟨ assoc p r u ⟩
  (p ∙ r) ∙ u
    ≡⟨ rwhisk α u ⟩
  (q ∙ s) ∙ u
    ≡⟨ assoc q s u ⟩
  q ∙ (s ∙ u)
    ≡⟨ lwhisk q β ⟩
  q ∙ (t ∙ v)
    ≡˘⟨ assoc q t v ⟩′
  (q ∙ t) ∙ v ∎
  where open ≡-Reasoning

vert : Square p q r s → Square t r u v → Square (p ∙ t) q u (s ∙ v)
vert {p = p} {q = q} {r = r} {s = s} {t = t} {u = u} {v = v} α β = begin
  (p ∙ t) ∙ u
    ≡⟨ assoc p t u ⟩
  p ∙ (t ∙ u)
    ≡⟨ lwhisk p β ⟩
  p ∙ (r ∙ v)
    ≡˘⟨ assoc p r v ⟩
  (p ∙ r) ∙ v
    ≡⟨ rwhisk α v ⟩
  (q ∙ s) ∙ v
    ≡⟨ assoc q s v ⟩′
  q ∙ (s ∙ v) ∎
  where open ≡-Reasoning
```

We prove lemmas 5.1 and 5.2. The helper functions here abstract over the equivalences between paths and degenerate squares at which point we can use `cancel→linv` to fix the type.

```agda
horiz→help : {p q r : x ≡ y} → (α : p ≡ q) → (β : q ≡ r) → α ∙ β ≡ cancel→ (horiz (cancel→′ α) (cancel→′ β))
horiz→help {p = refl} refl refl = refl

horiz→ : {p q r : x ≡ y} → (α : Square p refl refl q) → (β : Square q refl refl r) → cancel→ α ∙ cancel→ β ≡ cancel→ (horiz α β)
horiz→ α β = (horiz→help (cancel→ α) (cancel→ β)) ∙ cong₂ (λ a b → cancel→ (horiz a b)) (cancel→linv α) (cancel→linv β)

vert→help : {p q : x ≡ y} → {r s : y ≡ z} → (α : p ≡ q) → (β : r ≡ s) → α ⋆ β ≡ cancel→ (vert (cancel→′ α) (cancel→′ β))
vert→help {p = refl} {r = refl} refl refl = refl

vert→ : {p q : x ≡ y} → {r s : y ≡ z} → (α : Square p refl refl q) → (β : Square r refl refl s) → cancel→ α ⋆ cancel→ β ≡ cancel→ (vert α β)
vert→ α β = vert→help (cancel→ α) (cancel→ β) ∙ cong₂ (λ a b → cancel→ (vert a b)) (cancel→linv α) (cancel→linv β)
```

## Eckmann-Hilton
We can now prove Eckmann-Hilton, starting with Lemmas 2.1 and 2.2, which proceed by path induction as promised.

```agda
ulnat : (α : p ≡ q) → Square (lwhisk refl α) (lunit p) (lunit q) α
ulnat {p = refl} refl = refl

urnat : (α : p ≡ q) → Square (rwhisk α refl) (runit p) (runit q) α
urnat {q = refl} refl = refl

wlrnat : {p q : x ≡ y} → {r s : y ≡ z} → (α : p ≡ q) → (β : r ≡ s)
       → Square (lwhisk p β) (rwhisk α r) (rwhisk α s) (lwhisk q β)
wlrnat refl refl = refl
```

Eckmann-Hilton is then the following.

```agda
eh : (p q : refl {x = x} ≡ refl) → p ∙ q ≡ q ∙ p
eh p q = begin
  p ∙ q
    ≡˘⟨ cancel→ (ulnat p) ⋆ cancel→ (urnat q) ⟩
  lwhisk refl p ∙ rwhisk q refl
    ≡⟨ wlrnat q p ⟩
  rwhisk q refl ∙ lwhisk refl p
    ≡⟨ cancel→ (urnat q) ⋆ cancel→ (ulnat p) ⟩′
  q ∙ p ∎
  where open ≡-Reasoning
```

We can prove the lemmas for Eckmann-Hilton on reflexivity as in the paper. The helper functions here correspond to the 'pentagon' equations in the paper.

```agda
ehlreflhelp : {p q : x ≡ y} → (α : p ≡ q) → (r : y ≡ z) → (s : p ∙ r ≡ q ∙ r) → (θ : rwhisk α r ≡ s)
            → (sym (refl ⋆ θ) ∙ wlrnat α refl ∙ θ ⋆ refl) ∙ runit s ≡ lunit s
ehlreflhelp refl r .(rwhisk refl r) refl = refl

ehlrefl : (p : refl {x = x} ≡ refl) → eh refl p ∙ runit p ≡ lunit p
ehlrefl p = ehlreflhelp p refl p (cancel→ (urnat p))

ehrreflhelp : (p : x ≡ y) → {q r : y ≡ z} → (β : q ≡ r) → (s : p ∙ q ≡ p ∙ r) → (θ : lwhisk p β ≡ s)
            → (sym (θ ⋆ refl) ∙ wlrnat refl β ∙ refl ⋆ θ) ∙ lunit s ≡ runit s
ehrreflhelp p refl .(lwhisk p refl) refl = refl

ehrrefl : (p : refl {x = x} ≡ refl) → eh p refl ∙ lunit p ≡ runit p
ehrrefl p = ehrreflhelp refl p p (cancel→ (ulnat p))
```

We can also give proofs of both Lemmas 6.1 and 6.2. Again, as promised the results follow quickly from path induction. In the first two naturality lemmas we are left with a very degenerate square, which can be filled with `cancel↓′` on `refl`.

```agda
ehnatl : {p q : refl {x = x} ≡ refl} → (α : p ≡ q) → (r : refl {x = x} ≡ refl) → Square (rwhisk α r) (eh p r) (eh q r) (lwhisk r α)
ehnatl refl r = cancel↓′ refl

ehnatr : {p q : refl {x = x} ≡ refl} → (α : p ≡ q) → (r : refl {x = x} ≡ refl) → Square (lwhisk r α) (eh r p) (eh r q) (rwhisk α r)
ehnatr refl r = cancel↓′ refl

ehnatlnat : {p : refl {x = x} ≡ refl} → (α : refl ≡ p) → horiz (ehnatl α refl) (ulnat α) ≡ lwhisk (rwhisk α refl) (ehrrefl p) ∙ urnat α
ehnatlnat refl = refl

ehnatrnat : {p : refl {x = x} ≡ refl} → (α : refl ≡ p) → horiz (ehnatr α refl) (urnat α) ≡ lwhisk (lwhisk refl α) (ehlrefl p) ∙ ulnat α
ehnatrnat refl = refl
```

## The Syllepsis

We now have all the components of the syllepsis. The paper splits the syllepsis into a square `squareb`, and two triangles `trianglea` and `triangleb`. We cane construct `squareb` easily by path induction.

```agda
squareb : {p q r s : refl {x = x} ≡ refl} → (α : p ≡ q) → (β : r ≡ s) → Square (wlrnat α β ⋆ refl) (vert (ehnatr β p) (ehnatl α s)) (vert (ehnatl α r) (ehnatr β q)) (refl ⋆ sym (wlrnat β α))
squareb refl refl = cancel↓′ refl
```

We will construct triangles a and c with the second proof given in the paper. We start by proving lemma 7.2. We first use path induction over the last two arguments, and then pass from degenerate squares to paths in `squarelemhelp` which allows us to finish the proof using path induction.

```agda
squarelemhelp : {p q r : x ≡ y} → {u v w : y ≡ z}
              → (α : p ≡ q)
              → (β : q ≡ r)
              → (γ : u ≡ v)
              → (δ : v ≡ w)
              → α ⋆ γ ∙ β ⋆ δ ≡ (α ∙ β) ⋆ (γ ∙ δ)
squarelemhelp refl refl refl refl = refl

squarelem : {p q r : x ≡ y} → {u v w : y ≡ z}
          → (α : Square p refl refl q)
          → (β : Square q refl refl r)
          → (γ : Square u refl refl v)
          → (δ : Square v refl refl w)
          → (ϕ : Square p refl refl r)
          → (θ : Square u refl refl w)
          → (horiz α β ≡ ϕ)
          → (horiz γ δ ≡ θ)
          → cancel→ (vert α γ) ∙ cancel→ β ⋆ cancel→ δ ≡ cancel→ ϕ ⋆ cancel→ θ
squarelem α β γ δ .(horiz α β) .(horiz γ δ) refl refl = begin
  cancel→ (vert α γ) ∙ cancel→ β ⋆ cancel→ δ
    ≡˘⟨ cong (_∙ cancel→ β ⋆ cancel→ δ) (vert→ α γ) ⟩
  cancel→ α ⋆ cancel→ γ ∙ cancel→ β ⋆ cancel→ δ
    ≡⟨ squarelemhelp (cancel→ α) (cancel→ β) (cancel→ γ) (cancel→ δ) ⟩
  (cancel→ α ∙ cancel→ β) ⋆ (cancel→ γ ∙ cancel→ δ)
    ≡⟨ cong₂ _⋆_ (horiz→ α β) (horiz→ γ δ) ⟩′
  cancel→ (horiz α β) ⋆ cancel→ (horiz γ δ) ∎
  where open ≡-Reasoning
```

After this, triangles a and c can be constructed by applying `squarelem`, letting agda solve all the arguments apart from the last two, and then using `ehnatrnat` and `ehnatlnat` to fill the equalities. As noted in the introduction, there were exactly two places where the definitional equality `refl ∙ p = p` was used in the paper and this was for these two equalities. These are luckily easily fixed by applying a left unit path.

```agda
trianglea : (p q : refl {x = refl {x = x}} ≡ refl) → cancel→ (vert (ehnatr p refl) (ehnatl q refl))
                                                   ∙ cancel→ (urnat p) ⋆ cancel→ (ulnat q)
                                                   ≡ cancel→ (ulnat p) ⋆ cancel→ (urnat q)
trianglea p q = squarelem (ehnatr p refl) (urnat p) (ehnatl q refl) (ulnat q) (ulnat p) (urnat q) (ehnatrnat p ∙ lunit (ulnat p)) (ehnatlnat q ∙ lunit (urnat q))

trianglec : (p q : refl {x = refl {x = x}} ≡ refl) → cancel→ (vert (ehnatl q refl) (ehnatr p refl))
                                                   ∙ cancel→ (ulnat q) ⋆ cancel→ (urnat p)
                                                   ≡ cancel→ (urnat q) ⋆ cancel→ (ulnat p)
trianglec p q = squarelem (ehnatl q refl) (ulnat q) (ehnatr p refl) (urnat p) (urnat q) (ulnat p) (ehnatlnat q ∙ lunit (urnat q)) (ehnatrnat p ∙ lunit (ulnat p))
```

We then construct the syllepsis generator from Lemma 7.3. In contrast to the paper proof, we first induct on all of `a21`, `a31`, `a24`, `a53`, `a56`, and the lower triangle (note that `a31` is not inducted on in the paper proof). We then use a with extraction to get access to the path `ϕ ≡ ψ` so that we can induct on it. After this we simply need to rewrite by `t1` (using a `sym (runit _)` to simplify its type.

```agda
syllepsisgen : {a1 a2 a3 a4 a5 a6 : x ≡ y}
             → (a21 : a2 ≡ a1)
             → (a31 : a3 ≡ a1)
             → (a24 : a2 ≡ a4)
             → (a53 : a5 ≡ a3)
             → (a46 : a4 ≡ a6)
             → (a56 : a5 ≡ a6)
             → (ϕ : Square a2 refl refl a3)
             → (θ : Square a4 refl refl a5)
             → (t1 : cancel→ ϕ ∙ a31 ≡ a21)
             → (t2 : cancel→ θ ∙ a56 ≡ a46)
             → (square : Square (a24 ⋆ refl) ϕ θ (refl ⋆ sym a53))
             → (sym a21 ∙ a24 ∙ a46) ∙ (sym a56 ∙ a53 ∙ a31) ≡ refl
syllepsisgen refl refl refl refl .(cancel→ θ ∙ refl) refl ϕ θ t1 refl square with cancel↓ square
... | refl rewrite sym (runit _) ∙ t1 = refl
```

Finally we can use `syllepsisgen` with `trianglea`, `squareb` and `trianglec` to get the syllepsis.

```agda
syllepsis : (p q : refl {x = refl {x = x}} ≡ refl) → eh p q ∙ eh q p ≡ refl
syllepsis p q = syllepsisgen (cancel→ (ulnat p) ⋆ cancel→ (urnat q))
                             (cancel→ (urnat p) ⋆ cancel→ (ulnat q))
                             (wlrnat q p)
                             (wlrnat p q)
                             (cancel→ (urnat q) ⋆ cancel→ (ulnat p))
                             (cancel→ (ulnat q) ⋆ cancel→ (urnat p))
                             (vert (ehnatr p refl) (ehnatl q refl))
                             (vert (ehnatl q refl) (ehnatr p refl))
                             (trianglea p q)
                             (trianglec p q)
                             (squareb q p)
```

## Final remarks
Overall, the proof was easy to follow and translate into Agda, and I believe the final proof is very clean. We could neaten up the above proof slightly by using a right computing equality (such that `p ∙ refl = refl` definitionally) which should allow us to use the standard setup for equational reasoning.

Thanks goes to Kristina Sojakova and Alex Kavvos for constructing the original proof, writing the proof up, and presenting it at HoTT/UF and LICS.
