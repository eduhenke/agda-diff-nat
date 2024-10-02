module Data.DiffNat where
  
import Data.Nat as Nat
import Data.Nat.Properties as ℕ-Prop
open import Function using () renaming (_∘′_ to _∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

add = Nat._+_

infixr 5 _,_
infixr 5 _+_

module PropEq where
  infixr 5 _≐_
  data _≐_ {ℓ} {A : Set ℓ} (x : A) : A → Prop ℓ where
    refl : x ≐ x

  cong : ∀ {A B : Set} (f : A → B) {x y} → x ≐ y → f x ≐ f y
  cong f refl = refl

  cong₂ : ∀ {A B C : Set} (f : A → B → C) {x y u v} → x ≐ y → u ≐ v → f x u ≐ f y v
  cong₂ f refl refl = refl

  trans : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
  trans refl eq = eq

  sym : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
  sym refl = refl

  ≡→≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
  ≡→≐ Eq.refl = refl

open PropEq

private
  +-identityʳ′ : ∀ n → add n 0 ≐ n
  +-identityʳ′ n = ≡→≐ (ℕ-Prop.+-identityʳ n)

  +-assoc′ : ∀ m n → add (add m n) ≐ (add m) ∘ (add n)
  +-assoc′ Nat.zero    n = refl
  +-assoc′ (Nat.suc m) n = cong (_∘_ Nat.suc) (+-assoc′ m n)

-- "Difference nats" are isomorphic to ℕ but have _+_ associative up 
-- to beta-reduction, not just up to _≡_.

record ℕ : Set where
  constructor _,_
  field
    fn : Nat.ℕ → Nat.ℕ
    fn-ok : fn ≐ add (fn 0)

open ℕ

-- Convert ℕ to Nat.ℕ and back

↑ : Nat.ℕ → ℕ
↑ n = add n , cong add (sym (+-identityʳ′ n))

↓ : ℕ → Nat.ℕ
↓ (f , f-ok) = f 0

-- Constants

↑0 = ↑ 0
↑1 = ↑ 1

-- Addition

_+_ : ℕ → ℕ → ℕ
(f , f-ok) + (g , g-ok) = f ∘ g , f∘g-ok where
  f∘g-ok : (f ∘ g) ≐ add (f (g 0))
  f∘g-ok = trans
    (cong₂ _∘_ f-ok g-ok)
    (trans
      (sym (+-assoc′ (f 0) (g 0)))
      (cong (λ X → add (X (g 0))) (sym f-ok))
    )

-- Isomorphism which respects +

inject : ∀ m n → (fn m ≐ fn n) → (m ≐ n)
inject (f , f-ok) (.f , g-ok) refl = refl

iso : ∀ n → ↑ (↓ n) ≐ n
iso n = inject _ _ (sym (fn-ok n))

iso⁻¹ : ∀ n → ↓ (↑ n) ≐ n
iso⁻¹ Nat.zero = refl
iso⁻¹ (Nat.suc n) = cong Nat.suc (iso⁻¹ n)

iso-resp-+ : ∀ m n → ↓ (m + n) ≐ add (↓ m) (↓ n)
iso-resp-+ (f , f-ok) (g , g-ok) = cong (λ X → X (g 0)) f-ok

-- Properties of addition proven definitionally

+-assoc : ∀ l m n → l + m + n ≡ l + (m + n)
+-assoc l m n = Eq.refl

+-identityˡ : ∀ n → ↑0 + n ≡ n
+-identityˡ n = Eq.refl

+-identityʳ : ∀ n → n + ↑0 ≡ n
+-identityʳ n = Eq.refl
