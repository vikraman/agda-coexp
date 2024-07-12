module Coexp.Prelude where

open import Relation.Binary.PropositionalEquality

postulate
  TODO : ∀ {a} {A : Set a} -> A

postulate
  funext : ∀ {a b} {A : Set a} {B : Set b} {f g : A -> B} -> ((x : A) -> f x ≡ g x) -> f ≡ g

happly : ∀ {a b} {A : Set a} {B : Set b} {f g : A -> B} -> f ≡ g -> (x : A) -> f x ≡ g x
happly refl _ = refl

open import Data.Nat

recNat : ∀ {a} {A : Set a} -> A -> (A -> A) -> ℕ -> A
recNat a f zero = a
recNat a f (suc n) = f (recNat a f n)

primNat : ∀ {a} {A : Set a} -> A -> (ℕ -> A -> A) -> ℕ -> A
primNat a f zero = a
primNat a f (suc n) = f n (primNat a f n)

precNat : ∀ {a} {A : Set a} -> A -> (ℕ -> A -> A) -> ℕ -> A
precNat a f n = recNat a (f n) n
