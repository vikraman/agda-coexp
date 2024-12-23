module Coexp.Prelude where

open import Function
open import Relation.Binary.PropositionalEquality

postulate
  TODO : ∀ {a} {A : Set a} -> A

{-# BUILTIN REWRITE _≡_ #-}

module _ where
  postulate
    I : Set
    i0 i1 : I
    seg : i0 ≡ i1

  module _ {p} {P : Set p} where
    postulate
      I-rec : (p0 p1 : P) (p : p0 ≡ p1) -> I -> P
      I-rec-i0 : ∀ {p0} {p1} {p} -> I-rec p0 p1 p i0 ≡ p0
      {-# REWRITE I-rec-i0 #-}
      I-rec-i1 : ∀ {p0} {p1} {p} -> I-rec p0 p1 p i1 ≡ p1
      {-# REWRITE I-rec-i1 #-}
      I-rec-seg : ∀ {p0} {p1} {p} -> cong (I-rec p0 p1 p) seg ≡ p

funext : ∀ {a b} {A : Set a} {B : Set b} {f g : A -> B} -> ((x : A) -> f x ≡ g x) -> f ≡ g
funext {f = f} {g = g} H = cong (flip \a -> I-rec (f a) (g a) (H a)) seg

happly : ∀ {a b} {A : Set a} {B : Set b} {f g : A -> B} -> f ≡ g -> (x : A) -> f x ≡ g x
happly p x = cong (_$ x) p

happly-funext : ∀ {a b} {A : Set a} {B : Set b} {f g : A -> B} (H : (x : A) -> f x ≡ g x) -> ∀ x -> happly (funext H) x ≡ H x
happly-funext {f = f} {g = g} H x =
  happly (funext H) x                                         ≡⟨ refl ⟩
  cong (_$ x) (cong (flip \a -> I-rec (f a) (g a) (H a)) seg) ≡⟨ sym (cong-∘ seg) ⟩
  cong ((_$ x) ∘ (flip \a -> I-rec (f a) (g a) (H a))) seg    ≡⟨ I-rec-seg ⟩
  H x ∎
  where open ≡-Reasoning

open import Data.Nat

recNat : ∀ {a} {A : Set a} -> A -> (A -> A) -> ℕ -> A
recNat a f zero = a
recNat a f (suc n) = f (recNat a f n)

primNat : ∀ {a} {A : Set a} -> A -> (ℕ -> A -> A) -> ℕ -> A
primNat a f zero = a
primNat a f (suc n) = f n (primNat a f n)

precNat : ∀ {a} {A : Set a} -> A -> (ℕ -> A -> A) -> ℕ -> A
precNat a f n = recNat a (f n) n
