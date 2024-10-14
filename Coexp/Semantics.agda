module Coexp.Semantics where

open import Coexp.Prelude
open import Data.Unit
open import Data.Empty
open import Data.Product as P renaming (map to pmap)
open import Data.Sum as S renaming (map to smap)
open import Function
open import Data.Bool hiding (T)
open import Data.Nat
open import Relation.Binary.PropositionalEquality

infixr 20 _；_

-- categorical combinators for a ccc
_；_ : {X Y Z : Set} -> (X -> Y) -> (Y -> Z) -> (X -> Z)
f ； g = g ∘ f

elem : {X : Set} -> X -> ⊤ -> X
elem = const

idf : {X : Set} -> X -> X
idf = id

eval : {X Y : Set} -> (X -> Y) × X -> Y
eval (f , x) = f x

contramap : {X Y Z : Set} -> (X -> Y) -> (Z -> X) -> (Z -> Y)
contramap = _∘′_

compose : {X Y Z : Set} -> (Y -> Z) × (X -> Y) -> X -> Z
compose = uncurry contramap

distl : {X Y Z : Set} -> X × (Y ⊎ Z) -> X × Y ⊎ X × Z
distl = uncurry \x -> S.[ (x ,_) ； inj₁ , (x ,_) ； inj₂ ]′

distr : {X Y Z : Set} -> X × Y ⊎ X × Z -> X × (Y ⊎ Z)
distr = S.[ pmap id inj₁ , pmap id inj₂ ]′

⊎-eta : {X Y Z : Set} -> S.[ inj₁ {B = Y} , inj₂ {A = X} ]′ ≡ id {A = X ⊎ Y}
⊎-eta = funext \{ (inj₁ x) -> refl ; (inj₂ y) -> refl }

absurd : {X : Set} -> ⊥ -> X
absurd = ⊥-elim

absurd-eta : {X : Set} -> (f g : ⊥ -> X) -> f ≡ g
absurd-eta f g = funext λ ()

is-zero : ℕ -> ⊤ ⊎ ⊤
is-zero zero = inj₁ tt
is-zero (suc n) = inj₂ tt

variable
  X Y Z : Set
  x y z : X

-- strong monad T
record MonadStructure (T : Set -> Set) : Set₁ where
  field
    map : ∀ {X Y} -> (X -> Y) -> T X -> T Y
    map-id : map id ≡ id {A = T X}
    map-comp : {f : X -> Y} {g : Y -> Z} -> map (f ； g) ≡ map f ； map g
    eta : ∀ {X} -> X -> T X
    mu : ∀ {X} -> T (T X) -> T X
    unitl : map {Y = T X} eta ； mu ≡ id
    unitr : eta {X = T X} ； mu ≡ id
    assoc : mu {X = T X} ； mu ≡ map {Y = T X} mu ； mu

  -- haskell's bind
  bind : T X × (X -> T Y) -> T Y
  bind (k , f) = mu (map f k)

  -- kleisli lift
  lift : (X -> Y) -> X -> T Y
  lift = eta ∘_

  -- kleisli extension
  extend : (X -> T Y) -> T X -> T Y
  extend f = map f ； mu

  composek : (Y -> T Z) -> (X -> T Y) -> X -> T Z
  composek g f = f ； extend g

  -- strength combinators
  tau : X × T Y -> T (X × Y)
  tau (x , k) = map (\z -> x , z) k

  sigma : T X × Y -> T (X × Y)
  sigma (k , y) = map (\z -> z , y) k

  alpha : T X × T Y -> T (X × Y)
  alpha = sigma ； map tau ； mu

  beta : T X × T Y -> T (X × Y)
  beta = tau ； map sigma ； mu

  -- haskell's applicative
  ap : T (X -> Y) -> T X -> T Y
  ap = curry (beta ； map eval)

open MonadStructure

module Cont (R : Set) where

  T : Set -> Set
  T X = (X -> R) -> R

  M : MonadStructure T
  map M f g k = g (f ； k)
  map-id M = refl
  map-comp M = refl
  eta M x k = k x
  mu M g k = g \h -> h k
  unitl M = refl
  unitr M = refl
  assoc M = refl

  module T = MonadStructure M

  cocurry : (Y -> T (X ⊎ Z))  -> (Y × (X -> R) -> T Z)
  cocurry f (y , k1) k2 = f y S.[ k1 , k2 ]′

  councurry : (Y × (X -> R) -> T Z) -> (Y -> T (X ⊎ Z))
  councurry f y k = f (y , inj₁ ； k) (inj₂ ； k)

  councurry-cocurry : (f : Y -> T (X ⊎ Z)) -> councurry (cocurry f) ≡ f
  councurry-cocurry f =
    funext \y -> funext \k ->
      cong (f y) (funext \{ (inj₁ x) -> refl ; (inj₂ z) -> refl })

  cocurry-councurry : (g : Y × (X -> R) -> T Z) -> cocurry (councurry g) ≡ g
  cocurry-councurry g =
    funext \(y , k) -> refl

  coeval : Y -> T (X ⊎ (Y × (X -> R)))
  coeval = councurry T.eta

  couneval' : (X ⊎ Y) × (X -> R) -> T Y
  couneval' = cocurry T.eta

  couneval : T (X ⊎ Y) × (X -> R) -> T Y
  couneval = cocurry id

  𝒜 : X × (X -> R) -> T Y
  𝒜 = cocurry (inj₁ ； T.eta)

  idk : {X : Set} -> X -> T X
  idk = T.eta

  coelem : {X : Set} -> (X -> R) -> X -> T ⊥
  coelem = const ； flip
