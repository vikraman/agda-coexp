module Coexp.Kappa.Syntax where

open import Coexp.Prelude
open import Coexp.Meta.Prelude
open import Data.Nat

infixr 40 _`×_
infixr 20 _∘_

data Ty : Set where
  `1 : Ty
  _`×_ : Ty -> Ty -> Ty

open Ctx Ty public

syntax Arr Γ A B = Γ ⊢ A ->> B

data Arr : Ctx -> Ty -> Ty -> Set where

  var : (i : A ∈ Γ)
      ---------
      -> Γ ⊢ `1 ->> A

  id :
     ---------
     Γ ⊢ A ->> A

  bang :
       ----------
       Γ ⊢ A ->> `1

  _∘_ : Γ ⊢ B ->> C -> Γ ⊢ A ->> B
      ------------------------------
      -> Γ ⊢ A ->> C

  lift : Γ ⊢ `1 ->> C
       ------------------
       -> Γ ⊢ A ->> (C `× A)

  κ : (Γ ∙ C) ⊢ A ->> B
    ------------------
    -> Γ ⊢ C `× A ->> B

wk-arr : Wk Γ Δ -> Δ ⊢ A ->> B -> Γ ⊢ A ->> B
wk-arr π (var i) = var (wk-mem π i)
wk-arr π id = id
wk-arr π bang = bang
wk-arr π (e1 ∘ e2) = wk-arr π e1 ∘ wk-arr π e2
wk-arr π (lift e) = lift (wk-arr π e)
wk-arr π (κ e) = κ (wk-arr (wk-cong π) e)

open WkArr Arr wk-arr public
open SubVar `1 var public

sub-arr : Sub Γ Δ -> Δ ⊢ A ->> B -> Γ ⊢ A ->> B
sub-arr θ (var i) = sub-mem θ i
sub-arr θ id = id
sub-arr θ bang = bang
sub-arr θ (e1 ∘ e2) = sub-arr θ e1 ∘ sub-arr θ e2
sub-arr θ (lift e) = lift (sub-arr θ e)
sub-arr θ (κ e) = κ (sub-arr (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) e)

open SubArr sub-arr

variable
  e e1 e2 e3 e4 : Γ ⊢ A ->> B

syntax Eq Γ A B e1 e2 = Γ ⊢ e1 ≈ e2 ∶ A ->> B

data Eq (Γ : Ctx) : (A B : Ty) -> Γ ⊢ A ->> B -> Γ ⊢ A ->> B -> Set where

  unitl : (f : Γ ⊢ A ->> B)
        --------------
        -> Γ ⊢ f ≈ id ∘ f ∶ A ->> B

  unitr : (f : Γ ⊢ A ->> B)
        --------------
        -> Γ ⊢ f ∘ id ≈ f ∶ A ->> B

  assoc : (f : Γ ⊢ A ->> B) (g : Γ ⊢ B ->> C) (h : Γ ⊢ C ->> D)
        ---------------------------------------------------------
        -> Γ ⊢ (h ∘ g) ∘ f ≈ h ∘ (g ∘ f) ∶ A ->> D

  term : (f g : Γ ⊢ A ->> `1)
       -------------------------
       -> Γ ⊢ f ≈ g ∶ A ->> `1

  κ-beta : (f : (Γ ∙ C) ⊢ A ->> B) (c : Γ ⊢ `1 ->> C)
            ------------------------------------------------
            -> Γ ⊢ κ {C = C} f ∘ lift {A = A} c ≈ sub c f ∶ A ->> B

  κ-eta : (f : Γ ⊢ C `× A ->> B)
         ---------------------------------------------------
         -> Γ ⊢ κ {C = C} (wk f ∘ lift {A = A} (var h)) ≈ f ∶ C `× A ->> B
