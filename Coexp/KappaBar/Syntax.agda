module Coexp.KappaBar.Syntax where

open import Coexp.Prelude
open import Coexp.Meta.Prelude
open import Data.Nat

infixr 40 _`-_
infixr 20 _∘_

data Ty : Set where
  `0 : Ty
  _`-_ : Ty -> Ty -> Ty

open Ctx Ty public

syntax Arr Γ A B = Γ ⊢ A ->> B

data Arr : Ctx -> Ty -> Ty -> Set where

  covar : (i : A ∈ Γ)
        ----------------
        -> Γ ⊢ A ->> `0

  id :
     ------------
     Γ ⊢ A ->> A

  bang :
       ------------
       Γ ⊢ `0 ->> A

  _∘_ : Γ ⊢ B ->> C -> Γ ⊢ A ->> B
      --------------------------------
      -> Γ ⊢ A ->> C

  lift̃ : Γ ⊢ C ->> `0
        ------------------------
        -> Γ ⊢ A ->> (A `- C)

  κ̃ : (Γ ∙ C) ⊢ A ->> B
     -----------------------
     -> Γ ⊢ (A `- C) ->> B

wk-arr : Wk Γ Δ -> Δ ⊢ A ->> B -> Γ ⊢ A ->> B
wk-arr π (covar i) = covar (wk-mem π i)
wk-arr π id = id
wk-arr π bang = bang
wk-arr π (e1 ∘ e2) = wk-arr π e1 ∘ wk-arr π e2
wk-arr π (lift̃ e) = lift̃ (wk-arr π e)
wk-arr π (κ̃ e) = κ̃ (wk-arr (wk-cong π) e)

open WkArr Arr wk-arr public
open SubCoVar `0 covar public

sub-arr : Sub Γ Δ -> Δ ⊢ A ->> B -> Γ ⊢ A ->> B
sub-arr θ (covar i) = sub-mem θ i
sub-arr θ id = id
sub-arr θ bang = bang
sub-arr θ (e1 ∘ e2) = sub-arr θ e1 ∘ sub-arr θ e2
sub-arr θ (lift̃ e) = lift̃ (sub-arr θ e)
sub-arr θ (κ̃ e) = κ̃ (sub-arr (sub-ex (sub-wk (wk-wk wk-id) θ) (covar h)) e)

open SubArr sub-arr

variable
  e e1 e2 e3 e4 : Γ ⊢ A ->> B

syntax Eq Γ A B e1 e2 = Γ ⊢ e1 ≈ e2 ∶ A ->> B

data Eq (Γ : Ctx) : (A B : Ty) -> Γ ⊢ A ->> B -> Γ ⊢ A ->> B -> Set where

  unitl : (f : Γ ⊢ A ->> B)
        ----------------------------
        -> Γ ⊢ f ≈ id ∘ f ∶ A ->> B

  unitr : (f : Γ ⊢ A ->> B)
        ----------------------------
        -> Γ ⊢ f ∘ id ≈ f ∶ A ->> B

  assoc : (f : Γ ⊢ A ->> B) (g : Γ ⊢ B ->> C) (h : Γ ⊢ C ->> D)
        ---------------------------------------------------------
        -> Γ ⊢ (h ∘ g) ∘ f ≈ h ∘ (g ∘ f) ∶ A ->> D

  term : (f g : Γ ⊢ `0 ->> A)
       -------------------------
       -> Γ ⊢ f ≈ g ∶ `0 ->> A

  κ̃-beta : (f : (Γ ∙ C) ⊢ A ->> B) (c : Γ ⊢ C ->> `0)
          --------------------------------------------
          -> Γ ⊢ κ̃ f ∘ lift̃ c ≈ sub c f ∶ A ->> B

  κ̃-eta : (f : Γ ⊢ (A `- C) ->> B)
         --------------------------------------------------------
         -> Γ ⊢ κ̃ (wk f ∘ lift̃ (covar h)) ≈ f ∶ (A `- C) ->> B
