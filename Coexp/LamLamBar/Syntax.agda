module Coexp.LamLamBar.Syntax where

open import Coexp.Prelude
open import Coexp.Meta.Prelude
open import Data.Nat

infix 50 _*
infixr 40 _`×_
infixr 35 _`+_
infixr 25 _`⇒_

data Ty : Set where
    `Unit `Void `Nat : Ty
    _* : Ty -> Ty
    _`×_ _`⇒_ _`+_ : Ty -> Ty -> Ty

`Bool : Ty
`Bool = `Unit `+ `Unit

open Ctx Ty public

syntax Tm Γ A = Γ ⊢ A

data Tm : Ctx -> Ty -> Set where

  nat : (n : ℕ)
      -----------
      -> Γ ⊢ `Nat

  zero? : Γ ⊢ `Nat
        -----------
        -> Γ ⊢ `Bool

  var : (i : A ∈ Γ)
      ---------
      -> Γ ⊢ A

  lam : (Γ ∙ A) ⊢ B
      -----------------
      -> Γ ⊢ A `⇒ B

  app : Γ ⊢ A `⇒ B -> Γ ⊢ A
      -------------------------
              -> Γ ⊢ B

  pair : Γ ⊢ A -> Γ ⊢ B
      -------------------
       -> Γ ⊢ A `× B

  fst : Γ ⊢ A `× B
      ---------------
        -> Γ ⊢ A

  snd : Γ ⊢ A `× B
      ---------------
        -> Γ ⊢ B

  unit :
       -----------
        Γ ⊢ `Unit

  absurd : Γ ⊢ `Void
         ------------
         -> Γ ⊢ A

  inl : Γ ⊢ A
      ---------------
      -> Γ ⊢ A `+ B

  inr : Γ ⊢ B
      ---------------
      -> Γ ⊢ A `+ B

  case : Γ ⊢ A `+ B -> (Γ ∙ A) ⊢ C -> (Γ ∙ B) ⊢ C
       ---------------------------------------------
       -> Γ ⊢ C

  colam : (Γ ∙ A *) ⊢ B
        -----------------
        -> Γ ⊢ A `+ B

  coapp : Γ ⊢ A `+ B -> Γ ⊢ A *
        --------------------------
             -> Γ ⊢ B

  lett : Γ ⊢ A -> (Γ ∙ A) ⊢ B
       -----------------------
           -> Γ ⊢ B

wk-tm : Wk Γ Δ -> Δ ⊢ A -> Γ ⊢ A
wk-tm π (nat n) = nat n
wk-tm π (zero? e) = zero? (wk-tm π e)
wk-tm π (var x) = var (wk-mem π x)
wk-tm π (lam e) = lam (wk-tm (wk-cong π) e)
wk-tm π (app e1 e2) = app (wk-tm π e1) (wk-tm π e2)
wk-tm π (pair e1 e2) = pair (wk-tm π e1) (wk-tm π e2)
wk-tm π (fst e) = fst (wk-tm π e)
wk-tm π (snd e) = snd (wk-tm π e)
wk-tm π unit = unit
wk-tm π (absurd e) = absurd (wk-tm π e)
wk-tm π (inl e) = inl (wk-tm π e)
wk-tm π (inr e) = inr (wk-tm π e)
wk-tm π (case e1 e2 e3) = case (wk-tm π e1) (wk-tm (wk-cong π) e2) (wk-tm (wk-cong π) e3)
wk-tm π (colam e) = colam (wk-tm (wk-cong π) e)
wk-tm π (coapp e1 e2) = coapp (wk-tm π e1) (wk-tm π e2)
wk-tm π (lett e1 e2) = lett (wk-tm π e1) (wk-tm (wk-cong π) e2)

open WkTm Tm wk-tm public

sub-tm : Sub Γ Δ -> Δ ⊢ A -> Γ ⊢ A
sub-tm θ (nat n) = nat n
sub-tm θ (zero? e) = zero? (sub-tm θ e)
sub-tm θ (var x) =
  sub-mem θ x
sub-tm θ (lam e) =
  lam (sub-tm (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) e)
sub-tm θ (app e1 e2) = app (sub-tm θ e1) (sub-tm θ e2)
sub-tm θ (pair e1 e2) = pair (sub-tm θ e1) (sub-tm θ e2)
sub-tm θ (fst e) = fst (sub-tm θ e)
sub-tm θ (snd e) = snd (sub-tm θ e)
sub-tm θ unit = unit
sub-tm θ (absurd e) = absurd (sub-tm θ e)
sub-tm θ (inl e) = inl (sub-tm θ e)
sub-tm θ (inr e) = inr (sub-tm θ e)
sub-tm θ (case e1 e2 e3) =
  case (sub-tm θ e1)
       (sub-tm (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) e2)
       (sub-tm (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) e3)
sub-tm θ (colam e) =
  colam (sub-tm (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) e)
sub-tm θ (coapp e1 e2) = coapp (sub-tm θ e1) (sub-tm θ e2)
sub-tm θ (lett e1 e2) =
  lett (sub-tm θ e1) (sub-tm (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) e2)

variable
  n : ℕ
  x : A ∈ Γ
  v v1 v2 : Γ ⊢ A
  e e1 e2 e3 e4 : Γ ⊢ A

data isVal {Γ} : Γ ⊢ A -> Set where
  nat : isVal (nat n)
  zero? : {{isVal v}} -> isVal (zero? v)
  var : isVal (var x)
  lam : isVal (lam e)
  fst : {{isVal v}} -> isVal (fst v)
  snd : {{isVal v}} -> isVal (snd v)
  pair : {{isVal v1}} -> {{isVal v2}} -> isVal (pair v1 v2)
  unit : isVal unit
  inl : ∀ {B} -> {{isVal v}} -> isVal (inl {B = B} v)
  inr : ∀ {A} -> {{isVal v}} -> isVal (inr {A = A} v)
  lett : {{isVal e1}} -> {{isVal e2}} -> isVal (lett e1 e2)

open Val isVal

wk-tm-val : (π : Wk Γ Δ) -> (v : Δ ⊢ A) (ϕ : isVal v) -> isVal (wk-tm π v)
wk-tm-val π (nat n) nat = nat
wk-tm-val π (zero? v) (zero? {{ϕ}}) = zero? {{wk-tm-val π v ϕ}}
wk-tm-val π (var i) var = var
wk-tm-val π (lam v) lam = lam
wk-tm-val π (fst v) (fst {{ϕ}}) = fst {{wk-tm-val π v ϕ}}
wk-tm-val π (snd v) (snd {{ϕ}}) = snd {{wk-tm-val π v ϕ}}
wk-tm-val π (pair v1 v2) (pair {{ϕ1}} {{ϕ2}}) = pair {{wk-tm-val π v1 ϕ1}} {{wk-tm-val π v2 ϕ2}}
wk-tm-val π unit unit = unit
wk-tm-val π (inl v) (inl {{ϕ}}) = inl {{wk-tm-val π v ϕ}}
wk-tm-val π (inr v) (inr {{ϕ}}) = inr {{wk-tm-val π v ϕ}}
wk-tm-val π (lett v1 v2) (lett {{ϕ1}} {{ϕ2}}) = lett {{wk-tm-val π v1 ϕ1}} {{wk-tm-val (wk-cong π) v2 ϕ2}}

open SubTm wk-tm-val var var public

sub-tm-val : (θ : Sub Γ Δ) (ϕ : isSub θ) -> (v : Δ ⊢ A) (ψ : isVal v) -> isVal (sub-tm θ v)
sub-tm-val θ ϕ (nat n) nat = nat
sub-tm-val θ ϕ (zero? v) (zero? {{ψ}}) = zero? {{sub-tm-val θ ϕ v ψ}}
sub-tm-val θ ϕ (var i) var = sub-mem-val θ ϕ i
sub-tm-val θ ϕ (lam v) lam = lam
sub-tm-val θ ϕ (fst v) (fst {{ψ}}) = fst {{sub-tm-val θ ϕ v ψ}}
sub-tm-val θ ϕ (snd v) (snd {{ψ}}) = snd {{sub-tm-val θ ϕ v ψ}}
sub-tm-val θ ϕ (pair v1 v2) (pair {{ψ1}} {{ψ2}}) = pair {{sub-tm-val θ ϕ v1 ψ1}} {{sub-tm-val θ ϕ v2 ψ2}}
sub-tm-val θ ϕ unit unit = unit
sub-tm-val θ ϕ (inl v) (inl {{ψ}}) = inl {{sub-tm-val θ ϕ v ψ}}
sub-tm-val θ ϕ (inr v) (inr {{ψ}}) = inr {{sub-tm-val θ ϕ v ψ}}
sub-tm-val θ ϕ (lett v1 v2) (lett {{ψ1}} {{ψ2}}) =
  lett {{sub-tm-val θ ϕ v1 ψ1}}
       {{sub-tm-val (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) (sub-ex (sub-wk-sub (wk-wk wk-id) θ ϕ) var) v2 ψ2}}

syntax Eq Γ A e1 e2 = Γ ⊢ e1 ≈ e2 ∶ A

data Eq (Γ : Ctx) : (A : Ty) -> Γ ⊢ A -> Γ ⊢ A -> Set where

  -- equivalence rules
  ≈-refl  :
          -------------
          Γ ⊢ e ≈ e ∶ A

  ≈-sym   : Γ ⊢ e1 ≈ e2 ∶ A
          ------------------
          -> Γ ⊢ e2 ≈ e1 ∶ A

  ≈-trans : Γ ⊢ e1 ≈ e2 ∶ A -> Γ ⊢ e2 ≈ e3 ∶ A
          -------------------------------------
          -> Γ ⊢ e1 ≈ e3 ∶ A

  -- congruence rules
  fst-cong  : Γ ⊢ e1 ≈ e2 ∶ A `× B
            ---------------------------
            -> Γ ⊢ fst e1 ≈ fst e2 ∶ A

  snd-cong  : Γ ⊢ e1 ≈ e2 ∶ A `× B
            ---------------------------
            -> Γ ⊢ snd e1 ≈ snd e2 ∶ B

  pair-cong : Γ ⊢ e1 ≈ e2 ∶ A -> Γ ⊢ e3 ≈ e4 ∶ B
            ----------------------------------------
            -> Γ ⊢ pair e1 e3 ≈ pair e2 e4 ∶ A `× B

  -- and many more

  -- generators
  -- pair beta
  fst-beta : (v1 : Γ ⊢ A) {{ϕ1 : isVal v1}} -> (v2 : Γ ⊢ B) {{ϕ2 : isVal v2}}
           ---------------------------------------------------------------
           -> Γ ⊢ fst (pair v1 v2) ≈ v1 ∶ A

  snd-beta : (v1 : Γ ⊢ A) {{ϕ1 : isVal v1}} -> (v2 : Γ ⊢ B) {{ϕ2 : isVal v2}}
           ---------------------------------------------------------------
           -> Γ ⊢ snd (pair v1 v2) ≈ v2 ∶ B

  -- pair eta
  pair-eta : (v : Γ ⊢ A `× B) {{ϕ : isVal v}}
           -----------------------------------------
           -> Γ ⊢ pair (fst v) (snd v) ≈ v ∶ A `× B

  -- unit eta
  unit-eta : (v : Γ ⊢ `Unit) {{ϕ : isVal v}}
           --------------------------------
           -> Γ ⊢ v ≈ unit ∶ `Unit

  -- function beta: (λx.e)v ≈ [v/x]e
  lam-beta : (e : (Γ ∙ A) ⊢ B) -> (v : Γ ⊢ A) {{ϕ : isVal v}}
           ------------------------------------------------------
           -> Γ ⊢ app (lam e) v ≈ sub-tm (sub-ex sub-id v) e ∶ B

  -- function eta: λx.vx ≈ v
  lam-eta : (v : Γ ⊢ A `⇒ B) {{ϕ : isVal v}}
          ----------------------------------------------
          -> Γ ⊢ lam (app (wk v) (var h)) ≈ v ∶ A `⇒ B

  -- sum beta
  case-inl-beta : (v : Γ ⊢ A) {{ϕ : isVal v}} (e2 : (Γ ∙ A) ⊢ C) (e3 : (Γ ∙ B) ⊢ C)
                -------------------------------------------------------------------
                -> Γ ⊢ case (inl v) e2 e3 ≈ sub-tm (sub-ex sub-id v) e2 ∶ C

  case-inr-beta : (v : Γ ⊢ B) {{ϕ : isVal v}} (e2 : (Γ ∙ A) ⊢ C) (e3 : (Γ ∙ B) ⊢ C)
                -------------------------------------------------------------------
                -> Γ ⊢ case (inr v) e2 e3 ≈ sub-tm (sub-ex sub-id v) e3 ∶ C

  -- sum eta

  -- coexponential beta: (~λx.e)v ≈ [v/x]e
  colam-beta : (e : (Γ ∙ A *) ⊢ B) -> (v : Γ ⊢ A *) {{ϕ : isVal v}}
             ----------------------------------------------------------
             -> Γ ⊢ coapp (colam e) v ≈ sub-tm (sub-ex sub-id v) e ∶ B

  -- coexponential eta: (~λx.~vx) ≈ v
  colam-eta : (v : Γ ⊢ A `+ B) {{ϕ : isVal v}}
            -------------------------------------------------
            -> Γ ⊢ colam (coapp (wk v) (var h)) ≈ v ∶ A `+ B

  -- let beta: (let x = e in x) ≈ e
  lett-unit :
            --------------------------
            Γ ⊢ lett e (var h) ≈ e ∶ A
