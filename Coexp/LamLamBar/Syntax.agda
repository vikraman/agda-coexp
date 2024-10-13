module Coexp.LamLamBar.Syntax where

open import Coexp.Prelude
open import Coexp.Meta.Prelude
open import Data.Nat

infix 50 _*
infixr 40 _`×_
infixr 35 _`+_
infixr 25 _`⇒_

data Ty : Set where
    `Unit `Nat : Ty
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

-- syntactic sugar
lett : Γ ⊢ A -> (Γ ∙ A) ⊢ B
     -----------------------
         -> Γ ⊢ B
lett e1 e2 = app (lam e2) e1

absurd : Γ ⊢ `Unit *
       ----------------
       -> Γ ⊢ A
absurd = coapp (inl unit)

wk-tm : Wk Γ Δ -> Δ ⊢ A -> Γ ⊢ A
wk-tm π (nat n)         = nat n
wk-tm π (zero? e)       = zero? (wk-tm π e)
wk-tm π (var x)         = var (wk-mem π x)
wk-tm π (lam e)         = lam (wk-tm (wk-cong π) e)
wk-tm π (app e1 e2)     = app (wk-tm π e1) (wk-tm π e2)
wk-tm π (pair e1 e2)    = pair (wk-tm π e1) (wk-tm π e2)
wk-tm π (fst e)         = fst (wk-tm π e)
wk-tm π (snd e)         = snd (wk-tm π e)
wk-tm π unit            = unit
wk-tm π (inl e)         = inl (wk-tm π e)
wk-tm π (inr e)         = inr (wk-tm π e)
wk-tm π (case e1 e2 e3) = case (wk-tm π e1) (wk-tm (wk-cong π) e2) (wk-tm (wk-cong π) e3)
wk-tm π (colam e)       = colam (wk-tm (wk-cong π) e)
wk-tm π (coapp e1 e2)   = coapp (wk-tm π e1) (wk-tm π e2)

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
sub-tm θ (inl e) = inl (sub-tm θ e)
sub-tm θ (inr e) = inr (sub-tm θ e)
sub-tm θ (case e1 e2 e3) =
  case (sub-tm θ e1)
       (sub-tm (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) e2)
       (sub-tm (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) e3)
sub-tm θ (colam e) =
  colam (sub-tm (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) e)
sub-tm θ (coapp e1 e2) = coapp (sub-tm θ e1) (sub-tm θ e2)

variable
  n : ℕ
  x : A ∈ Γ
  v v1 v2 : Γ ⊢ A
  e e1 e2 e3 e4 : Γ ⊢ A

data isVal {Γ} : Γ ⊢ A -> Set where
  instance nat : isVal (nat n)
  instance zero? : {{isVal v}} -> isVal (zero? v)
  instance var : isVal (var x)
  instance lam : isVal (lam e)
  instance fst : {{isVal v}} -> isVal (fst v)
  instance snd : {{isVal v}} -> isVal (snd v)
  instance pair : {{isVal v1}} -> {{isVal v2}} -> isVal (pair v1 v2)
  instance unit : isVal unit
  instance inl : ∀ {B} -> {{isVal v}} -> isVal (inl {B = B} v)
  instance inr : ∀ {A} -> {{isVal v}} -> isVal (inr {A = A} v)

open Val isVal

wk-tm-val : (π : Wk Γ Δ) -> (v : Δ ⊢ A) {{ϕ : isVal v}} -> isVal (wk-tm π v)
wk-tm-val π (nat n)      {{nat}}   = nat
wk-tm-val π (zero? v)    {{zero?}} = zero? {{wk-tm-val π v}}
wk-tm-val π (var i)      {{var}}   = var
wk-tm-val π (lam v)      {{lam}}   = lam
wk-tm-val π (fst v)      {{fst}}   = fst {{wk-tm-val π v}}
wk-tm-val π (snd v)      {{snd}}   = snd {{wk-tm-val π v}}
wk-tm-val π (pair v1 v2) {{pair}}  = pair {{wk-tm-val π v1}} {{wk-tm-val π v2}}
wk-tm-val π unit         {{unit}}  = unit
wk-tm-val π (inl v)      {{inl}}   = inl {{wk-tm-val π v}}
wk-tm-val π (inr v)      {{inr}}   = inr {{wk-tm-val π v}}

open SubTm wk-tm-val var var public

sub-tm-val : (θ : Sub Γ Δ) (ϕ : isSub θ) -> (v : Δ ⊢ A) {{ψ : isVal v}} -> isVal (sub-tm θ v)
sub-tm-val θ ϕ (nat n)      {{nat}}   = nat
sub-tm-val θ ϕ (zero? v)    {{zero?}} = zero? {{sub-tm-val θ ϕ v}}
sub-tm-val θ ϕ (var i)      {{var}}   = sub-mem-val θ ϕ i
sub-tm-val θ ϕ (lam v)      {{lam}}   = lam
sub-tm-val θ ϕ (fst v)      {{fst}}   = fst {{sub-tm-val θ ϕ v}}
sub-tm-val θ ϕ (snd v)      {{snd}}   = snd {{sub-tm-val θ ϕ v}}
sub-tm-val θ ϕ (pair v1 v2) {{pair}}  = pair {{sub-tm-val θ ϕ v1}} {{sub-tm-val θ ϕ v2}}
sub-tm-val θ ϕ unit         {{unit}}  = unit
sub-tm-val θ ϕ (inl v)      {{inl}}   = inl {{sub-tm-val θ ϕ v}}
sub-tm-val θ ϕ (inr v)      {{inr}}   = inr {{sub-tm-val θ ϕ v}}

syntax Ev Γ C A = Γ ⊢ C ⇛ A

data Ev (Γ : Ctx) (C : Ty) : Ty -> Set where

  ø :
      ----------------
        Γ ⊢ C ⇛ C

  app-r : (e : Γ ⊢ A `⇒ B) -> (E : Γ ⊢ C ⇛ A)
        ------------------------------------------------------------
        -> Γ ⊢ C ⇛ B

  app-l : (E : Γ ⊢ C ⇛ (A `⇒ B)) -> (v : Γ ⊢ A) {{ϕ : isVal v}}
        ------------------------------------------------------------
        -> Γ ⊢ C ⇛ B

infix 5 _[[_]]
_[[_]] : (E : Γ ⊢ A ⇛ B) -> (e : Γ ⊢ A) -> Γ ⊢ B
ø [[ e ]]          = e
app-r e1 E [[ e ]] = app e1 (E [[ e ]])
app-l E v [[ e ]]  = app (E [[ e ]]) v

wk-ev : Wk Γ Δ -> Δ ⊢ A ⇛ B -> Γ ⊢ A ⇛ B
wk-ev π ø           = ø
wk-ev π (app-r e E) = app-r (wk-tm π e) (wk-ev π E)
wk-ev π (app-l E v) = app-l (wk-ev π E) (wk-tm π v) {{wk-tm-val π v}}

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
           -----------------------------------------
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
                --------------------------------------------------------------------
                -> Γ ⊢ case (inl v) e2 e3 ≈ sub-tm (sub-ex sub-id v) e2 ∶ C

  case-inr-beta : (v : Γ ⊢ B) {{ϕ : isVal v}} (e2 : (Γ ∙ A) ⊢ C) (e3 : (Γ ∙ B) ⊢ C)
                --------------------------------------------------------------------
                -> Γ ⊢ case (inr v) e2 e3 ≈ sub-tm (sub-ex sub-id v) e3 ∶ C

  -- sum eta

  -- coexponential beta: (~λx.e)v ≈ [v/x]e
  colam-beta : (e : (Γ ∙ A *) ⊢ B) -> (v : Γ ⊢ A *) {{ϕ : isVal v}}
             ----------------------------------------------------------
             -> Γ ⊢ coapp (colam e) v ≈ sub-tm (sub-ex sub-id v) e ∶ B

  -- coexponential eta: (~λx.~ex) ≈ e
  colam-eta : (e : Γ ⊢ A `+ B)
            -------------------------------------------------
            -> Γ ⊢ colam (coapp (wk e) (var h)) ≈ e ∶ A `+ B

  -- control effects
  colam-const : (e : Γ ⊢ B)
              -------------------------------------
              -> Γ ⊢ colam (wk e) ≈ inr e ∶ A `+ B

  colam-inr-pass : (e : Γ ⊢ B) (E : Γ ⊢ B ⇛ C)
                 ----------------------------------------------------------------------------------------------------
                 -> Γ ⊢ colam (wk-ev (wk-wk wk-id) E [[ coapp (inr (wk e)) (var h) ]]) ≈ inr (E [[ e ]]) ∶ A `+ C

  colam-inl-jump : (e : Γ ⊢ A) (E : Γ ⊢ B ⇛ C)
                 ----------------------------------------------------------------------------------------------------
                 -> Γ ⊢ colam (wk-ev (wk-wk wk-id) E [[ coapp (inl (wk e)) (var h) ]]) ≈ inl e ∶ A `+ C

  case-colam-beta : (v : (Γ ∙ A *) ⊢ B) {{ϕ : isVal v}} -> (e1 : (Γ ∙ A) ⊢ C) (e2 : (Γ ∙ B) ⊢ C)
                  ---------------------------------------------------------------------------------------------------------------
                  -> Γ ⊢ case (colam v) e1 e2 ≈ case (colam (sub-tm (sub-ex (sub-wk (wk-wk wk-id) sub-id) v) e2)) e1 (var h) ∶ C

  case-zeta : (e : Γ ⊢ A `+ B) (e1 : (Γ ∙ A) ⊢ C) (e2 : (Γ ∙ B) ⊢ C) (E : Γ ⊢ C ⇛ D)
            ------------------------------------------------------------------------------------------------------------
            -> Γ ⊢ E [[ case e e1 e2 ]] ≈ case e (wk-ev (wk-wk wk-id) E [[ e1 ]]) (wk-ev (wk-wk wk-id) E [[ e2 ]]) ∶ D
