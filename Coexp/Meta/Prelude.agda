module Coexp.Meta.Prelude where

open import Coexp.Prelude

module Ctx (Ty : Set) where

  infixl 15 _∙_
  infix 10 _∈_

  data Ctx : Set where
    ε : Ctx
    _∙_ : Ctx -> Ty -> Ctx

  variable
    A B C D : Ty
    Γ Δ Ψ : Ctx

  data _∈_ : Ty -> Ctx -> Set where
    h :
      ---------
      A ∈ Γ ∙ A

    t : A ∈ Γ
      -------------
      -> A ∈ Γ ∙ B

  syntax Wk Γ Δ = Γ ⊇ Δ

  data Wk : (Γ Δ : Ctx) -> Set where
    wk-ε : ε ⊇ ε
    wk-cong : (π : Wk Γ Δ) -> Wk (Γ ∙ A) (Δ ∙ A)
    wk-wk : (π : Wk Γ Δ) -> Wk (Γ ∙ A) Δ

  wk-id : Wk Γ Γ
  wk-id {Γ = ε} = wk-ε
  wk-id {Γ = Γ ∙ A} = wk-cong wk-id

  wk-mem : Wk Γ Δ -> A ∈ Δ -> A ∈ Γ
  wk-mem (wk-cong π) h = h
  wk-mem (wk-wk π) h = t (wk-mem π h)
  wk-mem (wk-cong π) (t i) = t (wk-mem π i)
  wk-mem (wk-wk π) (t i) = t (wk-mem π (t i))

  module WkTm (Tm : Ctx -> Ty -> Set) (wk-tm : ∀ {A Γ Δ} -> Wk Γ Δ -> Tm Δ A -> Tm Γ A) where

    wk : Tm Γ A -> Tm (Γ ∙ B) A
    wk = wk-tm (wk-wk wk-id)

    data Sub (Γ : Ctx) : (Δ : Ctx) -> Set where
      sub-ε : Sub Γ ε
      sub-ex : (θ : Sub Γ Δ) -> (e : Tm Γ A) -> Sub Γ (Δ ∙ A)

    sub-mem : Sub Γ Δ -> A ∈ Δ -> Tm Γ A
    sub-mem (sub-ex θ e) h = e
    sub-mem (sub-ex θ e) (t i) = sub-mem θ i

    sub-wk : Wk Γ Δ -> Sub Δ Ψ -> Sub Γ Ψ
    sub-wk π sub-ε = sub-ε
    sub-wk π (sub-ex θ e) = sub-ex (sub-wk π θ) (wk-tm π e)

    module Val (isVal : ∀ {Γ A} -> Tm Γ A -> Set) where
      variable
        π : Wk Γ Δ
        θ : Sub Γ Δ
        v v1 v2 : Tm Γ A
        x y z : A ∈ Γ

      data isSub {Γ} : Sub Γ Δ -> Set where
        sub-ε : isSub (sub-ε)
        sub-ex : (ϕ : isSub θ) -> (ψ : isVal v) -> isSub (sub-ex θ v)

      module SubTm (wk-tm-val : ∀ {A Γ Δ} -> (π : Wk Γ Δ) -> (v : Tm Δ A) {{ϕ : isVal v}} -> isVal (wk-tm π v))
                   (var : ∀ {A Γ} -> A ∈ Γ -> Tm Γ A)
                   (varIsVal : ∀ {Γ A} {x : A ∈ Γ} -> isVal (var x)) where

        sub-id : Sub Γ Γ
        sub-id {Γ = ε} = sub-ε
        sub-id {Γ = Γ ∙ A} = sub-ex (sub-wk (wk-wk wk-id) sub-id) (var h)

        sub-wk-sub : (π : Wk Γ Δ) -> (θ : Sub Δ Ψ) (ϕ : isSub θ) -> isSub (sub-wk π θ)
        sub-wk-sub π sub-ε sub-ε = sub-ε
        sub-wk-sub π (sub-ex θ e) (sub-ex ϕ ψ) = sub-ex (sub-wk-sub π θ ϕ) (wk-tm-val π e {{ψ}})

        sub-id-sub : {Γ : Ctx} -> isSub (sub-id {Γ})
        sub-id-sub {ε} = sub-ε
        sub-id-sub {Γ ∙ A} = sub-ex (sub-wk-sub (wk-wk wk-id) (sub-id {Γ}) sub-id-sub) varIsVal

        sub-mem-val : (θ : Sub Γ Δ) (ϕ : isSub θ) (i : A ∈ Δ) -> isVal (sub-mem θ i)
        sub-mem-val (sub-ex θ e) (sub-ex ϕ ψ) h = ψ
        sub-mem-val (sub-ex θ e) (sub-ex ϕ ψ) (t i) = sub-mem-val θ ϕ i

  module WkArr (Arr : Ctx -> Ty -> Ty -> Set) (wk-arr : ∀ {A B Γ Δ} -> Wk Γ Δ -> Arr Δ A B -> Arr Γ A B) where

    wk : Arr Γ A B -> Arr (Γ ∙ C) A B
    wk = wk-arr (wk-wk wk-id)

    module Sub (`1 : Ty) (var : ∀ {A Γ} -> A ∈ Γ -> Arr Γ `1 A) where

      data Sub (Γ : Ctx) : (Δ : Ctx) -> Set where
        sub-ε : Sub Γ ε
        sub-ex : (θ : Sub Γ Δ) -> (e : Arr Γ `1 A) -> Sub Γ (Δ ∙ A)

      sub-mem : Sub Γ Δ -> A ∈ Δ -> Arr Γ `1 A
      sub-mem (sub-ex θ e) h = e
      sub-mem (sub-ex θ e) (t i) = sub-mem θ i

      sub-wk : Wk Γ Δ -> Sub Δ Ψ -> Sub Γ Ψ
      sub-wk π sub-ε = sub-ε
      sub-wk π (sub-ex θ e) = sub-ex (sub-wk π θ) (wk-arr π e)

      sub-id : Sub Γ Γ
      sub-id {Γ = ε} = sub-ε
      sub-id {Γ = Γ ∙ A} = sub-ex (sub-wk (wk-wk wk-id) sub-id) (var h)

      module SubArr (sub-arr : ∀ {A B Γ Δ} -> Sub Γ Δ -> Arr Δ A B -> Arr Γ A B) where

        sub : Arr Γ `1 A -> Arr (Γ ∙ A) B C -> Arr Γ B C
        sub x f = sub-arr (sub-ex sub-id x) f
