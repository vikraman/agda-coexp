module Coexp.LamLamBar.Interp (R : Set) where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product as P renaming (map to pmap)
open import Data.Sum as S renaming (map to smap)
open import Function
open import Data.Bool hiding (T)
open import Relation.Binary.PropositionalEquality

open import Coexp.Prelude
open import Coexp.Semantics
open import Coexp.LamLamBar.Syntax

open Cont R

-- interpretation of types
-- functions are kleisli arrows
interpTy : Ty -> Set
interpTy `Nat     = ℕ
interpTy `Unit    = ⊤
interpTy (A ̃)    = interpTy A -> R
interpTy (A `× B) = interpTy A × interpTy B
interpTy (A `⇒ B) = interpTy A -> T (interpTy B)
interpTy (A `+ B) = interpTy A ⊎ interpTy B

-- interpretation of contexts
interpCtx : Ctx -> Set
interpCtx ε       = ⊤
interpCtx (Γ ∙ A) = interpCtx Γ × interpTy A

-- interpretation of membership
interpIn : A ∈ Γ -> interpCtx Γ -> interpTy A
interpIn h     = proj₂
interpIn (t i) = proj₁ ； interpIn i

-- interpretation of terms
interpTm : Γ ⊢ A -> interpCtx Γ -> T (interpTy A)
interpTm (nat n) =
  const n ； T.eta
interpTm (zero? e) =
  interpTm e ； T.map is-zero
interpTm (var i) =
  interpIn i ； T.eta
interpTm (lam e) =
  curry (interpTm e) ； T.eta
interpTm (app e1 e2) =
  let f = interpTm e1 ; x = interpTm e2
  in  < f , x > ； T.beta ； T.map eval ； T.mu
interpTm (pair e1 e2) =
  let f = interpTm e1 ; g = interpTm e2
  in < f , g > ； T.beta
interpTm (fst e) =
  interpTm e ； T.map proj₁
interpTm (snd e) =
  interpTm e ； T.map proj₂
interpTm unit =
  const tt ； T.eta
interpTm (inl e) =
  interpTm e ； T.map inj₁
interpTm (inr e) =
  interpTm e ； T.map inj₂
interpTm (case e e1 e2) =
  let f = interpTm e ; g1 = interpTm e1 ; g2 = interpTm e2
  in < id , f > ； T.tau ； T.map distl ； T.map S.[ g1 , g2 ] ； T.mu
interpTm (colam e) =
  councurry (interpTm e)
interpTm (coapp e1 e2) =
  let f = interpTm e1 ; g = interpTm e2
  in < f , g > ； T.tau ； T.map couneval ； T.mu

-- interpretation of weakening
interpWk : Wk Γ Δ -> interpCtx Γ -> interpCtx Δ
interpWk wk-ε        = const tt
interpWk (wk-cong π) = pmap (interpWk π) id
interpWk (wk-wk π)   = proj₁ ； interpWk π

interpWk-id-coh : interpWk (wk-id {Γ}) ≡ id
interpWk-id-coh {Γ = ε} = refl
interpWk-id-coh {Γ = Γ ∙ A} rewrite interpWk-id-coh {Γ = Γ} = refl
{-# REWRITE interpWk-id-coh #-}

interpWk-mem-coh : (π : Wk Γ Δ) (i : A ∈ Δ) -> interpIn (wk-mem π i) ≡ interpWk π ； interpIn i
interpWk-mem-coh (wk-cong π) h                                    = refl
interpWk-mem-coh (wk-cong π) (t i) rewrite interpWk-mem-coh π i   = refl
interpWk-mem-coh (wk-wk π) h rewrite interpWk-mem-coh π h         = refl
interpWk-mem-coh (wk-wk π) (t i) rewrite interpWk-mem-coh π (t i) = refl

interpWk-tm-coh : (π : Wk Γ Δ) (e : Δ ⊢ A) -> interpTm (wk-tm π e) ≡ interpWk π ； interpTm e
interpWk-tm-coh π (nat n) = refl
interpWk-tm-coh π (zero? e) rewrite interpWk-tm-coh π e = refl
interpWk-tm-coh π (var i) rewrite interpWk-mem-coh π i = refl
interpWk-tm-coh π (lam e) rewrite (interpWk-tm-coh (wk-cong π) e) = refl
interpWk-tm-coh π (app e1 e2) rewrite interpWk-tm-coh π e1 | interpWk-tm-coh π e2 = refl
interpWk-tm-coh π (pair e1 e2) rewrite interpWk-tm-coh π e1 | interpWk-tm-coh π e2 = refl
interpWk-tm-coh π (fst e) rewrite interpWk-tm-coh π e = refl
interpWk-tm-coh π (snd e) rewrite interpWk-tm-coh π e = refl
interpWk-tm-coh π unit = refl
interpWk-tm-coh π (inl e) rewrite interpWk-tm-coh π e = refl
interpWk-tm-coh π (inr e) rewrite interpWk-tm-coh π e = refl
interpWk-tm-coh π (case e1 e2 e3) rewrite interpWk-tm-coh π e1 | interpWk-tm-coh (wk-cong π) e2 | interpWk-tm-coh (wk-cong π) e3 =
  funext \γ -> funext \k -> cong (interpTm e1 (interpWk π γ)) (funext \{ (inj₁ a) -> refl ; (inj₂ b) -> refl })
interpWk-tm-coh π (colam e) rewrite interpWk-tm-coh (wk-cong π) e = refl
interpWk-tm-coh π (coapp e1 e2) rewrite interpWk-tm-coh π e1 | interpWk-tm-coh π e2 = refl
{-# REWRITE interpWk-tm-coh #-}

-- interpretation of values
interpVal : (e : Γ ⊢ A) -> {{ϕ : isVal e}} -> interpCtx Γ -> interpTy A
interpVal (nat n)      {{nat}}   = const n
interpVal (zero? e)    {{zero?}} = interpVal e ； is-zero
interpVal (var i)      {{var}}   = interpIn i
interpVal (lam e)      {{lam}}   = curry (interpTm e)
interpVal (fst e)      {{fst}}   = interpVal e ； proj₁
interpVal (snd e)      {{snd}}   = interpVal e ； proj₂
interpVal (pair e1 e2) {{pair}}  = < interpVal e1 , interpVal e2 >
interpVal unit         {{unit}}  = const tt
interpVal (inl e)      {{inl}}   = interpVal e ； inj₁
interpVal (inr e)      {{inr}}   = interpVal e ； inj₂

-- value interpretation coherence lemma
interpVal-tm-coh : (e : Γ ⊢ A) {{ϕ : isVal e}} -> interpTm e ≡ interpVal e ； T.eta
interpVal-tm-coh (nat n) {{nat}} = refl
interpVal-tm-coh (zero? e) {{zero? {{ϕ}}}}
  rewrite interpVal-tm-coh e {{ϕ}} = refl
interpVal-tm-coh (var i) {{var}} = refl
interpVal-tm-coh (lam e) {{lam}} = refl
interpVal-tm-coh (fst e) {{fst {{ϕ}}}}
  rewrite interpVal-tm-coh e {{ϕ}} = refl
interpVal-tm-coh (snd e) {{snd {{ϕ}}}}
    rewrite interpVal-tm-coh e {{ϕ}} = refl
interpVal-tm-coh (pair e1 e2) {{pair {{ϕ1}} {{ϕ2}}}}
  rewrite interpVal-tm-coh e1 {{ϕ1}} | interpVal-tm-coh e2 {{ϕ2}} = refl
interpVal-tm-coh unit {{unit}} = refl
interpVal-tm-coh (inl e) {{inl {{ϕ}}}}
  rewrite interpVal-tm-coh e {{ϕ}} = refl
interpVal-tm-coh (inr e) {{inr {{ϕ}}}}
  rewrite interpVal-tm-coh e {{ϕ}} = refl

interpVal-wk-coh : (π : Wk Γ Δ) (v : Δ ⊢ A) {{ϕ : isVal v}} -> interpVal (wk-tm π v) {{wk-tm-val π v}} ≡ interpWk π ； interpVal v
interpVal-wk-coh π (nat n) {{nat}} = refl
interpVal-wk-coh π (zero? v) {{zero? {{ϕ}}}} rewrite interpVal-wk-coh π v {{ϕ}} = refl
interpVal-wk-coh π (var i) {{var}} = interpWk-mem-coh π i
interpVal-wk-coh π (lam e) {{lam}} rewrite interpWk-tm-coh (wk-cong π) e = refl
interpVal-wk-coh π (fst v) {{fst {{ϕ}}}} rewrite interpVal-wk-coh π v {{ϕ}} = refl
interpVal-wk-coh π (snd v) {{snd {{ϕ}}}} rewrite interpVal-wk-coh π v {{ϕ}} = refl
interpVal-wk-coh π (pair v1 v2) {{pair {{ϕ1}} {{ϕ2}}}} rewrite interpVal-wk-coh π v1 {{ϕ1}} | interpVal-wk-coh π v2 {{ϕ2}} = refl
interpVal-wk-coh π unit {{unit}} = refl
interpVal-wk-coh π (inl v) {{inl {{ϕ}}}} rewrite interpVal-wk-coh π v {{ϕ}} = refl
interpVal-wk-coh π (inr v) {{inr {{ϕ}}}} rewrite interpVal-wk-coh π v {{ϕ}} = refl
{-# REWRITE interpVal-wk-coh #-}

open Val isVal

-- interpretation of substitutions
interpSub : (θ : Sub Γ Δ) (ϕ : isSub θ) -> interpCtx Γ -> interpCtx Δ
interpSub sub-ε sub-ε               = const tt
interpSub (sub-ex θ v) (sub-ex ϕ ψ) = < interpSub θ ϕ , interpVal v {{ψ}} >

interpSub-wk-coh : (π : Wk Γ Δ) -> (θ : Sub Δ Ψ) (ϕ : isSub θ) -> interpSub (sub-wk π θ) (sub-wk-sub π θ ϕ) ≡ interpWk π ； interpSub θ ϕ
interpSub-wk-coh π sub-ε sub-ε = refl
interpSub-wk-coh π (sub-ex θ v) (sub-ex ϕ ψ) rewrite interpSub-wk-coh π θ ϕ | interpVal-wk-coh π v {{ψ}} = refl
{-# REWRITE interpSub-wk-coh #-}

interpSub-id-coh : {Γ : Ctx} -> interpSub (sub-id {Γ}) (sub-id-sub {Γ}) ≡ id
interpSub-id-coh {ε} = refl
interpSub-id-coh {Γ ∙ A} =
  < interpSub (sub-wk (wk-wk wk-id) sub-id) (sub-wk-sub (wk-wk wk-id) sub-id sub-id-sub) , proj₂ > ≡⟨ cong (\f -> < f , proj₂ >) (interpSub-wk-coh (wk-wk wk-id) (sub-id {Γ}) sub-id-sub) ⟩
  < proj₁ ； interpWk wk-id ； interpSub sub-id sub-id-sub , proj₂ >                               ≡⟨ cong (\f -> < proj₁ ； interpWk wk-id ； f , proj₂ >) (interpSub-id-coh {Γ}) ⟩
  < proj₁ ； interpWk wk-id , proj₂ >                                                              ≡⟨ cong (\f -> < proj₁ ； f , proj₂ >) interpWk-id-coh ⟩
  id ∎
  where open ≡-Reasoning
{-# REWRITE interpSub-id-coh #-}

interpSub-mem-val-coh : (θ : Sub Γ Δ) (ϕ : isSub θ) (i : A ∈ Δ) -> interpVal (sub-mem θ i) {{sub-mem-val θ ϕ i}} ≡ interpSub θ ϕ ； interpIn i
interpSub-mem-val-coh (sub-ex θ e) (sub-ex ϕ ψ) h = refl
interpSub-mem-val-coh (sub-ex θ e) (sub-ex ϕ ψ) (t i) rewrite interpSub-mem-val-coh θ ϕ i = refl

interpSub-mem-tm-coh : (θ : Sub Γ Δ) (ϕ : isSub θ) (i : A ∈ Δ) -> interpTm (sub-mem θ i) ≡ interpSub θ ϕ ； interpIn i ； T.eta
interpSub-mem-tm-coh θ ϕ i rewrite interpVal-tm-coh (sub-mem θ i) {{sub-mem-val θ ϕ i}} | interpSub-mem-val-coh θ ϕ i = refl

interpSub-tm-coh : (θ : Sub Γ Δ) (ϕ : isSub θ) -> (e : Δ ⊢ A) -> interpTm (sub-tm θ e) ≡ interpSub θ ϕ ； interpTm e
interpSub-tm-coh θ ϕ (nat n) = refl
interpSub-tm-coh θ ϕ (zero? e) rewrite interpSub-tm-coh θ ϕ e = refl
interpSub-tm-coh θ ϕ (var i) rewrite interpSub-mem-tm-coh θ ϕ i = refl
interpSub-tm-coh θ ϕ (lam e) =
  curry (interpTm (sub-tm δ2 e)) ； T.eta                                 ≡⟨ cong (\h -> curry h ； T.eta) (interpSub-tm-coh δ2 ψ2 e) ⟩
  curry (interpSub δ2 ψ2 ； interpTm e) ； T.eta                          ≡⟨ refl ⟩
  curry (< interpSub δ1 ψ1 , proj₂ > ； interpTm e) ； T.eta              ≡⟨ cong (\h -> curry (< h , proj₂ > ； interpTm e) ； T.eta) (interpSub-wk-coh π1 θ ϕ) ⟩
  curry (< interpWk π1 ； interpSub θ ϕ , proj₂ > ； interpTm e) ； T.eta ≡⟨ cong (\h -> curry (< proj₁ ； h ； interpSub θ ϕ , proj₂ > ； interpTm e) ； T.eta) interpWk-id-coh  ⟩
  curry (< proj₁ ； interpSub θ ϕ , proj₂ > ； interpTm e) ； T.eta       ≡⟨ refl ⟩
  interpSub θ ϕ ； interpTm (lam e) ∎
  where open ≡-Reasoning
        π1 = wk-wk wk-id
        δ1 = sub-wk π1 θ ; ψ1 = sub-wk-sub π1 θ ϕ
        δ2 = sub-ex δ1 (var h) ; ψ2 = sub-ex ψ1 var
interpSub-tm-coh θ ϕ (app e1 e2) rewrite interpSub-tm-coh θ ϕ e1 | interpSub-tm-coh θ ϕ e2 = refl
interpSub-tm-coh θ ϕ (pair e1 e2) rewrite interpSub-tm-coh θ ϕ e1 | interpSub-tm-coh θ ϕ e2 = refl
interpSub-tm-coh θ ϕ (fst e) rewrite interpSub-tm-coh θ ϕ e = refl
interpSub-tm-coh θ ϕ (snd e) rewrite interpSub-tm-coh θ ϕ e = refl
interpSub-tm-coh θ ϕ unit = refl
interpSub-tm-coh θ ϕ (inl e) rewrite interpSub-tm-coh θ ϕ e = refl
interpSub-tm-coh θ ϕ (inr e) rewrite interpSub-tm-coh θ ϕ e = refl
interpSub-tm-coh {Γ = Γ} θ ϕ (case {A = A} {B} e1 e2 e3) rewrite
    interpSub-tm-coh θ ϕ e1
  | interpSub-tm-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) (sub-ex (sub-wk-sub (wk-wk wk-id) θ ϕ) var) e2
  | interpSub-tm-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) (sub-ex (sub-wk-sub (wk-wk wk-id) θ ϕ) var) e3
  | interpSub-wk-coh (wk-wk {A = A} wk-id) θ ϕ | interpSub-wk-coh (wk-wk {A = B} wk-id) θ ϕ
  | interpWk-id-coh {Γ = Γ} =
  funext \γ -> funext \k -> cong (interpTm e1 (interpSub θ ϕ γ)) (funext \{ (inj₁ a) -> refl ; (inj₂ b) -> refl })
interpSub-tm-coh θ ϕ (colam e) =
  councurry (interpTm (sub-tm δ2 e))                                      ≡⟨ cong councurry (interpSub-tm-coh δ2 ψ2 e) ⟩
  councurry (interpSub δ2 ψ2 ； interpTm e)                               ≡⟨ refl ⟩
  councurry (< interpSub δ1 ψ1 , proj₂ > ； interpTm e)                   ≡⟨ cong (\h -> councurry (< h , proj₂ > ； interpTm e)) (interpSub-wk-coh π1 θ ϕ) ⟩
  councurry (< interpWk π1 ； interpSub θ ϕ , proj₂ > ； interpTm e)      ≡⟨ cong (\h -> councurry (< proj₁ ； h ； interpSub θ ϕ , proj₂ > ； interpTm e)) interpWk-id-coh ⟩
  councurry (< proj₁ ； interpSub θ ϕ , proj₂ > ； interpTm e)            ≡⟨ refl ⟩
  interpSub θ ϕ ； interpTm (colam e) ∎
  where open ≡-Reasoning
        π1 = wk-wk wk-id
        δ1 = sub-wk π1 θ ; ψ1 = sub-wk-sub π1 θ ϕ
        δ2 = sub-ex δ1 (var h) ; ψ2 = sub-ex ψ1 var
interpSub-tm-coh θ ϕ (coapp e1 e2) rewrite interpSub-tm-coh θ ϕ e1 | interpSub-tm-coh θ ϕ e2 = refl

-- continuation semantics
lookup : A ∈ Γ -> interpCtx Γ -> interpTy A
lookup = interpIn

evalTm : Γ ⊢ A -> interpCtx Γ -> (interpTy A -> R) -> R
evalTm (nat n) γ k =
  k n
evalTm (zero? e) γ k =
  evalTm e γ \n ->
    k (is-zero n)
evalTm (var i) γ k =
  k (lookup i γ)
evalTm (lam e) γ k =
  k \a kb -> evalTm e (γ , a) kb
evalTm (app e1 e2) γ k =
  evalTm e2 γ \a ->
    evalTm e1 γ \f ->
      f a k
evalTm (pair e1 e2) γ k =
  evalTm e2 γ \b ->
    evalTm e1 γ \a ->
      k (a , b)
evalTm (fst e) γ k =
  evalTm e γ \p ->
    k (proj₁ p)
evalTm (snd e) γ k =
  evalTm e γ \p ->
    k (proj₂ p)
evalTm unit γ k =
  k tt
evalTm (inl e) γ k =
  evalTm e γ \a ->
    k (inj₁ a)
evalTm (inr e) γ k =
  evalTm e γ \b ->
    k (inj₂ b)
evalTm (case e1 e2 e3) γ k =
  evalTm e1 γ
    \{ (inj₁ a) -> evalTm e2 (γ , a) k
     ; (inj₂ b) -> evalTm e3 (γ , b) k }
evalTm (colam e) γ k =
  let ka = \a -> k (inj₁ a)
      kb = \b -> k (inj₂ b)
  in evalTm e (γ , ka) kb
evalTm (coapp e1 e2) γ k =
  evalTm e2 γ \ka ->
    evalTm e1 γ
      \{ (inj₁ a) -> ka a
       ; (inj₂ b) -> k b }

_ : evalTm {Γ = ε} (colam (zero? (coapp (inl (nat 1)) (var h)))) tt ≡ \k -> k (inj₁ 1)
_ = refl

_ : ∀ A -> evalTm {Γ = ε} (colam {A = A} (var h)) tt ≡ \k -> k (inj₂ (\a -> k (inj₁ a)))
_ = \A -> refl

-- both semantics agree
--
adequacy : (e : Γ ⊢ A) -> interpTm e ≡ evalTm e
adequacy (nat n) = refl
adequacy (zero? e) rewrite adequacy e = refl
adequacy (var x) = refl
adequacy (lam e) rewrite adequacy e = refl
adequacy (app e1 e2) rewrite adequacy e1 | adequacy e2 = refl
adequacy (pair e1 e2) rewrite adequacy e1 | adequacy e2 = refl
adequacy (fst e) rewrite adequacy e = refl
adequacy (snd e) rewrite adequacy e = refl
adequacy unit = refl
adequacy (inl e) rewrite adequacy e = refl
adequacy (inr e) rewrite adequacy e = refl
adequacy (case e1 e2 e3) rewrite adequacy e1 | adequacy e2 | adequacy e3 =
  funext \γ -> funext \k ->
    cong (evalTm e1 γ) (funext \{ (inj₁ a) -> refl ; (inj₂ b) -> refl })
adequacy (colam e) rewrite adequacy e = refl
adequacy (coapp e1 e2) rewrite adequacy e1 | adequacy e2 =
  funext \γ -> funext \k ->
    cong (evalTm e2 γ) (funext \k1 -> cong (evalTm e1 γ) (funext \{ (inj₁ a) -> refl ; (inj₂ b) -> refl }))

-- soundness of equational theory

interpWk-ev-coh : (π : Wk Γ Δ) (E : Δ ⊢ A ⇛ B) (e : Δ ⊢ A) -> interpTm (wk-ev π E [[ wk-tm π e ]]) ≡ interpWk π ； interpTm (E [[ e ]])
interpWk-ev-coh π ø e = interpWk-tm-coh π e
interpWk-ev-coh π (app-r e1 E) e rewrite interpWk-tm-coh π e1 | interpWk-ev-coh π E e = refl
interpWk-ev-coh π (app-l E v) e rewrite interpWk-tm-coh π v | interpWk-ev-coh π E e = refl
{-# REWRITE interpWk-ev-coh #-}

interpEv : Γ ⊢ C ⇛ A -> (f : interpCtx Γ -> T (interpTy C)) -> interpCtx Γ -> T (interpTy A)
interpEv ø = id
interpEv (app-r e E) f =
  let x = interpEv E f ; g = interpTm e
  in < g , x > ； T.beta ； T.map eval ； T.mu
interpEv (app-l E v) f =
  let x = interpVal v ; g = interpEv E f
  in < g , x > ； T.sigma ； T.map eval ； T.mu

interpEv-Tm-coh : (E : Γ ⊢ A ⇛ B) (e : Γ ⊢ A) -> interpTm (E [[ e ]]) ≡ interpEv E (interpTm e)
interpEv-Tm-coh ø e = refl
interpEv-Tm-coh (app-r e1 E) e rewrite interpEv-Tm-coh E e = refl
interpEv-Tm-coh (app-l E v {{ϕ}}) e rewrite interpEv-Tm-coh E e | interpVal-tm-coh v {{ϕ}} = refl
{-# REWRITE interpEv-Tm-coh #-}

interpWk-ev-coh' : (π : Wk Γ Δ) (E : Δ ⊢ A ⇛ B) (e : Γ ⊢ A) -> interpTm (wk-ev π E [[ e ]]) ≡ interpEv (wk-ev π E) (interpTm e)
interpWk-ev-coh' π ø e = refl
interpWk-ev-coh' π (app-r e1 E) e
  rewrite interpWk-ev-coh' π E e = refl
interpWk-ev-coh' π (app-l E v {{ϕ}}) e =
  interpTm (wk-ev π (app-l E v) [[ e ]])                                                            ≡⟨ refl ⟩
  interpTm (app-l (wk-ev π E) (wk-tm π v) [[ e ]])                                                  ≡⟨ refl ⟩
  interpTm (app (wk-ev π E [[ e ]]) (wk-tm π v))                                                    ≡⟨ refl ⟩
  < interpTm (wk-ev π E [[ e ]]) , interpTm (wk-tm π v) > ； T.beta ； T.map eval ； T.mu           ≡⟨ cong (\f -> < interpTm (wk-ev π E [[ e ]]) , f > ； T.beta ； T.map eval ； T.mu) (interpVal-tm-coh (wk-tm π v)) ⟩
  < interpTm (wk-ev π E [[ e ]]) , interpVal (wk-tm π v) ； T.eta > ； T.beta ； T.map eval ； T.mu ≡⟨ refl ⟩
  < interpTm (wk-ev π E [[ e ]]) , interpVal (wk-tm π v) > ； T.sigma ； T.map eval ； T.mu         ≡⟨ refl ⟩
  < interpEv (wk-ev π E) (interpTm e) , interpVal (wk-tm π v) > ； T.sigma ； T.map eval ； T.mu    ≡⟨ refl ⟩
  interpEv (app-l (wk-ev π E) (wk-tm π v)) (interpTm e)                                             ≡⟨ refl ⟩
  interpEv (wk-ev π (app-l E v)) (interpTm e) ∎
  where open ≡-Reasoning
        instance _ = wk-tm-val π v {{ϕ}}

interpEv-wk-coh : (π : Wk Γ Δ) (E : Δ ⊢ A ⇛ B) (f : interpCtx Δ -> T (interpTy A)) -> interpEv (wk-ev π E) (interpWk π ； f) ≡ interpWk π ； interpEv E f
interpEv-wk-coh π ø f = refl
interpEv-wk-coh π (app-r e E) f rewrite interpEv-wk-coh π E f = refl
interpEv-wk-coh π (app-l E v {{ϕ}}) f rewrite interpEv-wk-coh π E f | interpVal-wk-coh π v {{ϕ}} = refl

interpEv-wk-coh' : {e : Γ ⊢ A} (E : Γ ⊢ B ⇛ C)
                -> interpEv (wk-ev (wk-wk {A = A ̃} (wk-id {Γ = Γ})) E) (< proj₁ ； interpTm e ； T.map inj₁ , proj₂ > ； couneval)
                 ≡ < proj₁ ； interpTm e ； T.map inj₁ , proj₂ > ； couneval
interpEv-wk-coh' ø = refl
interpEv-wk-coh' {e = e1} (app-r e E) =
  interpEv (wk-ev π1 (app-r e E)) (< proj₁ ； interpTm e1 ； T.map inj₁ , proj₂ > ； couneval)                                                    ≡⟨ refl ⟩
  interpEv (app-r (wk-tm π1 e) (wk-ev π1 E)) (< proj₁ ； interpTm e1 ； T.map inj₁ , proj₂ > ； couneval)                                         ≡⟨ refl ⟩
  < interpTm (wk-tm π1 e) , interpEv (wk-ev π1 E) (< proj₁ ； interpTm e1 ； T.map inj₁ , proj₂ > ； couneval) > ； T.beta ； T.map eval ； T.mu  ≡⟨ cong (\f -> < interpTm (wk-tm π1 e) , f > ； T.beta ； T.map eval ； T.mu) (interpEv-wk-coh' {e = e1} E) ⟩
  < proj₁ ； interpTm e1 ； T.map inj₁ , proj₂ > ； couneval ∎
  where open ≡-Reasoning
        π1 = wk-wk wk-id
interpEv-wk-coh' {e = e} (app-l E v {{ϕ}}) =
  interpEv (wk-ev π1 (app-l E v)) (< proj₁ ； interpTm e ； T.map inj₁ , proj₂ > ； couneval)                                                     ≡⟨ refl ⟩
  interpEv (app-l (wk-ev π1 E) (wk-tm π1 v)) (< proj₁ ； interpTm e ； T.map inj₁ , proj₂ > ； couneval)                                          ≡⟨ refl ⟩
  < interpEv (wk-ev π1 E) (< proj₁ ； interpTm e ； T.map inj₁ , proj₂ > ； couneval) , interpVal (wk-tm π1 v) > ； T.sigma ； T.map eval ； T.mu ≡⟨ cong (\f -> < interpEv (wk-ev π1 E) (< proj₁ ； interpTm e ； T.map inj₁ , proj₂ > ； couneval) , f > ； T.sigma ； T.map eval ； T.mu) (interpVal-wk-coh π1 v) ⟩
  < interpEv (wk-ev π1 E) (< proj₁ ； interpTm e ； T.map inj₁ , proj₂ > ； couneval) , proj₁ ； interpVal v > ； T.sigma ； T.map eval ； T.mu   ≡⟨ cong (\f -> < f , proj₁ ； interpVal v > ； T.sigma ； T.map eval ； T.mu) (interpEv-wk-coh' {e = e} E) ⟩
  < < proj₁ ； interpTm e ； T.map inj₁ , proj₂ > ； couneval , proj₁ ； interpVal v > ； T.sigma ； T.map eval ； T.mu                           ≡⟨ refl ⟩
  < proj₁ ； interpTm e ； T.map inj₁ , proj₂ > ； couneval ∎
  where open ≡-Reasoning
        π1 = wk-wk wk-id
        instance _ = wk-tm-val π1 v {{ϕ}}

interpEv-wk-coh'' : (e : Γ ⊢ A `+ B) (e1 : (Γ ∙ A) ⊢ C) (e2 : (Γ ∙ B) ⊢ C) (E : Γ ⊢ C ⇛ D)
                 -> interpEv E (< id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpTm e1 , interpTm e2 ] ； T.mu)
                  ≡ < id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpEv (wk-ev (wk-wk wk-id) E) (interpTm e1) , interpEv (wk-ev (wk-wk wk-id) E) (interpTm e2) ] ； T.mu
interpEv-wk-coh'' e e1 e2 ø = refl
interpEv-wk-coh'' e e1 e2 (app-r e3 E) =
  interpEv (app-r e3 E) (< id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpTm e1 , interpTm e2 ] ； T.mu)                                                                                                                                                     ≡⟨ refl ⟩
  < interpTm e3 , interpEv E (< id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpTm e1 , interpTm e2 ] ； T.mu) > ； T.beta ； T.map eval ； T.mu                                                                                                              ≡⟨ cong (\f -> < interpTm e3 , f > ； T.beta ； T.map eval ； T.mu) (interpEv-wk-coh'' e e1 e2 E) ⟩
  < interpTm e3 , < id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpEv (wk-ev π1 E) (interpTm e1) , interpEv (wk-ev π2 E) (interpTm e2) ] ； T.mu > ； T.beta ； T.map eval ； T.mu                                                                           ≡⟨ refl ⟩
  < interpTm e3 , < id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpEv (wk-ev π1 E) (interpTm e1) , interpEv (wk-ev π2 E) (interpTm e2) ] ； T.mu > ； T.beta ； T.map eval ； T.mu                                                                           ≡⟨ (funext \γ -> funext \k -> cong (interpTm e γ) (funext \{ (inj₁ x) -> refl ; (inj₂ y) -> refl } )) ⟩
  < id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ < proj₁ ； interpTm e3 , interpEv (wk-ev π1 E) (interpTm e1) > ； T.beta ； T.map eval ； T.mu , < proj₁ ； interpTm e3 , interpEv (wk-ev π2 E) (interpTm e2) > ； T.beta ； T.map eval ； T.mu ] ； T.mu       ≡⟨ refl ⟩
  < id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ < interpTm (wk-tm π1 e3) , interpEv (wk-ev π1 E) (interpTm e1) > ； T.beta ； T.map eval ； T.mu , < interpTm (wk-tm π2 e3) , interpEv (wk-ev π2 E) (interpTm e2) > ； T.beta ； T.map eval ； T.mu ] ； T.mu   ≡⟨ refl ⟩
  < id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpEv (app-r (wk-tm π1 e3) (wk-ev π1 E)) (interpTm e1) , interpEv (app-r (wk-tm π2 e3) (wk-ev π2 E)) (interpTm e2) ] ； T.mu                                                                                 ≡⟨ refl ⟩
  < id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpEv (wk-ev π1 (app-r e3 E)) (interpTm e1) , interpEv (wk-ev π2 (app-r e3 E)) (interpTm e2) ] ； T.mu ∎
  where open ≡-Reasoning
        π1 = wk-wk wk-id
        π2 = wk-wk wk-id
interpEv-wk-coh'' e e1 e2 (app-l E v {{ϕ}}) =
  interpEv (app-l E v) (< id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpTm e1 , interpTm e2 ] ； T.mu)                                                                                                                                                      ≡⟨ refl ⟩
  < interpEv E (< id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpTm e1 , interpTm e2 ] ； T.mu) , interpVal v > ； T.sigma ； T.map eval ； T.mu                                                                                                             ≡⟨ cong (\f -> < f , interpVal v > ； T.sigma ； T.map eval ； T.mu) (interpEv-wk-coh'' e e1 e2 E) ⟩
  < < id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpEv (wk-ev (wk-wk wk-id) E) (interpTm e1) , interpEv (wk-ev (wk-wk wk-id) E) (interpTm e2) ] ； T.mu , interpVal v > ； T.sigma ； T.map eval ； T.mu                                                    ≡⟨ (funext \γ -> funext \k -> cong (interpTm e γ) (funext \{ (inj₁ x) -> refl ; (inj₂ y) -> refl })) ⟩
  < id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ < interpEv (wk-ev π1 E) (interpTm e1) , interpVal (wk-tm π1 v) > ； T.sigma ； T.map eval ； T.mu , < interpEv (wk-ev π2 E) (interpTm e2) , interpVal (wk-tm π2 v) > ； T.sigma ； T.map eval ； T.mu ] ； T.mu ≡⟨ refl ⟩
  < id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpEv (app-l (wk-ev π1 E) (wk-tm π1 v)) (interpTm e1) , interpEv (app-l (wk-ev π2 E) (wk-tm π2 v)) (interpTm e2) ] ； T.mu                                                                                   ≡⟨ refl ⟩
  < id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpEv (wk-ev π1 (app-l E v)) (interpTm e1) , interpEv (wk-ev π2 (app-l E v)) (interpTm e2) ] ； T.mu ∎
  where open ≡-Reasoning
        π1 = wk-wk wk-id
        π2 = wk-wk wk-id
        instance _ = wk-tm-val π1 v {{ϕ}}
        instance _ = wk-tm-val π2 v {{ϕ}}

interpEq : Γ ⊢ e1 ≈ e2 ∶ A -> interpTm e1 ≡ interpTm e2
interpEq ≈-refl = refl
interpEq (≈-sym eq) = sym (interpEq eq)
interpEq (≈-trans eq1 eq2) = trans (interpEq eq1) (interpEq eq2)
interpEq (fst-cong eq) = cong (_； T.map proj₁) (interpEq eq)
interpEq (snd-cong eq) = cong (_； T.map proj₂) (interpEq eq)
interpEq (pair-cong eq1 eq2) = cong₂ (\f g -> < f , g > ； T.beta) (interpEq eq1) (interpEq eq2)
interpEq (fst-beta v1 v2) =
  interpTm (pair v1 v2) ； T.map proj₁                                                                                 ≡⟨ cong (_； T.map proj₁) (interpVal-tm-coh (pair v1 v2)) ⟩
  interpVal (pair v1 v2) ； T.eta ； T.map proj₁                                                                       ≡⟨ refl ⟩
  interpVal (pair v1 v2) ； proj₁ ； T.eta                                                                             ≡⟨ refl ⟩
  interpVal v1 ； T.eta                                                                                                ≡⟨ sym (interpVal-tm-coh v1) ⟩
  interpTm v1 ∎
  where open ≡-Reasoning
interpEq (snd-beta v1 v2) =
  interpTm (pair v1 v2) ； T.map proj₂                                                                                 ≡⟨ cong (_； T.map proj₂) (interpVal-tm-coh (pair v1 v2)) ⟩
  interpVal (pair v1 v2) ； T.eta ； T.map proj₂                                                                       ≡⟨ refl ⟩
  interpVal (pair v1 v2) ； proj₂ ； T.eta                                                                             ≡⟨ refl ⟩
  interpVal v2 ； T.eta                                                                                                ≡⟨ sym (interpVal-tm-coh v2) ⟩
  interpTm v2 ∎
  where open ≡-Reasoning
interpEq (pair-eta v) =
  < interpTm v ； T.map proj₁ , interpTm v ； T.map proj₂ > ； T.beta                                                  ≡⟨ cong (\f -> < f ； T.map proj₁ , f ； T.map proj₂ > ； T.beta) (interpVal-tm-coh v) ⟩
  < interpVal v ； T.eta ； T.map proj₁ , interpVal v ； T.eta ； T.map proj₂ > ； T.beta                              ≡⟨ refl ⟩
  < interpVal v ； proj₁ ； T.eta , interpVal v ； proj₂ ； T.eta > ； T.beta                                          ≡⟨ refl ⟩
  interpVal v ； T.eta                                                                                                 ≡⟨ sym (interpVal-tm-coh v) ⟩
  interpTm v ∎
  where open ≡-Reasoning
interpEq (unit-eta v) =
  interpTm v                                                                                                           ≡⟨ interpVal-tm-coh v ⟩
  interpVal v ； T.eta                                                                                                 ≡⟨ cong (_； T.eta) refl ⟩
  interpVal unit ； T.eta                                                                                              ≡⟨ sym (interpVal-tm-coh unit) ⟩
  interpTm unit ∎
  where open ≡-Reasoning
interpEq (lam-beta e v {{ϕ}}) =
  < curry (interpTm e) ； T.eta , interpTm v > ； T.beta ； T.map eval ； T.mu                                         ≡⟨ cong (\f -> < curry (interpTm e) ； T.eta , f > ； T.beta ； T.map eval ； T.mu) (interpVal-tm-coh v) ⟩
  < curry (interpTm e) ； T.eta , interpVal v ； T.eta > ； T.beta ； T.map eval ； T.mu                               ≡⟨ refl ⟩
  < curry (interpTm e), interpVal v > ； pmap T.eta T.eta ； T.beta ； T.map eval ； T.mu                              ≡⟨ refl ⟩
  < curry (interpTm e), interpVal v > ； T.eta ； T.map eval ； T.mu                                                   ≡⟨ refl ⟩
  < curry (interpTm e), interpVal v > ； eval ； T.eta ； T.mu                                                         ≡⟨ refl ⟩
  < curry (interpTm e), interpVal v > ； eval                                                                          ≡⟨ refl ⟩
  < id , interpVal v > ； interpTm e                                                                                   ≡⟨ cong (\f -> < f , interpVal v > ； interpTm e) (sym interpSub-id-coh) ⟩
  < interpSub sub-id sub-id-sub , interpVal v > ； interpTm e                                                          ≡⟨ refl ⟩
  interpSub (sub-ex sub-id v) (sub-ex sub-id-sub ϕ) ； interpTm e                                                      ≡⟨ sym (interpSub-tm-coh (sub-ex sub-id v) (sub-ex sub-id-sub ϕ) e) ⟩
  interpTm (sub-tm (sub-ex sub-id v) e) ∎
  where open ≡-Reasoning
interpEq (lam-eta v {{ϕ}}) =
  curry (< interpTm (wk-tm (wk-wk wk-id) v) , interpTm (var h) > ； T.beta ； T.map eval ； T.mu) ； T.eta             ≡⟨ cong (\f -> curry (< f , interpTm (var h) > ； T.beta ； T.map eval ； T.mu) ； T.eta) (interpWk-tm-coh (wk-wk wk-id) v) ⟩
  curry (< interpWk (wk-wk wk-id) ； interpTm v , interpTm (var h) > ； T.beta ； T.map eval ； T.mu) ； T.eta         ≡⟨ cong (\f -> curry (< proj₁ ； f ； interpTm v , interpTm (var h) > ； T.beta ； T.map eval ； T.mu) ； T.eta) interpWk-id-coh ⟩
  curry (< proj₁ ； interpTm v , interpTm (var h) > ； T.beta ； T.map eval ； T.mu) ； T.eta                          ≡⟨ cong (\f -> curry (< proj₁ ； f , interpTm (var h) > ； T.beta ； T.map eval ； T.mu) ； T.eta) (interpVal-tm-coh v) ⟩
  curry (< proj₁ ； interpVal v ； T.eta , interpTm (var h) > ； T.beta ； T.map eval ； T.mu) ； T.eta                ≡⟨ refl ⟩
  interpVal v ； T.eta                                                                                                 ≡⟨ sym (interpVal-tm-coh v) ⟩
  interpTm v ∎
  where open ≡-Reasoning
interpEq (case-inl-beta v {{ϕ}} e2 e3) =
  < id , interpTm v ； T.map inj₁ > ； T.tau ； T.map distl ； T.map S.[ interpTm e2 , interpTm e3 ] ； T.mu           ≡⟨ cong (\f -> < id , f ； T.map inj₁ > ； T.tau ； T.map distl ； T.map S.[ interpTm e2 , interpTm e3 ] ； T.mu) (interpVal-tm-coh v) ⟩
  < id , interpVal v ； T.eta ； T.map inj₁ > ； T.tau ； T.map distl ； T.map S.[ interpTm e2 , interpTm e3 ] ； T.mu ≡⟨ refl ⟩
  < id , interpVal v > ； interpTm e2                                                                                  ≡⟨ cong (\f -> < f , interpVal v > ； interpTm e2) (sym interpSub-id-coh) ⟩
  < interpSub sub-id sub-id-sub , interpVal v > ； interpTm e2                                                         ≡⟨ refl ⟩
  interpSub (sub-ex sub-id v) (sub-ex sub-id-sub ϕ) ； interpTm e2                                                     ≡⟨ sym (interpSub-tm-coh (sub-ex sub-id v) (sub-ex sub-id-sub ϕ) e2) ⟩
  interpTm (sub-tm (sub-ex sub-id v) e2) ∎
  where open ≡-Reasoning
interpEq (case-inr-beta v {{ϕ}} e2 e3) =
  < id , interpTm v ； T.map inj₂ > ； T.tau ； T.map distl ； T.map S.[ interpTm e2 , interpTm e3 ] ； T.mu           ≡⟨ cong (\f -> < id , f ； T.map inj₂ > ； T.tau ； T.map distl ； T.map S.[ interpTm e2 , interpTm e3 ] ； T.mu) (interpVal-tm-coh v) ⟩
  < id , interpVal v ； T.eta ； T.map inj₂ > ； T.tau ； T.map distl ； T.map S.[ interpTm e2 , interpTm e3 ] ； T.mu ≡⟨ refl ⟩
  < id , interpVal v > ； interpTm e3                                                                                  ≡⟨ cong (\f -> < f , interpVal v > ； interpTm e3) (sym interpSub-id-coh) ⟩
  < interpSub sub-id sub-id-sub , interpVal v > ； interpTm e3                                                         ≡⟨ refl ⟩
  interpSub (sub-ex sub-id v) (sub-ex sub-id-sub ϕ) ； interpTm e3                                                     ≡⟨ sym (interpSub-tm-coh (sub-ex sub-id v) (sub-ex sub-id-sub ϕ) e3) ⟩
  interpTm (sub-tm (sub-ex sub-id v) e3) ∎
  where open ≡-Reasoning
interpEq (colam-beta e v {{ϕ}}) =
  < councurry (interpTm e) , interpTm v > ； T.tau ； T.map couneval ； T.mu                                           ≡⟨ cong (\f -> < councurry (interpTm e) , f > ； T.tau ； T.map couneval ； T.mu) (interpVal-tm-coh v) ⟩
  < councurry (interpTm e) , interpVal v ； T.eta > ； T.tau ； T.map couneval ； T.mu                                 ≡⟨ refl ⟩
  < councurry (interpTm e) , interpVal v > ； couneval                                                                 ≡⟨ refl ⟩
  < id , interpVal v > ； interpTm e                                                                                   ≡⟨ cong (\f -> < f , interpVal v > ； interpTm e) (sym interpSub-id-coh) ⟩
  < interpSub sub-id sub-id-sub , interpVal v > ； interpTm e                                                          ≡⟨ refl ⟩
  interpSub (sub-ex sub-id v) (sub-ex sub-id-sub ϕ) ； interpTm e                                                      ≡⟨ sym (interpSub-tm-coh (sub-ex sub-id v) (sub-ex sub-id-sub ϕ) e) ⟩
  interpTm (sub-tm (sub-ex sub-id v) e) ∎
  where open ≡-Reasoning
interpEq (colam-eta {A = A} e) =
  councurry (< interpTm (wk-tm π1 e) , interpTm {A = A ̃} (var h) > ； T.tau ； T.map couneval ； T.mu)                ≡⟨ cong (\f -> councurry (< f , interpTm {A = A ̃} (var h) > ； T.tau ； T.map couneval ； T.mu)) (interpWk-tm-coh π1 e) ⟩
  councurry (< interpWk π1 ； interpTm e , interpTm {A = A ̃} (var h) > ； T.tau ； T.map couneval ； T.mu)            ≡⟨ cong (\f -> councurry (< f ； interpTm e , interpTm {A = A ̃} (var h) > ； T.tau ； T.map couneval ； T.mu)) (cong (proj₁ ；_) interpWk-id-coh) ⟩
  councurry (< proj₁ ； interpTm e , interpTm {A = A ̃} (var h) > ； T.tau ； T.map (cocurry id) ； T.mu)              ≡⟨ refl ⟩
  councurry (cocurry (interpTm e))                                                                                     ≡⟨ councurry-cocurry (interpTm e) ⟩
  interpTm e ∎
  where open ≡-Reasoning
        π1 = wk-wk {A = A ̃} wk-id

interpEq (colam-const {A = A} e) =
  councurry (interpTm (wk-tm π1 e))     ≡⟨ cong councurry (interpWk-tm-coh π1 e) ⟩
  councurry (interpWk π1 ； interpTm e) ≡⟨ cong councurry (cong (\f -> proj₁ ； f ； interpTm e) interpWk-id-coh) ⟩
  councurry (proj₁ ； interpTm e)       ≡⟨ refl ⟩
  interpTm e ； T.map inj₂ ∎
  where open ≡-Reasoning
        π1 = wk-wk {A = A ̃} wk-id

interpEq (colam-inr-pass e E) =
  interpTm (colam (wk-ev π1 E [[ coapp (inr (wk e)) (var h) ]]))                                      ≡⟨ refl ⟩
  councurry (interpTm (wk-ev π1 E [[ coapp (inr (wk e)) (var h) ]]))                                  ≡⟨ cong councurry (interpWk-ev-coh' π1 E (coapp (inr (wk e)) (var h))) ⟩
  councurry (interpEv (wk-ev π1 E) (< interpWk π1 ； interpTm e ； T.map inj₂ , proj₂ > ； couneval)) ≡⟨ refl ⟩
  councurry (interpEv (wk-ev π1 E) (interpWk π1 ； interpTm e))                                       ≡⟨ cong councurry (interpEv-wk-coh π1 E (interpTm e)) ⟩
  councurry (interpWk π1 ； interpEv E (interpTm e))                                                  ≡⟨ refl ⟩
  interpEv E (interpTm e) ； T.map inj₂                                                               ≡⟨ refl ⟩
  interpTm (E [[ e ]]) ； T.map inj₂                                                                  ≡⟨ refl ⟩
  interpTm (inr (E [[ e ]])) ∎
  where open ≡-Reasoning
        π1 = wk-wk wk-id

interpEq (colam-inl-jump e E) =
  interpTm (colam (wk-ev π1 E [[ coapp (inl (wk e)) (var h) ]]))                                                                      ≡⟨ refl ⟩
  councurry (interpTm (wk-ev π1 E [[ coapp (inl (wk e)) (var h) ]]))                                                                  ≡⟨ cong councurry (interpWk-ev-coh' π1 E (coapp (inl (wk e)) (var h))) ⟩
  councurry (interpEv (wk-ev π1 E) (< interpWk π1 ； interpTm e ； T.map inj₁ , proj₂ ； T.eta > ； T.tau ； T.map couneval ； T.mu)) ≡⟨ refl ⟩
  councurry (interpEv (wk-ev π1 E) (< interpWk π1 ； interpTm e ； T.map inj₁ , proj₂ > ； couneval))                                 ≡⟨ cong councurry (interpEv-wk-coh' {e = e} E) ⟩
  councurry (< interpWk π1 ； interpTm e ； T.map inj₁ , proj₂ > ； couneval)                                                         ≡⟨ councurry-cocurry (interpTm e ； T.map inj₁) ⟩
  interpTm e ； T.map inj₁                                                                                                            ≡⟨ refl ⟩
  interpTm (inl e) ∎
  where open ≡-Reasoning
        π1 = wk-wk wk-id

interpEq (case-colam-beta v {{ϕ}} e1 e2) =
  interpTm (case (colam v) e1 e2)                                                                                                   ≡⟨ refl ⟩
  < id , councurry (interpTm v) > ； T.tau ； T.map distl ； T.map S.[ interpTm e1 , interpTm e2 ] ； T.mu                          ≡⟨ cong (\f -> < id , councurry f > ； T.tau ； T.map distl ； T.map S.[ interpTm e1 , interpTm e2 ] ； T.mu) (interpVal-tm-coh v) ⟩
  < id , councurry (interpVal v ； T.eta) > ； T.tau ； T.map distl ； T.map S.[ interpTm e1 , interpTm e2 ] ； T.mu                ≡⟨ refl ⟩
  < id , councurry (interpSub θ1 ϕ1 ； interpTm e2) > ； T.tau ； T.map distl ； T.map S.[ interpTm e1 , interpTm (var h) ] ； T.mu ≡⟨ cong (\f -> < id , councurry f > ； T.tau ； T.map distl ； T.map S.[ interpTm e1 , interpTm (var h) ] ； T.mu) (sym (interpSub-tm-coh θ1 ϕ1 e2)) ⟩
  < id , councurry (interpTm (sub-tm θ1 e2)) > ； T.tau ； T.map distl ； T.map S.[ interpTm e1 , interpTm (var h) ] ； T.mu        ≡⟨ refl ⟩
  interpTm (case (colam (sub-tm θ1 e2)) e1 (var h)) ∎
  where open ≡-Reasoning
        θ1 = sub-ex (sub-wk (wk-wk wk-id) sub-id) v
        ϕ1 = sub-ex (sub-wk-sub (wk-wk wk-id) sub-id sub-id-sub) ϕ

interpEq (case-zeta e e1 e2 E) =
  interpTm (E [[ case e e1 e2 ]])                                                                                                              ≡⟨ refl ⟩
  interpEv E (< id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpTm e1 , interpTm e2 ] ； T.mu)                                    ≡⟨ interpEv-wk-coh'' e e1 e2 E ⟩
  < id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpEv (wk-ev π1 E) (interpTm e1) , interpEv (wk-ev π2 E) (interpTm e2) ] ； T.mu ≡⟨ refl ⟩
  < id , interpTm e > ； T.tau ； T.map distl ； T.map S.[ interpTm (wk-ev π1 E [[ e1 ]]) , interpTm (wk-ev π2 E [[ e2 ]]) ] ； T.mu           ≡⟨ refl ⟩
  interpTm (case e (wk-ev π1 E [[ e1 ]]) (wk-ev π2 E [[ e2 ]])) ∎
  where open ≡-Reasoning
        π1 = wk-wk wk-id
        π2 = wk-wk wk-id
