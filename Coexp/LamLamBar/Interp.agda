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
interpTy `Nat = ℕ
interpTy `Unit = ⊤
interpTy `Void = ⊥
interpTy (A *) = interpTy A -> R
interpTy (A `× B) = interpTy A × interpTy B
interpTy (A `⇒ B) = interpTy A -> T (interpTy B)
interpTy (A `+ B) = interpTy A ⊎ interpTy B

-- interpretation of contexts
interpCtx : Ctx -> Set
interpCtx ε = ⊤
interpCtx (Γ ∙ A) = interpCtx Γ × interpTy A

-- interpretation of membership
interpIn : A ∈ Γ -> interpCtx Γ -> interpTy A
interpIn h = proj₂
interpIn (t i) = proj₁ ； interpIn i

-- interpretation of terms
interpTm : Γ ⊢ A -> interpCtx Γ -> T (interpTy A)
interpTm (nat n) =
  (\_ -> n) ； T.eta
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
  (\_ -> tt) ； T.eta
interpTm (absurd e) =
  interpTm e ； T.map ⊥-elim
interpTm (inl e) =
  interpTm e ； T.map inj₁
interpTm (inr e) =
  interpTm e ； T.map inj₂
interpTm (case e1 e2 e3) =
  let f = interpTm e1 ; g1 = interpTm e2 ; g2 = interpTm e3
  in < id , f > ； T.tau ； T.map distl ； T.map S.[ g1 , g2 ] ； T.mu
interpTm (colam e) =
  councurry (interpTm e)
interpTm (coapp e1 e2) =
  let f = interpTm e1 ; g = interpTm e2
  in < f , g > ； T.tau ； T.map coeval'' ； T.mu
interpTm (lett e1 e2) =
  let f = interpTm e1 ; g = curry (interpTm e2)
  in < f , g > ； T.bind

-- interpretation of weakening
interpWk : Wk Γ Δ -> interpCtx Γ -> interpCtx Δ
interpWk wk-ε = \_ -> tt
interpWk (wk-cong π) = pmap (interpWk π) id
interpWk (wk-wk π) = proj₁ ； interpWk π

interpWk-id-coh : interpWk (wk-id {Γ}) ≡ id
interpWk-id-coh {Γ = ε} = refl
interpWk-id-coh {Γ = Γ ∙ A} rewrite interpWk-id-coh {Γ = Γ} = refl

interpWk-mem-coh : (π : Wk Γ Δ) (i : A ∈ Δ) -> interpIn (wk-mem π i) ≡ interpWk π ； interpIn i
interpWk-mem-coh (wk-cong π) h = refl
interpWk-mem-coh (wk-cong π) (t i) rewrite interpWk-mem-coh π i = refl
interpWk-mem-coh (wk-wk π) h rewrite interpWk-mem-coh π h = refl
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
interpWk-tm-coh π (absurd e) rewrite interpWk-tm-coh π e = refl
interpWk-tm-coh π (inl e) rewrite interpWk-tm-coh π e = refl
interpWk-tm-coh π (inr e) rewrite interpWk-tm-coh π e = refl
interpWk-tm-coh π (case e1 e2 e3) rewrite interpWk-tm-coh π e1 | interpWk-tm-coh (wk-cong π) e2 | interpWk-tm-coh (wk-cong π) e3 =
  funext \γ -> funext \k -> cong (interpTm e1 (interpWk π γ)) (funext \{ (inj₁ a) -> refl ; (inj₂ b) -> refl })
interpWk-tm-coh π (colam e) rewrite interpWk-tm-coh (wk-cong π) e = refl
interpWk-tm-coh π (coapp e1 e2) rewrite interpWk-tm-coh π e1 | interpWk-tm-coh π e2 = refl
interpWk-tm-coh π (lett e1 e2) rewrite interpWk-tm-coh π e1 | interpWk-tm-coh (wk-cong π) e2 = refl

-- interpretation of values
interpVal : (e : Γ ⊢ A) -> isVal e -> interpCtx Γ -> interpTy A
interpVal (nat n) nat = \_ -> n
interpVal (zero? e) (zero? {{ϕ}}) = interpVal e ϕ ； is-zero
interpVal (var i) var = interpIn i
interpVal (lam e) lam = curry (interpTm e)
interpVal (fst e) (fst {{ϕ}}) = interpVal e ϕ ； proj₁
interpVal (snd e) (snd {{ϕ}}) = interpVal e ϕ ； proj₂
interpVal (pair e1 e2) (pair {{ϕ1}} {{ϕ2}}) = < interpVal e1 ϕ1 , interpVal e2 ϕ2 >
interpVal unit unit = \_ -> tt
interpVal (inl e) (inl {{ϕ}}) = interpVal e ϕ ； inj₁
interpVal (inr e) (inr {{ϕ}}) = interpVal e ϕ ； inj₂
interpVal (lett e1 e2) (lett {{ϕ1}} {{ϕ2}}) = < curry (interpVal e2 ϕ2) , interpVal e1 ϕ1 > ； eval

-- value interpretation coherence lemma
interpVal-tm-coh : (e : Γ ⊢ A) (ϕ : isVal e) -> interpTm e ≡ interpVal e ϕ ； T.eta
interpVal-tm-coh (nat n) nat = refl
interpVal-tm-coh (zero? e) (zero? {{ϕ}})
  rewrite interpVal-tm-coh e ϕ = refl
interpVal-tm-coh (var i) var = refl
interpVal-tm-coh (lam e) lam = refl
interpVal-tm-coh (fst e) (fst {{ϕ}})
  rewrite interpVal-tm-coh e ϕ = refl
interpVal-tm-coh (snd e) (snd {{ϕ}})
    rewrite interpVal-tm-coh e ϕ = refl
interpVal-tm-coh (pair e1 e2) (pair {{ϕ1}} {{ϕ2}})
  rewrite interpVal-tm-coh e1 ϕ1 | interpVal-tm-coh e2 ϕ2 = refl
interpVal-tm-coh unit unit = refl
interpVal-tm-coh (inl e) (inl {{ϕ}})
  rewrite interpVal-tm-coh e ϕ = refl
interpVal-tm-coh (inr e) (inr {{ϕ}})
  rewrite interpVal-tm-coh e ϕ = refl
interpVal-tm-coh (lett e1 e2) (lett {{ϕ1}} {{ϕ2}})
  rewrite interpVal-tm-coh e1 ϕ1 | interpVal-tm-coh e2 ϕ2 = refl

interpVal-wk-coh : (π : Wk Γ Δ) (v : Δ ⊢ A) (ϕ : isVal v) -> interpVal (wk-tm π v) (wk-tm-val π v ϕ) ≡ interpWk π ； interpVal v ϕ
interpVal-wk-coh π (nat n) nat = refl
interpVal-wk-coh π (zero? v) (zero? {{ϕ}}) rewrite interpVal-wk-coh π v ϕ = refl
interpVal-wk-coh π (var i) var = interpWk-mem-coh π i
interpVal-wk-coh π (lam e) lam rewrite interpWk-tm-coh (wk-cong π) e = refl
interpVal-wk-coh π (fst v) (fst {{ϕ}}) rewrite interpVal-wk-coh π v ϕ = refl
interpVal-wk-coh π (snd v) (snd {{ϕ}}) rewrite interpVal-wk-coh π v ϕ = refl
interpVal-wk-coh π (pair v1 v2) (pair {{ϕ1}} {{ϕ2}}) rewrite interpVal-wk-coh π v1 ϕ1 | interpVal-wk-coh π v2 ϕ2 = refl
interpVal-wk-coh π unit unit = refl
interpVal-wk-coh π (inl v) (inl {{ϕ}}) rewrite interpVal-wk-coh π v ϕ = refl
interpVal-wk-coh π (inr v) (inr {{ϕ}}) rewrite interpVal-wk-coh π v ϕ = refl
interpVal-wk-coh π (lett v1 v2) (lett {{ϕ1}} {{ϕ2}}) rewrite interpVal-wk-coh π v1 ϕ1 | interpVal-wk-coh (wk-cong π) v2 ϕ2 = refl

open Val isVal

-- interpretation of substitutions
interpSub : (θ : Sub Γ Δ) (ϕ : isSub θ) -> interpCtx Γ -> interpCtx Δ
interpSub sub-ε sub-ε = \_ -> tt
interpSub (sub-ex θ v) (sub-ex ϕ ψ) = < interpSub θ ϕ , interpVal v ψ >

interpSub-wk-coh : (π : Wk Γ Δ) -> (θ : Sub Δ Ψ) (ϕ : isSub θ) -> interpSub (sub-wk π θ) (sub-wk-sub π θ ϕ) ≡ interpWk π ； interpSub θ ϕ
interpSub-wk-coh π sub-ε sub-ε = refl
interpSub-wk-coh π (sub-ex θ v) (sub-ex ϕ ψ) rewrite interpSub-wk-coh π θ ϕ | interpVal-wk-coh π v ψ = refl

interpSub-id-coh : {Γ : Ctx} -> interpSub (sub-id {Γ}) (sub-id-sub {Γ}) ≡ id
interpSub-id-coh {ε} = refl
interpSub-id-coh {Γ ∙ A} =
  < interpSub (sub-wk (wk-wk wk-id) sub-id) (sub-wk-sub (wk-wk wk-id) sub-id sub-id-sub) , proj₂ > ≡⟨ cong (\f -> < f , proj₂ >) (interpSub-wk-coh (wk-wk wk-id) (sub-id {Γ}) sub-id-sub) ⟩
  < proj₁ ； interpWk wk-id ； interpSub sub-id sub-id-sub , proj₂ >                               ≡⟨ cong (\f -> < proj₁ ； interpWk wk-id ； f , proj₂ >) (interpSub-id-coh {Γ}) ⟩
  < proj₁ ； interpWk wk-id , proj₂ >                                                              ≡⟨ cong (\f -> < proj₁ ； f , proj₂ >) interpWk-id-coh ⟩
  id                                                                                               ∎
  where open ≡-Reasoning

interpSub-mem-val-coh : (θ : Sub Γ Δ) (ϕ : isSub θ) (i : A ∈ Δ) -> interpVal (sub-mem θ i) (sub-mem-val θ ϕ i) ≡ interpSub θ ϕ ； interpIn i
interpSub-mem-val-coh (sub-ex θ e) (sub-ex ϕ ψ) h = refl
interpSub-mem-val-coh (sub-ex θ e) (sub-ex ϕ ψ) (t i) rewrite interpSub-mem-val-coh θ ϕ i = refl

interpSub-mem-tm-coh : (θ : Sub Γ Δ) (ϕ : isSub θ) (i : A ∈ Δ) -> interpTm (sub-mem θ i) ≡ interpSub θ ϕ ； interpIn i ； T.eta
interpSub-mem-tm-coh θ ϕ i rewrite interpVal-tm-coh (sub-mem θ i) (sub-mem-val θ ϕ i) | interpSub-mem-val-coh θ ϕ i = refl

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
  interpSub θ ϕ ； interpTm (lam e)                                       ∎
  where open ≡-Reasoning
        π1 = wk-wk wk-id
        δ1 = sub-wk π1 θ ; ψ1 = sub-wk-sub π1 θ ϕ
        δ2 = sub-ex δ1 (var h) ; ψ2 = sub-ex ψ1 var
interpSub-tm-coh θ ϕ (app e1 e2) rewrite interpSub-tm-coh θ ϕ e1 | interpSub-tm-coh θ ϕ e2 = refl
interpSub-tm-coh θ ϕ (pair e1 e2) rewrite interpSub-tm-coh θ ϕ e1 | interpSub-tm-coh θ ϕ e2 = refl
interpSub-tm-coh θ ϕ (fst e) rewrite interpSub-tm-coh θ ϕ e = refl
interpSub-tm-coh θ ϕ (snd e) rewrite interpSub-tm-coh θ ϕ e = refl
interpSub-tm-coh θ ϕ unit = refl
interpSub-tm-coh θ ϕ (absurd e) rewrite interpSub-tm-coh θ ϕ e = refl
interpSub-tm-coh θ ϕ (inl e) rewrite interpSub-tm-coh θ ϕ e = refl
interpSub-tm-coh θ ϕ (inr e) rewrite interpSub-tm-coh θ ϕ e = refl
interpSub-tm-coh {Γ = Γ} θ ϕ (case {A = A} {B} e1 e2 e3) rewrite -- TODO: write proper proof
    interpSub-tm-coh θ ϕ e1
  | interpSub-tm-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) (sub-ex (sub-wk-sub (wk-wk wk-id) θ ϕ) var) e2
  | interpSub-tm-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) (sub-ex (sub-wk-sub (wk-wk wk-id) θ ϕ) var) e3
  | interpSub-wk-coh (wk-wk {A = A} wk-id) θ ϕ | interpSub-wk-coh (wk-wk {A = B} wk-id) θ ϕ
  | interpWk-id-coh {Γ = Γ} =
  funext \γ -> funext \k -> cong (interpTm e1 (interpSub θ ϕ γ)) (funext \{ (inj₁ a) → refl ; (inj₂ b) → refl })
interpSub-tm-coh θ ϕ (colam e) =
  councurry (interpTm (sub-tm δ2 e))                                 ≡⟨ cong councurry (interpSub-tm-coh δ2 ψ2 e) ⟩
  councurry (interpSub δ2 ψ2 ； interpTm e)                          ≡⟨ refl ⟩
  councurry (< interpSub δ1 ψ1 , proj₂ > ； interpTm e)              ≡⟨ cong (\h -> councurry (< h , proj₂ > ； interpTm e)) (interpSub-wk-coh π1 θ ϕ) ⟩
  councurry (< interpWk π1 ； interpSub θ ϕ , proj₂ > ； interpTm e) ≡⟨ cong (\h -> councurry (< proj₁ ； h ； interpSub θ ϕ , proj₂ > ； interpTm e)) interpWk-id-coh ⟩
  councurry (< proj₁ ； interpSub θ ϕ , proj₂ > ； interpTm e)       ≡⟨ refl ⟩
  interpSub θ ϕ ； interpTm (colam e)                                ∎
  where open ≡-Reasoning
        π1 = wk-wk wk-id
        δ1 = sub-wk π1 θ ; ψ1 = sub-wk-sub π1 θ ϕ
        δ2 = sub-ex δ1 (var h) ; ψ2 = sub-ex ψ1 var
interpSub-tm-coh θ ϕ (coapp e1 e2) rewrite interpSub-tm-coh θ ϕ e1 | interpSub-tm-coh θ ϕ e2 = refl
interpSub-tm-coh {Γ = Γ} θ ϕ (lett {A = A} e1 e2) rewrite -- TODO: write proper proof
    interpSub-tm-coh θ ϕ e1
  | interpSub-tm-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) (sub-ex (sub-wk-sub (wk-wk wk-id) θ ϕ) var) e2
  | interpSub-wk-coh (wk-wk {A = A} wk-id) θ ϕ
  | interpWk-id-coh {Γ = Γ} =
  refl

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
evalTm (absurd e) γ k =
  evalTm e γ ⊥-elim
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
evalTm (lett e1 e2) γ k =
  evalTm e1 γ \a ->
    evalTm e2 (γ , a) k

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
adequacy (absurd e) rewrite adequacy e =
  funext (\γ -> funext \k -> cong (evalTm e γ) (funext \()))
adequacy (inl e) rewrite adequacy e = refl
adequacy (inr e) rewrite adequacy e = refl
adequacy (case e1 e2 e3) rewrite adequacy e1 | adequacy e2 | adequacy e3 =
  funext \γ -> funext \k ->
    cong (evalTm e1 γ) (funext \{ (inj₁ a) -> refl ; (inj₂ b) -> refl })
adequacy (colam e) rewrite adequacy e = refl
adequacy (coapp e1 e2) rewrite adequacy e1 | adequacy e2 =
  funext \γ -> funext \k ->
    cong (evalTm e2 γ) (funext \k1 -> cong (evalTm e1 γ) (funext \{ (inj₁ a) -> refl ; (inj₂ b) -> refl }))
adequacy (lett e1 e2) rewrite adequacy e1 | adequacy e2 = refl
