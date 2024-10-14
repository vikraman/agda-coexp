module Coexp.KappaStar.Interp (R : Set) where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product as P renaming (map to pmap)
open import Data.Sum as S renaming (map to smap)
open import Function using (const ; flip ; _$_)
open import Data.Bool hiding (T)
open import Relation.Binary.PropositionalEquality

open import Coexp.Prelude
open import Coexp.Semantics
open import Coexp.KappaStar.Syntax

open Cont R

interpTy : Ty -> Set
interpTy `0 = ⊥
interpTy (A `- B) = interpTy A × (interpTy B -> R)

interpCtx : Ctx -> Set
interpCtx ε       = ⊤
interpCtx (Γ ∙ A) = interpCtx Γ × (interpTy A -> R)

interpIn : A ∈ Γ -> interpCtx Γ -> interpTy A -> T ⊥
interpIn h     = proj₂ ； coelem
interpIn (t i) = proj₁ ； interpIn i

interpArr : Γ ⊢ A ->> B -> interpCtx Γ -> interpTy A -> T (interpTy B)
interpArr (covar i) = interpIn i
interpArr id = const idk
interpArr bang = const absurd
interpArr (e1 ∘ e2) = < interpArr e1 , interpArr e2 > ； uncurry T.composek
interpArr (lift̃ e) = curry (P.map₁ (curry (flip (uncurry (interpArr e)) absurd)) ； P.swap ； T.eta)
interpArr (κ̃ e) = curry (interpArr e) ； uncurry ； flip contramap P.swap

interpWk : Wk Γ Δ -> interpCtx Γ -> interpCtx Δ
interpWk wk-ε        = const tt
interpWk (wk-cong π) = pmap (interpWk π) idf
interpWk (wk-wk π)   = proj₁ ； interpWk π

interpWk-id-coh : interpWk (wk-id {Γ}) ≡ idf
interpWk-id-coh {Γ = ε} = refl
interpWk-id-coh {Γ = Γ ∙ A} rewrite interpWk-id-coh {Γ} = refl
{-# REWRITE interpWk-id-coh #-}

interpSub : Sub Γ Δ -> interpCtx Γ -> interpCtx Δ
interpSub sub-ε        = const tt
interpSub (sub-ex θ e) = < interpSub θ , interpArr e ； curry (eval ； (_$ absurd)) >

interpSub-mem-arr-coh : (θ : Sub Γ Δ) (i : A ∈ Δ) -> interpArr (sub-mem θ i) ≡ interpSub θ ； interpIn i
interpSub-mem-arr-coh (sub-ex θ e) h =
  funext (\γ -> funext \k -> funext \f -> cong (interpArr e γ k) (absurd-eta f ⊥-elim))
interpSub-mem-arr-coh (sub-ex θ e) (t i) = interpSub-mem-arr-coh θ i

interpWk-mem-coh : (π : Wk Γ Δ) (i : A ∈ Δ) -> interpIn (wk-mem π i) ≡ interpWk π ； interpIn i
interpWk-mem-coh (wk-cong π) h = refl
interpWk-mem-coh (wk-cong π) (t i) rewrite interpWk-mem-coh π i = refl
interpWk-mem-coh (wk-wk π) h rewrite interpWk-mem-coh π h = refl
interpWk-mem-coh (wk-wk π) (t i) rewrite interpWk-mem-coh π (t i) = refl

interpArr-wk-coh : (π : Wk Γ Δ) (e : Δ ⊢ A ->> B) -> interpArr (wk-arr π e) ≡ interpWk π ； interpArr e
interpArr-wk-coh π (covar i) = interpWk-mem-coh π i
interpArr-wk-coh π id = refl
interpArr-wk-coh π bang = refl
interpArr-wk-coh π (e1 ∘ e2) rewrite interpArr-wk-coh π e1 | interpArr-wk-coh π e2 = refl
interpArr-wk-coh π (lift̃ e) rewrite interpArr-wk-coh π e = refl
interpArr-wk-coh π (κ̃ e) rewrite interpArr-wk-coh (wk-cong π) e = refl
{-# REWRITE interpArr-wk-coh #-}

interpSub-wk-coh : (π : Wk Γ Δ) (θ : Sub Δ Ψ) -> interpSub (sub-wk π θ) ≡ interpWk π ； interpSub θ
interpSub-wk-coh π sub-ε = refl
interpSub-wk-coh π (sub-ex θ e) rewrite interpSub-wk-coh π θ | interpArr-wk-coh π e = refl
{-# REWRITE interpSub-wk-coh #-}

interpSub-id-coh : interpSub (sub-id {Γ}) ≡ idf
interpSub-id-coh {Γ = ε} = refl
interpSub-id-coh {Γ = Γ ∙ A} = funext \p -> cong (_, p .proj₂) (happly interpSub-id-coh (p .proj₁))
{-# REWRITE interpSub-id-coh #-}

interpSub-arr-coh : (θ : Sub Γ Δ) (e : Δ ⊢ A ->> B) -> interpArr (sub-arr θ e) ≡ interpSub θ ； interpArr e
interpSub-arr-coh θ (covar i) = interpSub-mem-arr-coh θ i
interpSub-arr-coh θ id = refl
interpSub-arr-coh θ bang = refl
interpSub-arr-coh θ (e1 ∘ e2) rewrite interpSub-arr-coh θ e1 | interpSub-arr-coh θ e2 = refl
interpSub-arr-coh θ (lift̃ e) rewrite interpSub-arr-coh θ e = refl
interpSub-arr-coh θ (κ̃ e) rewrite interpSub-arr-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (covar h)) e = refl

interpEq : Γ ⊢ e1 ≈ e2 ∶ A ->> B -> interpArr e1 ≡ interpArr e2
interpEq (unitl _) = refl
interpEq (unitr _) = refl
interpEq (assoc _ _ _) = refl
interpEq (term f g) = funext \γ -> absurd-eta (interpArr f γ) (interpArr g γ)
interpEq (κ̃-beta f c) rewrite interpSub-arr-coh (sub-ex sub-id c) f = refl
interpEq (κ̃-eta _) = refl
