{-# OPTIONS --with-K #-}
module EdgeCountCycle where

open import Data.Nat using (ℕ)
open import Data.Nat.Base using (_/_; _*_; _+_; _∸_)
open import Data.Nat.Properties using (1+n≢n; 1+n≢0)
open import Data.Fin using (Fin)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Fin.Base using (toℕ; fromℕ; inject₁; cast; pred)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-fromℕ; _≟_; 0≢1+n)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; tabulate; sum; allFin; count)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; _≢_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_ ; proj₁ ; proj₂)
open import Function.Base
open import Relation.Nullary.Negation.Core using (_¬-⊎_)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_)
open import Function.Bundles using (_⤖_ ; _⇔_)
open import Relation.Unary using (Pred; Decidable ; _≐_)
open import Level using (Level)
open import Graphs
open import Cycles
open Dec
open EnumeratedFiniteGraph


private
  variable
    a p q : Level
    A B : Set a



-- countExtensionality :
module _ {P Q : Pred A p} (P? : Decidable P) (Q? : Decidable Q) where
  countExt : P ≐ Q → ∀ {n : ℕ} (xs : Vec A n) → count P? xs ≡ count Q? xs
  countExt P≐Q {ℕ.zero} [] = refl
  countExt P≐Q {ℕ.suc n₁} (x ∷ xs) with P? x | Q? x
  ... | (yes Px) | (yes Qx) = cong ℕ.suc (countExt P≐Q xs)
  ... | (yes Px) | (no ¬Qx) = ⊥-elim (¬Qx (P≐Q .proj₁ Px))
  ... | (no ¬Px) | (yes Qx) = ⊥-elim (¬Px (P≐Q .proj₂ Qx))
  ... | (no ¬Px) | (no ¬Qx) = countExt P≐Q xs


{- postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
-}

-- composing with a function:

compLemma : {P : Pred B p} (P? : Decidable P) (f : A → B) {n : ℕ} (g : Fin n → A)
          → count P? (tabulate (f ∘ g)) ≡ count (P? ∘ f) (tabulate g)
compLemma P? f {ℕ.zero} g = refl
compLemma P? f {ℕ.suc n₁} g with does (P? (f (g Fin.zero)))
... | true = cong ℕ.suc (compLemma P? f (g ∘ Fin.suc))
... | false = compLemma P? f (g ∘ Fin.suc)

-- count0 : ∀ (n : ℕ) (xs : Vec A n) → count (λ _ → ⊥) xs ≡ 0
-- count0 = ?



count1 : (n : ℕ) (i : Fin n) → count (_≟ i) (allFin n) ≡ 1
count1 ℕ.zero ()
count1 (ℕ.suc n₁) Fin.zero = cong ℕ.suc {!!}
count1 (ℕ.suc n₁) (Fin.suc i) =
  trans (compLemma (_≟ Fin.suc i) Fin.suc id)
        (trans (countExt (λ j →  Fin.suc j ≟ Fin.suc i) (_≟ i) {!!} (allFin n₁))
               (count1 _ i))

countMinus1 : (n : ℕ) (i : Fin (3 + n)) → count (λ j → minus1 j ≟ i) (allFin _) ≡ 1
countMinus1 ℕ.zero Fin.zero = refl
countMinus1 ℕ.zero (Fin.suc Fin.zero) = refl
countMinus1 ℕ.zero (Fin.suc (Fin.suc Fin.zero)) = refl


countMinus1 (ℕ.suc n₁) Fin.zero = cong ℕ.suc (trans (sym (compLemma (_≟ Fin.zero) (minus1 {n = ℕ.suc n₁}) λ i → Fin.suc (Fin.suc (Fin.suc i)))) {!!})
countMinus1 (ℕ.suc n₁) (Fin.suc i) = {!!}

-- countf1 : (n : ℕ) (i : Fin n) (f : Fin n ⤖ Fin n) → count (λ j → f j ≡ i) allFin ≡ 1
-- countf1 = ?



-- count⊎ : ∀ {P : Pred A p} {Q : Pred A q} (P : Decidable) (Q : Decidable) (xs : Vec A n) → count (P ⊎ Q) xs ≡ count P xs + count Q xs ∸ count (P × Q) xs
-- count⊎ = ?



-- cycle|E| : ∀ (n : ℕ) → 2|E| (3+ n cycle) ≡ (3 + n) * 2
-- cycle|E| ℕ.zero = refl
-- cycle|E| (ℕ.suc n₁) = begin
--                         (deg (3+ (ℕ.suc n₁) cycle) Fin.zero + sum (tabulate {n₁} (deg ∘ suc)))
--                       ≡⟨ ? ⟩
--                        (2 + (3 + n₁) * 2)
--                       ∎
