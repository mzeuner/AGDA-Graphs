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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; _≢_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_ ; proj₁ ; proj₂)
open import Function.Base using (id)
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
    A : Set a



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



-- count0 : ∀ (n : ℕ) (xs : Vec A n) → count (λ _ → ⊥) xs ≡ 0
-- count0 = ?



count1 : (n : ℕ) (i : Fin n) → count (_≟ i) (allFin n) ≡ 1
count1 ℕ.zero ()
count1 (ℕ.suc n₁) Fin.zero = cong ℕ.suc {!!}
count1 (ℕ.suc n₁) (Fin.suc i) = {!count1 _ i!}



-- countf1 : (n : ℕ) (i : Fin n) (f : Fin n ⤖ Fin n) → count (λ j → f j ≡ i) allFin ≡ 1
-- countf1 = ?



-- count⊎ : ∀ {P : Pred A p} {Q : Pred A q} (P : Decidable) (Q : Decidable) (xs : Vec A n) → count (P ⊎ Q) xs ≡ count P xs + count Q xs ∸ count (P × Q) xs
-- count⊎ = ?



cycle|E| : ∀ (n : ℕ) → 2|E| (3+ n cycle) ≡ (3 + n) * 2
cycle|E| ℕ.zero = refl
cycle|E| (ℕ.suc n₁) = {!!}
