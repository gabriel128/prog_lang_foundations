module Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _>_; s≤s; z≤n)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Isomorphismss using (_≃_; extensionality)

∀-elim : ∀ {A : Set} {B : A → Set} → (L : ∀ (x : A) → B x) → (M : A) → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
              (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
  {
  to = λ A→BxC → ⟨ proj₁ ∘ A→BxC , proj₂ ∘ A→BxC ⟩
  ; from = λ{ ⟨ A→B , A→C ⟩ A → ⟨ A→B A , A→C A ⟩}
  ; from∘to = λ x → refl
  ; to∘from = λ y → refl
  }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ A→B) = inj₁ ∘ A→B
⊎∀-implies-∀⊎ (inj₂ A→C) = inj₂ ∘ A→C


⊎∀-impliesConv-∀⊎ : ∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x ⊎ C x) → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
⊎∀-impliesConv-∀⊎ x = {!!}


-- Existensials

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B


∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
  ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set} → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
              ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ {A} =
  record
  { to = λ{ ⟨ x , inj₁ z ⟩ → inj₁ ⟨ x , z ⟩ ; ⟨ x , inj₂ y ⟩ → inj₂ ⟨ x , y ⟩}
  ; from = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ x , (inj₁ y) ⟩ ; (inj₂ ⟨ x , y ⟩) → ⟨ x , inj₂ y ⟩}
  ; from∘to = λ{ ⟨ x , inj₁ x₁ ⟩ → refl ; ⟨ x , inj₂ y ⟩ → refl}
  ; to∘from = λ{ (inj₁ ⟨ x , x₁ ⟩) → refl ; (inj₂ ⟨ x , x₁ ⟩) → refl}
  }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
                ∃[ x ] (B x × C x) →
                (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , ⟨ fst , snd ⟩ ⟩ = ⟨ ⟨ x , fst ⟩ , ⟨ x , snd ⟩ ⟩


-- Can't hold
-- ∃×-implies-×∃' : ∀ {A : Set} {B C : A → Set} →
--                 (∃[ x ] B x) × (∃[ x ] C x) →
--                  ∃[ x ] (B x × C x)
-- ∃×-implies-×∃' ⟨ ⟨ x , y ⟩ , ⟨ z , p ⟩ ⟩ = ⟨ x , ⟨ y , {!λ()!} ⟩ ⟩
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

∀-× : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
∀-× =
  record
  { to = λ{ x → ⟨ x aa , ⟨ x bb , x cc ⟩ ⟩ }
  ; from = λ{ ⟨ fst , snd ⟩ aa → fst ; ⟨ fst , snd ⟩ bb → proj₁ snd ; ⟨ fst , snd ⟩ cc → proj₂ snd}
  ; from∘to = λ x → {!!}
  ; to∘from = λ y → refl
  }

∃-⊎ : ∀ {B : Tri → Set} → (∃[ x ] B x) ≃ (B aa ⊎ B bb ⊎ B cc)
∃-⊎ =
  record
  { to = λ{ ⟨ aa , y ⟩ → inj₁ y ; ⟨ bb , y ⟩ → inj₂ (inj₁ y) ; ⟨ cc , y ⟩ → inj₂ (inj₂ y) }
  ; from = λ{ (inj₁ x) → ⟨ aa , x ⟩ ; (inj₂ (inj₁ x)) → ⟨ bb , x ⟩ ; (inj₂ (inj₂ y)) → ⟨ cc , y ⟩ }
  ; from∘to = λ{ ⟨ aa , x₁ ⟩ → refl ; ⟨ bb , x₁ ⟩ → refl ; ⟨ cc , x₁ ⟩ → refl}
  ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ y)) → refl}
  }

_ :  ∃[ m ] (m > 1)
_ = ⟨ suc (suc zero) , s≤s (s≤s Data.Nat.z≤n) ⟩

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ {n : ℕ}
    → odd n
    ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
    -----------
    → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero = ⟨ zero , refl ⟩
even-∃ (even-suc x) with (odd-∃ x)
even-∃ (even-suc x) | ⟨ n , refl ⟩ = ⟨ (suc n) , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩
