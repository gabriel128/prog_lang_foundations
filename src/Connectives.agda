module Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import Isomorphismss using (_≃_; _≲_; extensionality; _⇔_)
-- open ≃-Reasoning

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

proj₁ : {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
  { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
  ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
  ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
  ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
  }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
  { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
  ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
  ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
  ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
  }

-- Exercise

⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ (A → B) × (B → A)
⇔≃× = record
  { to = λ x → ⟨ _⇔_.to x , _⇔_.from x ⟩
  ; from = λ x → record { to = proj₁ x ; from = proj₂ x }
  ; from∘to = λ x → refl
  ; to∘from = λ y → η-× y
  }

-- Truth

data ⊤ : Set where

  tt :
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
  { to      = λ{ ⟨ tt , x ⟩ → x }
  ; from    = λ{ x → ⟨ tt , x ⟩ }
  ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
  ; to∘from = λ{ x → refl }
  }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ =
  record
  { to = λ{ ⟨ x , tt ⟩ → x }
  ; from = λ{ x → ⟨ x , tt ⟩}
  ; from∘to = λ{ ⟨ x , tt ⟩ → refl}
  ; to∘from = λ y → refl
  }

-- Disjunction

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
  -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) → case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

⊎-comm : ∀ {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
⊎-comm =
  record
  { to =
       case-⊎
       inj₂
       inj₁
  -- λ{ (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x }
  ; from = λ{ (inj₁ x) → inj₂ x ; (inj₂ x) →  inj₁ x }
  ; from∘to = λ{ (inj₁ x) → refl ; (inj₂ x) → refl }
  ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ x) → refl }
  }

intR : {A B : Set} → A → A ⊎ B
intR = inj₁

intL : {A B : Set} → B → A ⊎ B
intL = inj₂

-- case-⊎ : ∀ {A B C : Set}
  -- → (A → C)
  -- → (B → C)
  -- → A ⊎ B
  -- -----------
  -- → C

⊎-to : ∀ {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
⊎-to (inj₁ (inj₁ x)) = inj₁ x
⊎-to (inj₁ (inj₂ x)) = (inj₂ ∘ inj₁) x
⊎-to {A} {B} {C} (inj₂ x) = (inj₂ ∘ f ∘ inj₁) x
  where
    f = _≃_.to (⊎-comm {C} {B})

⊎-assoc-to : ∀ {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
⊎-assoc-to =
  case-⊎
  (case-⊎
    inj₁
    (intL ∘ intR))
  (inj₂ ∘ inj₂ )

⊎-assoc-from : ∀ {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
⊎-assoc-from = case-⊎ (intR ∘ intR) (case-⊎ (intR ∘ intL) intL)

⊎-from∘to : ∀ {A B C : Set} (x : (A ⊎ B) ⊎ C) → ⊎-assoc-from (⊎-assoc-to x) ≡ x
⊎-from∘to (inj₁ (inj₁ x)) = refl
⊎-from∘to (inj₁ (inj₂ x)) = refl
⊎-from∘to (inj₂ x) = refl

⊎-to∘from : ∀ {A B C : Set} (x : A ⊎ (B ⊎ C)) → ⊎-assoc-to (⊎-assoc-from x) ≡ x
⊎-to∘from (inj₁ x) = refl
⊎-to∘from (inj₂ (inj₁ x)) = refl
⊎-to∘from (inj₂ (inj₂ x)) = refl

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc {A} {B} {C} =
  record
  { to = ⊎-assoc-to
  ; from = ⊎-assoc-from
  ; from∘to = ⊎-from∘to
  ; to∘from = ⊎-to∘from
  }
