module Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _>_; _≤_; s≤s; z≤n)
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
even-∃ (even-suc x) | ⟨ n , refl ⟩ = ⟨ n , {!!} ⟩
-- ⟨ (suc n) , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩


even-∃' : ∀ {n : ℕ} → even n → ∃[ m ] (2 * m ≡ n)
odd-∃'  : ∀ {n : ℕ} →  odd n → ∃[ m ] (m * 2 + 1 ≡ n)

open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

n+0 : ∀ {n} → n + zero ≡ n
n+0 {zero} = refl
n+0 {suc n} = cong suc (n+0)

n+1 : ∀ {n} → suc n ≡ n + 1
n+1 {zero} = refl
n+1 {suc n} = cong suc n+1

suc+ : ∀ (m n : ℕ) → m + (suc n) ≡ suc (m + n)
suc+ zero n = refl
suc+ (suc m) n = cong suc (suc+ m n)

n*2 : ∀ {n} → n + n ≡ n * 2
n*2 {zero} = refl
n*2 {suc n} =
  begin
    suc (n + suc n)
  ≡⟨ cong suc (suc+ n n) ⟩
    suc (suc (n + n))
  ≡⟨ cong (suc ∘ suc) (n*2 {n}) ⟩
    suc (suc (n * 2))
  ∎

assoc : ∀ {m n z} → m + (n + z) ≡ m + n + z
assoc {zero} {n} {z} = refl
assoc {suc m} {n} {z} = cong suc assoc

x≤x : ∀ {x} → x ≤ x
x≤x {zero} = z≤n
x≤x {suc x} = s≤s x≤x

postulate
  x≤x+1 : ∀ {x} → x ≤ suc x
  x+→x : ∀ {x} → x ≤ suc x → x ≤ x
  x≤x+y : ∀ (x y : ℕ) → x ≤ y + (suc x)

-- x≤x+y : ∀ (x y : ℕ) → x ≤ y + (suc x)
-- x≤x+y x zero = x≤x+1
-- x≤x+y zero (suc y) = z≤n
-- x≤x+y (suc x) (suc y) with x+→x {x}
-- ...                   | z = s≤s {!!}

+suc : ∀ n → n + suc (n + 0) ≡ n * 2 + 1
+suc zero = refl
+suc (suc n) =
 begin
    suc (n + suc (suc (n + zero)))
  ≡⟨ cong suc (suc+ n (suc (n + zero))) ⟩
    suc (suc (n + (suc (n + zero))))
  ≡⟨ cong (suc ∘ suc) (suc+ (n) (n + zero)) ⟩
    suc (suc (suc (n + (n + zero))))
  ≡⟨ cong (suc ∘ suc ∘ suc) (assoc {n} {n} {zero}) ⟩
     suc (suc (suc (n + n + zero)))
  ≡⟨ cong (suc ∘ suc ∘ suc) (n+0 {n + n}) ⟩
    suc (suc (suc (n + n)))
  ≡⟨ cong (suc ∘ suc ∘ suc) n*2 ⟩
    suc (suc (suc (n * 2)))
  ≡⟨ cong (suc ∘ suc) n+1 ⟩
    suc (suc (n * 2 + 1))
  ∎

even-∃' even-zero = ⟨ zero , refl ⟩
even-∃' (even-suc x) with (odd-∃' x)
even-∃' (even-suc x) | ⟨ n , refl ⟩ = ⟨ suc n , Eq.cong suc (+suc n)  ⟩

∃-+-≤ : ∀ {y z} → y ≤ z → ∃[ x ] (x + y ≡ z)
∃-+-≤ {zero} {z} y≤z = ⟨ z , n+0 ⟩
∃-+-≤ {suc y} {suc z} (s≤s yz) with ∃-+-≤ {y} {z} yz
∃-+-≤ {suc y} {suc .(p + y)} (s≤s yz) | ⟨ p , refl ⟩ = ⟨ p , suc+ p y ⟩

∃-≤-+ : ∀ {y z} → ∃[ x ] (x + y ≡ z) → y ≤ z
∃-≤-+ ⟨ zero , refl ⟩ = x≤x
∃-≤-+ {zero} {.(suc (x + 0))} ⟨ suc x , refl ⟩ = z≤n
∃-≤-+ {suc y} {.(suc (x + suc y))} ⟨ suc x , refl ⟩ = s≤s (x≤x+y y x)

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set} → ∃[ x ] (¬ B x) → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , y ⟩ z = y (z x)
