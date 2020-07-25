module Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Relations using (_<_; z<s; s<s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; fromInj₁; fromInj₂ )
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Isomorphismss using (_≃_; extensionality)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x  =  λ ¬x → ¬x x

¬¬-intro′ : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

<-irreflexive : ∀ (n : ℕ) → n < n → ⊥
<-irreflexive (suc n) (_<_.s<s x) = <-irreflexive n x

<-trich : ∀ {m n : ℕ} →
    m < n × ¬ m ≡ n × ¬ n < m
  ⊎ ¬ m < n × m ≡ n × ¬ n < m
  ⊎  ¬ m < n × ¬ m ≡ n × n < m
<-trich {zero} {zero} = inj₂ (inj₁ ⟨ (λ()) , ⟨ refl , (λ()) ⟩ ⟩)
<-trich {zero} {suc n} = inj₁ ⟨ z<s , ⟨ (λ()) , (λ()) ⟩ ⟩
<-trich {suc m} {zero} = inj₂ (inj₂ ⟨ (λ()) , ⟨ (λ()) , z<s ⟩ ⟩)
<-trich {suc m} {suc n} with <-trich {m} {n}
<-trich {suc m} {suc n} | inj₁ ⟨ m<n , ⟨ ¬m≡n , ¬n<m ⟩ ⟩ =
        inj₁ ⟨ (s<s m<n) , ⟨ (λ{ refl → ¬n<m m<n }) , (λ{ (s<s x) → ¬n<m x}) ⟩ ⟩
<-trich {suc m} {suc n} | inj₂ (inj₁ ⟨ ¬m<n , ⟨ m≡n , ¬n<m ⟩ ⟩) =
        inj₂ (inj₁ ⟨ (λ{ (s<s m<n) → ¬m<n m<n}) , ⟨ cong suc (m≡n) , (λ{ (s<s n<m) → ¬n<m n<m}) ⟩ ⟩)
<-trich {suc m} {suc n} | inj₂ (inj₂ ⟨ ¬m<n , ⟨ ¬m≡n , n<m ⟩ ⟩) =
        inj₂ (inj₂ ⟨ (λ{ (s<s m<n) → ¬m<n m<n }) , ⟨ (λ{ refl → ¬m<n n<m }) , s<s n<m ⟩ ⟩)
