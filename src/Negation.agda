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

<-irreflexive : ∀ (n : ℕ) → ¬ n < n
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

⊎-dual-× : {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
  { to = λ{¬aorb → ⟨ (λ a → ¬aorb (inj₁ a) ) , (λ b → ¬aorb (inj₂ b)) ⟩}
  ; from = λ{ ⟨ fst , snd ⟩ (inj₁ x) → fst x ; ⟨ fst , snd ⟩ (inj₂ y) → snd y}
  ; from∘to = λ{ x → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl}}
  ; to∘from = λ{ y → refl}
  }

-- Excluded Middle

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ λ x → k (inj₁ x))

excl-mid : ∀ (A : Set) → Set
excl-mid A = A ⊎ ¬ A

¬¬-elim : ∀ (A : Set) → Set
¬¬-elim A = ¬ ¬ A → A

morgan : ∀ (A B : Set) → Set
morgan A B =  ¬ (¬ A × ¬ B) → A ⊎ B

pierceLaw : ∀ (A B : Set) → Set
pierceLaw A B = ((A → B) → A) → A

→as⊎ : ∀ (A B : Set) → Set
→as⊎ A B = (A → B) → ¬ A ⊎ B

vacuos : ∀ {A : Set} → ¬ A → (∀ {B : Set} → A → B)
vacuos ¬a a = ⊥-elim (¬a a)

em→¬¬elim : (∀ {A : Set} → excl-mid A) → ∀ {A : Set} → ¬¬-elim A
em→¬¬elim exm {A} y with exm {A}
em→¬¬elim exm {A} y | inj₁ x = x
em→¬¬elim exm {A} y | inj₂ ¬a = ⊥-elim (y ¬a)

¬¬-elim→morgan : (∀ {A : Set} → ¬¬-elim A) → ∀ {A B : Set} → morgan A B
¬¬-elim→morgan elim {A} {B} y = elim λ x → x (elim (λ z → y ⟨ (λ x → z (inj₁ x)) , (λ x → z (inj₂ x)) ⟩))

morgan→elim  : (∀ {A B : Set} →  morgan A B) → ∀ {A : Set} → ¬¬-elim A
morgan→elim morgan {A} y with em {A}
morgan→elim morgan {A} y | inj₁ x = x
morgan→elim morgan {A} y | inj₂ y₁ = ⊥-elim (y y₁)

¬¬elim→pierceLaw : (∀ {A : Set} → ¬¬-elim A) → ∀ {A B : Set} → pierceLaw A B
¬¬elim→pierceLaw ¬¬aToa {A} {B} y = ¬¬aToa λ ¬a → ¬a (y (vacuos ¬a))

pierceLawImplies→as⊎ : (∀ {A B : Set} →  pierceLaw A B) → ∀ {A B : Set} → →as⊎ A B
pierceLawImplies→as⊎ pierce {A} {B} a→b = pierce λ x → inj₁ λ a → x (inj₂ (a→b a))

identity : ∀{A : Set} → A → A
identity x = x

→as⊎impliesExm :  (∀ {A B : Set} → →as⊎ A B) → ∀ {A : Set} → excl-mid A
→as⊎impliesExm asu with (asu identity)
→as⊎impliesExm asu | inj₁ x = inj₂ x
→as⊎impliesExm asu | inj₂ y = inj₁ y
