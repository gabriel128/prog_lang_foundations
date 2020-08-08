module Integers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Induction1 using (+comm; *-comm; identityʳ; *-nullR)


infixl 6 _∸_

-- \bz
data 𝕫 : Set where
  _∸_ : ℕ → ℕ → 𝕫


postulate
  a∸a≡0 : ∀ {a : ℕ} → (a ∸ a) ≡ 0 ∸ 0

infixl 7 _⊞_
infixl 7 _⊠_

-- Equality of Integers
_z≡z_ : 𝕫 → 𝕫 → Set
(a ∸ b) z≡z (c ∸ d) = (a + c ≡ b + d)

_⊞_ : 𝕫 → 𝕫 → 𝕫
(a ∸ b) ⊞ (c ∸ d) = (a + c) ∸ (b + d)

_⊠_ : 𝕫 → 𝕫 → 𝕫
(a ∸ b) ⊠ (c ∸ d)  = (a * c + b * d) ∸ (a * d + b * c)

_ : 𝕫
_ = 6 ∸ 3

_ : (5 ∸ 2) ⊞ (3 ∸ 2) ≡ (8 ∸ 4)
_ =
  begin
    (5 ∸ 2) ⊞ (3 ∸ 2)
  ≡⟨⟩
    (5 + 3) ∸ (2 + 2)
  ≡⟨⟩
    (8 ∸ 4)
  ∎

-- Negation of Integers
-z : 𝕫 → 𝕫
-z (a ∸ b) = (b ∸ a)


-- -- Integers are a commutative Ring
-- (x + y) + z = x + (y + z)
-- (xy)z = x(yz)
-- x*1 = 1*x = x
-- x(y + z) = xy + xz
-- (y + z)x = yx + zx

+zcomm : ∀ {x y : 𝕫} → x ⊞ y ≡ y ⊞ x
+zcomm {a ∸ b} {c ∸ d} =
  begin
    (a + c) ∸ (b + d)
  ≡⟨ cong ((a + c) ∸_) (+comm b d) ⟩
    (a + c) ∸ (d + b)
  ≡⟨ cong (_∸ (d + b)) (+comm a c) ⟩
    (c + a) ∸ (d + b)
  ∎

+z+identity1 : ∀ {x : 𝕫} → x ⊞ (0 ∸ 0) ≡ (0 ∸ 0) ⊞ x
+z+identity1 {x} = +zcomm {x} {(0 ∸ 0)}

+z+identity2 : ∀ {x : 𝕫} → x ⊞ (0 ∸ 0) ≡ x
+z+identity2 {a ∸ b} =
  begin
    (a ∸ b) ⊞ (0 ∸ 0)
  ≡⟨⟩
    (a + 0) ∸ (b + 0)
  ≡⟨ cong ( _∸ (b + 0)) (identityʳ a) ⟩
    a ∸ (b + 0)
  ≡⟨ cong (a ∸_) (identityʳ b) ⟩
    (a ∸ b)
  ∎

+znull : ∀ {x : 𝕫} → x ⊞ (-z x) ≡ (0 ∸ 0)
+znull {a ∸ b} =
  begin
    (a + b) ∸ (b + a)
  ≡⟨ cong ((a + b) ∸_) (+comm b a) ⟩
    (a + b) ∸ (a + b)
  ≡⟨⟩
    (a ∸ a) ⊞ (b ∸ b)
  ≡⟨ cong (_⊞ (b ∸ b)) a∸a≡0  ⟩
    (0 ∸ 0) ⊞ (b ∸ b)
  ≡⟨ cong ((0 ∸ 0) ⊞_ ) a∸a≡0  ⟩
    (0 ∸ 0) ⊞ (0 ∸ 0)
  ≡⟨⟩
    (0 ∸ 0)
  ∎

*-zcomm : ∀ {x y : 𝕫} → x ⊠ y ≡ y ⊠ x
*-zcomm {a ∸ b} {c ∸ d}
  rewrite *-comm a c | *-comm b d | *-comm a d | *-comm b c =
  begin
    c * a + d * b ∸ (d * a + c * b)
  ≡⟨ cong (c * a + d * b ∸_) (+comm (d * a) (c * b)) ⟩
    c * a + d * b ∸ (c * b + d * a)
  ∎

*-identity : ∀ (m : ℕ) → m * 1 ≡ m
*-identity zero = refl
*-identity (suc x) = cong suc (*-identity x)

*-zindentity : ∀ {x : 𝕫} → x ⊠ (1 ∸ 0) ≡ x
-- *-zindentity {a ∸ b} rewrite *-nullR b | *-nullR a | *-identity a | *-identity b | identityʳ a = refl
*-zindentity {a ∸ b} rewrite *-nullR b | *-nullR a | *-identity a =
  begin
    (a + 0) ∸ b * 1
  ≡⟨ {!rewrite *-identity b!} ⟩
    a ∸ b
  ∎
