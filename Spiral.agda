module Spiral where

open import Data.Nat
  using (ℕ; suc; zero; _+_; _*_)
open import Data.Nat.Properties
  using ()
open import Data.Product
  using (Σ; _,_; _×_; proj₁; swap)
open import Data.Vec
  using (Vec; []; _∷_; _++_; map; reverse; unzip)
open import Function
  using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym)

open Data.Nat.Properties.SemiringSolver
  using (solve; _:=_; con; _:+_; _:*_)

-- The type of matrices of size m × n.
Matrix : ∀ {a} → Set a → ℕ → ℕ → Set a
Matrix A m n = Vec (Vec A n) m

-- Replicates a value n times.
pure : ∀ {n a} {A : Set a} → A → Vec A n
pure {zero}  _ = []
pure {suc _} x = x ∷ pure x

-- Spilts a matrix into first column and the rest.
split : ∀ {a m n} {A : Set a} → Matrix A m (suc n) → Vec A m × Matrix A m n
split = unzip ∘ map λ {(x ∷ xs) → x , xs}

-- Rotates a matrix 90° clockwise.
rotate : ∀ {m n a} {A : Set a} → Matrix A m n → Matrix A n m
rotate {_}     {zero}  _ = []
rotate {zero}  {_}     _ = pure []
rotate {suc _} {suc _} x with split x
... | xs , xss = reverse xs ∷ rotate xss

-- Writer monad.
module Writer where
  infixl 1 _>>=_
  infixr 1 _>=>_

  return : ∀ {a b} {A : Set a} {B : Set b} → A → A × Vec B 0
  return a = a , []

  _>>=_ : ∀ {m n a b c} {A : Set a} {B : Set b} {C : Set c} →
          A × Vec C m → (A → B × Vec C n) → B × Vec C (m + n)
  a , cs₁ >>= f with f a
  ... | b , cs₂ = b , cs₁ ++ cs₂

  _>=>_ : ∀ {m n a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
          (A → B × Vec D m) → (B → C × Vec D n) → (A → C × Vec D (m + n))
  f >=> g = λ x → f x >>= g

  liftM : ∀ {m a b c} {A : Set a} {B : Set b} {C : Set c} →
          (f : A → B) → A × Vec C m → B × Vec C m
  liftM f (a , cs) = f a , cs

open Writer

-- Few useful lemmas.
*-zero = solve 1 (λ m → m :* 0′ := 0′) refl
  where
  0′ = con 0

lem₁ = solve 2 (λ m n →
  4′ :+ 2′ :* m :+ 2′ :* n
    := 2′ :+ m :+ (1′ :+ n :+ (1′ :+ m :+ n))) refl
  where
  1′ = con 1
  2′ = con 2
  4′ = con 4

lem₂ = solve 2 (λ m n → m :+ 0′ :* n := m) refl
  where
  0′ = con 0

lem₃ = solve 1 (λ m → m :* 1′ := m) refl
  where
  1′ = con 1

lem₄ = solve 2 (λ m n →
  (2′ :+ m) :* (2′ :+ n)
    := (4′ :+ 2′ :* m :+ 2′ :* n) :+ m :* n) refl
  where
  2′ = con 2
  4′ = con 4

-- Variant of 'split' that rotates the rest of matrix 90° clockwise.
splitR : ∀ {m n a} {A : Set a} → Matrix A m (suc n) → Matrix A n m × Vec A m
splitR = liftM rotate ∘ swap ∘ split

-- Splits a matrix into outer edge and inner core.
outer : ∀ {m n a} {A : Set a} →
        Matrix A (2 + m) (2 + n) → Matrix A m n × Vec A (4 + 2 * m + 2 * n)
outer {m} {n} rewrite lem₁ m n = splitR >=> splitR >=> splitR >=> splitR

-- Produces a spiral of matrix by repeatedly applying 'outer'.
spiral : ∀ {m n a} {A : Set a} → Matrix A m n → Vec A (m * n)
spiral {zero}        {_}           as      = []
spiral {suc m}       {zero}        as      rewrite *-zero m = []
spiral {suc zero}    {suc zero}    (a ∷ _) = a
spiral {suc zero}    {suc (suc n)} (a ∷ _) rewrite lem₂ n (2 * n) = a
spiral {suc (suc m)} {suc zero}    as      rewrite lem₃ m = proj₁ (split as)
spiral {suc (suc m)} {suc (suc n)} as with outer as
... | i , o rewrite lem₄ m n = o ++ spiral i
