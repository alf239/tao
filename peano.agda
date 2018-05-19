module Peano where
  open import IPL

  data ℕ : Set where
    zero : ℕ -- Axiom 2.1. 0 is a natural number
    _++ : ℕ → ℕ -- Axiom 2.2. If n is a natural number, then n+ is also a natural number

  data _≡_ : ℕ → ℕ → Set where
    refl : {a : ℕ} → a ≡ a

  axiom23 : {n : ℕ} → ¬ (zero ≡ (n ++))
  axiom23 = λ ()

  axiom24 : {n m : ℕ} → (n ++) ≡ (m ++) → n ≡ m
  axiom24 = {!!}

  _+_ : ℕ → ℕ → ℕ -- Definition 2.2.1
  zero + m = m
  (n ++) + m = (n + m) ++
  
  lemma222 : (n : ℕ) → (zero + n) ≡ n
  lemma222 zero = refl
  lemma222 (n ++) = refl 
