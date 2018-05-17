module Peano where
  data ℕ : Set where
    zero : ℕ         -- Axiom 2.1. 0 is a natural number
    suc : ℕ → ℕ   -- Axiom 2.2. If n is a natural number, then n++ is also a natural number.

  data _≡_ : ℕ → ℕ → Set where
    x≡x : {n : ℕ} → n ≡ n
    x≡y : {n m : ℕ} → n ≡ m → m ≡ n
    x≡y≡z : {n m k :  ℕ} → n ≡ m → m ≡ k → n ≡ k

  data _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {n m : ℕ} → n ≤ m → suc n ≤ suc m

  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  (suc m) + n = suc (m + n)
