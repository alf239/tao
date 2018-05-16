data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {n m : ℕ} → n ≤ m → suc n ≤ suc m

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)
