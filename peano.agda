module Peano where
  open import IPL

  data ℕ : Set where
    zero : ℕ -- Axiom 2.1. 0 is a natural number
    _++ : ℕ → ℕ -- Axiom 2.2. If n is a natural number, then n++ is also a natural number

  data _≡_ : ℕ → ℕ → Set where
    refl : {a : ℕ} → a ≡ a

  axiom23 : {n : ℕ} → ¬ (zero ≡ (n ++))
  axiom23 = λ ()

  axiom24 : {n m : ℕ} → (n ++) ≡ (m ++) → n ≡ m
  axiom24 refl = refl

  _+_ : ℕ → ℕ → ℕ -- Definition 2.2.1
  zero + m = m
  (n ++) + m = (n + m) ++

  ≡-sec : {n m : ℕ} → n ≡ m → (n ++) ≡ (m ++)
  ≡-sec refl = refl 
  
  lemma222 : (n : ℕ) → (n + zero) ≡ n
  lemma222 zero = refl
  lemma222 (n ++) = ≡-sec (lemma222 n) 

  lemma223 :  (n m : ℕ) → (n + (m ++)) ≡ ((n + m) ++)
  lemma223 zero m = refl
  lemma223 (n ++) m =  ≡-sec (lemma223 n m)
