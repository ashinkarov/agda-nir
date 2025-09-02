{-# OPTIONS --guardedness #-}
open import Data.Product hiding (map; zip)
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.List as L using (List; []; _∷_) 
open import Function

-- State monad from the Standard Library
open import Effect.Monad 
open import Effect.Monad.State
open RawMonadState {{...}}
open RawMonad {{...}} hiding (_⊗_; zip)
instance
  _ = monad
  _ = monadState 


module _ where

-- Agda streams
module AgdaS where

  -- Classic definition of a stream
  record Stream (X : Set) : Set where
    coinductive
    field
      head : X
      tail : Stream X

  open Stream


  variable
    X Y Z S : Set

  -- Prefix of a stream
  take : ℕ → Stream X → List X
  take zero xs = []
  take (suc n) xs = xs .head ∷ take n (xs .tail)

  -- Stream where all the elements are set to `x` (the argument of K) 
  K : X → Stream X
  K x .head = x
  K x .tail = K x

  -- Shortcuts for the types
  --State : Set → Set → Set
  --State S X = S → S × X

  Trans : Set → Set → Set
  Trans X Y = Stream X → Stream Y

  -- Map the function to all elements of the stream
  map : (X → Y) → Trans X Y
  map f xs .head = f (xs .head)
  map f xs .tail = map f (xs .tail)


  zip : Stream X → Stream Y → Stream (X × Y)
  zip xs ys .head = xs .head , ys .head
  zip xs ys .tail = zip (xs .tail) (ys .tail)

  split : Stream X → Stream X × Stream X 
  split xs .proj₁ = xs
  split xs .proj₂ = xs

  data Types : ℕ → Set₁ where
    [_] : Set → Types 0
    _∷_ : ∀ {n} → Set → Types n → Types (suc n)

  data Streams : {n : ℕ} → Types n → Set₁ where
    [_] : Stream X → Streams [ X ]
    _∷_ : ∀ {n}{t : Types n}{X} → Stream X → Streams t → Streams (X ∷ t)

  prod : ∀ {n} → Types n → Set
  prod [ x ] = x
  prod (x ∷ ts) = x × prod ts

  zip-n : ∀ {n}{ts : Types n} → Streams ts → Stream (prod ts)
  zip-n [ s ] = s
  zip-n (x ∷ ss) = zip x (zip-n ss)
   

  -- Feedback combinator maps a stateful function over
  -- a stream as follows:
  --
  --   x : Stream
  --   x = x₀ x₁ x₂ ...
  -- 
  --   i : inital state value
  --   f : stateful function
  --
  --   s₀ y₀ = f x₀ i
  --   s₁ y₁ = f x₁ s₀
  --   s₂ y₂ = f x₂ s₁
  --   ...
  --   
  --   => y₀ y₁ y₂ ...
  --
  feed : (f : X → State S Y) (i : S) → Trans X Y
  feed f i xs .head = runState (f (xs .head)) i .proj₂
  feed f i xs .tail = feed f (runState (f (xs .head)) i .proj₁)
                             (xs .tail)

  -- Something like a leaky example we discussed (very much simplified).
  leaky : Stream ℕ → Stream ℕ
  leaky = feed LI 0  --  map (_+ 1) ∘ feed LI 0 ∘ map (_* 2)
    where
      -- State counts the number of steps from the last
      -- reset and resets when the numbers is >= 2.
      LI : ℕ → State ℕ ℕ
      --LI n s = if s <ᵇ 2 then (1 + s , 0) else (0 , n) 
      LI n = do
        s ← get
        case (s <ᵇ 2) of λ where
          true → do
            put (1 + s)
            return 0
          false → do
            put 0
            return n

  -- Stream of natural numbers
  nats : ℕ → Stream ℕ
  nats n .head = n
  nats n .tail = nats (1 + n)

  -- Example of applying leaky, comutes:
  --   0 ∷ 0 ∷ 3 ∷ 0 ∷ 0 ∷ 6 ∷ 0 ∷ 0 ∷ 9 ∷ 0 ∷ []
  ex = take 10 (leaky (nats 1))


-- This is a very rough sketch how the langauge of functions
-- and boxes can be formalised.  We can discuss what else is
-- needed, and we can significantly improve this.
module Lang where

  infixr 5 _⇒_
  data Ty : Set where
    unit : Ty
    nat bool : Ty -- whatever base types
    stream : Ty → Ty
    _⊗_ : Ty → Ty → Ty
    _⇒_ : Ty → Ty → Ty

  variable
    τ σ δ : Ty

  -- I am inlining state definition so that we have less
  -- objects in the language.  We might reconsider this later.
  state : Ty → Ty → Ty
  state σ τ = σ ⇒ (σ ⊗ τ)

  infixl 5 _`$_
  data E (V : Ty → Set) : Ty → Set where
    `_     : V τ → E V τ
    `plus  : E V (nat ⇒ nat ⇒ nat)
    `lt  : E V (nat ⇒ nat ⇒ bool)
    `ifte : E V bool → E V τ → E V τ → E V τ
    `nat  : ℕ → E V nat
    _`$_  : E V (τ ⇒ σ) → E V τ → E V σ
    `lam  : (V τ → E V σ) → E V (τ ⇒ σ)
    `pair : E V τ → E V σ → E V (τ ⊗ σ)
    `fst : E V (τ ⊗ σ) → E V τ
    `snd : E V (τ ⊗ σ) → E V σ
    `tt : E V unit
    -- We can have lets to share variables if we need them
    -- but let's think about this later.
    --`let : E V τ → E V (τ ⇒ σ) → E V σ

  variable
    V : Ty → Set

  -- State monad combinators implemented within the language
  `ret  : E V (τ ⇒ state σ τ)
  `ret = `lam λ t → `lam λ s → `pair (` s) (` t)

  `get  : E V (state σ σ)
  `get = `lam λ s → `pair (` s) (` s)

  `put  : E V (σ ⇒ state σ unit)
  `put = `lam λ s → `lam λ _ → `pair (` s) `tt

  _`>>=_ : E V (state σ τ) → E V (τ ⇒ state σ δ) → E V (state σ δ)
  --v `>>= f = `lam λ s → `let (v `$ ` s) (`lam λ x → (f `$ `snd (` x) `$ `fst (` x)))
  v `>>= f = `lam λ s →  ((f `$ `snd (v `$ ` s) `$ `fst (v `$ ` s)))


  data Box (V : Ty → Set) : Ty → Set where
    `zip : Box V (stream τ ⇒ stream σ ⇒ stream (τ ⊗ σ)) 
    `split : Box V (stream τ ⇒ (stream τ ⊗ stream τ))
    `map : E V (τ ⇒ σ) → Box V (stream τ ⇒ stream σ)
    `feed : E V (τ ⇒ state σ δ) → E V σ → Box V (stream τ ⇒ stream δ)
    _`∘_ : Box V (stream δ ⇒ stream σ) → Box V (stream τ ⇒ stream δ)
         → Box V (stream τ ⇒ stream σ)
     
  -- leaky-like example expressed in the DSL of E and Box
  `leaky : Box V (stream nat ⇒ stream nat)
  `leaky = `feed (`lam λ n → `get 
                  `>>= `lam λ s → `ifte  (`lt `$ ` s `$ `nat 2) 
                                         ((`put `$ (`plus `$ `nat 1 `$ ` s))
                                          `>>= `lam λ _ → `ret `$ `nat 0 )
                                         ((`put `$ `nat 0)
                                          `>>= `lam λ _ → `ret `$ ` n))
                 (`nat 0)


-- Here is how we interpret our Langauge as Agda Streams
module Interp where    
  open import Effect.Monad.State.Transformer using (mkStateT)
  open import Effect.Monad.Identity using (mkIdentity)
  open Lang
  open AgdaS hiding (leaky)

  ⟦_⟧ : Ty → Set
  ⟦ unit ⟧ = ⊤
  ⟦ nat ⟧ = ℕ
  ⟦ bool ⟧ = Bool
  ⟦ stream τ ⟧ = Stream ⟦ τ ⟧
  ⟦ τ ⊗ σ ⟧ = ⟦ τ ⟧ × ⟦ σ ⟧
  ⟦ τ ⇒ σ ⟧ = ⟦ τ ⟧ → ⟦ σ ⟧

  ⟦_⟧ᵉ : E ⟦_⟧ τ → ⟦ τ ⟧
  ⟦_⟧ᵇ : Box ⟦_⟧ τ → ⟦ τ ⟧

  ⟦ `zip ⟧ᵇ = zip
  ⟦ `split ⟧ᵇ = split
  ⟦ `map f ⟧ᵇ = map ⟦ f ⟧ᵉ
  ⟦ `feed f s ⟧ᵇ =
    -- Just some wrappers from stdlib
    feed (λ t → mkStateT λ s → mkIdentity (⟦ f ⟧ᵉ t s)) ⟦ s ⟧ᵉ
  ⟦ b `∘ c ⟧ᵇ = ⟦ b ⟧ᵇ ∘ ⟦ c ⟧ᵇ

  ⟦ ` x ⟧ᵉ = x
  ⟦ `plus ⟧ᵉ = _+_
  ⟦ `lt ⟧ᵉ = _<ᵇ_
  ⟦ `ifte p t f ⟧ᵉ = if ⟦ p ⟧ᵉ then ⟦ t ⟧ᵉ else ⟦ f ⟧ᵉ
  ⟦ `nat x ⟧ᵉ = x
  ⟦ e `$ e₁ ⟧ᵉ = ⟦ e ⟧ᵉ ⟦ e₁ ⟧ᵉ
  ⟦ `lam f ⟧ᵉ x = ⟦ f x ⟧ᵉ 
  ⟦ `pair e e₁ ⟧ᵉ = ⟦ e ⟧ᵉ , ⟦ e₁ ⟧ᵉ
  ⟦ `fst e ⟧ᵉ = ⟦ e ⟧ᵉ .proj₁
  ⟦ `snd e ⟧ᵉ = ⟦ e ⟧ᵉ .proj₂
  ⟦ `tt ⟧ᵉ = tt

  -- Sanity check: normalise Interp.leaky and it should look
  -- like AgdaS.leaky.
  leaky = ⟦ `leaky ⟧ᵇ


-- A straight-forward way to traverse PHOAS representation
-- for primitive "compilation"
module Show where

  import Data.Nat.Show as ℕ
  open import Data.String hiding (show)
  open import Text.Printf
  open Lang

  fresh : ℕ → String
  fresh = printf "x%u"
 
  -- We just represent variables as natural numbers, and we
  -- do not carry any other information.
  show : E (const ℕ) τ → State ℕ String
  show (` x) = return (fresh x)
  show `plus = return "plus"
  show `lt = return "lt"
  show (`ifte e e₁ e₂) = do
    p ← show e
    t ← show e₁
    f ← show e₂
    return (printf "if (%s) then (%s) else (%s)" p t f)
  show (`nat x) = return (ℕ.show x)
  show (e `$ e₁) = do
    f ← show e
    x ← show e₁
    return (printf "(%s) (%s)" f x)
  show (`lam e) = do
    -- get the current counter of fresh variables
    n ← get
    -- increase it in the state
    modify suc
    -- make a name of the argument
    let x = fresh n
    b ← show (e n)
    return (printf "λ %s → (%s)" x b)

  show (`pair e e₁) = do
    x ← show e
    y ← show e₁
    return (printf "(%s) , (%s)" x y)
  show (`fst e) = do
    x ← show e
    return (printf "fst (%s)" x)
  show (`snd e) = do
    x ← show e
    return (printf "snd (%s)" x)
  show `tt = return "tt"

  ex : E V (nat ⇒ state nat nat)
  ex = (`lam λ n → `get 
                  `>>= `lam λ s → `ifte  (`lt `$ ` s `$ `nat 2) 
                                         ((`put `$ (`plus `$ `nat 1 `$ ` s))
                                          `>>= `lam λ _ → `ret `$ `nat 0 )
                                         ((`put `$ `nat 0)
                                          `>>= `lam λ _ → `ret `$ ` n))

  -- Works, but gets an ugly result
  test = runState (show ex) 0 .proj₂

  -- I didn't do this for Box, but it is even simpler,
  -- as there are no variable binders.


-- Here I tried to get away with hacky implementation of
-- normalisation by evaluation.  It almost works, but maybe
-- we want to do this properly, or maybe just use deep embedding.
module Opts where

  open import Relation.Binary.PropositionalEquality
  import Data.Nat.Show as ℕ
  open import Data.String hiding (show)
  open import Text.Printf
  open Lang

  fresh : ℕ → String
  fresh = printf "x%u"
  
  Val : Ty → Set
  Val (τ ⇒ σ) = Val τ → State ℕ (Val σ)
  Val (τ ⊗ σ) = Val τ × Val σ
  Val _ = String

  to-val : E Val τ → State ℕ (Val τ)
  toS : Val τ → State ℕ String
  fromS : String → Val τ

  to-val (` x) = return x
  to-val `plus = return λ x → return λ y → return (printf "%s + %s" x y)
  to-val `lt = return λ x → return λ y → return (printf "%s <ᵇ %s" x y)
  to-val (`ifte p t f) = do
    ps ← to-val p
    tv ← to-val t
    fv ← to-val f
    ts ← toS tv
    fs ← toS fv
    return (fromS (printf "if (%s) then (%s) else (%s)" ps ts fs))
  to-val (`nat x) = return (ℕ.show x)
  --to-val (`ifte p t f `$ e₁) = to-val (`ifte p (t `$ e₁) (f `$ e₁))
  to-val (e `$ e₁) = do
    f ← to-val e
    x ← to-val e₁
    f x
  to-val (`lam f) = return λ x → to-val (f x)
  to-val (`pair e e₁) = do
    x ← to-val e
    y ← to-val e₁
    return (x , y)
  to-val (`fst (`ifte p t f)) = do
    p′ ← to-val p
    t′ ← to-val (`fst t) >>= toS
    f′ ← to-val (`fst f) >>= toS
    return (fromS (printf "if %s then %s else %s" p′ t′ f′))

  --to-val (`fst (`let x b)) = to-val (`let x (`lam λ t → `fst (b `$ ` t)))
  to-val (`fst e) = proj₁ <$> to-val e

  to-val (`snd (`ifte p t f)) = do
    p′ ← to-val p
    t′ ← to-val (`snd t) >>= toS
    f′ ← to-val (`snd f) >>= toS
    return (fromS (printf "if %s then %s else %s" p′ t′ f′))
  to-val (`snd e) = proj₂ <$> to-val e
  to-val `tt = return "tt"
  --to-val (`let e e₁) = do
  --  n ← get
  --  modify suc
  --  let x = fresh n
  --  v ← to-val e
  --  b ← to-val e₁
  --  vs ← toS v
  --  b′ ← b (fromS x) 
  --  bs ← toS b′
  --  return (fromS (printf "let %s := %s in\n%s" x vs bs))

  toS {unit} v = return v
  toS {nat} v = return v
  toS {bool} v = return v
  toS {stream τ} v = return v
  toS {τ ⊗ τ₁} (v , w) = do
    l ← toS v
    r ← toS w
    return (printf "(%s , %s)" l r)
  toS {τ ⇒ σ} f = do
    n ← get
    modify suc
    let x = fresh n
    v ← f (fromS {τ} x)
    v ← toS v
    return (printf "λ %s → (%s)" x v)

  fromS {unit} s = s
  fromS {nat} s = s
  fromS {bool} s = s
  fromS {stream τ} s = s
  fromS {τ ⊗ σ} s = fromS (printf "fst (%s)" s) , fromS (printf "snd (%s)" s)
  fromS {τ ⇒ σ} s x = do
    x ← toS x
    return (fromS (printf "(%s) (%s)" s x))

  test₁ : E V (state nat (nat ⇒ nat))
  test₁ = `get `>>= `lam λ x →
         (`put `$ (`plus `$ ` x `$ `nat 1)) `>>= `lam λ _ → 
         `ifte  (`lt `$ ` x `$ `nat 0) 
                (`ret `$ `lam λ y → ` x) 
                (`ret `$ `lam λ z → ` z) 

  test₂ : E V (state nat nat)
  test₂ = `get `>>= `lam λ x → (`put `$ ` x) `>>= `lam λ _ → `ret `$ `nat 5

  test₃ :  E V (nat ⇒ state nat nat)
  test₃ = (`lam λ n → `get 
           `>>= `lam λ s → `ifte (`lt `$ ` s `$ `nat 2) 
                                 ((`put `$ (`plus `$ `nat 1 `$ ` s))
                                  `>>= `lam λ _ → `ret `$ `nat 0 )
                                 ((`put `$ `nat 0)
                                    `>>= `lam λ _ → `ret `$ ` n))


  ret = runState (toS {τ = nat ⇒ state nat (nat )} (runState (to-val test₃) 0 .proj₂)) 0 .proj₂


  -- This is just my copy-pasting of the generaterd code back into Agda.
  variable
    A B : Set

  fst : A × B → A
  fst = proj₁
  snd : A × B → B
  snd = proj₂

  -- The thing here is that it eta-expands the pair of functions,
  -- and therefore inlines the big if.  Below, you can see that
  -- the two expressions are actually equal.
  qq : ℕ → ℕ → (ℕ × ℕ)
  qq = λ x0 → (λ x1 → ((fst ((if (x1 <ᵇ 2) then (λ x2 → ((1 + x1 , 0))) else (λ x3 → ((0 , x0)))) (x1)) , snd ((if (x1 <ᵇ 2) then (λ x2 → ((1 + x1 , 0))) else (λ x3 → ((0 , x0)))) (x1)))))

  qq′ : ℕ → ℕ → (ℕ × ℕ)
  qq′ = λ x0 x1 → ((if (x1 <ᵇ 2) then (λ x2 → ((1 + x1 , 0))) else (λ x3 → ((0 , x0)))) (x1))

  _ : qq ≡ qq′
  _ = refl



